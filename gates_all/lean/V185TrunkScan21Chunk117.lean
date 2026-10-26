import V185TrunkScan21Chunk116

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1421772 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1421772 : Nat := 118140960795 + 1421772 * 2 ^ 59
def prefixEnd_1421772 : Nat := 4983230072969 + 3 ^ 40 * 1421772 * 2
def baseEnd_1421772 : Nat := 324467740935251797427287

theorem tailTrace_1421772 : CollatzResearch.WordTrace tailWord_1421772 prefixEnd_1421772 324467740935251797427287 := by
  unfold tailWord_1421772
  simp only [CollatzResearch.WordTrace]
  refine ⟨25928142502585169085437785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34570856670113558780583713 25928142502585169085437785)
  ·
    refine ⟨19446106876938876814078339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25928142502585169085437785 19446106876938876814078339)
    ·
      refine ⟨29169160315408315221117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19446106876938876814078339 29169160315408315221117509)
      ·
        refine ⟨5469217559139059103959533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29169160315408315221117509 5469217559139059103959533)
        ·
          refine ⟨2050956584677147163984825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5469217559139059103959533 2050956584677147163984825)
          ·
            refine ⟨1538217438507860372988619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050956584677147163984825 1538217438507860372988619)
            ·
              refine ⟨2307326157761790559482929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538217438507860372988619 2307326157761790559482929)
              ·
                refine ⟨1730494618321342919612197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307326157761790559482929 1730494618321342919612197)
                ·
                  refine ⟨324467740935251797427287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730494618321342919612197 324467740935251797427287)
                  ·
                    rfl

theorem cell21_1421772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1421772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421772 prefixEnd_1421772 := by exact prefixLift 1421772
  have htrace : WordTrace (prefixWord ++ tailWord_1421772) baseStart_1421772 baseEnd_1421772 := by
    simpa [prefixWord, tailWord_1421772, baseEnd_1421772] using wordTrace_append hprefix tailTrace_1421772
  have hstable : (prefixWord ++ tailWord_1421772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421772).length < 2 ^ (prefixWord ++ tailWord_1421772).sum := by decide
  have hdescent : baseEnd_1421772 < baseStart_1421772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421814 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1421814 : Nat := 118140960795 + 1421814 * 2 ^ 59
def prefixEnd_1421814 : Nat := 4983230072969 + 3 ^ 40 * 1421814 * 2
def baseEnd_1421814 : Nat := 324477325907469057727201

theorem tailTrace_1421814 : CollatzResearch.WordTrace tailWord_1421814 prefixEnd_1421814 324477325907469057727201 := by
  unfold tailWord_1421814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241113554438636208994031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34571877914012119562602997 3241113554438636208994031)
  ·
    refine ⟨4861670331657954313491047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3241113554438636208994031 4861670331657954313491047)
    ·
      refine ⟨7292505497486931470236571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861670331657954313491047 7292505497486931470236571)
      ·
        refine ⟨10938758246230397205354857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7292505497486931470236571 10938758246230397205354857)
        ·
          refine ⟨8204068684672797904016143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10938758246230397205354857 8204068684672797904016143)
          ·
            refine ⟨12306103027009196856024215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8204068684672797904016143 12306103027009196856024215)
            ·
              refine ⟨18459154540513795284036323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12306103027009196856024215 18459154540513795284036323)
              ·
                refine ⟨27688731810770692926054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459154540513795284036323 27688731810770692926054485)
                ·
                  refine ⟨324477325907469057727201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27688731810770692926054485 324477325907469057727201)
                  ·
                    rfl

theorem cell21_1421814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1421814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421814 prefixEnd_1421814 := by exact prefixLift 1421814
  have htrace : WordTrace (prefixWord ++ tailWord_1421814) baseStart_1421814 baseEnd_1421814 := by
    simpa [prefixWord, tailWord_1421814, baseEnd_1421814] using wordTrace_append hprefix tailTrace_1421814
  have hstable : (prefixWord ++ tailWord_1421814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421814).length < 2 ^ (prefixWord ++ tailWord_1421814).sum := by decide
  have hdescent : baseEnd_1421814 < baseStart_1421814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421848 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_1421848 : Nat := 118140960795 + 1421848 * 2 ^ 59
def prefixEnd_1421848 : Nat := 4983230072969 + 3 ^ 40 * 1421848 * 2
def baseEnd_1421848 : Nat := 324485085170692554160465

theorem tailTrace_1421848 : CollatzResearch.WordTrace tailWord_1421848 prefixEnd_1421848 324485085170692554160465 := by
  unfold tailWord_1421848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25929528476447501575321099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34572704635263335433761465 25929528476447501575321099)
  ·
    refine ⟨38894292714671252362981649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25929528476447501575321099 38894292714671252362981649)
    ·
      refine ⟨29170719536003439272236237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38894292714671252362981649 29170719536003439272236237)
      ·
        refine ⟨10939019826001289727088589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29170719536003439272236237 10939019826001289727088589)
        ·
          refine ⟨4102132434750483647658221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10939019826001289727088589 4102132434750483647658221)
          ·
            refine ⟨1538299663031431367871833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4102132434750483647658221 1538299663031431367871833)
            ·
              refine ⟨1153724747273573525903875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538299663031431367871833 1153724747273573525903875)
              ·
                refine ⟨1730587120910360288855813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153724747273573525903875 1730587120910360288855813)
                ·
                  refine ⟨324485085170692554160465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730587120910360288855813 324485085170692554160465)
                  ·
                    rfl

theorem cell21_1421848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_1421848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421848 prefixEnd_1421848 := by exact prefixLift 1421848
  have htrace : WordTrace (prefixWord ++ tailWord_1421848) baseStart_1421848 baseEnd_1421848 := by
    simpa [prefixWord, tailWord_1421848, baseEnd_1421848] using wordTrace_append hprefix tailTrace_1421848
  have hstable : (prefixWord ++ tailWord_1421848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421848).length < 2 ^ (prefixWord ++ tailWord_1421848).sum := by decide
  have hdescent : baseEnd_1421848 < baseStart_1421848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421873 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_1421873 : Nat := 118140960795 + 1421873 * 2 ^ 59
def prefixEnd_1421873 : Nat := 4983230072969 + 3 ^ 40 * 1421873 * 2
def baseEnd_1421873 : Nat := 324490790511298066243747

theorem tailTrace_1421873 : CollatzResearch.WordTrace tailWord_1421873 prefixEnd_1421873 324490790511298066243747 := by
  unfold tailWord_1421873
  simp only [CollatzResearch.WordTrace]
  refine ⟨51859968777804432420302273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34573312518536288280201515 51859968777804432420302273)
  ·
    refine ⟨38894976583353324315226705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51859968777804432420302273 38894976583353324315226705)
    ·
      refine ⟨29171232437514993236420029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38894976583353324315226705 29171232437514993236420029)
      ·
        refine ⟨10939212164068122463657511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29171232437514993236420029 10939212164068122463657511)
        ·
          refine ⟨16408818246102183695486267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10939212164068122463657511 16408818246102183695486267)
          ·
            refine ⟨24613227369153275543229401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16408818246102183695486267 24613227369153275543229401)
            ·
              refine ⟨18459920526864956657422051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24613227369153275543229401 18459920526864956657422051)
              ·
                refine ⟨27689880790297434986133077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459920526864956657422051 27689880790297434986133077)
                ·
                  refine ⟨324490790511298066243747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27689880790297434986133077 324490790511298066243747)
                  ·
                    rfl

theorem cell21_1421873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_1421873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421873 prefixEnd_1421873 := by exact prefixLift 1421873
  have htrace : WordTrace (prefixWord ++ tailWord_1421873) baseStart_1421873 baseEnd_1421873 := by
    simpa [prefixWord, tailWord_1421873, baseEnd_1421873] using wordTrace_append hprefix tailTrace_1421873
  have hstable : (prefixWord ++ tailWord_1421873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421873).length < 2 ^ (prefixWord ++ tailWord_1421873).sum := by decide
  have hdescent : baseEnd_1421873 < baseStart_1421873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421893 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1421893 : Nat := 118140960795 + 1421893 * 2 ^ 59
def prefixEnd_1421893 : Nat := 4983230072969 + 3 ^ 40 * 1421893 * 2
def baseEnd_1421893 : Nat := 324495354783782475910373

theorem tailTrace_1421893 : CollatzResearch.WordTrace tailWord_1421893 prefixEnd_1421893 324495354783782475910373 := by
  unfold tailWord_1421893
  simp only [CollatzResearch.WordTrace]
  refine ⟨51860698237731975836030333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34573798825154650557353555 51860698237731975836030333)
  ·
    refine ⟨19447761839149490938511375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51860698237731975836030333 19447761839149490938511375)
    ·
      refine ⟨29171642758724236407767063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447761839149490938511375 29171642758724236407767063)
      ·
        refine ⟨43757464138086354611650595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29171642758724236407767063 43757464138086354611650595)
        ·
          refine ⟨65636196207129531917475893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43757464138086354611650595 65636196207129531917475893)
          ·
            refine ⟨6153393394418393617263365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65636196207129531917475893 6153393394418393617263365)
            ·
              refine ⟨1153761261453448803236881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6153393394418393617263365 1153761261453448803236881)
              ·
                refine ⟨865320946090086602427661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153761261453448803236881 865320946090086602427661)
                ·
                  refine ⟨324495354783782475910373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865320946090086602427661 324495354783782475910373)
                  ·
                    rfl

theorem cell21_1421893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1421893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421893 prefixEnd_1421893 := by exact prefixLift 1421893
  have htrace : WordTrace (prefixWord ++ tailWord_1421893) baseStart_1421893 baseEnd_1421893 := by
    simpa [prefixWord, tailWord_1421893, baseEnd_1421893] using wordTrace_append hprefix tailTrace_1421893
  have hstable : (prefixWord ++ tailWord_1421893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421893).length < 2 ^ (prefixWord ++ tailWord_1421893).sum := by decide
  have hdescent : baseEnd_1421893 < baseStart_1421893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421921 : List Nat := [1, 2, 3, 1, 1, 5, 3, 5]
def baseStart_1421921 : Nat := 118140960795 + 1421921 * 2 ^ 59
def prefixEnd_1421921 : Nat := 4983230072969 + 3 ^ 40 * 1421921 * 2
def baseEnd_1421921 : Nat := 108167248255086883147883

theorem tailTrace_1421921 : CollatzResearch.WordTrace tailWord_1421921 prefixEnd_1421921 108167248255086883147883 := by
  unfold tailWord_1421921
  simp only [CollatzResearch.WordTrace]
  refine ⟨51861719481630536618049617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34574479654420357745366411 51861719481630536618049617)
  ·
    refine ⟨38896289611222902463537213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51861719481630536618049617 38896289611222902463537213)
    ·
      refine ⟨14586108604208588423826455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38896289611222902463537213 14586108604208588423826455)
      ·
        refine ⟨21879162906312882635739683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14586108604208588423826455 21879162906312882635739683)
        ·
          refine ⟨32818744359469323953609525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21879162906312882635739683 32818744359469323953609525)
          ·
            refine ⟨3076757283700249120650893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32818744359469323953609525 3076757283700249120650893)
            ·
              refine ⟨1153783981387593420244085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3076757283700249120650893 1153783981387593420244085)
              ·
                refine ⟨108167248255086883147883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153783981387593420244085 108167248255086883147883)
                ·
                  rfl

theorem cell21_1421921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].length) (baseStart_1421921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421921 prefixEnd_1421921 := by exact prefixLift 1421921
  have htrace : WordTrace (prefixWord ++ tailWord_1421921) baseStart_1421921 baseEnd_1421921 := by
    simpa [prefixWord, tailWord_1421921, baseEnd_1421921] using wordTrace_append hprefix tailTrace_1421921
  have hstable : (prefixWord ++ tailWord_1421921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421921).length < 2 ^ (prefixWord ++ tailWord_1421921).sum := by decide
  have hdescent : baseEnd_1421921 < baseStart_1421921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421941 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1421941 : Nat := 118140960795 + 1421941 * 2 ^ 59
def prefixEnd_1421941 : Nat := 4983230072969 + 3 ^ 40 * 1421941 * 2
def baseEnd_1421941 : Nat := 324506309037745059110275

theorem tailTrace_1421941 : CollatzResearch.WordTrace tailWord_1421941 prefixEnd_1421941 324506309037745059110275 := by
  unfold tailWord_1421941
  simp only [CollatzResearch.WordTrace]
  refine ⟨51862448941558080033777677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34574965961038720022518451 51862448941558080033777677)
  ·
    refine ⟨19448418353084280012666629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51862448941558080033777677 19448418353084280012666629)
    ·
      refine ⟨3646578441203302502374993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19448418353084280012666629 3646578441203302502374993)
      ·
        refine ⟨2734933830902476876781245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3646578441203302502374993 2734933830902476876781245)
        ·
          refine ⟨1025600186588428828792967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2734933830902476876781245 1025600186588428828792967)
          ·
            refine ⟨1538400279882643243189451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025600186588428828792967 1538400279882643243189451)
            ·
              refine ⟨2307600419823964864784177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538400279882643243189451 2307600419823964864784177)
              ·
                refine ⟨1730700314867973648588133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307600419823964864784177 1730700314867973648588133)
                ·
                  refine ⟨324506309037745059110275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730700314867973648588133 324506309037745059110275)
                  ·
                    rfl

theorem cell21_1421941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1421941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421941 prefixEnd_1421941 := by exact prefixLift 1421941
  have htrace : WordTrace (prefixWord ++ tailWord_1421941) baseStart_1421941 baseEnd_1421941 := by
    simpa [prefixWord, tailWord_1421941, baseEnd_1421941] using wordTrace_append hprefix tailTrace_1421941
  have hstable : (prefixWord ++ tailWord_1421941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421941).length < 2 ^ (prefixWord ++ tailWord_1421941).sum := by decide
  have hdescent : baseEnd_1421941 < baseStart_1421941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421952 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1421952 : Nat := 118140960795 + 1421952 * 2 ^ 59
def prefixEnd_1421952 : Nat := 4983230072969 + 3 ^ 40 * 1421952 * 2
def baseEnd_1421952 : Nat := 324508819387611484426919

theorem tailTrace_1421952 : CollatzResearch.WordTrace tailWord_1421952 prefixEnd_1421952 324508819387611484426919 := by
  unfold tailWord_1421952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25931425072259114456214055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34575233429678819274952073 25931425072259114456214055)
  ·
    refine ⟨38897137608388671684321083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25931425072259114456214055 38897137608388671684321083)
    ·
      refine ⟨58345706412583007526481625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38897137608388671684321083 58345706412583007526481625)
      ·
        refine ⟨43759279809437255644861219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58345706412583007526481625 43759279809437255644861219)
        ·
          refine ⟨65638919714155883467291829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43759279809437255644861219 65638919714155883467291829)
          ·
            refine ⟨6153648723202114075058609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65638919714155883467291829 6153648723202114075058609)
            ·
              refine ⟨4615236542401585556293957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6153648723202114075058609 4615236542401585556293957)
              ·
                refine ⟨865356851700297291805117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4615236542401585556293957 865356851700297291805117)
                ·
                  refine ⟨324508819387611484426919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865356851700297291805117 324508819387611484426919)
                  ·
                    rfl

theorem cell21_1421952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1421952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421952 prefixEnd_1421952 := by exact prefixLift 1421952
  have htrace : WordTrace (prefixWord ++ tailWord_1421952) baseStart_1421952 baseEnd_1421952 := by
    simpa [prefixWord, tailWord_1421952, baseEnd_1421952] using wordTrace_append hprefix tailTrace_1421952
  have hstable : (prefixWord ++ tailWord_1421952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421952).length < 2 ^ (prefixWord ++ tailWord_1421952).sum := by decide
  have hdescent : baseEnd_1421952 < baseStart_1421952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421997 : List Nat := [1, 5, 2, 1, 1, 4, 7]
def baseStart_1421997 : Nat := 118140960795 + 1421997 * 2 ^ 59
def prefixEnd_1421997 : Nat := 4983230072969 + 3 ^ 40 * 1421997 * 2
def baseEnd_1421997 : Nat := 36057676555633489575203

theorem tailTrace_1421997 : CollatzResearch.WordTrace tailWord_1421997 prefixEnd_1421997 36057676555633489575203 := by
  unfold tailWord_1421997
  simp only [CollatzResearch.WordTrace]
  refine ⟨51864491429355201597816245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34576327619570134398544163 51864491429355201597816245)
  ·
    refine ⟨4862296071502050149795273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51864491429355201597816245 4862296071502050149795273)
    ·
      refine ⟨3646722053626537612346455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4862296071502050149795273 3646722053626537612346455)
      ·
        refine ⟨5470083080439806418519683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646722053626537612346455 5470083080439806418519683)
        ·
          refine ⟨8205124620659709627779525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470083080439806418519683 8205124620659709627779525)
          ·
            refine ⟨1538460866373695555208661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8205124620659709627779525 1538460866373695555208661)
            ·
              refine ⟨36057676555633489575203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1538460866373695555208661 36057676555633489575203)
              ·
                rfl

theorem cell21_1421997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 7].length) (baseStart_1421997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1421997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1421997 prefixEnd_1421997 := by exact prefixLift 1421997
  have htrace : WordTrace (prefixWord ++ tailWord_1421997) baseStart_1421997 baseEnd_1421997 := by
    simpa [prefixWord, tailWord_1421997, baseEnd_1421997] using wordTrace_append hprefix tailTrace_1421997
  have hstable : (prefixWord ++ tailWord_1421997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421997).length < 2 ^ (prefixWord ++ tailWord_1421997).sum := by decide
  have hdescent : baseEnd_1421997 < baseStart_1421997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422056 : List Nat := [2, 1, 4, 1, 4, 9]
def baseStart_1422056 : Nat := 118140960795 + 1422056 * 2 ^ 59
def prefixEnd_1422056 : Nat := 4983230072969 + 3 ^ 40 * 1422056 * 2
def baseEnd_1422056 : Nat := 12019724207575200544199

theorem tailTrace_1422056 : CollatzResearch.WordTrace tailWord_1422056 prefixEnd_1422056 12019724207575200544199 := by
  unfold tailWord_1422056
  simp only [CollatzResearch.WordTrace]
  refine ⟨25933321668070727337107011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34577762224094303116142681 25933321668070727337107011)
  ·
    refine ⟨38899982502106091005660517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25933321668070727337107011 38899982502106091005660517)
    ·
      refine ⟨7293746719144892063561347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38899982502106091005660517 7293746719144892063561347)
      ·
        refine ⟨10940620078717338095342021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293746719144892063561347 10940620078717338095342021)
        ·
          refine ⟨2051366264759500892876629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10940620078717338095342021 2051366264759500892876629)
          ·
            refine ⟨12019724207575200544199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2051366264759500892876629 12019724207575200544199)
            ·
              rfl

theorem cell21_1422056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 9].length) (baseStart_1422056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422056 prefixEnd_1422056 := by exact prefixLift 1422056
  have htrace : WordTrace (prefixWord ++ tailWord_1422056) baseStart_1422056 baseEnd_1422056 := by
    simpa [prefixWord, tailWord_1422056, baseEnd_1422056] using wordTrace_append hprefix tailTrace_1422056
  have hstable : (prefixWord ++ tailWord_1422056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422056).length < 2 ^ (prefixWord ++ tailWord_1422056).sum := by decide
  have hdescent : baseEnd_1422056 < baseStart_1422056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422062 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_1422062 : Nat := 118140960795 + 1422062 * 2 ^ 59
def prefixEnd_1422062 : Nat := 4983230072969 + 3 ^ 40 * 1422062 * 2
def baseEnd_1422062 : Nat := 324533922886275737593361

theorem tailTrace_1422062 : CollatzResearch.WordTrace tailWord_1422062 prefixEnd_1422062 324533922886275737593361 := by
  unfold tailWord_1422062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483357771764964712366555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34577908116079811799288293 6483357771764964712366555)
  ·
    refine ⟨9725036657647447068549833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6483357771764964712366555 9725036657647447068549833)
    ·
      refine ⟨7293777493235585301412375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9725036657647447068549833 7293777493235585301412375)
      ·
        refine ⟨10940666239853377952118563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293777493235585301412375 10940666239853377952118563)
        ·
          refine ⟨16410999359780066928177845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940666239853377952118563 16410999359780066928177845)
          ·
            refine ⟨1538531189979381274516673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16410999359780066928177845 1538531189979381274516673)
            ·
              refine ⟨1153898392484535955887505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538531189979381274516673 1153898392484535955887505)
              ·
                refine ⟨865423794363401966915629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153898392484535955887505 865423794363401966915629)
                ·
                  refine ⟨324533922886275737593361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865423794363401966915629 324533922886275737593361)
                  ·
                    rfl

theorem cell21_1422062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_1422062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422062 prefixEnd_1422062 := by exact prefixLift 1422062
  have htrace : WordTrace (prefixWord ++ tailWord_1422062) baseStart_1422062 baseEnd_1422062 := by
    simpa [prefixWord, tailWord_1422062, baseEnd_1422062] using wordTrace_append hprefix tailTrace_1422062
  have hstable : (prefixWord ++ tailWord_1422062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422062).length < 2 ^ (prefixWord ++ tailWord_1422062).sum := by decide
  have hdescent : baseEnd_1422062 < baseStart_1422062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422087 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_1422087 : Nat := 118140960795 + 1422087 * 2 ^ 59
def prefixEnd_1422087 : Nat := 4983230072969 + 3 ^ 40 * 1422087 * 2
def baseEnd_1422087 : Nat := 324539628226881249676643

theorem tailTrace_1422087 : CollatzResearch.WordTrace tailWord_1422087 prefixEnd_1422087 324539628226881249676643 := by
  unfold tailWord_1422087
  simp only [CollatzResearch.WordTrace]
  refine ⟨51867773999029146968592515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34578515999352764645728343 51867773999029146968592515)
  ·
    refine ⟨77801660998543720452888773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51867773999029146968592515 77801660998543720452888773)
    ·
      refine ⟨14587811437226947584916645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77801660998543720452888773 14587811437226947584916645)
      ·
        refine ⟨2735214644480052672171871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14587811437226947584916645 2735214644480052672171871)
        ·
          refine ⟨4102821966720079008257807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735214644480052672171871 4102821966720079008257807)
          ·
            refine ⟨6154232950080118512386711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102821966720079008257807 6154232950080118512386711)
            ·
              refine ⟨9231349425120177768580067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154232950080118512386711 9231349425120177768580067)
              ·
                refine ⟨13847024137680266652870101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231349425120177768580067 13847024137680266652870101)
                ·
                  refine ⟨324539628226881249676643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13847024137680266652870101 324539628226881249676643)
                  ·
                    rfl

theorem cell21_1422087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_1422087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422087 prefixEnd_1422087 := by exact prefixLift 1422087
  have htrace : WordTrace (prefixWord ++ tailWord_1422087) baseStart_1422087 baseEnd_1422087 := by
    simpa [prefixWord, tailWord_1422087, baseEnd_1422087] using wordTrace_append hprefix tailTrace_1422087
  have hstable : (prefixWord ++ tailWord_1422087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422087).length < 2 ^ (prefixWord ++ tailWord_1422087).sum := by decide
  have hdescent : baseEnd_1422087 < baseStart_1422087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422101 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_1422101 : Nat := 118140960795 + 1422101 * 2 ^ 59
def prefixEnd_1422101 : Nat := 4983230072969 + 3 ^ 40 * 1422101 * 2
def baseEnd_1422101 : Nat := 324542823217620336443281

theorem tailTrace_1422101 : CollatzResearch.WordTrace tailWord_1422101 prefixEnd_1422101 324542823217620336443281 := by
  unfold tailWord_1422101
  simp only [CollatzResearch.WordTrace]
  refine ⟨51868284620978427359602157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34578856413985618239734771 51868284620978427359602157)
  ·
    refine ⟨19450606732866910259850809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51868284620978427359602157 19450606732866910259850809)
    ·
      refine ⟨14587955049650182694888107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19450606732866910259850809 14587955049650182694888107)
      ·
        refine ⟨21881932574475274042332161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14587955049650182694888107 21881932574475274042332161)
        ·
          refine ⟨16411449430856455531749121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21881932574475274042332161 16411449430856455531749121)
          ·
            refine ⟨12308587073142341648811841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16411449430856455531749121 12308587073142341648811841)
            ·
              refine ⟨9231440304856756236608881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12308587073142341648811841 9231440304856756236608881)
              ·
                refine ⟨6923580228642567177456661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9231440304856756236608881 6923580228642567177456661)
                ·
                  refine ⟨324542823217620336443281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6923580228642567177456661 324542823217620336443281)
                  ·
                    rfl

theorem cell21_1422101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_1422101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422101 prefixEnd_1422101 := by exact prefixLift 1422101
  have htrace : WordTrace (prefixWord ++ tailWord_1422101) baseStart_1422101 baseEnd_1422101 := by
    simpa [prefixWord, tailWord_1422101, baseEnd_1422101] using wordTrace_append hprefix tailTrace_1422101
  have hstable : (prefixWord ++ tailWord_1422101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422101).length < 2 ^ (prefixWord ++ tailWord_1422101).sum := by decide
  have hdescent : baseEnd_1422101 < baseStart_1422101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422180 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1422180 : Nat := 118140960795 + 1422180 * 2 ^ 59
def prefixEnd_1422180 : Nat := 4983230072969 + 3 ^ 40 * 1422180 * 2
def baseEnd_1422180 : Nat := 324560852093933754626453

theorem tailTrace_1422180 : CollatzResearch.WordTrace tailWord_1422180 prefixEnd_1422180 324560852093933754626453 := by
  unfold tailWord_1422180
  simp only [CollatzResearch.WordTrace]
  refine ⟨25935582993846111925863997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34580777325128149234485329 25935582993846111925863997)
  ·
    refine ⟨9725843622692291972198999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25935582993846111925863997 9725843622692291972198999)
    ·
      refine ⟨14588765434038437958298499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9725843622692291972198999 14588765434038437958298499)
      ·
        refine ⟨21883148151057656937447749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588765434038437958298499 21883148151057656937447749)
        ·
          refine ⟨4103090278323310675771453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21883148151057656937447749 4103090278323310675771453)
          ·
            refine ⟨1538658854371241503414295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4103090278323310675771453 1538658854371241503414295)
            ·
              refine ⟨2307988281556862255121443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538658854371241503414295 2307988281556862255121443)
              ·
                refine ⟨3461982422335293382682165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307988281556862255121443 3461982422335293382682165)
                ·
                  refine ⟨324560852093933754626453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461982422335293382682165 324560852093933754626453)
                  ·
                    rfl

theorem cell21_1422180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1422180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422180 prefixEnd_1422180 := by exact prefixLift 1422180
  have htrace : WordTrace (prefixWord ++ tailWord_1422180) baseStart_1422180 baseEnd_1422180 := by
    simpa [prefixWord, tailWord_1422180, baseEnd_1422180] using wordTrace_append hprefix tailTrace_1422180
  have hstable : (prefixWord ++ tailWord_1422180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422180).length < 2 ^ (prefixWord ++ tailWord_1422180).sum := by decide
  have hdescent : baseEnd_1422180 < baseStart_1422180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422318 : List Nat := [4, 1, 2, 1, 4, 2, 2, 5]
def baseStart_1422318 : Nat := 118140960795 + 1422318 * 2 ^ 59
def prefixEnd_1422318 : Nat := 4983230072969 + 3 ^ 40 * 1422318 * 2
def baseEnd_1422318 : Nat := 108197448524692060442057

theorem tailTrace_1422318 : CollatzResearch.WordTrace tailWord_1422318 prefixEnd_1422318 108197448524692060442057 := by
  unfold tailWord_1422318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484524907649034177531451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34584132840794848946834405 6484524907649034177531451)
  ·
    refine ⟨9726787361473551266297177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6484524907649034177531451 9726787361473551266297177)
    ·
      refine ⟨7295090521105163449722883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9726787361473551266297177 7295090521105163449722883)
      ·
        refine ⟨10942635781657745174584325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295090521105163449722883 10942635781657745174584325)
        ·
          refine ⟨2051744209060827220234561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10942635781657745174584325 2051744209060827220234561)
          ·
            refine ⟨1538808156795620415175921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051744209060827220234561 1538808156795620415175921)
            ·
              refine ⟨1154106117596715311381941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538808156795620415175921 1154106117596715311381941)
              ·
                refine ⟨108197448524692060442057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1154106117596715311381941 108197448524692060442057)
                ·
                  rfl

theorem cell21_1422318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_1422318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422318 prefixEnd_1422318 := by exact prefixLift 1422318
  have htrace : WordTrace (prefixWord ++ tailWord_1422318) baseStart_1422318 baseEnd_1422318 := by
    simpa [prefixWord, tailWord_1422318, baseEnd_1422318] using wordTrace_append hprefix tailTrace_1422318
  have hstable : (prefixWord ++ tailWord_1422318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422318).length < 2 ^ (prefixWord ++ tailWord_1422318).sum := by decide
  have hdescent : baseEnd_1422318 < baseStart_1422318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422332 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1422332 : Nat := 118140960795 + 1422332 * 2 ^ 59
def prefixEnd_1422332 : Nat := 4983230072969 + 3 ^ 40 * 1422332 * 2
def baseEnd_1422332 : Nat := 324595540564815268092809

theorem tailTrace_1422332 : CollatzResearch.WordTrace tailWord_1422332 prefixEnd_1422332 324595540564815268092809 := by
  unfold tailWord_1422332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938354941570776905630625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34584473255427702540840833 25938354941570776905630625)
  ·
    refine ⟨19453766206178082679222969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25938354941570776905630625 19453766206178082679222969)
    ·
      refine ⟨14590324654633562009417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19453766206178082679222969 14590324654633562009417227)
      ·
        refine ⟨21885486981950343014125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14590324654633562009417227 21885486981950343014125841)
        ·
          refine ⟨16414115236462757260594381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21885486981950343014125841 16414115236462757260594381)
          ·
            refine ⟨6155293213673533972722893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16414115236462757260594381 6155293213673533972722893)
            ·
              refine ⟨2308234955127575239771085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6155293213673533972722893 2308234955127575239771085)
              ·
                refine ⟨865588108172840714914157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308234955127575239771085 865588108172840714914157)
                ·
                  refine ⟨324595540564815268092809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865588108172840714914157 324595540564815268092809)
                  ·
                    rfl

theorem cell21_1422332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1422332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422332 prefixEnd_1422332 := by exact prefixLift 1422332
  have htrace : WordTrace (prefixWord ++ tailWord_1422332) baseStart_1422332 baseEnd_1422332 := by
    simpa [prefixWord, tailWord_1422332, baseEnd_1422332] using wordTrace_append hprefix tailTrace_1422332
  have hstable : (prefixWord ++ tailWord_1422332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422332).length < 2 ^ (prefixWord ++ tailWord_1422332).sum := by decide
  have hdescent : baseEnd_1422332 < baseStart_1422332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422360 : List Nat := [2, 1, 2, 3, 2, 3, 2, 6]
def baseStart_1422360 : Nat := 118140960795 + 1422360 * 2 ^ 59
def prefixEnd_1422360 : Nat := 4983230072969 + 3 ^ 40 * 1422360 * 2
def baseEnd_1422360 : Nat := 108200643515431147208695

theorem tailTrace_1422360 : CollatzResearch.WordTrace tailWord_1422360 prefixEnd_1422360 108200643515431147208695 := by
  unfold tailWord_1422360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938865563520057296640267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34585154084693409728853689 25938865563520057296640267)
  ·
    refine ⟨38908298345280085944960401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25938865563520057296640267 38908298345280085944960401)
    ·
      refine ⟨29181223758960064458720301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38908298345280085944960401 29181223758960064458720301)
      ·
        refine ⟨10942958909610024172020113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29181223758960064458720301 10942958909610024172020113)
        ·
          refine ⟨8207219182207518129015085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10942958909610024172020113 8207219182207518129015085)
          ·
            refine ⟨3077707193327819298380657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8207219182207518129015085 3077707193327819298380657)
            ·
              refine ⟨2308280394995864473785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077707193327819298380657 2308280394995864473785493)
              ·
                refine ⟨108200643515431147208695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2308280394995864473785493 108200643515431147208695)
                ·
                  rfl

theorem cell21_1422360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_1422360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422360 prefixEnd_1422360 := by exact prefixLift 1422360
  have htrace : WordTrace (prefixWord ++ tailWord_1422360) baseStart_1422360 baseEnd_1422360 := by
    simpa [prefixWord, tailWord_1422360, baseEnd_1422360] using wordTrace_append hprefix tailTrace_1422360
  have hstable : (prefixWord ++ tailWord_1422360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422360).length < 2 ^ (prefixWord ++ tailWord_1422360).sum := by decide
  have hdescent : baseEnd_1422360 < baseStart_1422360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422391 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 3]
def baseStart_1422391 : Nat := 118140960795 + 1422391 * 2 ^ 59
def prefixEnd_1422391 : Nat := 4983230072969 + 3 ^ 40 * 1422391 * 2
def baseEnd_1422391 : Nat := 324609005168644276609355

theorem tailTrace_1422391 : CollatzResearch.WordTrace tailWord_1422391 prefixEnd_1422391 324609005168644276609355 := by
  unfold tailWord_1422391
  simp only [CollatzResearch.WordTrace]
  refine ⟨51878861789927806887659027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34585907859951871258439351 51878861789927806887659027)
  ·
    refine ⟨77818292684891710331488541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51878861789927806887659027 77818292684891710331488541)
    ·
      refine ⟨29181859756834391374308203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77818292684891710331488541 29181859756834391374308203)
      ·
        refine ⟨43772789635251587061462305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29181859756834391374308203 43772789635251587061462305)
        ·
          refine ⟨32829592226438690296096729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43772789635251587061462305 32829592226438690296096729)
          ·
            refine ⟨24622194169829017722072547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32829592226438690296096729 24622194169829017722072547)
            ·
              refine ⟨36933291254743526583108821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24622194169829017722072547 36933291254743526583108821)
              ·
                refine ⟨865624013783051404291613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36933291254743526583108821 865624013783051404291613)
                ·
                  refine ⟨324609005168644276609355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865624013783051404291613 324609005168644276609355)
                  ·
                    rfl

theorem cell21_1422391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].length) (baseStart_1422391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422391 prefixEnd_1422391 := by exact prefixLift 1422391
  have htrace : WordTrace (prefixWord ++ tailWord_1422391) baseStart_1422391 baseEnd_1422391 := by
    simpa [prefixWord, tailWord_1422391, baseEnd_1422391] using wordTrace_append hprefix tailTrace_1422391
  have hstable : (prefixWord ++ tailWord_1422391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422391).length < 2 ^ (prefixWord ++ tailWord_1422391).sum := by decide
  have hdescent : baseEnd_1422391 < baseStart_1422391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422405 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1422405 : Nat := 118140960795 + 1422405 * 2 ^ 59
def prefixEnd_1422405 : Nat := 4983230072969 + 3 ^ 40 * 1422405 * 2
def baseEnd_1422405 : Nat := 324612200159383363375993

theorem tailTrace_1422405 : CollatzResearch.WordTrace tailWord_1422405 prefixEnd_1422405 324612200159383363375993 := by
  unfold tailWord_1422405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51879372411877087278668669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34586248274584724852445779 51879372411877087278668669)
  ·
    refine ⟨19454764654453907729500751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51879372411877087278668669 19454764654453907729500751)
    ·
      refine ⟨29182146981680861594251127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19454764654453907729500751 29182146981680861594251127)
      ·
        refine ⟨43773220472521292391376691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29182146981680861594251127 43773220472521292391376691)
        ·
          refine ⟨65659830708781938587065037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43773220472521292391376691 65659830708781938587065037)
          ·
            refine ⟨24622436515793226970149389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65659830708781938587065037 24622436515793226970149389)
            ·
              refine ⟨9233413693422460113806021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24622436515793226970149389 9233413693422460113806021)
              ·
                refine ⟨1731265067516711271338629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9233413693422460113806021 1731265067516711271338629)
                ·
                  refine ⟨324612200159383363375993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731265067516711271338629 324612200159383363375993)
                  ·
                    rfl

theorem cell21_1422405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1422405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422405 prefixEnd_1422405 := by exact prefixLift 1422405
  have htrace : WordTrace (prefixWord ++ tailWord_1422405) baseStart_1422405 baseEnd_1422405 := by
    simpa [prefixWord, tailWord_1422405, baseEnd_1422405] using wordTrace_append hprefix tailTrace_1422405
  have hstable : (prefixWord ++ tailWord_1422405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422405).length < 2 ^ (prefixWord ++ tailWord_1422405).sum := by decide
  have hdescent : baseEnd_1422405 < baseStart_1422405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422450 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1422450 : Nat := 118140960795 + 1422450 * 2 ^ 59
def prefixEnd_1422450 : Nat := 4983230072969 + 3 ^ 40 * 1422450 * 2
def baseEnd_1422450 : Nat := 324622469772473285125901

theorem tailTrace_1422450 : CollatzResearch.WordTrace tailWord_1422450 prefixEnd_1422450 324622469772473285125901 := by
  unfold tailWord_1422450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970253424178514991014201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34587342464476039976037869 12970253424178514991014201)
  ·
    refine ⟨9727690068133886243260651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12970253424178514991014201 9727690068133886243260651)
    ·
      refine ⟨14591535102200829364890977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9727690068133886243260651 14591535102200829364890977)
      ·
        refine ⟨10943651326650622023668233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14591535102200829364890977 10943651326650622023668233)
        ·
          refine ⟨8207738494987966517751175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10943651326650622023668233 8207738494987966517751175)
          ·
            refine ⟨12311607742481949776626763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8207738494987966517751175 12311607742481949776626763)
            ·
              refine ⟨18467411613722924664940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12311607742481949776626763 18467411613722924664940145)
              ·
                refine ⟨13850558710292193498705109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18467411613722924664940145 13850558710292193498705109)
                ·
                  refine ⟨324622469772473285125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13850558710292193498705109 324622469772473285125901)
                  ·
                    rfl

theorem cell21_1422450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1422450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422450 prefixEnd_1422450 := by exact prefixLift 1422450
  have htrace : WordTrace (prefixWord ++ tailWord_1422450) baseStart_1422450 baseEnd_1422450 := by
    simpa [prefixWord, tailWord_1422450, baseEnd_1422450] using wordTrace_append hprefix tailTrace_1422450
  have hstable : (prefixWord ++ tailWord_1422450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422450).length < 2 ^ (prefixWord ++ tailWord_1422450).sum := by decide
  have hdescent : baseEnd_1422450 < baseStart_1422450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422453 : List Nat := [1, 3, 4, 3, 1, 1, 8]
def baseStart_1422453 : Nat := 118140960795 + 1422453 * 2 ^ 59
def prefixEnd_1422453 : Nat := 4983230072969 + 3 ^ 40 * 1422453 * 2
def baseEnd_1422453 : Nat := 36069239379260660730655

theorem tailTrace_1422453 : CollatzResearch.WordTrace tailWord_1422453 prefixEnd_1422453 36069239379260660730655 := by
  unfold tailWord_1422453
  simp only [CollatzResearch.WordTrace]
  refine ⟨51881123115703191476416013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34587415410468794317610675 51881123115703191476416013)
  ·
    refine ⟨19455421168388696803656005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51881123115703191476416013 19455421168388696803656005)
    ·
      refine ⟨3647891469072880650685501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19455421168388696803656005 3647891469072880650685501)
      ·
        refine ⟨1367959300902330244007063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3647891469072880650685501 1367959300902330244007063)
        ·
          refine ⟨2051938951353495366010595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367959300902330244007063 2051938951353495366010595)
          ·
            refine ⟨3077908427030243049015893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051938951353495366010595 3077908427030243049015893)
            ·
              refine ⟨36069239379260660730655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3077908427030243049015893 36069239379260660730655)
              ·
                rfl

theorem cell21_1422453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 8].length) (baseStart_1422453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422453 prefixEnd_1422453 := by exact prefixLift 1422453
  have htrace : WordTrace (prefixWord ++ tailWord_1422453) baseStart_1422453 baseEnd_1422453 := by
    simpa [prefixWord, tailWord_1422453, baseEnd_1422453] using wordTrace_append hprefix tailTrace_1422453
  have hstable : (prefixWord ++ tailWord_1422453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422453).length < 2 ^ (prefixWord ++ tailWord_1422453).sum := by decide
  have hdescent : baseEnd_1422453 < baseStart_1422453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422467 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 3]
def baseStart_1422467 : Nat := 118140960795 + 1422467 * 2 ^ 59
def prefixEnd_1422467 : Nat := 4983230072969 + 3 ^ 40 * 1422467 * 2
def baseEnd_1422467 : Nat := 324626349404085033342533

theorem tailTrace_1422467 : CollatzResearch.WordTrace tailWord_1422467 prefixEnd_1422467 324626349404085033342533 := by
  unfold tailWord_1422467
  simp only [CollatzResearch.WordTrace]
  refine ⟨51881633737652471867425655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34587755825101647911617103 51881633737652471867425655)
  ·
    refine ⟨77822450606478707801138483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51881633737652471867425655 77822450606478707801138483)
    ·
      refine ⟨116733675909718061701707725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77822450606478707801138483 116733675909718061701707725)
      ·
        refine ⟨43775128466144273138140397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116733675909718061701707725 43775128466144273138140397)
        ·
          refine ⟨16415673174804102426802649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43775128466144273138140397 16415673174804102426802649)
          ·
            refine ⟨12311754881103076820101987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16415673174804102426802649 12311754881103076820101987)
            ·
              refine ⟨18467632321654615230152981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12311754881103076820101987 18467632321654615230152981)
              ·
                refine ⟨865670265077560088913421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18467632321654615230152981 865670265077560088913421)
                ·
                  refine ⟨324626349404085033342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865670265077560088913421 324626349404085033342533)
                  ·
                    rfl

theorem cell21_1422467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].length) (baseStart_1422467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422467 prefixEnd_1422467 := by exact prefixLift 1422467
  have htrace : WordTrace (prefixWord ++ tailWord_1422467) baseStart_1422467 baseEnd_1422467 := by
    simpa [prefixWord, tailWord_1422467, baseEnd_1422467] using wordTrace_append hprefix tailTrace_1422467
  have hstable : (prefixWord ++ tailWord_1422467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422467).length < 2 ^ (prefixWord ++ tailWord_1422467).sum := by decide
  have hdescent : baseEnd_1422467 < baseStart_1422467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422518 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1422518 : Nat := 118140960795 + 1422518 * 2 ^ 59
def prefixEnd_1422518 : Nat := 4983230072969 + 3 ^ 40 * 1422518 * 2
def baseEnd_1422518 : Nat := 324637988298920277992429

theorem tailTrace_1422518 : CollatzResearch.WordTrace tailWord_1422518 prefixEnd_1422518 324637988298920277992429 := by
  unfold tailWord_1422518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242718366279231723595763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34588995906978471718354805 3242718366279231723595763)
  ·
    refine ⟨4864077549418847585393645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242718366279231723595763 4864077549418847585393645)
    ·
      refine ⟨1824029081032067844522617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4864077549418847585393645 1824029081032067844522617)
      ·
        refine ⟨1368021810774050883391963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824029081032067844522617 1368021810774050883391963)
        ·
          refine ⟨2052032716161076325087945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368021810774050883391963 2052032716161076325087945)
          ·
            refine ⟨1539024537120807243815959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052032716161076325087945 1539024537120807243815959)
            ·
              refine ⟨2308536805681210865723939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539024537120807243815959 2308536805681210865723939)
              ·
                refine ⟨3462805208521816298585909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308536805681210865723939 3462805208521816298585909)
                ·
                  refine ⟨324637988298920277992429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3462805208521816298585909 324637988298920277992429)
                  ·
                    rfl

theorem cell21_1422518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1422518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422518 prefixEnd_1422518 := by exact prefixLift 1422518
  have htrace : WordTrace (prefixWord ++ tailWord_1422518) baseStart_1422518 baseEnd_1422518 := by
    simpa [prefixWord, tailWord_1422518, baseEnd_1422518] using wordTrace_append hprefix tailTrace_1422518
  have hstable : (prefixWord ++ tailWord_1422518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422518).length < 2 ^ (prefixWord ++ tailWord_1422518).sum := by decide
  have hdescent : baseEnd_1422518 < baseStart_1422518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422529 : List Nat := [1, 2, 6, 1, 1, 2, 2, 6]
def baseStart_1422529 : Nat := 118140960795 + 1422529 * 2 ^ 59
def prefixEnd_1422529 : Nat := 4983230072969 + 3 ^ 40 * 1422529 * 2
def baseEnd_1422529 : Nat := 108213499549595567769691

theorem tailTrace_1422529 : CollatzResearch.WordTrace tailWord_1422529 prefixEnd_1422529 108213499549595567769691 := by
  unfold tailWord_1422529
  simp only [CollatzResearch.WordTrace]
  refine ⟨51883895063427856456182641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34589263375618570970788427 51883895063427856456182641)
  ·
    refine ⟨38912921297570892342136981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51883895063427856456182641 38912921297570892342136981)
    ·
      refine ⟨1824043185823635578537671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38912921297570892342136981 1824043185823635578537671)
      ·
        refine ⟨2736064778735453367806507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824043185823635578537671 2736064778735453367806507)
        ·
          refine ⟨4104097168103180051709761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736064778735453367806507 4104097168103180051709761)
          ·
            refine ⟨3078072876077385038782321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4104097168103180051709761 3078072876077385038782321)
            ·
              refine ⟨2308554657058038779086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078072876077385038782321 2308554657058038779086741)
              ·
                refine ⟨108213499549595567769691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2308554657058038779086741 108213499549595567769691)
                ·
                  rfl

theorem cell21_1422529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_1422529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422529 prefixEnd_1422529 := by exact prefixLift 1422529
  have htrace : WordTrace (prefixWord ++ tailWord_1422529) baseStart_1422529 baseEnd_1422529 := by
    simpa [prefixWord, tailWord_1422529, baseEnd_1422529] using wordTrace_append hprefix tailTrace_1422529
  have hstable : (prefixWord ++ tailWord_1422529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422529).length < 2 ^ (prefixWord ++ tailWord_1422529).sum := by decide
  have hdescent : baseEnd_1422529 < baseStart_1422529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422532 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1422532 : Nat := 118140960795 + 1422532 * 2 ^ 59
def prefixEnd_1422532 : Nat := 4983230072969 + 3 ^ 40 * 1422532 * 2
def baseEnd_1422532 : Nat := 324641183289659364759067

theorem tailTrace_1422532 : CollatzResearch.WordTrace tailWord_1422532 prefixEnd_1422532 324641183289659364759067 := by
  unfold tailWord_1422532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25942002241208493984270925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34589336321611325312361233 25942002241208493984270925)
  ·
    refine ⟨9728250840453185244101597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25942002241208493984270925 9728250840453185244101597)
    ·
      refine ⟨3648094065169944466538099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9728250840453185244101597 3648094065169944466538099)
      ·
        refine ⟨5472141097754916699807149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648094065169944466538099 5472141097754916699807149)
        ·
          refine ⟨2052052911658093762427681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5472141097754916699807149 2052052911658093762427681)
          ·
            refine ⟨1539039683743570321820761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052052911658093762427681 1539039683743570321820761)
            ·
              refine ⟨1154279762807677741365571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539039683743570321820761 1154279762807677741365571)
              ·
                refine ⟨1731419644211516612048357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154279762807677741365571 1731419644211516612048357)
                ·
                  refine ⟨324641183289659364759067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731419644211516612048357 324641183289659364759067)
                  ·
                    rfl

theorem cell21_1422532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1422532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422532 prefixEnd_1422532 := by exact prefixLift 1422532
  have htrace : WordTrace (prefixWord ++ tailWord_1422532) baseStart_1422532 baseEnd_1422532 := by
    simpa [prefixWord, tailWord_1422532, baseEnd_1422532] using wordTrace_append hprefix tailTrace_1422532
  have hstable : (prefixWord ++ tailWord_1422532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422532).length < 2 ^ (prefixWord ++ tailWord_1422532).sum := by decide
  have hdescent : baseEnd_1422532 < baseStart_1422532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422580 : List Nat := [2, 6, 1, 2, 2, 1, 1, 6]
def baseStart_1422580 : Nat := 118140960795 + 1422580 * 2 ^ 59
def prefixEnd_1422580 : Nat := 4983230072969 + 3 ^ 40 * 1422580 * 2
def baseEnd_1422580 : Nat := 108217379181207315986323

theorem tailTrace_1422580 : CollatzResearch.WordTrace tailWord_1422580 prefixEnd_1422580 108217379181207315986323 := by
  unfold tailWord_1422580
  simp only [CollatzResearch.WordTrace]
  refine ⟨25942877593121546083144597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34590503457495394777526129 25942877593121546083144597)
  ·
    refine ⟨1216072387177572472647403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25942877593121546083144597 1216072387177572472647403)
    ·
      refine ⟨1824108580766358708971105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216072387177572472647403 1824108580766358708971105)
      ·
        refine ⟨1368081435574769031728329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824108580766358708971105 1368081435574769031728329)
        ·
          refine ⟨1026061076681076773796247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1368081435574769031728329 1026061076681076773796247)
          ·
            refine ⟨1539091615021615160694371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026061076681076773796247 1539091615021615160694371)
            ·
              refine ⟨2308637422532422741041557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539091615021615160694371 2308637422532422741041557)
              ·
                refine ⟨108217379181207315986323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2308637422532422741041557 108217379181207315986323)
                ·
                  rfl

theorem cell21_1422580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_1422580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422580 prefixEnd_1422580 := by exact prefixLift 1422580
  have htrace : WordTrace (prefixWord ++ tailWord_1422580) baseStart_1422580 baseEnd_1422580 := by
    simpa [prefixWord, tailWord_1422580, baseEnd_1422580] using wordTrace_append hprefix tailTrace_1422580
  have hstable : (prefixWord ++ tailWord_1422580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422580).length < 2 ^ (prefixWord ++ tailWord_1422580).sum := by decide
  have hdescent : baseEnd_1422580 < baseStart_1422580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422650 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_1422650 : Nat := 118140960795 + 1422650 * 2 ^ 59
def prefixEnd_1422650 : Nat := 4983230072969 + 3 ^ 40 * 1422650 * 2
def baseEnd_1422650 : Nat := 324668112497317381792159

theorem tailTrace_1422650 : CollatzResearch.WordTrace tailWord_1422650 prefixEnd_1422650 324668112497317381792159 := by
  unfold tailWord_1422650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972077073997373530334351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34592205530659662747558269 12972077073997373530334351)
  ·
    refine ⟨19458115610996060295501527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12972077073997373530334351 19458115610996060295501527)
    ·
      refine ⟨29187173416494090443252291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19458115610996060295501527 29187173416494090443252291)
      ·
        refine ⟨43780760124741135664878437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29187173416494090443252291 43780760124741135664878437)
        ·
          refine ⟨8208892523388962937164707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43780760124741135664878437 8208892523388962937164707)
          ·
            refine ⟨12313338785083444405747061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8208892523388962937164707 12313338785083444405747061)
            ·
              refine ⟨1154375511101572913038787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12313338785083444405747061 1154375511101572913038787)
              ·
                refine ⟨1731563266652359369558181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154375511101572913038787 1731563266652359369558181)
                ·
                  refine ⟨324668112497317381792159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731563266652359369558181 324668112497317381792159)
                  ·
                    rfl

theorem cell21_1422650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_1422650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422650 prefixEnd_1422650 := by exact prefixLift 1422650
  have htrace : WordTrace (prefixWord ++ tailWord_1422650) baseStart_1422650 baseEnd_1422650 := by
    simpa [prefixWord, tailWord_1422650, baseEnd_1422650] using wordTrace_append hprefix tailTrace_1422650
  have hstable : (prefixWord ++ tailWord_1422650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422650).length < 2 ^ (prefixWord ++ tailWord_1422650).sum := by decide
  have hdescent : baseEnd_1422650 < baseStart_1422650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422723 : List Nat := [1, 1, 1, 3, 5, 1, 2, 7]
def baseStart_1422723 : Nat := 118140960795 + 1422723 * 2 ^ 59
def prefixEnd_1422723 : Nat := 4983230072969 + 3 ^ 40 * 1422723 * 2
def baseEnd_1422723 : Nat := 108228257363961825691781

theorem tailTrace_1422723 : CollatzResearch.WordTrace tailWord_1422723 prefixEnd_1422723 108228257363961825691781 := by
  unfold tailWord_1422723
  simp only [CollatzResearch.WordTrace]
  refine ⟨51890970824725027588744823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34593980549816685059163215 51890970824725027588744823)
  ·
    refine ⟨77836456237087541383117235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51890970824725027588744823 77836456237087541383117235)
    ·
      refine ⟨116754684355631312074675853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77836456237087541383117235 116754684355631312074675853)
      ·
        refine ⟨43783006633361742028003445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116754684355631312074675853 43783006633361742028003445)
        ·
          refine ⟨4104656871877663315125323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43783006633361742028003445 4104656871877663315125323)
          ·
            refine ⟨6156985307816494972687985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104656871877663315125323 6156985307816494972687985)
            ·
              refine ⟨4617738980862371229515989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156985307816494972687985 4617738980862371229515989)
              ·
                refine ⟨108228257363961825691781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4617738980862371229515989 108228257363961825691781)
                ·
                  rfl

theorem cell21_1422723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_1422723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422723 prefixEnd_1422723 := by exact prefixLift 1422723
  have htrace : WordTrace (prefixWord ++ tailWord_1422723) baseStart_1422723 baseEnd_1422723 := by
    simpa [prefixWord, tailWord_1422723, baseEnd_1422723] using wordTrace_append hprefix tailTrace_1422723
  have hstable : (prefixWord ++ tailWord_1422723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422723).length < 2 ^ (prefixWord ++ tailWord_1422723).sum := by decide
  have hdescent : baseEnd_1422723 < baseStart_1422723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422737 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_1422737 : Nat := 118140960795 + 1422737 * 2 ^ 59
def prefixEnd_1422737 : Nat := 4983230072969 + 3 ^ 40 * 1422737 * 2
def baseEnd_1422737 : Nat := 324687967082624563841981

theorem tailTrace_1422737 : CollatzResearch.WordTrace tailWord_1422737 prefixEnd_1422737 324687967082624563841981 := by
  unfold tailWord_1422737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891481446674307979754465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34594320964449538653169643 51891481446674307979754465)
  ·
    refine ⟨38918611085005730984815849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51891481446674307979754465 38918611085005730984815849)
    ·
      refine ⟨29188958313754298238611887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38918611085005730984815849 29188958313754298238611887)
      ·
        refine ⟨43783437470631447357917831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29188958313754298238611887 43783437470631447357917831)
        ·
          refine ⟨65675156205947171036876747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43783437470631447357917831 65675156205947171036876747)
          ·
            refine ⟨98512734308920756555315121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65675156205947171036876747 98512734308920756555315121)
            ·
              refine ⟨73884550731690567416486341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98512734308920756555315121 73884550731690567416486341)
              ·
                refine ⟨13853353262191981390591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73884550731690567416486341 13853353262191981390591189)
                ·
                  refine ⟨324687967082624563841981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13853353262191981390591189 324687967082624563841981)
                  ·
                    rfl

theorem cell21_1422737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_1422737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422737 prefixEnd_1422737 := by exact prefixLift 1422737
  have htrace : WordTrace (prefixWord ++ tailWord_1422737) baseStart_1422737 baseEnd_1422737 := by
    simpa [prefixWord, tailWord_1422737, baseEnd_1422737] using wordTrace_append hprefix tailTrace_1422737
  have hstable : (prefixWord ++ tailWord_1422737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422737).length < 2 ^ (prefixWord ++ tailWord_1422737).sum := by decide
  have hdescent : baseEnd_1422737 < baseStart_1422737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422788 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1422788 : Nat := 118140960795 + 1422788 * 2 ^ 59
def prefixEnd_1422788 : Nat := 4983230072969 + 3 ^ 40 * 1422788 * 2
def baseEnd_1422788 : Nat := 324699605977459808491877

theorem tailTrace_1422788 : CollatzResearch.WordTrace tailWord_1422788 prefixEnd_1422788 324699605977459808491877 := by
  unfold tailWord_1422788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25946670784744771844930509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34595561046326362459907345 25946670784744771844930509)
  ·
    refine ⟨9730001544279289441848941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25946670784744771844930509 9730001544279289441848941)
    ·
      refine ⟨3648750579104733540693353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9730001544279289441848941 3648750579104733540693353)
      ·
        refine ⟨2736562934328550155520015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648750579104733540693353 2736562934328550155520015)
        ·
          refine ⟨4104844401492825233280023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736562934328550155520015 4104844401492825233280023)
          ·
            refine ⟨6157266602239237849920035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104844401492825233280023 6157266602239237849920035)
            ·
              refine ⟨9235899903358856774880053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157266602239237849920035 9235899903358856774880053)
              ·
                refine ⟨865865615939892822645005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9235899903358856774880053 865865615939892822645005)
                ·
                  refine ⟨324699605977459808491877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865865615939892822645005 324699605977459808491877)
                  ·
                    rfl

theorem cell21_1422788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1422788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422788 prefixEnd_1422788 := by exact prefixLift 1422788
  have htrace : WordTrace (prefixWord ++ tailWord_1422788) baseStart_1422788 baseEnd_1422788 := by
    simpa [prefixWord, tailWord_1422788, baseEnd_1422788] using wordTrace_append hprefix tailTrace_1422788
  have hstable : (prefixWord ++ tailWord_1422788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422788).length < 2 ^ (prefixWord ++ tailWord_1422788).sum := by decide
  have hdescent : baseEnd_1422788 < baseStart_1422788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422830 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1422830 : Nat := 118140960795 + 1422830 * 2 ^ 59
def prefixEnd_1422830 : Nat := 4983230072969 + 3 ^ 40 * 1422830 * 2
def baseEnd_1422830 : Nat := 324709190949677068791791

theorem tailTrace_1422830 : CollatzResearch.WordTrace tailWord_1422830 prefixEnd_1422830 324709190949677068791791 := by
  unfold tailWord_1422830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486859179417173107861243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34596582290224923241926629 6486859179417173107861243)
  ·
    refine ⟨9730288769125759661791865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486859179417173107861243 9730288769125759661791865)
    ·
      refine ⟨7297716576844319746343899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9730288769125759661791865 7297716576844319746343899)
      ·
        refine ⟨10946574865266479619515849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297716576844319746343899 10946574865266479619515849)
        ·
          refine ⟨8209931148949859714636887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10946574865266479619515849 8209931148949859714636887)
          ·
            refine ⟨12314896723424789571955331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209931148949859714636887 12314896723424789571955331)
            ·
              refine ⟨18472345085137184357932997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12314896723424789571955331 18472345085137184357932997)
              ·
                refine ⟨3463564703463222067112437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18472345085137184357932997 3463564703463222067112437)
                ·
                  refine ⟨324709190949677068791791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3463564703463222067112437 324709190949677068791791)
                  ·
                    rfl

theorem cell21_1422830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1422830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422830 prefixEnd_1422830 := by exact prefixLift 1422830
  have htrace : WordTrace (prefixWord ++ tailWord_1422830) baseStart_1422830 baseEnd_1422830 := by
    simpa [prefixWord, tailWord_1422830, baseEnd_1422830] using wordTrace_append hprefix tailTrace_1422830
  have hstable : (prefixWord ++ tailWord_1422830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422830).length < 2 ^ (prefixWord ++ tailWord_1422830).sum := by decide
  have hdescent : baseEnd_1422830 < baseStart_1422830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1422844 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1422844 : Nat := 118140960795 + 1422844 * 2 ^ 59
def prefixEnd_1422844 : Nat := 4983230072969 + 3 ^ 40 * 1422844 * 2
def baseEnd_1422844 : Nat := 324712385940416155558429

theorem tailTrace_1422844 : CollatzResearch.WordTrace tailWord_1422844 prefixEnd_1422844 324712385940416155558429 := by
  unfold tailWord_1422844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25947692028643332626949793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34596922704857776835933057 25947692028643332626949793)
  ·
    refine ⟨19460769021482499470212345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25947692028643332626949793 19460769021482499470212345)
    ·
      refine ⟨14595576766111874602659259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19460769021482499470212345 14595576766111874602659259)
      ·
        refine ⟨21893365149167811903988889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14595576766111874602659259 21893365149167811903988889)
        ·
          refine ⟨16420023861875858927991667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21893365149167811903988889 16420023861875858927991667)
          ·
            refine ⟨24630035792813788391987501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16420023861875858927991667 24630035792813788391987501)
            ·
              refine ⟨9236263422305170646995313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24630035792813788391987501 9236263422305170646995313)
              ·
                refine ⟨6927197566728877985246485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9236263422305170646995313 6927197566728877985246485)
                ·
                  refine ⟨324712385940416155558429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6927197566728877985246485 324712385940416155558429)
                  ·
                    rfl

theorem cell21_1422844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1422844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1422844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1422844 prefixEnd_1422844 := by exact prefixLift 1422844
  have htrace : WordTrace (prefixWord ++ tailWord_1422844) baseStart_1422844 baseEnd_1422844 := by
    simpa [prefixWord, tailWord_1422844, baseEnd_1422844] using wordTrace_append hprefix tailTrace_1422844
  have hstable : (prefixWord ++ tailWord_1422844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1422844).length < 2 ^ (prefixWord ++ tailWord_1422844).sum := by decide
  have hdescent : baseEnd_1422844 < baseStart_1422844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1422844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423030 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1423030 : Nat := 118140960795 + 1423030 * 2 ^ 59
def prefixEnd_1423030 : Nat := 4983230072969 + 3 ^ 40 * 1423030 * 2
def baseEnd_1423030 : Nat := 324754833674521165458049

theorem tailTrace_1423030 : CollatzResearch.WordTrace tailWord_1423030 prefixEnd_1423030 324754833674521165458049 := by
  unfold tailWord_1423030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243885502163301188760659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34601445356408546013447029 3243885502163301188760659)
  ·
    refine ⟨4865828253244951783140989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243885502163301188760659 4865828253244951783140989)
    ·
      refine ⟨1824685594966856918677871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4865828253244951783140989 1824685594966856918677871)
      ·
        refine ⟨2737028392450285378016807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824685594966856918677871 2737028392450285378016807)
        ·
          refine ⟨4105542588675428067025211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737028392450285378016807 4105542588675428067025211)
          ·
            refine ⟨6158313883013142100537817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105542588675428067025211 6158313883013142100537817)
            ·
              refine ⟨4618735412259856575403363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158313883013142100537817 4618735412259856575403363)
              ·
                refine ⟨6928103118389784863105045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618735412259856575403363 6928103118389784863105045)
                ·
                  refine ⟨324754833674521165458049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6928103118389784863105045 324754833674521165458049)
                  ·
                    rfl

theorem cell21_1423030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1423030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423030 prefixEnd_1423030 := by exact prefixLift 1423030
  have htrace : WordTrace (prefixWord ++ tailWord_1423030) baseStart_1423030 baseEnd_1423030 := by
    simpa [prefixWord, tailWord_1423030, baseEnd_1423030] using wordTrace_append hprefix tailTrace_1423030
  have hstable : (prefixWord ++ tailWord_1423030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423030).length < 2 ^ (prefixWord ++ tailWord_1423030).sum := by decide
  have hdescent : baseEnd_1423030 < baseStart_1423030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423089 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_1423089 : Nat := 118140960795 + 1423089 * 2 ^ 59
def prefixEnd_1423089 : Nat := 4983230072969 + 3 ^ 40 * 1423089 * 2
def baseEnd_1423089 : Nat := 324768298278350173974595

theorem tailTrace_1423089 : CollatzResearch.WordTrace tailWord_1423089 prefixEnd_1423089 324768298278350173974595 := by
  unfold tailWord_1423089
  simp only [CollatzResearch.WordTrace]
  refine ⟨51904319941399072096568321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34602879960932714731045547 51904319941399072096568321)
  ·
    refine ⟨38928239956049304072426241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51904319941399072096568321 38928239956049304072426241)
    ·
      refine ⟨29196179967036978054319681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38928239956049304072426241 29196179967036978054319681)
      ·
        refine ⟨21897134975277733540739761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29196179967036978054319681 21897134975277733540739761)
        ·
          refine ⟨16422851231458300155554821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21897134975277733540739761 16422851231458300155554821)
          ·
            refine ⟨3079284605898431279166529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16422851231458300155554821 3079284605898431279166529)
            ·
              refine ⟨2309463454423823459374897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079284605898431279166529 2309463454423823459374897)
              ·
                refine ⟨1732097590817867594531173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309463454423823459374897 1732097590817867594531173)
                ·
                  refine ⟨324768298278350173974595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732097590817867594531173 324768298278350173974595)
                  ·
                    rfl

theorem cell21_1423089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_1423089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423089 prefixEnd_1423089 := by exact prefixLift 1423089
  have htrace : WordTrace (prefixWord ++ tailWord_1423089) baseStart_1423089 baseEnd_1423089 := by
    simpa [prefixWord, tailWord_1423089, baseEnd_1423089] using wordTrace_append hprefix tailTrace_1423089
  have hstable : (prefixWord ++ tailWord_1423089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423089).length < 2 ^ (prefixWord ++ tailWord_1423089).sum := by decide
  have hdescent : baseEnd_1423089 < baseStart_1423089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423131 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_1423131 : Nat := 118140960795 + 1423131 * 2 ^ 59
def prefixEnd_1423131 : Nat := 4983230072969 + 3 ^ 40 * 1423131 * 2
def baseEnd_1423131 : Nat := 324777883250567434274509

theorem tailTrace_1423131 : CollatzResearch.WordTrace tailWord_1423131 prefixEnd_1423131 324777883250567434274509 := by
  unfold tailWord_1423131
  simp only [CollatzResearch.WordTrace]
  refine ⟨51905851807246913269597247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34603901204831275513064831 51905851807246913269597247)
  ·
    refine ⟨77858777710870369904395871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51905851807246913269597247 77858777710870369904395871)
    ·
      refine ⟨116788166566305554856593807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77858777710870369904395871 116788166566305554856593807)
      ·
        refine ⟨175182249849458332284890711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116788166566305554856593807 175182249849458332284890711)
        ·
          refine ⟨262773374774187498427336067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175182249849458332284890711 262773374774187498427336067)
          ·
            refine ⟨394160062161281247641004101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262773374774187498427336067 394160062161281247641004101)
            ·
              refine ⟨73905011655240233932688269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394160062161281247641004101 73905011655240233932688269)
              ·
                refine ⟨27714379370715087724758101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73905011655240233932688269 27714379370715087724758101)
                ·
                  refine ⟨324777883250567434274509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27714379370715087724758101 324777883250567434274509)
                  ·
                    rfl

theorem cell21_1423131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_1423131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423131 prefixEnd_1423131 := by exact prefixLift 1423131
  have htrace : WordTrace (prefixWord ++ tailWord_1423131) baseStart_1423131 baseEnd_1423131 := by
    simpa [prefixWord, tailWord_1423131, baseEnd_1423131] using wordTrace_append hprefix tailTrace_1423131
  have hstable : (prefixWord ++ tailWord_1423131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423131).length < 2 ^ (prefixWord ++ tailWord_1423131).sum := by decide
  have hdescent : baseEnd_1423131 < baseStart_1423131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423148 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_1423148 : Nat := 118140960795 + 1423148 * 2 ^ 59
def prefixEnd_1423148 : Nat := 4983230072969 + 3 ^ 40 * 1423148 * 2
def baseEnd_1423148 : Nat := 324781762882179182491141

theorem tailTrace_1423148 : CollatzResearch.WordTrace tailWord_1423148 prefixEnd_1423148 324781762882179182491141 := by
  unfold tailWord_1423148
  simp only [CollatzResearch.WordTrace]
  refine ⟨25953235924092662586483049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34604314565456883448644065 25953235924092662586483049)
  ·
    refine ⟨19464926943069496939862287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25953235924092662586483049 19464926943069496939862287)
    ·
      refine ⟨29197390414604245409793431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19464926943069496939862287 29197390414604245409793431)
      ·
        refine ⟨43796085621906368114690147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29197390414604245409793431 43796085621906368114690147)
        ·
          refine ⟨65694128432859552172035221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43796085621906368114690147 65694128432859552172035221)
          ·
            refine ⟨3079412270290291508064151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65694128432859552172035221 3079412270290291508064151)
            ·
              refine ⟨4619118405435437262096227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079412270290291508064151 4619118405435437262096227)
              ·
                refine ⟨6928677608153155893144341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619118405435437262096227 6928677608153155893144341)
                ·
                  refine ⟨324781762882179182491141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6928677608153155893144341 324781762882179182491141)
                  ·
                    rfl

theorem cell21_1423148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_1423148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423148 prefixEnd_1423148 := by exact prefixLift 1423148
  have htrace : WordTrace (prefixWord ++ tailWord_1423148) baseStart_1423148 baseEnd_1423148 := by
    simpa [prefixWord, tailWord_1423148, baseEnd_1423148] using wordTrace_append hprefix tailTrace_1423148
  have hstable : (prefixWord ++ tailWord_1423148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423148).length < 2 ^ (prefixWord ++ tailWord_1423148).sum := by decide
  have hdescent : baseEnd_1423148 < baseStart_1423148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423196 : List Nat := [2, 2, 4, 2, 2, 2, 7]
def baseStart_1423196 : Nat := 118140960795 + 1423196 * 2 ^ 59
def prefixEnd_1423196 : Nat := 4983230072969 + 3 ^ 40 * 1423196 * 2
def baseEnd_1423196 : Nat := 36088079681793529521227

theorem tailTrace_1423196 : CollatzResearch.WordTrace tailWord_1423196 prefixEnd_1423196 36088079681793529521227 := by
  unfold tailWord_1423196
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954111276005714685356721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34605481701340952913808961 25954111276005714685356721)
  ·
    refine ⟨19465583457004286014017541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25954111276005714685356721 19465583457004286014017541)
    ·
      refine ⟨3649796898188303627628289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19465583457004286014017541 3649796898188303627628289)
      ·
        refine ⟨2737347673641227720721217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649796898188303627628289 2737347673641227720721217)
        ·
          refine ⟨2053010755230920790540913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737347673641227720721217 2053010755230920790540913)
          ·
            refine ⟨1539758066423190592905685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053010755230920790540913 1539758066423190592905685)
            ·
              refine ⟨36088079681793529521227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1539758066423190592905685 36088079681793529521227)
              ·
                rfl

theorem cell21_1423196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 7].length) (baseStart_1423196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423196 prefixEnd_1423196 := by exact prefixLift 1423196
  have htrace : WordTrace (prefixWord ++ tailWord_1423196) baseStart_1423196 baseEnd_1423196 := by
    simpa [prefixWord, tailWord_1423196, baseEnd_1423196] using wordTrace_append hprefix tailTrace_1423196
  have hstable : (prefixWord ++ tailWord_1423196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423196).length < 2 ^ (prefixWord ++ tailWord_1423196).sum := by decide
  have hdescent : baseEnd_1423196 < baseStart_1423196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423317 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1423317 : Nat := 118140960795 + 1423317 * 2 ^ 59
def prefixEnd_1423317 : Nat := 4983230072969 + 3 ^ 40 * 1423317 * 2
def baseEnd_1423317 : Nat := 324820330984672444174129

theorem tailTrace_1423317 : CollatzResearch.WordTrace tailWord_1423317 prefixEnd_1423317 324820330984672444174129 := by
  unfold tailWord_1423317
  simp only [CollatzResearch.WordTrace]
  refine ⟨51912635784573067035868205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34608423856382044690578803 51912635784573067035868205)
  ·
    refine ⟨19467238419214900138450577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51912635784573067035868205 19467238419214900138450577)
    ·
      refine ⟨14600428814411175103837933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19467238419214900138450577 14600428814411175103837933)
      ·
        refine ⟨5475160805404190663939225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14600428814411175103837933 5475160805404190663939225)
        ·
          refine ⟨4106370604053142997954419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5475160805404190663939225 4106370604053142997954419)
          ·
            refine ⟨6159555906079714496931629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106370604053142997954419 6159555906079714496931629)
            ·
              refine ⟨2309833464779892936349361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6159555906079714496931629 2309833464779892936349361)
              ·
                refine ⟨1732375098584919702262021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309833464779892936349361 1732375098584919702262021)
                ·
                  refine ⟨324820330984672444174129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732375098584919702262021 324820330984672444174129)
                  ·
                    rfl

theorem cell21_1423317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1423317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423317 prefixEnd_1423317 := by exact prefixLift 1423317
  have htrace : WordTrace (prefixWord ++ tailWord_1423317) baseStart_1423317 baseEnd_1423317 := by
    simpa [prefixWord, tailWord_1423317, baseEnd_1423317] using wordTrace_append hprefix tailTrace_1423317
  have hstable : (prefixWord ++ tailWord_1423317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423317).length < 2 ^ (prefixWord ++ tailWord_1423317).sum := by decide
  have hdescent : baseEnd_1423317 < baseStart_1423317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423393 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_1423393 : Nat := 118140960795 + 1423393 * 2 ^ 59
def prefixEnd_1423393 : Nat := 4983230072969 + 3 ^ 40 * 1423393 * 2
def baseEnd_1423393 : Nat := 324837675220113200907307

theorem tailTrace_1423393 : CollatzResearch.WordTrace tailWord_1423393 prefixEnd_1423393 324837675220113200907307 := by
  unfold tailWord_1423393
  simp only [CollatzResearch.WordTrace]
  refine ⟨51915407732297732015634833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34610271821531821343756555 51915407732297732015634833)
  ·
    refine ⟨38936555799223299011726125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51915407732297732015634833 38936555799223299011726125)
    ·
      refine ⟨14601208424708737129397297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38936555799223299011726125 14601208424708737129397297)
      ·
        refine ⟨10950906318531552847047973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14601208424708737129397297 10950906318531552847047973)
        ·
          refine ⟨2053294934724666158821495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10950906318531552847047973 2053294934724666158821495)
          ·
            refine ⟨3079942402086999238232243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053294934724666158821495 3079942402086999238232243)
            ·
              refine ⟨4619913603130498857348365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079942402086999238232243 4619913603130498857348365)
              ·
                refine ⟨1732467601173937071505637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4619913603130498857348365 1732467601173937071505637)
                ·
                  refine ⟨324837675220113200907307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732467601173937071505637 324837675220113200907307)
                  ·
                    rfl

theorem cell21_1423393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_1423393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423393 prefixEnd_1423393 := by exact prefixLift 1423393
  have htrace : WordTrace (prefixWord ++ tailWord_1423393) baseStart_1423393 baseEnd_1423393 := by
    simpa [prefixWord, tailWord_1423393, baseEnd_1423393] using wordTrace_append hprefix tailTrace_1423393
  have hstable : (prefixWord ++ tailWord_1423393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423393).length < 2 ^ (prefixWord ++ tailWord_1423393).sum := by decide
  have hdescent : baseEnd_1423393 < baseStart_1423393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423480 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_1423480 : Nat := 118140960795 + 1423480 * 2 ^ 59
def prefixEnd_1423480 : Nat := 4983230072969 + 3 ^ 40 * 1423480 * 2
def baseEnd_1423480 : Nat := 324857529805420382957129

theorem tailTrace_1423480 : CollatzResearch.WordTrace tailWord_1423480 prefixEnd_1423480 324857529805420382957129 := by
  unfold tailWord_1423480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959290441491272937025947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34612387255321697249367929 25959290441491272937025947)
  ·
    refine ⟨38938935662236909405538921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25959290441491272937025947 38938935662236909405538921)
    ·
      refine ⟨29204201746677682054154191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38938935662236909405538921 29204201746677682054154191)
      ·
        refine ⟨43806302620016523081231287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29204201746677682054154191 43806302620016523081231287)
        ·
          refine ⟨65709453930024784621846931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43806302620016523081231287 65709453930024784621846931)
          ·
            refine ⟨98564180895037176932770397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65709453930024784621846931 98564180895037176932770397)
            ·
              refine ⟨36961567835638941349788899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98564180895037176932770397 36961567835638941349788899)
              ·
                refine ⟨55442351753458412024683349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36961567835638941349788899 55442351753458412024683349)
                ·
                  refine ⟨324857529805420382957129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55442351753458412024683349 324857529805420382957129)
                  ·
                    rfl

theorem cell21_1423480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_1423480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423480 prefixEnd_1423480 := by exact prefixLift 1423480
  have htrace : WordTrace (prefixWord ++ tailWord_1423480) baseStart_1423480 baseEnd_1423480 := by
    simpa [prefixWord, tailWord_1423480, baseEnd_1423480] using wordTrace_append hprefix tailTrace_1423480
  have hstable : (prefixWord ++ tailWord_1423480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423480).length < 2 ^ (prefixWord ++ tailWord_1423480).sum := by decide
  have hdescent : baseEnd_1423480 < baseStart_1423480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423497 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1423497 : Nat := 118140960795 + 1423497 * 2 ^ 59
def prefixEnd_1423497 : Nat := 4983230072969 + 3 ^ 40 * 1423497 * 2
def baseEnd_1423497 : Nat := 324861409437032131173761

theorem tailTrace_1423497 : CollatzResearch.WordTrace tailWord_1423497 prefixEnd_1423497 324861409437032131173761 := by
  unfold tailWord_1423497
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919200923920957777420745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34612800615947305184947163 51919200923920957777420745)
  ·
    refine ⟨38939400692940718333065559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51919200923920957777420745 38939400692940718333065559)
    ·
      refine ⟨58409101039411077499598339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38939400692940718333065559 58409101039411077499598339)
      ·
        refine ⟨87613651559116616249397509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58409101039411077499598339 87613651559116616249397509)
        ·
          refine ⟨16427559667334365546762033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87613651559116616249397509 16427559667334365546762033)
          ·
            refine ⟨12320669750500774160071525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16427559667334365546762033 12320669750500774160071525)
            ·
              refine ⟨2310125578218895155013411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12320669750500774160071525 2310125578218895155013411)
              ·
                refine ⟨3465188367328342732520117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310125578218895155013411 3465188367328342732520117)
                ·
                  refine ⟨324861409437032131173761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465188367328342732520117 324861409437032131173761)
                  ·
                    rfl

theorem cell21_1423497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1423497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423497 prefixEnd_1423497 := by exact prefixLift 1423497
  have htrace : WordTrace (prefixWord ++ tailWord_1423497) baseStart_1423497 baseEnd_1423497 := by
    simpa [prefixWord, tailWord_1423497, baseEnd_1423497] using wordTrace_append hprefix tailTrace_1423497
  have hstable : (prefixWord ++ tailWord_1423497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423497).length < 2 ^ (prefixWord ++ tailWord_1423497).sum := by decide
  have hdescent : baseEnd_1423497 < baseStart_1423497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423548 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1423548 : Nat := 118140960795 + 1423548 * 2 ^ 59
def prefixEnd_1423548 : Nat := 4983230072969 + 3 ^ 40 * 1423548 * 2
def baseEnd_1423548 : Nat := 324873048331867375823657

theorem tailTrace_1423548 : CollatzResearch.WordTrace tailWord_1423548 prefixEnd_1423548 324873048331867375823657 := by
  unfold tailWord_1423548
  simp only [CollatzResearch.WordTrace]
  refine ⟨25960530523368096743763649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34614040697824128991684865 25960530523368096743763649)
  ·
    refine ⟨19470397892526072557822737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25960530523368096743763649 19470397892526072557822737)
    ·
      refine ⟨14602798419394554418367053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19470397892526072557822737 14602798419394554418367053)
      ·
        refine ⟨5476049407272957906887645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14602798419394554418367053 5476049407272957906887645)
        ·
          refine ⟨2053518527727359215082867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5476049407272957906887645 2053518527727359215082867)
          ·
            refine ⟨3080277791591038822624301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053518527727359215082867 3080277791591038822624301)
            ·
              refine ⟨1155104171846639558484113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3080277791591038822624301 1155104171846639558484113)
              ·
                refine ⟨866328128884979668863085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155104171846639558484113 866328128884979668863085)
                ·
                  refine ⟨324873048331867375823657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866328128884979668863085 324873048331867375823657)
                  ·
                    rfl

theorem cell21_1423548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1423548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423548 prefixEnd_1423548 := by exact prefixLift 1423548
  have htrace : WordTrace (prefixWord ++ tailWord_1423548) baseStart_1423548 baseEnd_1423548 := by
    simpa [prefixWord, tailWord_1423548, baseEnd_1423548] using wordTrace_append hprefix tailTrace_1423548
  have hstable : (prefixWord ++ tailWord_1423548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423548).length < 2 ^ (prefixWord ++ tailWord_1423548).sum := by decide
  have hdescent : baseEnd_1423548 < baseStart_1423548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423666 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1423666 : Nat := 118140960795 + 1423666 * 2 ^ 59
def prefixEnd_1423666 : Nat := 4983230072969 + 3 ^ 40 * 1423666 * 2
def baseEnd_1423666 : Nat := 324899977539525392856749

theorem tailTrace_1423666 : CollatzResearch.WordTrace tailWord_1423666 prefixEnd_1423666 324899977539525392856749 := by
  unfold tailWord_1423666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981341215077174910080713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34616909906872466426881901 12981341215077174910080713)
  ·
    refine ⟨9736005911307881182560535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12981341215077174910080713 9736005911307881182560535)
    ·
      refine ⟨14604008866961821773840803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9736005911307881182560535 14604008866961821773840803)
      ·
        refine ⟨21906013300442732660761205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604008866961821773840803 21906013300442732660761205)
        ·
          refine ⟨2053688746916506186946363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21906013300442732660761205 2053688746916506186946363)
          ·
            refine ⟨3080533120374759280419545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053688746916506186946363 3080533120374759280419545)
            ·
              refine ⟨2310399840281069460314659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080533120374759280419545 2310399840281069460314659)
              ·
                refine ⟨3465599760421604190471989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310399840281069460314659 3465599760421604190471989)
                ·
                  refine ⟨324899977539525392856749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465599760421604190471989 324899977539525392856749)
                  ·
                    rfl

theorem cell21_1423666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1423666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423666 prefixEnd_1423666 := by exact prefixLift 1423666
  have htrace : WordTrace (prefixWord ++ tailWord_1423666) baseStart_1423666 baseEnd_1423666 := by
    simpa [prefixWord, tailWord_1423666, baseEnd_1423666] using wordTrace_append hprefix tailTrace_1423666
  have hstable : (prefixWord ++ tailWord_1423666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423666).length < 2 ^ (prefixWord ++ tailWord_1423666).sum := by decide
  have hdescent : baseEnd_1423666 < baseStart_1423666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423773 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1423773 : Nat := 118140960795 + 1423773 * 2 ^ 59
def prefixEnd_1423773 : Nat := 4983230072969 + 3 ^ 40 * 1423773 * 2
def baseEnd_1423773 : Nat := 324924396397316984573197

theorem tailTrace_1423773 : CollatzResearch.WordTrace tailWord_1423773 prefixEnd_1423773 324924396397316984573197 := by
  unfold tailWord_1423773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51929267470921056914467973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34619511647280704609645315 51929267470921056914467973)
  ·
    refine ⟨9736737650797698171462745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51929267470921056914467973 9736737650797698171462745)
    ·
      refine ⟨7302553238098273628597059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9736737650797698171462745 7302553238098273628597059)
      ·
        refine ⟨10953829857147410442895589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302553238098273628597059 10953829857147410442895589)
        ·
          refine ⟨2053843098215139458042923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10953829857147410442895589 2053843098215139458042923)
          ·
            refine ⟨3080764647322709187064385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053843098215139458042923 3080764647322709187064385)
            ·
              refine ⟨2310573485492031890298289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080764647322709187064385 2310573485492031890298289)
              ·
                refine ⟨1732930114119023917723717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310573485492031890298289 1732930114119023917723717)
                ·
                  refine ⟨324924396397316984573197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732930114119023917723717 324924396397316984573197)
                  ·
                    rfl

theorem cell21_1423773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1423773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423773 prefixEnd_1423773 := by exact prefixLift 1423773
  have htrace : WordTrace (prefixWord ++ tailWord_1423773) baseStart_1423773 baseEnd_1423773 := by
    simpa [prefixWord, tailWord_1423773, baseEnd_1423773] using wordTrace_append hprefix tailTrace_1423773
  have hstable : (prefixWord ++ tailWord_1423773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423773).length < 2 ^ (prefixWord ++ tailWord_1423773).sum := by decide
  have hdescent : baseEnd_1423773 < baseStart_1423773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423801 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_1423801 : Nat := 118140960795 + 1423801 * 2 ^ 59
def prefixEnd_1423801 : Nat := 4983230072969 + 3 ^ 40 * 1423801 * 2
def baseEnd_1423801 : Nat := 324930786378795158106473

theorem tailTrace_1423801 : CollatzResearch.WordTrace tailWord_1423801 prefixEnd_1423801 324930786378795158106473 := by
  unfold tailWord_1423801
  simp only [CollatzResearch.WordTrace]
  refine ⟨51930288714819617696487257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34620192476546411797658171 51930288714819617696487257)
  ·
    refine ⟨38947716536114713272365443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51930288714819617696487257 38947716536114713272365443)
    ·
      refine ⟨58421574804172069908548165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38947716536114713272365443 58421574804172069908548165)
      ·
        refine ⟨10954045275782263107852781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58421574804172069908548165 10954045275782263107852781)
        ·
          refine ⟨4107766978418348665444793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954045275782263107852781 4107766978418348665444793)
          ·
            refine ⟨3080825233813761499083595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4107766978418348665444793 3080825233813761499083595)
            ·
              refine ⟨4621237850720642248625393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080825233813761499083595 4621237850720642248625393)
              ·
                refine ⟨3465928388040481686469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621237850720642248625393 3465928388040481686469045)
                ·
                  refine ⟨324930786378795158106473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465928388040481686469045 324930786378795158106473)
                  ·
                    rfl

theorem cell21_1423801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_1423801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423801 prefixEnd_1423801 := by exact prefixLift 1423801
  have htrace : WordTrace (prefixWord ++ tailWord_1423801) baseStart_1423801 baseEnd_1423801 := by
    simpa [prefixWord, tailWord_1423801, baseEnd_1423801] using wordTrace_append hprefix tailTrace_1423801
  have hstable : (prefixWord ++ tailWord_1423801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423801).length < 2 ^ (prefixWord ++ tailWord_1423801).sum := by decide
  have hdescent : baseEnd_1423801 < baseStart_1423801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423818 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_1423818 : Nat := 118140960795 + 1423818 * 2 ^ 59
def prefixEnd_1423818 : Nat := 4983230072969 + 3 ^ 40 * 1423818 * 2
def baseEnd_1423818 : Nat := 324934666010406906323105

theorem tailTrace_1423818 : CollatzResearch.WordTrace tailWord_1423818 prefixEnd_1423818 324934666010406906323105 := by
  unfold tailWord_1423818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12982727188939507399964027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34620605837172019733237405 12982727188939507399964027)
  ·
    refine ⟨19474090783409261099946041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12982727188939507399964027 19474090783409261099946041)
    ·
      refine ⟨14605568087556945824959531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19474090783409261099946041 14605568087556945824959531)
      ·
        refine ⟨21908352131335418737439297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14605568087556945824959531 21908352131335418737439297)
        ·
          refine ⟨16431264098501564053079473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21908352131335418737439297 16431264098501564053079473)
          ·
            refine ⟨12323448073876173039809605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16431264098501564053079473 12323448073876173039809605)
            ·
              refine ⟨2310646513851782444964301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12323448073876173039809605 2310646513851782444964301)
              ·
                refine ⟨866492442694418416861613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310646513851782444964301 866492442694418416861613)
                ·
                  refine ⟨324934666010406906323105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866492442694418416861613 324934666010406906323105)
                  ·
                    rfl

theorem cell21_1423818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_1423818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423818 prefixEnd_1423818 := by exact prefixLift 1423818
  have htrace : WordTrace (prefixWord ++ tailWord_1423818) baseStart_1423818 baseEnd_1423818 := by
    simpa [prefixWord, tailWord_1423818, baseEnd_1423818] using wordTrace_append hprefix tailTrace_1423818
  have hstable : (prefixWord ++ tailWord_1423818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423818).length < 2 ^ (prefixWord ++ tailWord_1423818).sum := by decide
  have hdescent : baseEnd_1423818 < baseStart_1423818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423891 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_1423891 : Nat := 118140960795 + 1423891 * 2 ^ 59
def prefixEnd_1423891 : Nat := 4983230072969 + 3 ^ 40 * 1423891 * 2
def baseEnd_1423891 : Nat := 324951325604975001606289

theorem tailTrace_1423891 : CollatzResearch.WordTrace tailWord_1423891 prefixEnd_1423891 324951325604975001606289 := by
  unfold tailWord_1423891
  simp only [CollatzResearch.WordTrace]
  refine ⟨51933571284493563067263527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34622380856329042044842351 51933571284493563067263527)
  ·
    refine ⟨77900356926740344600895291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51933571284493563067263527 77900356926740344600895291)
    ·
      refine ⟨116850535390110516901342937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77900356926740344600895291 116850535390110516901342937)
      ·
        refine ⟨87637901542582887676007203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116850535390110516901342937 87637901542582887676007203)
        ·
          refine ⟨131456852313874331514010805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87637901542582887676007203 131456852313874331514010805)
          ·
            refine ⟨12324079904425718579438513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131456852313874331514010805 12324079904425718579438513)
            ·
              refine ⟨9243059928319288934578885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12324079904425718579438513 9243059928319288934578885)
              ·
                refine ⟨1733073736559866675233541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9243059928319288934578885 1733073736559866675233541)
                ·
                  refine ⟨324951325604975001606289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733073736559866675233541 324951325604975001606289)
                  ·
                    rfl

theorem cell21_1423891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_1423891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423891 prefixEnd_1423891 := by exact prefixLift 1423891
  have htrace : WordTrace (prefixWord ++ tailWord_1423891) baseStart_1423891 baseEnd_1423891 := by
    simpa [prefixWord, tailWord_1423891, baseEnd_1423891] using wordTrace_append hprefix tailTrace_1423891
  have hstable : (prefixWord ++ tailWord_1423891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423891).length < 2 ^ (prefixWord ++ tailWord_1423891).sum := by decide
  have hdescent : baseEnd_1423891 < baseStart_1423891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1423942 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1423942 : Nat := 118140960795 + 1423942 * 2 ^ 59
def prefixEnd_1423942 : Nat := 4983230072969 + 3 ^ 40 * 1423942 * 2
def baseEnd_1423942 : Nat := 324962964499810246256185

theorem tailTrace_1423942 : CollatzResearch.WordTrace tailWord_1423942 prefixEnd_1423942 324962964499810246256185 := by
  unfold tailWord_1423942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622982231478399961792815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34623620938205865851580053 1622982231478399961792815)
  ·
    refine ⟨2434473347217599942689223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622982231478399961792815 2434473347217599942689223)
    ·
      refine ⟨3651710020826399914033835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434473347217599942689223 3651710020826399914033835)
      ·
        refine ⟨5477565031239599871050753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651710020826399914033835 5477565031239599871050753)
        ·
          refine ⟨4108173773429699903288065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5477565031239599871050753 4108173773429699903288065)
          ·
            refine ⟨3081130330072274927466049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108173773429699903288065 3081130330072274927466049)
            ·
              refine ⟨2310847747554206195599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081130330072274927466049 2310847747554206195599537)
              ·
                refine ⟨1733135810665654646699653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310847747554206195599537 1733135810665654646699653)
                ·
                  refine ⟨324962964499810246256185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733135810665654646699653 324962964499810246256185)
                  ·
                    rfl

theorem cell21_1423942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1423942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1423942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1423942 prefixEnd_1423942 := by exact prefixLift 1423942
  have htrace : WordTrace (prefixWord ++ tailWord_1423942) baseStart_1423942 baseEnd_1423942 := by
    simpa [prefixWord, tailWord_1423942, baseEnd_1423942] using wordTrace_append hprefix tailTrace_1423942
  have hstable : (prefixWord ++ tailWord_1423942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1423942).length < 2 ^ (prefixWord ++ tailWord_1423942).sum := by decide
  have hdescent : baseEnd_1423942 < baseStart_1423942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1423942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424032 : List Nat := [2, 1, 1, 4, 5, 1, 2, 5]
def baseStart_1424032 : Nat := 118140960795 + 1424032 * 2 ^ 59
def prefixEnd_1424032 : Nat := 4983230072969 + 3 ^ 40 * 1424032 * 2
def baseEnd_1424032 : Nat := 108327834575330029918667

theorem tailTrace_1424032 : CollatzResearch.WordTrace tailWord_1424032 prefixEnd_1424032 108327834575330029918667 := by
  unfold tailWord_1424032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969356988491372074073175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34625809317988496098764233 25969356988491372074073175)
  ·
    refine ⟨38954035482737058111109763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25969356988491372074073175 38954035482737058111109763)
    ·
      refine ⟨58431053224105587166664645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38954035482737058111109763 58431053224105587166664645)
      ·
        refine ⟨10955822479519797593749621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58431053224105587166664645 10955822479519797593749621)
        ·
          refine ⟨1027108357454981024414027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10955822479519797593749621 1027108357454981024414027)
          ·
            refine ⟨1540662536182471536621041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027108357454981024414027 1540662536182471536621041)
            ·
              refine ⟨1155496902136853652465781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540662536182471536621041 1155496902136853652465781)
              ·
                refine ⟨108327834575330029918667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155496902136853652465781 108327834575330029918667)
                ·
                  rfl

theorem cell21_1424032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_1424032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424032 prefixEnd_1424032 := by exact prefixLift 1424032
  have htrace : WordTrace (prefixWord ++ tailWord_1424032) baseStart_1424032 baseEnd_1424032 := by
    simpa [prefixWord, tailWord_1424032, baseEnd_1424032] using wordTrace_append hprefix tailTrace_1424032
  have hstable : (prefixWord ++ tailWord_1424032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424032).length < 2 ^ (prefixWord ++ tailWord_1424032).sum := by decide
  have hdescent : baseEnd_1424032 < baseStart_1424032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424074 : List Nat := [3, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1424074 : Nat := 118140960795 + 1424074 * 2 ^ 59
def prefixEnd_1424074 : Nat := 4983230072969 + 3 ^ 40 * 1424074 * 2
def baseEnd_1424074 : Nat := 108331029566069116685305

theorem tailTrace_1424074 : CollatzResearch.WordTrace tailWord_1424074 prefixEnd_1424074 108331029566069116685305 := by
  unfold tailWord_1424074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985061460707646330293819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34626830561887056880783517 12985061460707646330293819)
  ·
    refine ⟨19477592191061469495440729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985061460707646330293819 19477592191061469495440729)
    ·
      refine ⟨14608194143296102121580547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19477592191061469495440729 14608194143296102121580547)
      ·
        refine ⟨21912291214944153182370821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14608194143296102121580547 21912291214944153182370821)
        ·
          refine ⟨4108554602802028721694529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21912291214944153182370821 4108554602802028721694529)
          ·
            refine ⟨3081415952101521541270897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108554602802028721694529 3081415952101521541270897)
            ·
              refine ⟨2311061964076141155953173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081415952101521541270897 2311061964076141155953173)
              ·
                refine ⟨108331029566069116685305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2311061964076141155953173 108331029566069116685305)
                ·
                  rfl

theorem cell21_1424074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1424074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424074 prefixEnd_1424074 := by exact prefixLift 1424074
  have htrace : WordTrace (prefixWord ++ tailWord_1424074) baseStart_1424074 baseEnd_1424074 := by
    simpa [prefixWord, tailWord_1424074, baseEnd_1424074] using wordTrace_append hprefix tailTrace_1424074
  have hstable : (prefixWord ++ tailWord_1424074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424074).length < 2 ^ (prefixWord ++ tailWord_1424074).sum := by decide
  have hdescent : baseEnd_1424074 < baseStart_1424074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424122 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_1424122 : Nat := 118140960795 + 1424122 * 2 ^ 59
def prefixEnd_1424122 : Nat := 4983230072969 + 3 ^ 40 * 1424122 * 2
def baseEnd_1424122 : Nat := 325004042952169933255817

theorem tailTrace_1424122 : CollatzResearch.WordTrace tailWord_1424122 prefixEnd_1424122 325004042952169933255817 := by
  unfold tailWord_1424122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985499136664172379730655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34627997697771126345948413 12985499136664172379730655)
  ·
    refine ⟨19478248704996258569595983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985499136664172379730655 19478248704996258569595983)
    ·
      refine ⟨29217373057494387854393975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19478248704996258569595983 29217373057494387854393975)
      ·
        refine ⟨43826059586241581781590963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29217373057494387854393975 43826059586241581781590963)
        ·
          refine ⟨65739089379362372672386445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43826059586241581781590963 65739089379362372672386445)
          ·
            refine ⟨24652158517260889752144917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65739089379362372672386445 24652158517260889752144917)
            ·
              refine ⟨1155569930496604207131793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24652158517260889752144917 1155569930496604207131793)
              ·
                refine ⟨866677447872453155348845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155569930496604207131793 866677447872453155348845)
                ·
                  refine ⟨325004042952169933255817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866677447872453155348845 325004042952169933255817)
                  ·
                    rfl

theorem cell21_1424122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_1424122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424122 prefixEnd_1424122 := by exact prefixLift 1424122
  have htrace : WordTrace (prefixWord ++ tailWord_1424122) baseStart_1424122 baseEnd_1424122 := by
    simpa [prefixWord, tailWord_1424122, baseEnd_1424122] using wordTrace_append hprefix tailTrace_1424122
  have hstable : (prefixWord ++ tailWord_1424122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424122).length < 2 ^ (prefixWord ++ tailWord_1424122).sum := by decide
  have hdescent : baseEnd_1424122 < baseStart_1424122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424170 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1424170 : Nat := 118140960795 + 1424170 * 2 ^ 59
def prefixEnd_1424170 : Nat := 4983230072969 + 3 ^ 40 * 1424170 * 2
def baseEnd_1424170 : Nat := 325014997206132516455719

theorem tailTrace_1424170 : CollatzResearch.WordTrace tailWord_1424170 prefixEnd_1424170 325014997206132516455719 := by
  unfold tailWord_1424170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985936812620698429167491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34629164833655195811113309 12985936812620698429167491)
  ·
    refine ⟨19478905218931047643751237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985936812620698429167491 19478905218931047643751237)
    ·
      refine ⟨3652294728549571433203357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19478905218931047643751237 3652294728549571433203357)
      ·
        refine ⟨1369610523206089287451259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3652294728549571433203357 1369610523206089287451259)
        ·
          refine ⟨2054415784809133931176889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369610523206089287451259 2054415784809133931176889)
          ·
            refine ⟨1540811838606850448382667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054415784809133931176889 1540811838606850448382667)
            ·
              refine ⟨2311217757910275672574001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540811838606850448382667 2311217757910275672574001)
              ·
                refine ⟨1733413318432706754430501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311217757910275672574001 1733413318432706754430501)
                ·
                  refine ⟨325014997206132516455719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733413318432706754430501 325014997206132516455719)
                  ·
                    rfl

theorem cell21_1424170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1424170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424170 prefixEnd_1424170 := by exact prefixLift 1424170
  have htrace : WordTrace (prefixWord ++ tailWord_1424170) baseStart_1424170 baseEnd_1424170 := by
    simpa [prefixWord, tailWord_1424170, baseEnd_1424170] using wordTrace_append hprefix tailTrace_1424170
  have hstable : (prefixWord ++ tailWord_1424170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424170).length < 2 ^ (prefixWord ++ tailWord_1424170).sum := by decide
  have hdescent : baseEnd_1424170 < baseStart_1424170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424181 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1424181 : Nat := 118140960795 + 1424181 * 2 ^ 59
def prefixEnd_1424181 : Nat := 4983230072969 + 3 ^ 40 * 1424181 * 2
def baseEnd_1424181 : Nat := 325017507555998941772363

theorem tailTrace_1424181 : CollatzResearch.WordTrace tailWord_1424181 prefixEnd_1424181 325017507555998941772363 := by
  unfold tailWord_1424181
  simp only [CollatzResearch.WordTrace]
  refine ⟨51944148453442942595320397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34629432302295295063546931 51944148453442942595320397)
  ·
    refine ⟨19479055670041103473245149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51944148453442942595320397 19479055670041103473245149)
    ·
      refine ⟨7304645876265413802466931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19479055670041103473245149 7304645876265413802466931)
      ·
        refine ⟨10956968814398120703700397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7304645876265413802466931 10956968814398120703700397)
        ·
          refine ⟨4108863305399295263887649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10956968814398120703700397 4108863305399295263887649)
          ·
            refine ⟨3081647479049471447915737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108863305399295263887649 3081647479049471447915737)
            ·
              refine ⟨2311235609287103585936803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081647479049471447915737 2311235609287103585936803)
              ·
                refine ⟨3466853413930655378905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311235609287103585936803 3466853413930655378905205)
                ·
                  refine ⟨325017507555998941772363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3466853413930655378905205 325017507555998941772363)
                  ·
                    rfl

theorem cell21_1424181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1424181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424181 prefixEnd_1424181 := by exact prefixLift 1424181
  have htrace : WordTrace (prefixWord ++ tailWord_1424181) baseStart_1424181 baseEnd_1424181 := by
    simpa [prefixWord, tailWord_1424181, baseEnd_1424181] using wordTrace_append hprefix tailTrace_1424181
  have hstable : (prefixWord ++ tailWord_1424181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424181).length < 2 ^ (prefixWord ++ tailWord_1424181).sum := by decide
  have hdescent : baseEnd_1424181 < baseStart_1424181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424240 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_1424240 : Nat := 118140960795 + 1424240 * 2 ^ 59
def prefixEnd_1424240 : Nat := 4983230072969 + 3 ^ 40 * 1424240 * 2
def baseEnd_1424240 : Nat := 325030972159827950288909

theorem tailTrace_1424240 : CollatzResearch.WordTrace tailWord_1424240 prefixEnd_1424240 325030972159827950288909 := by
  unfold tailWord_1424240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25973150180114597835859087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34630866906819463781145449 25973150180114597835859087)
  ·
    refine ⟨38959725270171896753788631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25973150180114597835859087 38959725270171896753788631)
    ·
      refine ⟨58439587905257845130682947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38959725270171896753788631 58439587905257845130682947)
      ·
        refine ⟨87659381857886767696024421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58439587905257845130682947 87659381857886767696024421)
        ·
          refine ⟨16436134098353768943004579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87659381857886767696024421 16436134098353768943004579)
          ·
            refine ⟨24654201147530653414506869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436134098353768943004579 24654201147530653414506869)
            ·
              refine ⟨2311331357580998757610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24654201147530653414506869 2311331357580998757610019)
              ·
                refine ⟨3466997036371498136415029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311331357580998757610019 3466997036371498136415029)
                ·
                  refine ⟨325030972159827950288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3466997036371498136415029 325030972159827950288909)
                  ·
                    rfl

theorem cell21_1424240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_1424240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424240 prefixEnd_1424240 := by exact prefixLift 1424240
  have htrace : WordTrace (prefixWord ++ tailWord_1424240) baseStart_1424240 baseEnd_1424240 := by
    simpa [prefixWord, tailWord_1424240, baseEnd_1424240] using wordTrace_append hprefix tailTrace_1424240
  have hstable : (prefixWord ++ tailWord_1424240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424240).length < 2 ^ (prefixWord ++ tailWord_1424240).sum := by decide
  have hdescent : baseEnd_1424240 < baseStart_1424240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424246 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1424246 : Nat := 118140960795 + 1424246 * 2 ^ 59
def prefixEnd_1424246 : Nat := 4983230072969 + 3 ^ 40 * 1424246 * 2
def baseEnd_1424246 : Nat := 325032341441573273188897

theorem tailTrace_1424246 : CollatzResearch.WordTrace tailWord_1424246 prefixEnd_1424246 325032341441573273188897 := by
  unfold tailWord_1424246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246657449887966168527287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34631012798804972464291061 3246657449887966168527287)
  ·
    refine ⟨4869986174831949252790931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3246657449887966168527287 4869986174831949252790931)
    ·
      refine ⟨7304979262247923879186397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869986174831949252790931 7304979262247923879186397)
      ·
        refine ⟨2739367223342971454694899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7304979262247923879186397 2739367223342971454694899)
        ·
          refine ⟨4109050835014457182042349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739367223342971454694899 4109050835014457182042349)
          ·
            refine ⟨1540894063130421443265881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4109050835014457182042349 1540894063130421443265881)
            ·
              refine ⟨1155670547347816082449411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540894063130421443265881 1155670547347816082449411)
              ·
                refine ⟨1733505821021724123674117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155670547347816082449411 1733505821021724123674117)
                ·
                  refine ⟨325032341441573273188897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733505821021724123674117 325032341441573273188897)
                  ·
                    rfl

theorem cell21_1424246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1424246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424246 prefixEnd_1424246 := by exact prefixLift 1424246
  have htrace : WordTrace (prefixWord ++ tailWord_1424246) baseStart_1424246 baseEnd_1424246 := by
    simpa [prefixWord, tailWord_1424246, baseEnd_1424246] using wordTrace_append hprefix tailTrace_1424246
  have hstable : (prefixWord ++ tailWord_1424246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424246).length < 2 ^ (prefixWord ++ tailWord_1424246).sum := by decide
  have hdescent : baseEnd_1424246 < baseStart_1424246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424330 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1424330 : Nat := 118140960795 + 1424330 * 2 ^ 59
def prefixEnd_1424330 : Nat := 4983230072969 + 3 ^ 40 * 1424330 * 2
def baseEnd_1424330 : Nat := 325051511386007793788725

theorem tailTrace_1424330 : CollatzResearch.WordTrace tailWord_1424330 prefixEnd_1424330 325051511386007793788725 := by
  unfold tailWord_1424330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987395732475785260623611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34633055286602094028329629 12987395732475785260623611)
  ·
    refine ⟨19481093598713677890935417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987395732475785260623611 19481093598713677890935417)
    ·
      refine ⟨14610820199035258418201563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19481093598713677890935417 14610820199035258418201563)
      ·
        refine ⟨21916230298552887627302345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14610820199035258418201563 21916230298552887627302345)
        ·
          refine ⟨16437172723914665720476759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21916230298552887627302345 16437172723914665720476759)
          ·
            refine ⟨24655759085871998580715139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16437172723914665720476759 24655759085871998580715139)
            ·
              refine ⟨36983638628807997871072709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24655759085871998580715139 36983638628807997871072709)
              ·
                refine ⟨6934432242901499600826133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36983638628807997871072709 6934432242901499600826133)
                ·
                  refine ⟨325051511386007793788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6934432242901499600826133 325051511386007793788725)
                  ·
                    rfl

theorem cell21_1424330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1424330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424330 prefixEnd_1424330 := by exact prefixLift 1424330
  have htrace : WordTrace (prefixWord ++ tailWord_1424330) baseStart_1424330 baseEnd_1424330 := by
    simpa [prefixWord, tailWord_1424330, baseEnd_1424330] using wordTrace_append hprefix tailTrace_1424330
  have hstable : (prefixWord ++ tailWord_1424330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424330).length < 2 ^ (prefixWord ++ tailWord_1424330).sum := by decide
  have hdescent : baseEnd_1424330 < baseStart_1424330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424454 : List Nat := [6, 1, 1, 1, 1, 11]
def baseStart_1424454 : Nat := 118140960795 + 1424454 * 2 ^ 59
def prefixEnd_1424454 : Nat := 4983230072969 + 3 ^ 40 * 1424454 * 2
def baseEnd_1424454 : Nat := 12039992958348560508215

theorem tailTrace_1424454 : CollatzResearch.WordTrace tailWord_1424454 prefixEnd_1424454 12039992958348560508215 := by
  unfold tailWord_1424454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623565799420434694375263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34636070387635940146672277 1623565799420434694375263)
  ·
    refine ⟨2435348699130652041562895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623565799420434694375263 2435348699130652041562895)
    ·
      refine ⟨3653023048695978062344343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435348699130652041562895 3653023048695978062344343)
      ·
        refine ⟨5479534573043967093516515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653023048695978062344343 5479534573043967093516515)
        ·
          refine ⟨8219301859565950640274773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479534573043967093516515 8219301859565950640274773)
          ·
            refine ⟨12039992958348560508215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8219301859565950640274773 12039992958348560508215)
            ·
              rfl

theorem cell21_1424454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 11].length) (baseStart_1424454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424454 prefixEnd_1424454 := by exact prefixLift 1424454
  have htrace : WordTrace (prefixWord ++ tailWord_1424454) baseStart_1424454 baseEnd_1424454 := by
    simpa [prefixWord, tailWord_1424454, baseEnd_1424454] using wordTrace_append hprefix tailTrace_1424454
  have hstable : (prefixWord ++ tailWord_1424454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424454).length < 2 ^ (prefixWord ++ tailWord_1424454).sum := by decide
  have hdescent : baseEnd_1424454 < baseStart_1424454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424502 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1424502 : Nat := 118140960795 + 1424502 * 2 ^ 59
def prefixEnd_1424502 : Nat := 4983230072969 + 3 ^ 40 * 1424502 * 2
def baseEnd_1424502 : Nat := 325090764129373716921707

theorem tailTrace_1424502 : CollatzResearch.WordTrace tailWord_1424502 prefixEnd_1424502 325090764129373716921707 := by
  unfold tailWord_1424502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247241017830000901109735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34637237523520009611837173 3247241017830000901109735)
  ·
    refine ⟨4870861526745001351664603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3247241017830000901109735 4870861526745001351664603)
    ·
      refine ⟨7306292290117502027496905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870861526745001351664603 7306292290117502027496905)
      ·
        refine ⟨5479719217588126520622679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7306292290117502027496905 5479719217588126520622679)
        ·
          refine ⟨8219578826382189780934019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479719217588126520622679 8219578826382189780934019)
          ·
            refine ⟨12329368239573284671401029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219578826382189780934019 12329368239573284671401029)
            ·
              refine ⟨2311756544919990875887693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12329368239573284671401029 2311756544919990875887693)
              ·
                refine ⟨866908704344996578457885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311756544919990875887693 866908704344996578457885)
                ·
                  refine ⟨325090764129373716921707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866908704344996578457885 325090764129373716921707)
                  ·
                    rfl

theorem cell21_1424502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1424502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424502 prefixEnd_1424502 := by exact prefixLift 1424502
  have htrace : WordTrace (prefixWord ++ tailWord_1424502) baseStart_1424502 baseEnd_1424502 := by
    simpa [prefixWord, tailWord_1424502, baseEnd_1424502] using wordTrace_append hprefix tailTrace_1424502
  have hstable : (prefixWord ++ tailWord_1424502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424502).length < 2 ^ (prefixWord ++ tailWord_1424502).sum := by decide
  have hdescent : baseEnd_1424502 < baseStart_1424502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424513 : List Nat := [1, 2, 4, 2, 2, 2, 8]
def baseStart_1424513 : Nat := 118140960795 + 1424513 * 2 ^ 59
def prefixEnd_1424513 : Nat := 4983230072969 + 3 ^ 40 * 1424513 * 2
def baseEnd_1424513 : Nat := 36121474942137793582039

theorem tailTrace_1424513 : CollatzResearch.WordTrace tailWord_1424513 prefixEnd_1424513 36121474942137793582039 := by
  unfold tailWord_1424513
  simp only [CollatzResearch.WordTrace]
  refine ⟨51956257488240163296406193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34637504992160108864270795 51956257488240163296406193)
  ·
    refine ⟨38967193116180122472304645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51956257488240163296406193 38967193116180122472304645)
    ·
      refine ⟨7306348709283772963557121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38967193116180122472304645 7306348709283772963557121)
      ·
        refine ⟨5479761531962829722667841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7306348709283772963557121 5479761531962829722667841)
        ·
          refine ⟨4109821148972122292000881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479761531962829722667841 4109821148972122292000881)
          ·
            refine ⟨3082365861729091719000661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4109821148972122292000881 3082365861729091719000661)
            ·
              refine ⟨36121474942137793582039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3082365861729091719000661 36121474942137793582039)
              ·
                rfl

theorem cell21_1424513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 8].length) (baseStart_1424513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424513 prefixEnd_1424513 := by exact prefixLift 1424513
  have htrace : WordTrace (prefixWord ++ tailWord_1424513) baseStart_1424513 baseEnd_1424513 := by
    simpa [prefixWord, tailWord_1424513, baseEnd_1424513] using wordTrace_append hprefix tailTrace_1424513
  have hstable : (prefixWord ++ tailWord_1424513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424513).length < 2 ^ (prefixWord ++ tailWord_1424513).sum := by decide
  have hdescent : baseEnd_1424513 < baseStart_1424513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424516 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1424516 : Nat := 118140960795 + 1424516 * 2 ^ 59
def prefixEnd_1424516 : Nat := 4983230072969 + 3 ^ 40 * 1424516 * 2
def baseEnd_1424516 : Nat := 325093959120112803688345

theorem tailTrace_1424516 : CollatzResearch.WordTrace tailWord_1424516 prefixEnd_1424516 325093959120112803688345 := by
  unfold tailWord_1424516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978183453614647404382701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34637577938152863205843601 25978183453614647404382701)
  ·
    refine ⟨9741818795105492776643513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25978183453614647404382701 9741818795105492776643513)
    ·
      refine ⟨7306364096329119582482635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9741818795105492776643513 7306364096329119582482635)
      ·
        refine ⟨10959546144493679373723953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7306364096329119582482635 10959546144493679373723953)
        ·
          refine ⟨8219659608370259530292965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10959546144493679373723953 8219659608370259530292965)
          ·
            refine ⟨1541186176569423661929931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8219659608370259530292965 1541186176569423661929931)
            ·
              refine ⟨2311779264854135492894897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541186176569423661929931 2311779264854135492894897)
              ·
                refine ⟨1733834448640601619671173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311779264854135492894897 1733834448640601619671173)
                ·
                  refine ⟨325093959120112803688345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733834448640601619671173 325093959120112803688345)
                  ·
                    rfl

theorem cell21_1424516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1424516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424516 prefixEnd_1424516 := by exact prefixLift 1424516
  have htrace : WordTrace (prefixWord ++ tailWord_1424516) baseStart_1424516 baseEnd_1424516 := by
    simpa [prefixWord, tailWord_1424516, baseEnd_1424516] using wordTrace_append hprefix tailTrace_1424516
  have hstable : (prefixWord ++ tailWord_1424516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424516).length < 2 ^ (prefixWord ++ tailWord_1424516).sum := by decide
  have hdescent : baseEnd_1424516 < baseStart_1424516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424685 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1424685 : Nat := 118140960795 + 1424685 * 2 ^ 59
def prefixEnd_1424685 : Nat := 4983230072969 + 3 ^ 40 * 1424685 * 2
def baseEnd_1424685 : Nat := 325132527222606065371333

theorem tailTrace_1424685 : CollatzResearch.WordTrace tailWord_1424685 prefixEnd_1424685 325132527222606065371333 := by
  unfold tailWord_1424685
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962530843617036671667509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34641687229078024447778339 51962530843617036671667509)
  ·
    refine ⟨4871487266589097187968829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51962530843617036671667509 4871487266589097187968829)
    ·
      refine ⟨1826807724970911445488311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4871487266589097187968829 1826807724970911445488311)
      ·
        refine ⟨2740211587456367168232467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826807724970911445488311 2740211587456367168232467)
        ·
          refine ⟨4110317381184550752348701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740211587456367168232467 4110317381184550752348701)
          ·
            refine ⟨1541369017944206532130763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4110317381184550752348701 1541369017944206532130763)
            ·
              refine ⟨2312053526916309798196145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541369017944206532130763 2312053526916309798196145)
              ·
                refine ⟨1734040145187232348647109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312053526916309798196145 1734040145187232348647109)
                ·
                  refine ⟨325132527222606065371333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734040145187232348647109 325132527222606065371333)
                  ·
                    rfl

theorem cell21_1424685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1424685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424685 prefixEnd_1424685 := by exact prefixLift 1424685
  have htrace : WordTrace (prefixWord ++ tailWord_1424685) baseStart_1424685 baseEnd_1424685 := by
    simpa [prefixWord, tailWord_1424685, baseEnd_1424685] using wordTrace_append hprefix tailTrace_1424685
  have hstable : (prefixWord ++ tailWord_1424685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424685).length < 2 ^ (prefixWord ++ tailWord_1424685).sum := by decide
  have hdescent : baseEnd_1424685 < baseStart_1424685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424893 : List Nat := [1, 4, 1, 1, 1, 4, 4, 5]
def baseStart_1424893 : Nat := 118140960795 + 1424893 * 2 ^ 59
def prefixEnd_1424893 : Nat := 4983230072969 + 3 ^ 40 * 1424893 * 2
def baseEnd_1424893 : Nat := 108393331885481308634747

theorem tailTrace_1424893 : CollatzResearch.WordTrace tailWord_1424893 prefixEnd_1424893 108393331885481308634747 := by
  unfold tailWord_1424893
  simp only [CollatzResearch.WordTrace]
  refine ⟨51970117226863488195239333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34646744817908992130159555 51970117226863488195239333)
  ·
    refine ⟨9744396980036904036607375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51970117226863488195239333 9744396980036904036607375)
    ·
      refine ⟨14616595470055356054911063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744396980036904036607375 14616595470055356054911063)
      ·
        refine ⟨21924893205083034082366595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14616595470055356054911063 21924893205083034082366595)
        ·
          refine ⟨32887339807624551123549893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21924893205083034082366595 32887339807624551123549893)
          ·
            refine ⟨6166376213929603335665605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32887339807624551123549893 6166376213929603335665605)
            ·
              refine ⟨1156195540111800625437301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6166376213929603335665605 1156195540111800625437301)
              ·
                refine ⟨108393331885481308634747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156195540111800625437301 108393331885481308634747)
                ·
                  rfl

theorem cell21_1424893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].length) (baseStart_1424893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424893 prefixEnd_1424893 := by exact prefixLift 1424893
  have htrace : WordTrace (prefixWord ++ tailWord_1424893) baseStart_1424893 baseEnd_1424893 := by
    simpa [prefixWord, tailWord_1424893, baseEnd_1424893] using wordTrace_append hprefix tailTrace_1424893
  have hstable : (prefixWord ++ tailWord_1424893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424893).length < 2 ^ (prefixWord ++ tailWord_1424893).sum := by decide
  have hdescent : baseEnd_1424893 < baseStart_1424893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424910 : List Nat := [4, 1, 1, 2, 5, 1, 7]
def baseStart_1424910 : Nat := 118140960795 + 1424910 * 2 ^ 59
def prefixEnd_1424910 : Nat := 4983230072969 + 3 ^ 40 * 1424910 * 2
def baseEnd_1424910 : Nat := 36131541698672852680097

theorem tailTrace_1424910 : CollatzResearch.WordTrace tailWord_1424910 prefixEnd_1424910 36131541698672852680097 := by
  unfold tailWord_1424910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496342158475237512326023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34647158178534600065738789 6496342158475237512326023)
  ·
    refine ⟨9744513237712856268489035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6496342158475237512326023 9744513237712856268489035)
    ·
      refine ⟨14616769856569284402733553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744513237712856268489035 14616769856569284402733553)
      ·
        refine ⟨10962577392426963302050165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14616769856569284402733553 10962577392426963302050165)
        ·
          refine ⟨1027741630540027809567203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10962577392426963302050165 1027741630540027809567203)
          ·
            refine ⟨1541612445810041714350805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027741630540027809567203 1541612445810041714350805)
            ·
              refine ⟨36131541698672852680097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1541612445810041714350805 36131541698672852680097)
              ·
                rfl

theorem cell21_1424910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 7].length) (baseStart_1424910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424910 prefixEnd_1424910 := by exact prefixLift 1424910
  have htrace : WordTrace (prefixWord ++ tailWord_1424910) baseStart_1424910 baseEnd_1424910 := by
    simpa [prefixWord, tailWord_1424910, baseEnd_1424910] using wordTrace_append hprefix tailTrace_1424910
  have hstable : (prefixWord ++ tailWord_1424910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424910).length < 2 ^ (prefixWord ++ tailWord_1424910).sum := by decide
  have hdescent : baseEnd_1424910 < baseStart_1424910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1424952 : List Nat := [2, 1, 2, 1, 4, 2, 2, 7]
def baseStart_1424952 : Nat := 118140960795 + 1424952 * 2 ^ 59
def prefixEnd_1424952 : Nat := 4983230072969 + 3 ^ 40 * 1424952 * 2
def baseEnd_1424952 : Nat := 108397820086757644806929

theorem tailTrace_1424952 : CollatzResearch.WordTrace tailWord_1424952 prefixEnd_1424952 108397820086757644806929 := by
  unfold tailWord_1424952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986134566824870635818555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34648179422433160847758073 25986134566824870635818555)
  ·
    refine ⟨38979201850237305953727833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25986134566824870635818555 38979201850237305953727833)
    ·
      refine ⟨29234401387677979465295875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38979201850237305953727833 29234401387677979465295875)
      ·
        refine ⟨43851602081516969197943813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29234401387677979465295875 43851602081516969197943813)
        ·
          refine ⟨8222175390284431724614465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43851602081516969197943813 8222175390284431724614465)
          ·
            refine ⟨6166631542713323793460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8222175390284431724614465 6166631542713323793460849)
            ·
              refine ⟨4624973657034992845095637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6166631542713323793460849 4624973657034992845095637)
              ·
                refine ⟨108397820086757644806929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4624973657034992845095637 108397820086757644806929)
                ·
                  rfl

theorem cell21_1424952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_1424952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1424952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1424952 prefixEnd_1424952 := by exact prefixLift 1424952
  have htrace : WordTrace (prefixWord ++ tailWord_1424952) baseStart_1424952 baseEnd_1424952 := by
    simpa [prefixWord, tailWord_1424952, baseEnd_1424952] using wordTrace_append hprefix tailTrace_1424952
  have hstable : (prefixWord ++ tailWord_1424952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1424952).length < 2 ^ (prefixWord ++ tailWord_1424952).sum := by decide
  have hdescent : baseEnd_1424952 < baseStart_1424952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1424952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425000 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1425000 : Nat := 118140960795 + 1425000 * 2 ^ 59
def prefixEnd_1425000 : Nat := 4983230072969 + 3 ^ 40 * 1425000 * 2
def baseEnd_1425000 : Nat := 325204414514235517620689

theorem tailTrace_1425000 : CollatzResearch.WordTrace tailWord_1425000 prefixEnd_1425000 325204414514235517620689 := by
  unfold tailWord_1425000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25987009918737922734692227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34649346558317230312922969 25987009918737922734692227)
  ·
    refine ⟨38980514878106884102038341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25987009918737922734692227 38980514878106884102038341)
    ·
      refine ⟨7308846539645040769132189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38980514878106884102038341 7308846539645040769132189)
      ·
        refine ⟨2740817452366890288424571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7308846539645040769132189 2740817452366890288424571)
        ·
          refine ⟨4111226178550335432636857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740817452366890288424571 4111226178550335432636857)
          ·
            refine ⟨3083419633912751574477643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111226178550335432636857 3083419633912751574477643)
            ·
              refine ⟨4625129450869127361716465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083419633912751574477643 4625129450869127361716465)
              ·
                refine ⟨3468847088151845521287349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4625129450869127361716465 3468847088151845521287349)
                ·
                  refine ⟨325204414514235517620689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468847088151845521287349 325204414514235517620689)
                  ·
                    rfl

theorem cell21_1425000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1425000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425000 prefixEnd_1425000 := by exact prefixLift 1425000
  have htrace : WordTrace (prefixWord ++ tailWord_1425000) baseStart_1425000 baseEnd_1425000 := by
    simpa [prefixWord, tailWord_1425000, baseEnd_1425000] using wordTrace_append hprefix tailTrace_1425000
  have hstable : (prefixWord ++ tailWord_1425000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425000).length < 2 ^ (prefixWord ++ tailWord_1425000).sum := by decide
  have hdescent : baseEnd_1425000 < baseStart_1425000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425031 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_1425031 : Nat := 118140960795 + 1425031 * 2 ^ 59
def prefixEnd_1425031 : Nat := 4983230072969 + 3 ^ 40 * 1425031 * 2
def baseEnd_1425031 : Nat := 325211489136586352603959

theorem tailTrace_1425031 : CollatzResearch.WordTrace tailWord_1425031 prefixEnd_1425031 325211489136586352603959 := by
  unfold tailWord_1425031
  simp only [CollatzResearch.WordTrace]
  refine ⟨51975150500363537763762947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34650100333575691842508631 51975150500363537763762947)
  ·
    refine ⟨77962725750545306645644421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51975150500363537763762947 77962725750545306645644421)
    ·
      refine ⟨14618011078227244996058329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77962725750545306645644421 14618011078227244996058329)
      ·
        refine ⟨10963508308670433747043747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14618011078227244996058329 10963508308670433747043747)
        ·
          refine ⟨16445262463005650620565621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963508308670433747043747 16445262463005650620565621)
          ·
            refine ⟨1541743355906779745678027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16445262463005650620565621 1541743355906779745678027)
            ·
              refine ⟨2312615033860169618517041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541743355906779745678027 2312615033860169618517041)
              ·
                refine ⟨1734461275395127213887781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312615033860169618517041 1734461275395127213887781)
                ·
                  refine ⟨325211489136586352603959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734461275395127213887781 325211489136586352603959)
                  ·
                    rfl

theorem cell21_1425031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_1425031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425031 prefixEnd_1425031 := by exact prefixLift 1425031
  have htrace : WordTrace (prefixWord ++ tailWord_1425031) baseStart_1425031 baseEnd_1425031 := by
    simpa [prefixWord, tailWord_1425031, baseEnd_1425031] using wordTrace_append hprefix tailTrace_1425031
  have hstable : (prefixWord ++ tailWord_1425031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425031).length < 2 ^ (prefixWord ++ tailWord_1425031).sum := by decide
  have hdescent : baseEnd_1425031 < baseStart_1425031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425166 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1425166 : Nat := 118140960795 + 1425166 * 2 ^ 59
def prefixEnd_1425166 : Nat := 4983230072969 + 3 ^ 40 * 1425166 * 2
def baseEnd_1425166 : Nat := 325242297975856117853683

theorem tailTrace_1425166 : CollatzResearch.WordTrace tailWord_1425166 prefixEnd_1425166 325242297975856117853683 := by
  unfold tailWord_1425166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497509294359306977490919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34653382903249637213284901 6497509294359306977490919)
  ·
    refine ⟨9746263941538960466236379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497509294359306977490919 9746263941538960466236379)
    ·
      refine ⟨14619395912308440699354569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9746263941538960466236379 14619395912308440699354569)
      ·
        refine ⟨10964546934231330524515927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14619395912308440699354569 10964546934231330524515927)
        ·
          refine ⟨16446820401346995786773891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10964546934231330524515927 16446820401346995786773891)
          ·
            refine ⟨24670230602020493680160837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16446820401346995786773891 24670230602020493680160837)
            ·
              refine ⟨4625668237878842565030157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24670230602020493680160837 4625668237878842565030157)
              ·
                refine ⟨1734625589204565961886309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4625668237878842565030157 1734625589204565961886309)
                ·
                  refine ⟨325242297975856117853683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734625589204565961886309 325242297975856117853683)
                  ·
                    rfl

theorem cell21_1425166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1425166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425166 prefixEnd_1425166 := by exact prefixLift 1425166
  have htrace : WordTrace (prefixWord ++ tailWord_1425166) baseStart_1425166 baseEnd_1425166 := by
    simpa [prefixWord, tailWord_1425166, baseEnd_1425166] using wordTrace_append hprefix tailTrace_1425166
  have hstable : (prefixWord ++ tailWord_1425166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425166).length < 2 ^ (prefixWord ++ tailWord_1425166).sum := by decide
  have hdescent : baseEnd_1425166 < baseStart_1425166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425172 : List Nat := [2, 4, 4, 1, 1, 1, 3, 5]
def baseStart_1425172 : Nat := 118140960795 + 1425172 * 2 ^ 59
def prefixEnd_1425172 : Nat := 4983230072969 + 3 ^ 40 * 1425172 * 2
def baseEnd_1425172 : Nat := 108414555752533813584557

theorem tailTrace_1425172 : CollatzResearch.WordTrace tailWord_1425172 prefixEnd_1425172 108414555752533813584557 := by
  unfold tailWord_1425172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25990146596426359422322885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34653528795235145896430513 25990146596426359422322885)
  ·
    refine ⟨4873152486829942391685541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25990146596426359422322885 4873152486829942391685541)
    ·
      refine ⟨913716091280614198441039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4873152486829942391685541 913716091280614198441039)
      ·
        refine ⟨1370574136920921297661559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913716091280614198441039 1370574136920921297661559)
        ·
          refine ⟨2055861205381381946492339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370574136920921297661559 2055861205381381946492339)
          ·
            refine ⟨3083791808072072919738509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055861205381381946492339 3083791808072072919738509)
            ·
              refine ⟨1156421928027027344901941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3083791808072072919738509 1156421928027027344901941)
              ·
                refine ⟨108414555752533813584557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156421928027027344901941 108414555752533813584557)
                ·
                  rfl

theorem cell21_1425172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_1425172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425172 prefixEnd_1425172 := by exact prefixLift 1425172
  have htrace : WordTrace (prefixWord ++ tailWord_1425172) baseStart_1425172 baseEnd_1425172 := by
    simpa [prefixWord, tailWord_1425172, baseEnd_1425172] using wordTrace_append hprefix tailTrace_1425172
  have hstable : (prefixWord ++ tailWord_1425172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425172).length < 2 ^ (prefixWord ++ tailWord_1425172).sum := by decide
  have hdescent : baseEnd_1425172 < baseStart_1425172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425262 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1425262 : Nat := 118140960795 + 1425262 * 2 ^ 59
def prefixEnd_1425262 : Nat := 4983230072969 + 3 ^ 40 * 1425262 * 2
def baseEnd_1425262 : Nat := 325264206483781284253487

theorem tailTrace_1425262 : CollatzResearch.WordTrace tailWord_1425262 prefixEnd_1425262 325264206483781284253487 := by
  unfold tailWord_1425262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497946970315833026927755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34655717175017776143614693 6497946970315833026927755)
  ·
    refine ⟨9746920455473749540391633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497946970315833026927755 9746920455473749540391633)
    ·
      refine ⟨7310190341605312155293725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9746920455473749540391633 7310190341605312155293725)
      ·
        refine ⟨2741321378101992058235147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7310190341605312155293725 2741321378101992058235147)
        ·
          refine ⟨4111982067152988087352721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741321378101992058235147 4111982067152988087352721)
          ·
            refine ⟨3083986550364741065514541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111982067152988087352721 3083986550364741065514541)
            ·
              refine ⟨1156494956386777899567953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3083986550364741065514541 1156494956386777899567953)
              ·
                refine ⟨867371217290083424675965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156494956386777899567953 867371217290083424675965)
                ·
                  refine ⟨325264206483781284253487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867371217290083424675965 325264206483781284253487)
                  ·
                    rfl

theorem cell21_1425262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1425262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425262 prefixEnd_1425262 := by exact prefixLift 1425262
  have htrace : WordTrace (prefixWord ++ tailWord_1425262) baseStart_1425262 baseEnd_1425262 := by
    simpa [prefixWord, tailWord_1425262, baseEnd_1425262] using wordTrace_append hprefix tailTrace_1425262
  have hstable : (prefixWord ++ tailWord_1425262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425262).length < 2 ^ (prefixWord ++ tailWord_1425262).sum := by decide
  have hdescent : baseEnd_1425262 < baseStart_1425262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425391 : List Nat := [1, 1, 2, 1, 4, 2, 2, 8]
def baseStart_1425391 : Nat := 118140960795 + 1425391 * 2 ^ 59
def prefixEnd_1425391 : Nat := 4983230072969 + 3 ^ 40 * 1425391 * 2
def baseEnd_1425391 : Nat := 108431215347101908867741

theorem tailTrace_1425391 : CollatzResearch.WordTrace tailWord_1425391 prefixEnd_1425391 108431215347101908867741 := by
  unfold tailWord_1425391
  simp only [CollatzResearch.WordTrace]
  refine ⟨51988280779059319246868027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34658853852706212831245351 51988280779059319246868027)
  ·
    refine ⟨77982421168588978870302041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51988280779059319246868027 77982421168588978870302041)
    ·
      refine ⟨58486815876441734152726531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77982421168588978870302041 58486815876441734152726531)
      ·
        refine ⟨87730223814662601229089797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58486815876441734152726531 87730223814662601229089797)
        ·
          refine ⟨16449416965249237730454337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87730223814662601229089797 16449416965249237730454337)
          ·
            refine ⟨12337062723936928297840753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16449416965249237730454337 12337062723936928297840753)
            ·
              refine ⟨9252797042952696223380565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12337062723936928297840753 9252797042952696223380565)
              ·
                refine ⟨108431215347101908867741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9252797042952696223380565 108431215347101908867741)
                ·
                  rfl

theorem cell21_1425391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_1425391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425391 prefixEnd_1425391 := by exact prefixLift 1425391
  have htrace : WordTrace (prefixWord ++ tailWord_1425391) baseStart_1425391 baseEnd_1425391 := by
    simpa [prefixWord, tailWord_1425391, baseEnd_1425391] using wordTrace_append hprefix tailTrace_1425391
  have hstable : (prefixWord ++ tailWord_1425391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425391).length < 2 ^ (prefixWord ++ tailWord_1425391).sum := by decide
  have hdescent : baseEnd_1425391 < baseStart_1425391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425490 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1425490 : Nat := 118140960795 + 1425490 * 2 ^ 59
def prefixEnd_1425490 : Nat := 4983230072969 + 3 ^ 40 * 1425490 * 2
def baseEnd_1425490 : Nat := 325316239190103554453021

theorem tailTrace_1425490 : CollatzResearch.WordTrace tailWord_1425490 prefixEnd_1425490 325316239190103554453021 := by
  unfold tailWord_1425490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997972901425164788680481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34661261070467106103147949 12997972901425164788680481)
  ·
    refine ⟨9748479676068873591510361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12997972901425164788680481 9748479676068873591510361)
    ·
      refine ⟨7311359757051655193632771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9748479676068873591510361 7311359757051655193632771)
      ·
        refine ⟨10967039635577482790449157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7311359757051655193632771 10967039635577482790449157)
        ·
          refine ⟨2056319931670778023209217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10967039635577482790449157 2056319931670778023209217)
          ·
            refine ⟨1542239948753083517406913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056319931670778023209217 1542239948753083517406913)
            ·
              refine ⟨1156679961564812638055185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542239948753083517406913 1156679961564812638055185)
              ·
                refine ⟨867509971173609478541389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156679961564812638055185 867509971173609478541389)
                ·
                  refine ⟨325316239190103554453021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867509971173609478541389 325316239190103554453021)
                  ·
                    rfl

theorem cell21_1425490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1425490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425490 prefixEnd_1425490 := by exact prefixLift 1425490
  have htrace : WordTrace (prefixWord ++ tailWord_1425490) baseStart_1425490 baseEnd_1425490 := by
    simpa [prefixWord, tailWord_1425490, baseEnd_1425490] using wordTrace_append hprefix tailTrace_1425490
  have hstable : (prefixWord ++ tailWord_1425490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425490).length < 2 ^ (prefixWord ++ tailWord_1425490).sum := by decide
  have hdescent : baseEnd_1425490 < baseStart_1425490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425498 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1425498 : Nat := 118140960795 + 1425498 * 2 ^ 59
def prefixEnd_1425498 : Nat := 4983230072969 + 3 ^ 40 * 1425498 * 2
def baseEnd_1425498 : Nat := 325318064899097318319671

theorem tailTrace_1425498 : CollatzResearch.WordTrace tailWord_1425498 prefixEnd_1425498 325318064899097318319671 := by
  unfold tailWord_1425498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998045847417919130253287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34661455593114451014008765 12998045847417919130253287)
  ·
    refine ⟨19497068771126878695379931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998045847417919130253287 19497068771126878695379931)
    ·
      refine ⟨29245603156690318043069897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19497068771126878695379931 29245603156690318043069897)
      ·
        refine ⟨21934202367517738532302423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29245603156690318043069897 21934202367517738532302423)
        ·
          refine ⟨32901303551276607798453635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21934202367517738532302423 32901303551276607798453635)
          ·
            refine ⟨49351955326914911697680453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32901303551276607798453635 49351955326914911697680453)
            ·
              refine ⟨9253491623796545943315085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49351955326914911697680453 9253491623796545943315085)
              ·
                refine ⟨3470059358923704728743157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9253491623796545943315085 3470059358923704728743157)
                ·
                  refine ⟨325318064899097318319671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3470059358923704728743157 325318064899097318319671)
                  ·
                    rfl

theorem cell21_1425498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1425498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425498 prefixEnd_1425498 := by exact prefixLift 1425498
  have htrace : WordTrace (prefixWord ++ tailWord_1425498) baseStart_1425498 baseEnd_1425498 := by
    simpa [prefixWord, tailWord_1425498, baseEnd_1425498] using wordTrace_append hprefix tailTrace_1425498
  have hstable : (prefixWord ++ tailWord_1425498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425498).length < 2 ^ (prefixWord ++ tailWord_1425498).sum := by decide
  have hdescent : baseEnd_1425498 < baseStart_1425498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425501 : List Nat := [1, 4, 4, 1, 1, 1, 3, 6]
def baseStart_1425501 : Nat := 118140960795 + 1425501 * 2 ^ 59
def prefixEnd_1425501 : Nat := 4983230072969 + 3 ^ 40 * 1425501 * 2
def baseEnd_1425501 : Nat := 108439583179989993256555

theorem tailTrace_1425501 : CollatzResearch.WordTrace tailWord_1425501 prefixEnd_1425501 108439583179989993256555 := by
  unfold tailWord_1425501
  simp only [CollatzResearch.WordTrace]
  refine ⟨51992292808660808033372357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34661528539107205355581571 51992292808660808033372357)
  ·
    refine ⟨9748554901623901506257317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51992292808660808033372357 9748554901623901506257317)
    ·
      refine ⟨1827854044054481532423247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9748554901623901506257317 1827854044054481532423247)
      ·
        refine ⟨2741781066081722298634871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827854044054481532423247 2741781066081722298634871)
        ·
          refine ⟨4112671599122583447952307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741781066081722298634871 4112671599122583447952307)
          ·
            refine ⟨6169007398683875171928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112671599122583447952307 6169007398683875171928461)
            ·
              refine ⟨2313377774506453189473173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6169007398683875171928461 2313377774506453189473173)
              ·
                refine ⟨108439583179989993256555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2313377774506453189473173 108439583179989993256555)
                ·
                  rfl

theorem cell21_1425501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_1425501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425501 prefixEnd_1425501 := by exact prefixLift 1425501
  have htrace : WordTrace (prefixWord ++ tailWord_1425501) baseStart_1425501 baseEnd_1425501 := by
    simpa [prefixWord, tailWord_1425501, baseEnd_1425501] using wordTrace_append hprefix tailTrace_1425501
  have hstable : (prefixWord ++ tailWord_1425501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425501).length < 2 ^ (prefixWord ++ tailWord_1425501).sum := by decide
  have hdescent : baseEnd_1425501 < baseStart_1425501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425532 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1425532 : Nat := 118140960795 + 1425532 * 2 ^ 59
def prefixEnd_1425532 : Nat := 4983230072969 + 3 ^ 40 * 1425532 * 2
def baseEnd_1425532 : Nat := 325325824162320814752935

theorem tailTrace_1425532 : CollatzResearch.WordTrace tailWord_1425532 prefixEnd_1425532 325325824162320814752935 := by
  unfold tailWord_1425532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996711735774250163875425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34662282314365666885167233 25996711735774250163875425)
  ·
    refine ⟨19497533801830687622906569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25996711735774250163875425 19497533801830687622906569)
    ·
      refine ⟨14623150351373015717179927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19497533801830687622906569 14623150351373015717179927)
      ·
        refine ⟨21934725527059523575769891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14623150351373015717179927 21934725527059523575769891)
        ·
          refine ⟨32902088290589285363654837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21934725527059523575769891 32902088290589285363654837)
          ·
            refine ⟨3084570777242745502842641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32902088290589285363654837 3084570777242745502842641)
            ·
              refine ⟨2313428082932059127131981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084570777242745502842641 2313428082932059127131981)
              ·
                refine ⟨867535531099522172674493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313428082932059127131981 867535531099522172674493)
                ·
                  refine ⟨325325824162320814752935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867535531099522172674493 325325824162320814752935)
                  ·
                    rfl

theorem cell21_1425532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1425532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425532 prefixEnd_1425532 := by exact prefixLift 1425532
  have htrace : WordTrace (prefixWord ++ tailWord_1425532) baseStart_1425532 baseEnd_1425532 := by
    simpa [prefixWord, tailWord_1425532, baseEnd_1425532] using wordTrace_append hprefix tailTrace_1425532
  have hstable : (prefixWord ++ tailWord_1425532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425532).length < 2 ^ (prefixWord ++ tailWord_1425532).sum := by decide
  have hdescent : baseEnd_1425532 < baseStart_1425532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425546 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1425546 : Nat := 118140960795 + 1425546 * 2 ^ 59
def prefixEnd_1425546 : Nat := 4983230072969 + 3 ^ 40 * 1425546 * 2
def baseEnd_1425546 : Nat := 325329019153059901519573

theorem tailTrace_1425546 : CollatzResearch.WordTrace tailWord_1425546 prefixEnd_1425546 325329019153059901519573 := by
  unfold tailWord_1425546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998483523374445179690123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34662622728998520479173661 12998483523374445179690123)
  ·
    refine ⟨19497725285061667769535185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998483523374445179690123 19497725285061667769535185)
    ·
      refine ⟨14623293963796250827151389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19497725285061667769535185 14623293963796250827151389)
      ·
        refine ⟨5483735236423594060181771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14623293963796250827151389 5483735236423594060181771)
        ·
          refine ⟨8225602854635391090272657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483735236423594060181771 8225602854635391090272657)
          ·
            refine ⟨6169202140976543317704493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8225602854635391090272657 6169202140976543317704493)
            ·
              refine ⟨2313450802866203744139185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6169202140976543317704493 2313450802866203744139185)
              ·
                refine ⟨1735088102149652808104389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313450802866203744139185 1735088102149652808104389)
                ·
                  refine ⟨325329019153059901519573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735088102149652808104389 325329019153059901519573)
                  ·
                    rfl

theorem cell21_1425546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1425546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425546 prefixEnd_1425546 := by exact prefixLift 1425546
  have htrace : WordTrace (prefixWord ++ tailWord_1425546) baseStart_1425546 baseEnd_1425546 := by
    simpa [prefixWord, tailWord_1425546, baseEnd_1425546] using wordTrace_append hprefix tailTrace_1425546
  have hstable : (prefixWord ++ tailWord_1425546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425546).length < 2 ^ (prefixWord ++ tailWord_1425546).sum := by decide
  have hdescent : baseEnd_1425546 < baseStart_1425546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425664 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_1425664 : Nat := 118140960795 + 1425664 * 2 ^ 59
def prefixEnd_1425664 : Nat := 4983230072969 + 3 ^ 40 * 1425664 * 2
def baseEnd_1425664 : Nat := 325355948360717918552665

theorem tailTrace_1425664 : CollatzResearch.WordTrace tailWord_1425664 prefixEnd_1425664 325355948360717918552665 := by
  unfold tailWord_1425664
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999118953535143435778023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34665491938046857914370697 25999118953535143435778023)
  ·
    refine ⟨38998678430302715153667035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25999118953535143435778023 38998678430302715153667035)
    ·
      refine ⟨58498017645454072730500553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38998678430302715153667035 58498017645454072730500553)
      ·
        refine ⟨43873513234090554547875415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58498017645454072730500553 43873513234090554547875415)
        ·
          refine ⟨65810269851135831821813123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43873513234090554547875415 65810269851135831821813123)
          ·
            refine ⟨98715404776703747732719685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65810269851135831821813123 98715404776703747732719685)
            ·
              refine ⟨18509138395631952699884941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98715404776703747732719685 18509138395631952699884941)
              ·
                refine ⟨6940926898361982262456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18509138395631952699884941 6940926898361982262456853)
                ·
                  refine ⟨325355948360717918552665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6940926898361982262456853 325355948360717918552665)
                  ·
                    rfl

theorem cell21_1425664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_1425664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425664 prefixEnd_1425664 := by exact prefixLift 1425664
  have htrace : WordTrace (prefixWord ++ tailWord_1425664) baseStart_1425664 baseEnd_1425664 := by
    simpa [prefixWord, tailWord_1425664, baseEnd_1425664] using wordTrace_append hprefix tailTrace_1425664
  have hstable : (prefixWord ++ tailWord_1425664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425664).length < 2 ^ (prefixWord ++ tailWord_1425664).sum := by decide
  have hdescent : baseEnd_1425664 < baseStart_1425664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425667 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 3]
def baseStart_1425667 : Nat := 118140960795 + 1425667 * 2 ^ 59
def prefixEnd_1425667 : Nat := 4983230072969 + 3 ^ 40 * 1425667 * 2
def baseEnd_1425667 : Nat := 325356633001590580002659

theorem tailTrace_1425667 : CollatzResearch.WordTrace tailWord_1425667 prefixEnd_1425667 325356633001590580002659 := by
  unfold tailWord_1425667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51998347326059418383915255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34665564884039612255943503 51998347326059418383915255)
  ·
    refine ⟨77997520989089127575872883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51998347326059418383915255 77997520989089127575872883)
    ·
      refine ⟨116996281483633691363809325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77997520989089127575872883 116996281483633691363809325)
      ·
        refine ⟨43873605556362634261428497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116996281483633691363809325 43873605556362634261428497)
        ·
          refine ⟨32905204167271975696071373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43873605556362634261428497 32905204167271975696071373)
          ·
            refine ⟨12339451562726990886026765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32905204167271975696071373 12339451562726990886026765)
            ·
              refine ⟨4627294336022621582260037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12339451562726990886026765 4627294336022621582260037)
              ·
                refine ⟨867617688004241546673757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4627294336022621582260037 867617688004241546673757)
                ·
                  refine ⟨325356633001590580002659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867617688004241546673757 325356633001590580002659)
                  ·
                    rfl

theorem cell21_1425667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].length) (baseStart_1425667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425667 prefixEnd_1425667 := by exact prefixLift 1425667
  have htrace : WordTrace (prefixWord ++ tailWord_1425667) baseStart_1425667 baseEnd_1425667 := by
    simpa [prefixWord, tailWord_1425667, baseEnd_1425667] using wordTrace_append hprefix tailTrace_1425667
  have hstable : (prefixWord ++ tailWord_1425667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425667).length < 2 ^ (prefixWord ++ tailWord_1425667).sum := by decide
  have hdescent : baseEnd_1425667 < baseStart_1425667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425681 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_1425681 : Nat := 118140960795 + 1425681 * 2 ^ 59
def prefixEnd_1425681 : Nat := 4983230072969 + 3 ^ 40 * 1425681 * 2
def baseEnd_1425681 : Nat := 325359827992329666769297

theorem tailTrace_1425681 : CollatzResearch.WordTrace tailWord_1425681 prefixEnd_1425681 325359827992329666769297 := by
  unfold tailWord_1425681
  simp only [CollatzResearch.WordTrace]
  refine ⟨51998857948008698774924897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34665905298672465849949931 51998857948008698774924897)
  ·
    refine ⟨38999143461006524081193673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51998857948008698774924897 38999143461006524081193673)
    ·
      refine ⟨29249357595754893060895255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38999143461006524081193673 29249357595754893060895255)
      ·
        refine ⟨43874036393632339591342883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29249357595754893060895255 43874036393632339591342883)
        ·
          refine ⟨65811054590448509387014325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43874036393632339591342883 65811054590448509387014325)
          ·
            refine ⟨6169786367854547755032593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65811054590448509387014325 6169786367854547755032593)
            ·
              refine ⟨4627339775890910816274445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169786367854547755032593 4627339775890910816274445)
              ·
                refine ⟨1735252415959091556102917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4627339775890910816274445 1735252415959091556102917)
                ·
                  refine ⟨325359827992329666769297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735252415959091556102917 325359827992329666769297)
                  ·
                    rfl

theorem cell21_1425681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_1425681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425681 prefixEnd_1425681 := by exact prefixLift 1425681
  have htrace : WordTrace (prefixWord ++ tailWord_1425681) baseStart_1425681 baseEnd_1425681 := by
    simpa [prefixWord, tailWord_1425681, baseEnd_1425681] using wordTrace_append hprefix tailTrace_1425681
  have hstable : (prefixWord ++ tailWord_1425681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425681).length < 2 ^ (prefixWord ++ tailWord_1425681).sum := by decide
  have hdescent : baseEnd_1425681 < baseStart_1425681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425732 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1425732 : Nat := 118140960795 + 1425732 * 2 ^ 59
def prefixEnd_1425732 : Nat := 4983230072969 + 3 ^ 40 * 1425732 * 2
def baseEnd_1425732 : Nat := 325371466887164911419193

theorem tailTrace_1425732 : CollatzResearch.WordTrace tailWord_1425732 prefixEnd_1425732 325371466887164911419193 := by
  unfold tailWord_1425732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000359035411967242515725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34667145380549289656687633 26000359035411967242515725)
  ·
    refine ⟨9750134638279487715943397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26000359035411967242515725 9750134638279487715943397)
    ·
      refine ⟨1828150244677403946739387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9750134638279487715943397 1828150244677403946739387)
      ·
        refine ⟨2742225367016105920109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828150244677403946739387 2742225367016105920109081)
        ·
          refine ⟨2056669025262079440081811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742225367016105920109081 2056669025262079440081811)
          ·
            refine ⟨3085003537893119160122717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056669025262079440081811 3085003537893119160122717)
            ·
              refine ⟨1156876326709919685046019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085003537893119160122717 1156876326709919685046019)
              ·
                refine ⟨1735314490064879527569029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156876326709919685046019 1735314490064879527569029)
                ·
                  refine ⟨325371466887164911419193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1735314490064879527569029 325371466887164911419193)
                  ·
                    rfl

theorem cell21_1425732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1425732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425732 prefixEnd_1425732 := by exact prefixLift 1425732
  have htrace : WordTrace (prefixWord ++ tailWord_1425732) baseStart_1425732 baseEnd_1425732 := by
    simpa [prefixWord, tailWord_1425732, baseEnd_1425732] using wordTrace_append hprefix tailTrace_1425732
  have hstable : (prefixWord ++ tailWord_1425732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425732).length < 2 ^ (prefixWord ++ tailWord_1425732).sum := by decide
  have hdescent : baseEnd_1425732 < baseStart_1425732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425830 : List Nat := [21]
def baseStart_1425830 : Nat := 118140960795 + 1425830 * 2 ^ 59
def prefixEnd_1425830 : Nat := 4983230072969 + 3 ^ 40 * 1425830 * 2
def baseEnd_1425830 : Nat := 49595158028096101019

theorem tailTrace_1425830 : CollatzResearch.WordTrace tailWord_1425830 prefixEnd_1425830 49595158028096101019 := by
  unfold tailWord_1425830
  simp only [CollatzResearch.WordTrace]
  refine ⟨49595158028096101019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 21 34669528282979264814732629 49595158028096101019)
  ·
    rfl

theorem cell21_1425830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 21].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 21].length) (baseStart_1425830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425830 prefixEnd_1425830 := by exact prefixLift 1425830
  have htrace : WordTrace (prefixWord ++ tailWord_1425830) baseStart_1425830 baseEnd_1425830 := by
    simpa [prefixWord, tailWord_1425830, baseEnd_1425830] using wordTrace_append hprefix tailTrace_1425830
  have hstable : (prefixWord ++ tailWord_1425830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425830).length < 2 ^ (prefixWord ++ tailWord_1425830).sum := by decide
  have hdescent : baseEnd_1425830 < baseStart_1425830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425847 : List Nat := [1, 1, 3, 1, 3, 3, 3, 6]
def baseStart_1425847 : Nat := 118140960795 + 1425847 * 2 ^ 59
def prefixEnd_1425847 : Nat := 4983230072969 + 3 ^ 40 * 1425847 * 2
def baseEnd_1425847 : Nat := 108465903817983422334097

theorem tailTrace_1425847 : CollatzResearch.WordTrace tailWord_1425847 prefixEnd_1425847 108465903817983422334097 := by
  unfold tailWord_1425847
  simp only [CollatzResearch.WordTrace]
  refine ⟨52004912465407309125467795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34669941643604872750311863 52004912465407309125467795)
  ·
    refine ⟨78007368698110963688201693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52004912465407309125467795 78007368698110963688201693)
    ·
      refine ⟨29252763261791611383075635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78007368698110963688201693 29252763261791611383075635)
      ·
        refine ⟨43879144892687417074613453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29252763261791611383075635 43879144892687417074613453)
        ·
          refine ⟨16454679334757781402980045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43879144892687417074613453 16454679334757781402980045)
          ·
            refine ⟨6170504750534168026117517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16454679334757781402980045 6170504750534168026117517)
            ·
              refine ⟨2313939281450313009794069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6170504750534168026117517 2313939281450313009794069)
              ·
                refine ⟨108465903817983422334097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2313939281450313009794069 108465903817983422334097)
                ·
                  rfl

theorem cell21_1425847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_1425847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425847 prefixEnd_1425847 := by exact prefixLift 1425847
  have htrace : WordTrace (prefixWord ++ tailWord_1425847) baseStart_1425847 baseEnd_1425847 := by
    simpa [prefixWord, tailWord_1425847, baseEnd_1425847] using wordTrace_append hprefix tailTrace_1425847
  have hstable : (prefixWord ++ tailWord_1425847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425847).length < 2 ^ (prefixWord ++ tailWord_1425847).sum := by decide
  have hdescent : baseEnd_1425847 < baseStart_1425847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425864 : List Nat := [2, 1, 3, 1, 3, 3, 3, 5]
def baseStart_1425864 : Nat := 118140960795 + 1425864 * 2 ^ 59
def prefixEnd_1425864 : Nat := 4983230072969 + 3 ^ 40 * 1425864 * 2
def baseEnd_1425864 : Nat := 108467197028520671739641

theorem tailTrace_1425864 : CollatzResearch.WordTrace tailWord_1425864 prefixEnd_1425864 108467197028520671739641 := by
  unfold tailWord_1425864
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002766253172860514418323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34670355004230480685891097 26002766253172860514418323)
  ·
    refine ⟨39004149379759290771627485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26002766253172860514418323 39004149379759290771627485)
    ·
      refine ⟨14626556017409734039360307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39004149379759290771627485 14626556017409734039360307)
      ·
        refine ⟨21939834026114601059040461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14626556017409734039360307 21939834026114601059040461)
        ·
          refine ⟨8227437759792975397140173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21939834026114601059040461 8227437759792975397140173)
          ·
            refine ⟨3085289159922365773927565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8227437759792975397140173 3085289159922365773927565)
            ·
              refine ⟨1156983434970887165222837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085289159922365773927565 1156983434970887165222837)
              ·
                refine ⟨108467197028520671739641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156983434970887165222837 108467197028520671739641)
                ·
                  rfl

theorem cell21_1425864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_1425864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425864 prefixEnd_1425864 := by exact prefixLift 1425864
  have htrace : WordTrace (prefixWord ++ tailWord_1425864) baseStart_1425864 baseEnd_1425864 := by
    simpa [prefixWord, tailWord_1425864, baseEnd_1425864] using wordTrace_append hprefix tailTrace_1425864
  have hstable : (prefixWord ++ tailWord_1425864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425864).length < 2 ^ (prefixWord ++ tailWord_1425864).sum := by decide
  have hdescent : baseEnd_1425864 < baseStart_1425864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425895 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 3]
def baseStart_1425895 : Nat := 118140960795 + 1425895 * 2 ^ 59
def prefixEnd_1425895 : Nat := 4983230072969 + 3 ^ 40 * 1425895 * 2
def baseEnd_1425895 : Nat := 325408665707912850202193

theorem tailTrace_1425895 : CollatzResearch.WordTrace tailWord_1425895 prefixEnd_1425895 325408665707912850202193 := by
  unfold tailWord_1425895
  simp only [CollatzResearch.WordTrace]
  refine ⟨52006663169233413323215139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34671108779488942215476759 52006663169233413323215139)
  ·
    refine ⟨78009994753850119984822709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52006663169233413323215139 78009994753850119984822709)
    ·
      refine ⟨7313437008173448748577129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78009994753850119984822709 7313437008173448748577129)
      ·
        refine ⟨5485077756130086561432847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7313437008173448748577129 5485077756130086561432847)
        ·
          refine ⟨8227616634195129842149271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485077756130086561432847 8227616634195129842149271)
          ·
            refine ⟨12341424951292694763223907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227616634195129842149271 12341424951292694763223907)
            ·
              refine ⟨18512137426939042144835861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12341424951292694763223907 18512137426939042144835861)
              ·
                refine ⟨867756441887767600539181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18512137426939042144835861 867756441887767600539181)
                ·
                  refine ⟨325408665707912850202193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867756441887767600539181 325408665707912850202193)
                  ·
                    rfl

theorem cell21_1425895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].length) (baseStart_1425895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425895 prefixEnd_1425895 := by exact prefixLift 1425895
  have htrace : WordTrace (prefixWord ++ tailWord_1425895) baseStart_1425895 baseEnd_1425895 := by
    simpa [prefixWord, tailWord_1425895, baseEnd_1425895] using wordTrace_append hprefix tailTrace_1425895
  have hstable : (prefixWord ++ tailWord_1425895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425895).length < 2 ^ (prefixWord ++ tailWord_1425895).sum := by decide
  have hdescent : baseEnd_1425895 < baseStart_1425895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1425940 : List Nat := [2, 4, 3, 1, 1, 1, 9]
def baseStart_1425940 : Nat := 118140960795 + 1425940 * 2 ^ 59
def prefixEnd_1425940 : Nat := 4983230072969 + 3 ^ 40 * 1425940 * 2
def baseEnd_1425940 : Nat := 36157659480111419105789

theorem tailTrace_1425940 : CollatzResearch.WordTrace tailWord_1425940 prefixEnd_1425940 36157659480111419105789 := by
  unfold tailWord_1425940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004152227035193004301637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34672202969380257339068849 26004152227035193004301637)
  ·
    refine ⟨4875778542569098688306557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26004152227035193004301637 4875778542569098688306557)
    ·
      refine ⟨1828416953463412008114959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4875778542569098688306557 1828416953463412008114959)
      ·
        refine ⟨2742625430195118012172439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828416953463412008114959 2742625430195118012172439)
        ·
          refine ⟨4113938145292677018258659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742625430195118012172439 4113938145292677018258659)
          ·
            refine ⟨6170907217939015527387989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113938145292677018258659 6170907217939015527387989)
            ·
              refine ⟨36157659480111419105789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6170907217939015527387989 36157659480111419105789)
              ·
                rfl

theorem cell21_1425940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 9].length) (baseStart_1425940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1425940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1425940 prefixEnd_1425940 := by exact prefixLift 1425940
  have htrace : WordTrace (prefixWord ++ tailWord_1425940) baseStart_1425940 baseEnd_1425940 := by
    simpa [prefixWord, tailWord_1425940, baseEnd_1425940] using wordTrace_append hprefix tailTrace_1425940
  have hstable : (prefixWord ++ tailWord_1425940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1425940).length < 2 ^ (prefixWord ++ tailWord_1425940).sum := by decide
  have hdescent : baseEnd_1425940 < baseStart_1425940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1425940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426030 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1426030 : Nat := 118140960795 + 1426030 * 2 ^ 59
def prefixEnd_1426030 : Nat := 4983230072969 + 3 ^ 40 * 1426030 * 2
def baseEnd_1426030 : Nat := 325439474547182615451917

theorem tailTrace_1426030 : CollatzResearch.WordTrace tailWord_1426030 prefixEnd_1426030 325439474547182615451917 := by
  unfold tailWord_1426030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501448377968041422422443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34674391349162887586253029 6501448377968041422422443)
  ·
    refine ⟨9752172566952062133633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501448377968041422422443 9752172566952062133633665)
    ·
      refine ⟨7314129425214046600225249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9752172566952062133633665 7314129425214046600225249)
      ·
        refine ⟨5485597068910534950168937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314129425214046600225249 5485597068910534950168937)
        ·
          refine ⟨4114197801682901212626703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485597068910534950168937 4114197801682901212626703)
          ·
            refine ⟨6171296702524351818940055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114197801682901212626703 6171296702524351818940055)
            ·
              refine ⟨9256945053786527728410083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171296702524351818940055 9256945053786527728410083)
              ·
                refine ⟨13885417580679791592615125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256945053786527728410083 13885417580679791592615125)
                ·
                  refine ⟨325439474547182615451917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13885417580679791592615125 325439474547182615451917)
                  ·
                    rfl

theorem cell21_1426030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1426030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426030 prefixEnd_1426030 := by exact prefixLift 1426030
  have htrace : WordTrace (prefixWord ++ tailWord_1426030) baseStart_1426030 baseEnd_1426030 := by
    simpa [prefixWord, tailWord_1426030, baseEnd_1426030] using wordTrace_append hprefix tailTrace_1426030
  have hstable : (prefixWord ++ tailWord_1426030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426030).length < 2 ^ (prefixWord ++ tailWord_1426030).sum := by decide
  have hdescent : baseEnd_1426030 < baseStart_1426030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426050 : List Nat := [3, 4, 3, 1, 1, 1, 8]
def baseStart_1426050 : Nat := 118140960795 + 1426050 * 2 ^ 59
def prefixEnd_1426050 : Nat := 4983230072969 + 3 ^ 40 * 1426050 * 2
def baseEnd_1426050 : Nat := 36160448757740780568727

theorem tailTrace_1426050 : CollatzResearch.WordTrace tailWord_1426050 prefixEnd_1426050 36160448757740780568727 := by
  unfold tailWord_1426050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003079120917968698776901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34674877655781249863405069 13003079120917968698776901)
  ·
    refine ⟨2438077335172119131020669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13003079120917968698776901 2438077335172119131020669)
    ·
      refine ⟨914279000689544674132751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2438077335172119131020669 914279000689544674132751)
      ·
        refine ⟨1371418501034317011199127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914279000689544674132751 1371418501034317011199127)
        ·
          refine ⟨2057127751551475516798691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371418501034317011199127 2057127751551475516798691)
          ·
            refine ⟨3085691627327213275198037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057127751551475516798691 3085691627327213275198037)
            ·
              refine ⟨36160448757740780568727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3085691627327213275198037 36160448757740780568727)
              ·
                rfl

theorem cell21_1426050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 8].length) (baseStart_1426050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426050 prefixEnd_1426050 := by exact prefixLift 1426050
  have htrace : WordTrace (prefixWord ++ tailWord_1426050) baseStart_1426050 baseEnd_1426050 := by
    simpa [prefixWord, tailWord_1426050, baseEnd_1426050] using wordTrace_append hprefix tailTrace_1426050
  have hstable : (prefixWord ++ tailWord_1426050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426050).length < 2 ^ (prefixWord ++ tailWord_1426050).sum := by decide
  have hdescent : baseEnd_1426050 < baseStart_1426050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426120 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_1426120 : Nat := 118140960795 + 1426120 * 2 ^ 59
def prefixEnd_1426120 : Nat := 4983230072969 + 3 ^ 40 * 1426120 * 2
def baseEnd_1426120 : Nat := 325460013773362458951733

theorem tailTrace_1426120 : CollatzResearch.WordTrace tailWord_1426120 prefixEnd_1426120 325460013773362458951733 := by
  unfold tailWord_1426120
  simp only [CollatzResearch.WordTrace]
  refine ⟨26007434796709138375077907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34676579728945517833437209 26007434796709138375077907)
  ·
    refine ⟨39011152195063707562616861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26007434796709138375077907 39011152195063707562616861)
    ·
      refine ⟨14629182073148890335981323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39011152195063707562616861 14629182073148890335981323)
      ·
        refine ⟨21943773109723335503971985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629182073148890335981323 21943773109723335503971985)
        ·
          refine ⟨16457829832292501627978989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21943773109723335503971985 16457829832292501627978989)
          ·
            refine ⟨6171686187109688110492121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16457829832292501627978989 6171686187109688110492121)
            ·
              refine ⟨4628764640332266082869091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171686187109688110492121 4628764640332266082869091)
              ·
                refine ⟨6943146960498399124303637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628764640332266082869091 6943146960498399124303637)
                ·
                  refine ⟨325460013773362458951733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6943146960498399124303637 325460013773362458951733)
                  ·
                    rfl

theorem cell21_1426120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_1426120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426120 prefixEnd_1426120 := by exact prefixLift 1426120
  have htrace : WordTrace (prefixWord ++ tailWord_1426120) baseStart_1426120 baseEnd_1426120 := by
    simpa [prefixWord, tailWord_1426120, baseEnd_1426120] using wordTrace_append hprefix tailTrace_1426120
  have hstable : (prefixWord ++ tailWord_1426120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426120).length < 2 ^ (prefixWord ++ tailWord_1426120).sum := by decide
  have hdescent : baseEnd_1426120 < baseStart_1426120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426230 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1426230 : Nat := 118140960795 + 1426230 * 2 ^ 59
def prefixEnd_1426230 : Nat := 4983230072969 + 3 ^ 40 * 1426230 * 2
def baseEnd_1426230 : Nat := 325485117272026712118175

theorem tailTrace_1426230 : CollatzResearch.WordTrace tailWord_1426230 prefixEnd_1426230 325485117272026712118175 := by
  unfold tailWord_1426230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251180101438735346041259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34679254415346510357773429 3251180101438735346041259)
  ·
    refine ⟨4876770152158103019061889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3251180101438735346041259 4876770152158103019061889)
    ·
      refine ⟨3657577614118577264296417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4876770152158103019061889 3657577614118577264296417)
      ·
        refine ⟨2743183210588932948222313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657577614118577264296417 2743183210588932948222313)
        ·
          refine ⟨2057387407941699711166735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743183210588932948222313 2057387407941699711166735)
          ·
            refine ⟨3086081111912549566750103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057387407941699711166735 3086081111912549566750103)
            ·
              refine ⟨4629121667868824350125155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086081111912549566750103 4629121667868824350125155)
              ·
                refine ⟨6943682501803236525187733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629121667868824350125155 6943682501803236525187733)
                ·
                  refine ⟨325485117272026712118175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6943682501803236525187733 325485117272026712118175)
                  ·
                    rfl

theorem cell21_1426230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1426230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426230 prefixEnd_1426230 := by exact prefixLift 1426230
  have htrace : WordTrace (prefixWord ++ tailWord_1426230) baseStart_1426230 baseEnd_1426230 := by
    simpa [prefixWord, tailWord_1426230, baseEnd_1426230] using wordTrace_append hprefix tailTrace_1426230
  have hstable : (prefixWord ++ tailWord_1426230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426230).length < 2 ^ (prefixWord ++ tailWord_1426230).sum := by decide
  have hdescent : baseEnd_1426230 < baseStart_1426230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426275 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 3]
def baseStart_1426275 : Nat := 118140960795 + 1426275 * 2 ^ 59
def prefixEnd_1426275 : Nat := 4983230072969 + 3 ^ 40 * 1426275 * 2
def baseEnd_1426275 : Nat := 325495386885116633868083

theorem tailTrace_1426275 : CollatzResearch.WordTrace tailWord_1426275 prefixEnd_1426275 325495386885116633868083 := by
  unfold tailWord_1426275
  simp only [CollatzResearch.WordTrace]
  refine ⟨52020522907856738222048279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34680348605237825481365519 52020522907856738222048279)
  ·
    refine ⟨78030784361785107333072419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52020522907856738222048279 78030784361785107333072419)
    ·
      refine ⟨117046176542677660999608629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78030784361785107333072419 117046176542677660999608629)
      ·
        refine ⟨10973079050876030718713309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117046176542677660999608629 10973079050876030718713309)
        ·
          refine ⟨4114904644078511519517491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10973079050876030718713309 4114904644078511519517491)
          ·
            refine ⟨6172356966117767279276237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114904644078511519517491 6172356966117767279276237)
            ·
              refine ⟨2314633862294162729728589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6172356966117767279276237 2314633862294162729728589)
              ·
                refine ⟨867987698360311023648221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2314633862294162729728589 867987698360311023648221)
                ·
                  refine ⟨325495386885116633868083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867987698360311023648221 325495386885116633868083)
                  ·
                    rfl

theorem cell21_1426275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].length) (baseStart_1426275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426275 prefixEnd_1426275 := by exact prefixLift 1426275
  have htrace : WordTrace (prefixWord ++ tailWord_1426275) baseStart_1426275 baseEnd_1426275 := by
    simpa [prefixWord, tailWord_1426275, baseEnd_1426275] using wordTrace_append hprefix tailTrace_1426275
  have hstable : (prefixWord ++ tailWord_1426275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426275).length < 2 ^ (prefixWord ++ tailWord_1426275).sum := by decide
  have hdescent : baseEnd_1426275 < baseStart_1426275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426379 : List Nat := [1, 1, 1, 1, 3, 6, 3, 5]
def baseStart_1426379 : Nat := 118140960795 + 1426379 * 2 ^ 59
def prefixEnd_1426379 : Nat := 4983230072969 + 3 ^ 40 * 1426379 * 2
def baseEnd_1426379 : Nat := 108506373700678521378179

theorem tailTrace_1426379 : CollatzResearch.WordTrace tailWord_1426379 prefixEnd_1426379 108506373700678521378179 := by
  unfold tailWord_1426379
  simp only [CollatzResearch.WordTrace]
  refine ⟨52024316099479963983834191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34682877399653309322556127 52024316099479963983834191)
  ·
    refine ⟨78036474149219945975751287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52024316099479963983834191 78036474149219945975751287)
    ·
      refine ⟨117054711223829918963626931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78036474149219945975751287 117054711223829918963626931)
      ·
        refine ⟨175582066835744878445440397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117054711223829918963626931 175582066835744878445440397)
        ·
          refine ⟨65843275063404329417040149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175582066835744878445440397 65843275063404329417040149)
          ·
            refine ⟨3086403518597077941423757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65843275063404329417040149 3086403518597077941423757)
            ·
              refine ⟨1157401319473904228033909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3086403518597077941423757 1157401319473904228033909)
              ·
                refine ⟨108506373700678521378179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1157401319473904228033909 108506373700678521378179)
                ·
                  rfl

theorem cell21_1426379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 5].length) (baseStart_1426379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426379 prefixEnd_1426379 := by exact prefixLift 1426379
  have htrace : WordTrace (prefixWord ++ tailWord_1426379) baseStart_1426379 baseEnd_1426379 := by
    simpa [prefixWord, tailWord_1426379, baseEnd_1426379] using wordTrace_append hprefix tailTrace_1426379
  have hstable : (prefixWord ++ tailWord_1426379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426379).length < 2 ^ (prefixWord ++ tailWord_1426379).sum := by decide
  have hdescent : baseEnd_1426379 < baseStart_1426379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426410 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1426410 : Nat := 118140960795 + 1426410 * 2 ^ 59
def prefixEnd_1426410 : Nat := 4983230072969 + 3 ^ 40 * 1426410 * 2
def baseEnd_1426410 : Nat := 325526195724386399117807

theorem tailTrace_1426410 : CollatzResearch.WordTrace tailWord_1426410 prefixEnd_1426410 325526195724386399117807 := by
  unfold tailWord_1426410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006361690591914069553171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34683631174911770852141789 13006361690591914069553171)
  ·
    refine ⟨19509542535887871104329757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13006361690591914069553171 19509542535887871104329757)
    ·
      refine ⟨7316078450957951664123659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19509542535887871104329757 7316078450957951664123659)
      ·
        refine ⟨10974117676436927496185489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316078450957951664123659 10974117676436927496185489)
        ·
          refine ⟨8230588257327695622139117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10974117676436927496185489 8230588257327695622139117)
          ·
            refine ⟨3086470596497885858302169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8230588257327695622139117 3086470596497885858302169)
            ·
              refine ⟨2314852947373414393726627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086470596497885858302169 2314852947373414393726627)
              ·
                refine ⟨3472279421060121590589941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314852947373414393726627 3472279421060121590589941)
                ·
                  refine ⟨325526195724386399117807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472279421060121590589941 325526195724386399117807)
                  ·
                    rfl

theorem cell21_1426410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1426410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426410 prefixEnd_1426410 := by exact prefixLift 1426410
  have htrace : WordTrace (prefixWord ++ tailWord_1426410) baseStart_1426410 baseEnd_1426410 := by
    simpa [prefixWord, tailWord_1426410, baseEnd_1426410] using wordTrace_append hprefix tailTrace_1426410
  have hstable : (prefixWord ++ tailWord_1426410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426410).length < 2 ^ (prefixWord ++ tailWord_1426410).sum := by decide
  have hdescent : baseEnd_1426410 < baseStart_1426410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426430 : List Nat := [4, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1426430 : Nat := 118140960795 + 1426430 * 2 ^ 59
def prefixEnd_1426430 : Nat := 4983230072969 + 3 ^ 40 * 1426430 * 2
def baseEnd_1426430 : Nat := 108510253332290269594811

theorem tailTrace_1426430 : CollatzResearch.WordTrace tailWord_1426430 prefixEnd_1426430 108510253332290269594811 := by
  unfold tailWord_1426430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503272027786899961742593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34684117481530133129293829 6503272027786899961742593)
  ·
    refine ⟨4877454020840174971306945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6503272027786899961742593 4877454020840174971306945)
    ·
      refine ⟨3658090515630131228480209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4877454020840174971306945 3658090515630131228480209)
      ·
        refine ⟨2743567886722598421360157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658090515630131228480209 2743567886722598421360157)
        ·
          refine ⟨1028837957520974408010059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2743567886722598421360157 1028837957520974408010059)
          ·
            refine ⟨1543256936281461612015089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028837957520974408010059 1543256936281461612015089)
            ·
              refine ⟨1157442702211096209011317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543256936281461612015089 1157442702211096209011317)
              ·
                refine ⟨108510253332290269594811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1157442702211096209011317 108510253332290269594811)
                ·
                  rfl

theorem cell21_1426430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1426430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426430 prefixEnd_1426430 := by exact prefixLift 1426430
  have htrace : WordTrace (prefixWord ++ tailWord_1426430) baseStart_1426430 baseEnd_1426430 := by
    simpa [prefixWord, tailWord_1426430, baseEnd_1426430] using wordTrace_append hprefix tailTrace_1426430
  have hstable : (prefixWord ++ tailWord_1426430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426430).length < 2 ^ (prefixWord ++ tailWord_1426430).sum := by decide
  have hdescent : baseEnd_1426430 < baseStart_1426430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426455 : List Nat := [1, 1, 3, 5, 1, 3, 7]
def baseStart_1426455 : Nat := 118140960795 + 1426455 * 2 ^ 59
def prefixEnd_1426455 : Nat := 4983230072969 + 3 ^ 40 * 1426455 * 2
def baseEnd_1426455 : Nat := 36170718370830702318635

theorem tailTrace_1426455 : CollatzResearch.WordTrace tailWord_1426455 prefixEnd_1426455 36170718370830702318635 := by
  unfold tailWord_1426455
  simp only [CollatzResearch.WordTrace]
  refine ⟨52027088047204628963600819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34684725364803085975733879 52027088047204628963600819)
  ·
    refine ⟨78040632070806943445401229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52027088047204628963600819 78040632070806943445401229)
    ·
      refine ⟨29265237026552603792025461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78040632070806943445401229 29265237026552603792025461)
      ·
        refine ⟨2743615971239306605502387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29265237026552603792025461 2743615971239306605502387)
        ·
          refine ⟨4115423956858959908253581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743615971239306605502387 4115423956858959908253581)
          ·
            refine ⟨1543283983822109965595093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4115423956858959908253581 1543283983822109965595093)
            ·
              refine ⟨36170718370830702318635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1543283983822109965595093 36170718370830702318635)
              ·
                rfl

theorem cell21_1426455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 7].length) (baseStart_1426455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426455 prefixEnd_1426455 := by exact prefixLift 1426455
  have htrace : WordTrace (prefixWord ++ tailWord_1426455) baseStart_1426455 baseEnd_1426455 := by
    simpa [prefixWord, tailWord_1426455, baseEnd_1426455] using wordTrace_append hprefix tailTrace_1426455
  have hstable : (prefixWord ++ tailWord_1426455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426455).length < 2 ^ (prefixWord ++ tailWord_1426455).sum := by decide
  have hdescent : baseEnd_1426455 < baseStart_1426455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426514 : List Nat := [3, 2, 2, 1, 3, 10]
def baseStart_1426514 : Nat := 118140960795 + 1426514 * 2 ^ 59
def prefixEnd_1426514 : Nat := 4983230072969 + 3 ^ 40 * 1426514 * 2
def baseEnd_1426514 : Nat := 12057404812640938125343

theorem tailTrace_1426514 : CollatzResearch.WordTrace tailWord_1426514 prefixEnd_1426514 12057404812640938125343 := by
  unfold tailWord_1426514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007309988497720509999649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34686159969327254693332397 13007309988497720509999649)
  ·
    refine ⟨9755482491373290382499737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13007309988497720509999649 9755482491373290382499737)
    ·
      refine ⟨7316611868529967786874803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9755482491373290382499737 7316611868529967786874803)
      ·
        refine ⟨10974917802794951680312205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316611868529967786874803 10974917802794951680312205)
        ·
          refine ⟨4115594176048106880117077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10974917802794951680312205 4115594176048106880117077)
          ·
            refine ⟨12057404812640938125343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4115594176048106880117077 12057404812640938125343)
            ·
              rfl

theorem cell21_1426514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 10].length) (baseStart_1426514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426514 prefixEnd_1426514 := by exact prefixLift 1426514
  have htrace : WordTrace (prefixWord ++ tailWord_1426514) baseStart_1426514 baseEnd_1426514 := by
    simpa [prefixWord, tailWord_1426514, baseEnd_1426514] using wordTrace_append hprefix tailTrace_1426514
  have hstable : (prefixWord ++ tailWord_1426514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426514).length < 2 ^ (prefixWord ++ tailWord_1426514).sum := by decide
  have hdescent : baseEnd_1426514 < baseStart_1426514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426593 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1426593 : Nat := 118140960795 + 1426593 * 2 ^ 59
def prefixEnd_1426593 : Nat := 4983230072969 + 3 ^ 40 * 1426593 * 2
def baseEnd_1426593 : Nat := 325567958817618747567433

theorem tailTrace_1426593 : CollatzResearch.WordTrace tailWord_1426593 prefixEnd_1426593 325567958817618747567433 := by
  unfold tailWord_1426593
  simp only [CollatzResearch.WordTrace]
  refine ⟨52032121320704678532124433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34688080880469785688082955 52032121320704678532124433)
  ·
    refine ⟨39024090990528508899093325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52032121320704678532124433 39024090990528508899093325)
    ·
      refine ⟨14634034121448190837159997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39024090990528508899093325 14634034121448190837159997)
      ·
        refine ⟨5487762795543071563934999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14634034121448190837159997 5487762795543071563934999)
        ·
          refine ⟨8231644193314607345902499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487762795543071563934999 8231644193314607345902499)
          ·
            refine ⟨12347466289971911018853749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231644193314607345902499 12347466289971911018853749)
            ·
              refine ⟨1157574964684866658017539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12347466289971911018853749 1157574964684866658017539)
              ·
                refine ⟨1736362447027299987026309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157574964684866658017539 1736362447027299987026309)
                ·
                  refine ⟨325567958817618747567433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736362447027299987026309 325567958817618747567433)
                  ·
                    rfl

theorem cell21_1426593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1426593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426593 prefixEnd_1426593 := by exact prefixLift 1426593
  have htrace : WordTrace (prefixWord ++ tailWord_1426593) baseStart_1426593 baseEnd_1426593 := by
    simpa [prefixWord, tailWord_1426593, baseEnd_1426593] using wordTrace_append hprefix tailTrace_1426593
  have hstable : (prefixWord ++ tailWord_1426593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426593).length < 2 ^ (prefixWord ++ tailWord_1426593).sum := by decide
  have hdescent : baseEnd_1426593 < baseStart_1426593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426604 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_1426604 : Nat := 118140960795 + 1426604 * 2 ^ 59
def prefixEnd_1426604 : Nat := 4983230072969 + 3 ^ 40 * 1426604 * 2
def baseEnd_1426604 : Nat := 325570469167485172884077

theorem tailTrace_1426604 : CollatzResearch.WordTrace tailWord_1426604 prefixEnd_1426604 325570469167485172884077 := by
  unfold tailWord_1426604
  simp only [CollatzResearch.WordTrace]
  refine ⟨26016261261832413705387433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34688348349109884940516577 26016261261832413705387433)
  ·
    refine ⟨19512195946374310279040575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26016261261832413705387433 19512195946374310279040575)
    ·
      refine ⟨29268293919561465418560863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19512195946374310279040575 29268293919561465418560863)
      ·
        refine ⟨43902440879342198127841295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29268293919561465418560863 43902440879342198127841295)
        ·
          refine ⟨65853661319013297191761943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43902440879342198127841295 65853661319013297191761943)
          ·
            refine ⟨98780491978519945787642915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65853661319013297191761943 98780491978519945787642915)
            ·
              refine ⟨148170737967779918681464373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98780491978519945787642915 148170737967779918681464373)
              ·
                refine ⟨13891006684479367376387285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148170737967779918681464373 13891006684479367376387285)
                ·
                  refine ⟨325570469167485172884077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13891006684479367376387285 325570469167485172884077)
                  ·
                    rfl

theorem cell21_1426604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_1426604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426604 prefixEnd_1426604 := by exact prefixLift 1426604
  have htrace : WordTrace (prefixWord ++ tailWord_1426604) baseStart_1426604 baseEnd_1426604 := by
    simpa [prefixWord, tailWord_1426604, baseEnd_1426604] using wordTrace_append hprefix tailTrace_1426604
  have hstable : (prefixWord ++ tailWord_1426604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426604).length < 2 ^ (prefixWord ++ tailWord_1426604).sum := by decide
  have hdescent : baseEnd_1426604 < baseStart_1426604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426630 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1426630 : Nat := 118140960795 + 1426630 * 2 ^ 59
def prefixEnd_1426630 : Nat := 4983230072969 + 3 ^ 40 * 1426630 * 2
def baseEnd_1426630 : Nat := 325576402721714905450691

theorem tailTrace_1426630 : CollatzResearch.WordTrace tailWord_1426630 prefixEnd_1426630 325576402721714905450691 := by
  unfold tailWord_1426630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626045963174082307850667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34688980547713755900814229 1626045963174082307850667)
  ·
    refine ⟨2439068944761123461776001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626045963174082307850667 2439068944761123461776001)
    ·
      refine ⟨1829301708570842596332001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2439068944761123461776001 1829301708570842596332001)
      ·
        refine ⟨1371976281428131947249001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829301708570842596332001 1371976281428131947249001)
        ·
          refine ⟨1028982211071098960436751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371976281428131947249001 1028982211071098960436751)
          ·
            refine ⟨1543473316606648440655127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028982211071098960436751 1543473316606648440655127)
            ·
              refine ⟨2315209974909972660982691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543473316606648440655127 2315209974909972660982691)
              ·
                refine ⟨3472814962364958991474037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315209974909972660982691 3472814962364958991474037)
                ·
                  refine ⟨325576402721714905450691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472814962364958991474037 325576402721714905450691)
                  ·
                    rfl

theorem cell21_1426630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1426630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426630 prefixEnd_1426630 := by exact prefixLift 1426630
  have htrace : WordTrace (prefixWord ++ tailWord_1426630) baseStart_1426630 baseEnd_1426630 := by
    simpa [prefixWord, tailWord_1426630, baseEnd_1426630] using wordTrace_append hprefix tailTrace_1426630
  have hstable : (prefixWord ++ tailWord_1426630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426630).length < 2 ^ (prefixWord ++ tailWord_1426630).sum := by decide
  have hdescent : baseEnd_1426630 < baseStart_1426630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426644 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1426644 : Nat := 118140960795 + 1426644 * 2 ^ 59
def prefixEnd_1426644 : Nat := 4983230072969 + 3 ^ 40 * 1426644 * 2
def baseEnd_1426644 : Nat := 325579597712453992217329

theorem tailTrace_1426644 : CollatzResearch.WordTrace tailWord_1426644 prefixEnd_1426644 325579597712453992217329 := by
  unfold tailWord_1426644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26016990721759957121115493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34689320962346609494820657 26016990721759957121115493)
  ·
    refine ⟨4878185760329991960209155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26016990721759957121115493 4878185760329991960209155)
    ·
      refine ⟨7317278640494987940313733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4878185760329991960209155 7317278640494987940313733)
      ·
        refine ⟨1371989745092810238808825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7317278640494987940313733 1371989745092810238808825)
        ·
          refine ⟨1028992308819607679106619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371989745092810238808825 1028992308819607679106619)
          ·
            refine ⟨1543488463229411518659929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028992308819607679106619 1543488463229411518659929)
            ·
              refine ⟨1157616347422058638994947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543488463229411518659929 1157616347422058638994947)
              ·
                refine ⟨1736424521133087958492421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157616347422058638994947 1736424521133087958492421)
                ·
                  refine ⟨325579597712453992217329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736424521133087958492421 325579597712453992217329)
                  ·
                    rfl

theorem cell21_1426644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1426644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426644 prefixEnd_1426644 := by exact prefixLift 1426644
  have htrace : WordTrace (prefixWord ++ tailWord_1426644) baseStart_1426644 baseEnd_1426644 := by
    simpa [prefixWord, tailWord_1426644, baseEnd_1426644] using wordTrace_append hprefix tailTrace_1426644
  have hstable : (prefixWord ++ tailWord_1426644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426644).length < 2 ^ (prefixWord ++ tailWord_1426644).sum := by decide
  have hdescent : baseEnd_1426644 < baseStart_1426644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426666 : List Nat := [3, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1426666 : Nat := 118140960795 + 1426666 * 2 ^ 59
def prefixEnd_1426666 : Nat := 4983230072969 + 3 ^ 40 * 1426666 * 2
def baseEnd_1426666 : Nat := 108528206137395614283539

theorem tailTrace_1426666 : CollatzResearch.WordTrace tailWord_1426666 prefixEnd_1426666 108528206137395614283539 := by
  unfold tailWord_1426666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008695962360052999882963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34689855899626807999687901 13008695962360052999882963)
  ·
    refine ⟨19513043943540079499824445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13008695962360052999882963 19513043943540079499824445)
    ·
      refine ⟨7317391478827529812434167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19513043943540079499824445 7317391478827529812434167)
      ·
        refine ⟨10976087218241294718651251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317391478827529812434167 10976087218241294718651251)
        ·
          refine ⟨16464130827361942077976877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10976087218241294718651251 16464130827361942077976877)
          ·
            refine ⟨6174049060260728279241329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16464130827361942077976877 6174049060260728279241329)
            ·
              refine ⟨4630536795195546209430997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6174049060260728279241329 4630536795195546209430997)
              ·
                refine ⟨108528206137395614283539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4630536795195546209430997 108528206137395614283539)
                ·
                  rfl

theorem cell21_1426666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1426666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426666 prefixEnd_1426666 := by exact prefixLift 1426666
  have htrace : WordTrace (prefixWord ++ tailWord_1426666) baseStart_1426666 baseEnd_1426666 := by
    simpa [prefixWord, tailWord_1426666, baseEnd_1426666] using wordTrace_append hprefix tailTrace_1426666
  have hstable : (prefixWord ++ tailWord_1426666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426666).length < 2 ^ (prefixWord ++ tailWord_1426666).sum := by decide
  have hdescent : baseEnd_1426666 < baseStart_1426666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426773 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1426773 : Nat := 118140960795 + 1426773 * 2 ^ 59
def prefixEnd_1426773 : Nat := 4983230072969 + 3 ^ 40 * 1426773 * 2
def baseEnd_1426773 : Nat := 325609037269978434567065

theorem tailTrace_1426773 : CollatzResearch.WordTrace tailWord_1426773 prefixEnd_1426773 325609037269978434567065 := by
  unfold tailWord_1426773
  simp only [CollatzResearch.WordTrace]
  refine ⟨52038686460052569273676973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34692457640035046182451315 52038686460052569273676973)
  ·
    refine ⟨19514507422519713477628865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52038686460052569273676973 19514507422519713477628865)
    ·
      refine ⟨14635880566889785108221649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19514507422519713477628865 14635880566889785108221649)
      ·
        refine ⟨10976910425167338831166237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14635880566889785108221649 10976910425167338831166237)
        ·
          refine ⟨4116341409437752061687339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10976910425167338831166237 4116341409437752061687339)
          ·
            refine ⟨6174512114156628092531009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116341409437752061687339 6174512114156628092531009)
            ·
              refine ⟨4630884085617471069398257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6174512114156628092531009 4630884085617471069398257)
              ·
                refine ⟨3473163064213103302048693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630884085617471069398257 3473163064213103302048693)
                ·
                  refine ⟨325609037269978434567065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3473163064213103302048693 325609037269978434567065)
                  ·
                    rfl

theorem cell21_1426773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1426773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426773 prefixEnd_1426773 := by exact prefixLift 1426773
  have htrace : WordTrace (prefixWord ++ tailWord_1426773) baseStart_1426773 baseEnd_1426773 := by
    simpa [prefixWord, tailWord_1426773, baseEnd_1426773] using wordTrace_append hprefix tailTrace_1426773
  have hstable : (prefixWord ++ tailWord_1426773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426773).length < 2 ^ (prefixWord ++ tailWord_1426773).sum := by decide
  have hdescent : baseEnd_1426773 < baseStart_1426773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426787 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_1426787 : Nat := 118140960795 + 1426787 * 2 ^ 59
def prefixEnd_1426787 : Nat := 4983230072969 + 3 ^ 40 * 1426787 * 2
def baseEnd_1426787 : Nat := 325612232260717521333703

theorem tailTrace_1426787 : CollatzResearch.WordTrace tailWord_1426787 prefixEnd_1426787 325612232260717521333703 := by
  unfold tailWord_1426787
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039197082001849664686615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34692798054667899776457743 52039197082001849664686615)
  ·
    refine ⟨78058795623002774497029923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52039197082001849664686615 78058795623002774497029923)
    ·
      refine ⟨117088193434504161745544885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78058795623002774497029923 117088193434504161745544885)
      ·
        refine ⟨10977018134484765163644833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117088193434504161745544885 10977018134484765163644833)
        ·
          refine ⟨8232763600863573872733625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10977018134484765163644833 8232763600863573872733625)
          ·
            refine ⟨6174572700647680404550219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8232763600863573872733625 6174572700647680404550219)
            ·
              refine ⟨9261859050971520606825329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174572700647680404550219 9261859050971520606825329)
              ·
                refine ⟨6946394288228640455118997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9261859050971520606825329 6946394288228640455118997)
                ·
                  refine ⟨325612232260717521333703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6946394288228640455118997 325612232260717521333703)
                  ·
                    rfl

theorem cell21_1426787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_1426787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426787 prefixEnd_1426787 := by exact prefixLift 1426787
  have htrace : WordTrace (prefixWord ++ tailWord_1426787) baseStart_1426787 baseEnd_1426787 := by
    simpa [prefixWord, tailWord_1426787, baseEnd_1426787] using wordTrace_append hprefix tailTrace_1426787
  have hstable : (prefixWord ++ tailWord_1426787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426787).length < 2 ^ (prefixWord ++ tailWord_1426787).sum := by decide
  have hdescent : baseEnd_1426787 < baseStart_1426787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426801 : List Nat := [1, 2, 2, 2, 1, 2, 11]
def baseStart_1426801 : Nat := 118140960795 + 1426801 * 2 ^ 59
def prefixEnd_1426801 : Nat := 4983230072969 + 3 ^ 40 * 1426801 * 2
def baseEnd_1426801 : Nat := 36179491916828512011149

theorem tailTrace_1426801 : CollatzResearch.WordTrace tailWord_1426801 prefixEnd_1426801 36179491916828512011149 := by
  unfold tailWord_1426801
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039707703951130055696257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34693138469300753370464171 52039707703951130055696257)
  ·
    refine ⟨39029780777963347541772193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52039707703951130055696257 39029780777963347541772193)
    ·
      refine ⟨29272335583472510656329145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39029780777963347541772193 29272335583472510656329145)
      ·
        refine ⟨21954251687604382992246859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29272335583472510656329145 21954251687604382992246859)
        ·
          refine ⟨32931377531406574488370289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21954251687604382992246859 32931377531406574488370289)
          ·
            refine ⟨24698533148554930866277717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32931377531406574488370289 24698533148554930866277717)
            ·
              refine ⟨36179491916828512011149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24698533148554930866277717 36179491916828512011149)
              ·
                rfl

theorem cell21_1426801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 11].length) (baseStart_1426801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426801 prefixEnd_1426801 := by exact prefixLift 1426801
  have htrace : WordTrace (prefixWord ++ tailWord_1426801) baseStart_1426801 baseEnd_1426801 := by
    simpa [prefixWord, tailWord_1426801, baseEnd_1426801] using wordTrace_append hprefix tailTrace_1426801
  have hstable : (prefixWord ++ tailWord_1426801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426801).length < 2 ^ (prefixWord ++ tailWord_1426801).sum := by decide
  have hdescent : baseEnd_1426801 < baseStart_1426801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426953 : List Nat := [1, 2, 1, 1, 3, 1, 5, 7]
def baseStart_1426953 : Nat := 118140960795 + 1426953 * 2 ^ 59
def prefixEnd_1426953 : Nat := 4983230072969 + 3 ^ 40 * 1426953 * 2
def baseEnd_1426953 : Nat := 108550038574112707188899

theorem tailTrace_1426953 : CollatzResearch.WordTrace tailWord_1426953 prefixEnd_1426953 108550038574112707188899 := by
  unfold tailWord_1426953
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045251599400460015229513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34696834399600306676819675 52045251599400460015229513)
  ·
    refine ⟨39033938699550345011422135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52045251599400460015229513 39033938699550345011422135)
    ·
      refine ⟨58550908049325517517133203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39033938699550345011422135 58550908049325517517133203)
      ·
        refine ⟨87826362073988276275699805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58550908049325517517133203 87826362073988276275699805)
        ·
          refine ⟨32934885777745603603387427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87826362073988276275699805 32934885777745603603387427)
          ·
            refine ⟨49402328666618405405081141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32934885777745603603387427 49402328666618405405081141)
            ·
              refine ⟨4631468312495475506726357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49402328666618405405081141 4631468312495475506726357)
              ·
                refine ⟨108550038574112707188899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4631468312495475506726357 108550038574112707188899)
                ·
                  rfl

theorem cell21_1426953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_1426953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426953 prefixEnd_1426953 := by exact prefixLift 1426953
  have htrace : WordTrace (prefixWord ++ tailWord_1426953) baseStart_1426953 baseEnd_1426953 := by
    simpa [prefixWord, tailWord_1426953, baseEnd_1426953] using wordTrace_append hprefix tailTrace_1426953
  have hstable : (prefixWord ++ tailWord_1426953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426953).length < 2 ^ (prefixWord ++ tailWord_1426953).sum := by decide
  have hdescent : baseEnd_1426953 < baseStart_1426953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1426990 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1426990 : Nat := 118140960795 + 1426990 * 2 ^ 59
def prefixEnd_1426990 : Nat := 4983230072969 + 3 ^ 40 * 1426990 * 2
def baseEnd_1426990 : Nat := 325658559626434279449955

theorem tailTrace_1426990 : CollatzResearch.WordTrace tailWord_1426990 prefixEnd_1426990 325658559626434279449955 := by
  unfold tailWord_1426990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505825137533301916790803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34697734066844276889550949 6505825137533301916790803)
  ·
    refine ⟨9758737706299952875186205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6505825137533301916790803 9758737706299952875186205)
    ·
      refine ⟨3659526639862482328194827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9758737706299952875186205 3659526639862482328194827)
      ·
        refine ⟨5489289959793723492292241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659526639862482328194827 5489289959793723492292241)
        ·
          refine ⟨4116967469845292619219181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489289959793723492292241 4116967469845292619219181)
          ·
            refine ⟨1543862801191984732207193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4116967469845292619219181 1543862801191984732207193)
            ·
              refine ⟨1157897100893988549155395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543862801191984732207193 1157897100893988549155395)
              ·
                refine ⟨1736845651340982823733093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157897100893988549155395 1736845651340982823733093)
                ·
                  refine ⟨325658559626434279449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1736845651340982823733093 325658559626434279449955)
                  ·
                    rfl

theorem cell21_1426990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1426990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1426990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1426990 prefixEnd_1426990 := by exact prefixLift 1426990
  have htrace : WordTrace (prefixWord ++ tailWord_1426990) baseStart_1426990 baseEnd_1426990 := by
    simpa [prefixWord, tailWord_1426990, baseEnd_1426990] using wordTrace_append hprefix tailTrace_1426990
  have hstable : (prefixWord ++ tailWord_1426990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1426990).length < 2 ^ (prefixWord ++ tailWord_1426990).sum := by decide
  have hdescent : baseEnd_1426990 < baseStart_1426990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1426990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427122 : List Nat := [3, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1427122 : Nat := 118140960795 + 1427122 * 2 ^ 59
def prefixEnd_1427122 : Nat := 4983230072969 + 3 ^ 40 * 1427122 * 2
def baseEnd_1427122 : Nat := 108562894608277127749895

theorem tailTrace_1427122 : CollatzResearch.WordTrace tailWord_1427122 prefixEnd_1427122 108562894608277127749895 := by
  unfold tailWord_1427122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012853883947050469532905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34700943690525467918754413 13012853883947050469532905)
  ·
    refine ⟨9759640412960287852149679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13012853883947050469532905 9759640412960287852149679)
    ·
      refine ⟨14639460619440431778224519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9759640412960287852149679 14639460619440431778224519)
      ·
        refine ⟨21959190929160647667336779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14639460619440431778224519 21959190929160647667336779)
        ·
          refine ⟨32938786393740971501005169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21959190929160647667336779 32938786393740971501005169)
          ·
            refine ⟨24704089795305728625753877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32938786393740971501005169 24704089795305728625753877)
            ·
              refine ⟨1158004209154956029332213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24704089795305728625753877 1158004209154956029332213)
              ·
                refine ⟨108562894608277127749895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158004209154956029332213 108562894608277127749895)
                ·
                  rfl

theorem cell21_1427122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1427122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427122 prefixEnd_1427122 := by exact prefixLift 1427122
  have htrace : WordTrace (prefixWord ++ tailWord_1427122) baseStart_1427122 baseEnd_1427122 := by
    simpa [prefixWord, tailWord_1427122, baseEnd_1427122] using wordTrace_append hprefix tailTrace_1427122
  have hstable : (prefixWord ++ tailWord_1427122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427122).length < 2 ^ (prefixWord ++ tailWord_1427122).sum := by decide
  have hdescent : baseEnd_1427122 < baseStart_1427122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427153 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_1427153 : Nat := 118140960795 + 1427153 * 2 ^ 59
def prefixEnd_1427153 : Nat := 4983230072969 + 3 ^ 40 * 1427153 * 2
def baseEnd_1427153 : Nat := 325695758447182218232955

theorem tailTrace_1427153 : CollatzResearch.WordTrace tailWord_1427153 prefixEnd_1427153 325695758447182218232955 := by
  unfold tailWord_1427153
  simp only [CollatzResearch.WordTrace]
  refine ⟨52052546198675894172510113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34701697465783929448340075 52052546198675894172510113)
  ·
    refine ⟨39039409649006920629382585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52052546198675894172510113 39039409649006920629382585)
    ·
      refine ⟨29279557236755190472036939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39039409649006920629382585 29279557236755190472036939)
      ·
        refine ⟨43919335855132785708055409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29279557236755190472036939 43919335855132785708055409)
        ·
          refine ⟨32939501891349589281041557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43919335855132785708055409 32939501891349589281041557)
          ·
            refine ⟨1544039151157011997548823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32939501891349589281041557 1544039151157011997548823)
            ·
              refine ⟨2316058726735517996323235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544039151157011997548823 2316058726735517996323235)
              ·
                refine ⟨3474088090103276994484853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316058726735517996323235 3474088090103276994484853)
                ·
                  refine ⟨325695758447182218232955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474088090103276994484853 325695758447182218232955)
                  ·
                    rfl

theorem cell21_1427153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_1427153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427153 prefixEnd_1427153 := by exact prefixLift 1427153
  have htrace : WordTrace (prefixWord ++ tailWord_1427153) baseStart_1427153 baseEnd_1427153 := by
    simpa [prefixWord, tailWord_1427153, baseEnd_1427153] using wordTrace_append hprefix tailTrace_1427153
  have hstable : (prefixWord ++ tailWord_1427153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427153).length < 2 ^ (prefixWord ++ tailWord_1427153).sum := by decide
  have hdescent : baseEnd_1427153 < baseStart_1427153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427167 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_1427167 : Nat := 118140960795 + 1427167 * 2 ^ 59
def prefixEnd_1427167 : Nat := 4983230072969 + 3 ^ 40 * 1427167 * 2
def baseEnd_1427167 : Nat := 325698953437921304999593

theorem tailTrace_1427167 : CollatzResearch.WordTrace tailWord_1427167 prefixEnd_1427167 325698953437921304999593 := by
  unfold tailWord_1427167
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053056820625174563519755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34702037880416783042346503 52053056820625174563519755)
  ·
    refine ⟨78079585230937761845279633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52053056820625174563519755 78079585230937761845279633)
    ·
      refine ⟨58559688923203321383959725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78079585230937761845279633 58559688923203321383959725)
      ·
        refine ⟨21959883346201245518984897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58559688923203321383959725 21959883346201245518984897)
        ·
          refine ⟨16469912509650934139238673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21959883346201245518984897 16469912509650934139238673)
          ·
            refine ⟨12352434382238200604429005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16469912509650934139238673 12352434382238200604429005)
            ·
              refine ⟨4632162893339325226660877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12352434382238200604429005 4632162893339325226660877)
              ·
                refine ⟨1737061085002246959997829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4632162893339325226660877 1737061085002246959997829)
                ·
                  refine ⟨325698953437921304999593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737061085002246959997829 325698953437921304999593)
                  ·
                    rfl

theorem cell21_1427167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_1427167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427167 prefixEnd_1427167 := by exact prefixLift 1427167
  have htrace : WordTrace (prefixWord ++ tailWord_1427167) baseStart_1427167 baseEnd_1427167 := by
    simpa [prefixWord, tailWord_1427167, baseEnd_1427167] using wordTrace_append hprefix tailTrace_1427167
  have hstable : (prefixWord ++ tailWord_1427167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427167).length < 2 ^ (prefixWord ++ tailWord_1427167).sum := by decide
  have hdescent : baseEnd_1427167 < baseStart_1427167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427195 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_1427195 : Nat := 118140960795 + 1427195 * 2 ^ 59
def prefixEnd_1427195 : Nat := 4983230072969 + 3 ^ 40 * 1427195 * 2
def baseEnd_1427195 : Nat := 325705343419399478532869

theorem tailTrace_1427195 : CollatzResearch.WordTrace tailWord_1427195 prefixEnd_1427195 325705343419399478532869 := by
  unfold tailWord_1427195
  simp only [CollatzResearch.WordTrace]
  refine ⟨52054078064523735345539039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34702718709682490230359359 52054078064523735345539039)
  ·
    refine ⟨78081117096785603018308559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52054078064523735345539039 78081117096785603018308559)
    ·
      refine ⟨117121675645178404527462839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78081117096785603018308559 117121675645178404527462839)
      ·
        refine ⟨175682513467767606791194259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117121675645178404527462839 175682513467767606791194259)
        ·
          refine ⟨263523770201651410186791389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175682513467767606791194259 263523770201651410186791389)
          ·
            refine ⟨98821413825619278820046771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263523770201651410186791389 98821413825619278820046771)
            ·
              refine ⟨148232120738428918230070157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98821413825619278820046771 148232120738428918230070157)
              ·
                refine ⟨55587045276910844336276309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148232120738428918230070157 55587045276910844336276309)
                ·
                  refine ⟨325705343419399478532869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55587045276910844336276309 325705343419399478532869)
                  ·
                    rfl

theorem cell21_1427195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_1427195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427195 prefixEnd_1427195 := by exact prefixLift 1427195
  have htrace : WordTrace (prefixWord ++ tailWord_1427195) baseStart_1427195 baseEnd_1427195 := by
    simpa [prefixWord, tailWord_1427195, baseEnd_1427195] using wordTrace_append hprefix tailTrace_1427195
  have hstable : (prefixWord ++ tailWord_1427195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427195).length < 2 ^ (prefixWord ++ tailWord_1427195).sum := by decide
  have hdescent : baseEnd_1427195 < baseStart_1427195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427198 : List Nat := [4, 2, 2, 1, 3, 9]
def baseStart_1427198 : Nat := 118140960795 + 1427198 * 2 ^ 59
def prefixEnd_1427198 : Nat := 4983230072969 + 3 ^ 40 * 1427198 * 2
def baseEnd_1427198 : Nat := 12063186224454523703069

theorem tailTrace_1427198 : CollatzResearch.WordTrace tailWord_1427198 prefixEnd_1427198 12063186224454523703069 := by
  unfold tailWord_1427198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6506773435439108357237281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34702791655675244571932165 6506773435439108357237281)
  ·
    refine ⟨4880080076579331267927961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6506773435439108357237281 4880080076579331267927961)
    ·
      refine ⟨3660060057434498450945971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4880080076579331267927961 3660060057434498450945971)
      ·
        refine ⟨5490090086151747676418957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660060057434498450945971 5490090086151747676418957)
        ·
          refine ⟨2058783782306905378657109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5490090086151747676418957 2058783782306905378657109)
          ·
            refine ⟨12063186224454523703069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2058783782306905378657109 12063186224454523703069)
            ·
              rfl

theorem cell21_1427198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 9].length) (baseStart_1427198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427198 prefixEnd_1427198 := by exact prefixLift 1427198
  have htrace : WordTrace (prefixWord ++ tailWord_1427198) baseStart_1427198 baseEnd_1427198 := by
    simpa [prefixWord, tailWord_1427198, baseEnd_1427198] using wordTrace_append hprefix tailTrace_1427198
  have hstable : (prefixWord ++ tailWord_1427198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427198).length < 2 ^ (prefixWord ++ tailWord_1427198).sum := by decide
  have hdescent : baseEnd_1427198 < baseStart_1427198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427333 : List Nat := [1, 3, 1, 1, 3, 2, 4, 6]
def baseStart_1427333 : Nat := 118140960795 + 1427333 * 2 ^ 59
def prefixEnd_1427333 : Nat := 4983230072969 + 3 ^ 40 * 1427333 * 2
def baseEnd_1427333 : Nat := 108578945633180635077529

theorem tailTrace_1427333 : CollatzResearch.WordTrace tailWord_1427333 prefixEnd_1427333 108578945633180635077529 := by
  unfold tailWord_1427333
  simp only [CollatzResearch.WordTrace]
  refine ⟨52059111338023784914062653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34706074225349189942708435 52059111338023784914062653)
  ·
    refine ⟨19522166751758919342773495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52059111338023784914062653 19522166751758919342773495)
    ·
      refine ⟨29283250127638379014160243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522166751758919342773495 29283250127638379014160243)
      ·
        refine ⟨43924875191457568521240365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29283250127638379014160243 43924875191457568521240365)
        ·
          refine ⟨16471828196796588195465137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43924875191457568521240365 16471828196796588195465137)
          ·
            refine ⟨12353871147597441146598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16471828196796588195465137 12353871147597441146598853)
            ·
              refine ⟨2316350840174520214987285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12353871147597441146598853 2316350840174520214987285)
              ·
                refine ⟨108578945633180635077529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2316350840174520214987285 108578945633180635077529)
                ·
                  rfl

theorem cell21_1427333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_1427333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427333 prefixEnd_1427333 := by exact prefixLift 1427333
  have htrace : WordTrace (prefixWord ++ tailWord_1427333) baseStart_1427333 baseEnd_1427333 := by
    simpa [prefixWord, tailWord_1427333, baseEnd_1427333] using wordTrace_append hprefix tailTrace_1427333
  have hstable : (prefixWord ++ tailWord_1427333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427333).length < 2 ^ (prefixWord ++ tailWord_1427333).sum := by decide
  have hdescent : baseEnd_1427333 < baseStart_1427333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427336 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_1427336 : Nat := 118140960795 + 1427336 * 2 ^ 59
def prefixEnd_1427336 : Nat := 4983230072969 + 3 ^ 40 * 1427336 * 2
def baseEnd_1427336 : Nat := 325737521540414566682581

theorem tailTrace_1427336 : CollatzResearch.WordTrace tailWord_1427336 prefixEnd_1427336 325737521540414566682581 := by
  unfold tailWord_1427336
  simp only [CollatzResearch.WordTrace]
  refine ⟨26029610378506458213210931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34706147171341944284281241 26029610378506458213210931)
  ·
    refine ⟨39044415567759687319816397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26029610378506458213210931 39044415567759687319816397)
    ·
      refine ⟨14641655837909882744931149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39044415567759687319816397 14641655837909882744931149)
      ·
        refine ⟨5490620939216206029349181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14641655837909882744931149 5490620939216206029349181)
        ·
          refine ⟨2058982852206077261005943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5490620939216206029349181 2058982852206077261005943)
          ·
            refine ⟨3088474278309115891508915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058982852206077261005943 3088474278309115891508915)
            ·
              refine ⟨4632711417463673837263373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088474278309115891508915 4632711417463673837263373)
              ·
                refine ⟨1737266781548877688973765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4632711417463673837263373 1737266781548877688973765)
                ·
                  refine ⟨325737521540414566682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737266781548877688973765 325737521540414566682581)
                  ·
                    rfl

theorem cell21_1427336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_1427336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427336 prefixEnd_1427336 := by exact prefixLift 1427336
  have htrace : WordTrace (prefixWord ++ tailWord_1427336) baseStart_1427336 baseEnd_1427336 := by
    simpa [prefixWord, tailWord_1427336, baseEnd_1427336] using wordTrace_append hprefix tailTrace_1427336
  have hstable : (prefixWord ++ tailWord_1427336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427336).length < 2 ^ (prefixWord ++ tailWord_1427336).sum := by decide
  have hdescent : baseEnd_1427336 < baseStart_1427336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427378 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1427378 : Nat := 118140960795 + 1427378 * 2 ^ 59
def prefixEnd_1427378 : Nat := 4983230072969 + 3 ^ 40 * 1427378 * 2
def baseEnd_1427378 : Nat := 325747106512631826982495

theorem tailTrace_1427378 : CollatzResearch.WordTrace tailWord_1427378 prefixEnd_1427378 325747106512631826982495 := by
  unfold tailWord_1427378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015188155715189399862697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34707168415240505066300525 13015188155715189399862697)
  ·
    refine ⟨9761391116786392049897023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13015188155715189399862697 9761391116786392049897023)
    ·
      refine ⟨14642086675179588074845535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761391116786392049897023 14642086675179588074845535)
      ·
        refine ⟨21963130012769382112268303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14642086675179588074845535 21963130012769382112268303)
        ·
          refine ⟨32944695019154073168402455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21963130012769382112268303 32944695019154073168402455)
          ·
            refine ⟨49417042528731109752603683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32944695019154073168402455 49417042528731109752603683)
            ·
              refine ⟨74125563793096664628905525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49417042528731109752603683 74125563793096664628905525)
              ·
                refine ⟨6949271605602812308959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74125563793096664628905525 6949271605602812308959893)
                ·
                  refine ⟨325747106512631826982495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6949271605602812308959893 325747106512631826982495)
                  ·
                    rfl

theorem cell21_1427378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1427378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427378 prefixEnd_1427378 := by exact prefixLift 1427378
  have htrace : WordTrace (prefixWord ++ tailWord_1427378) baseStart_1427378 baseEnd_1427378 := by
    simpa [prefixWord, tailWord_1427378, baseEnd_1427378] using wordTrace_append hprefix tailTrace_1427378
  have hstable : (prefixWord ++ tailWord_1427378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427378).length < 2 ^ (prefixWord ++ tailWord_1427378).sum := by decide
  have hdescent : baseEnd_1427378 < baseStart_1427378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427460 : List Nat := [2, 3, 2, 4, 1, 2, 2, 5]
def baseStart_1427460 : Nat := 118140960795 + 1427460 * 2 ^ 59
def prefixEnd_1427460 : Nat := 4983230072969 + 3 ^ 40 * 1427460 * 2
def baseEnd_1427460 : Nat := 108588606676605968871887

theorem tailTrace_1427460 : CollatzResearch.WordTrace tailWord_1427460 prefixEnd_1427460 108588606676605968871887 := by
  unfold tailWord_1427460
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031871704281842801967917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34709162272375790402623889 26031871704281842801967917)
  ·
    refine ⟨9761951889105691050737969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26031871704281842801967917 9761951889105691050737969)
    ·
      refine ⟨7321463916829268288053477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9761951889105691050737969 7321463916829268288053477)
      ·
        refine ⟨1372774484405487804010027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7321463916829268288053477 1372774484405487804010027)
        ·
          refine ⟨2059161726608231706015041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372774484405487804010027 2059161726608231706015041)
          ·
            refine ⟨1544371294956173779511281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059161726608231706015041 1544371294956173779511281)
            ·
              refine ⟨1158278471217130334633461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544371294956173779511281 1158278471217130334633461)
              ·
                refine ⟨108588606676605968871887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158278471217130334633461 108588606676605968871887)
                ·
                  rfl

theorem cell21_1427460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_1427460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427460 prefixEnd_1427460 := by exact prefixLift 1427460
  have htrace : WordTrace (prefixWord ++ tailWord_1427460) baseStart_1427460 baseEnd_1427460 := by
    simpa [prefixWord, tailWord_1427460, baseEnd_1427460] using wordTrace_append hprefix tailTrace_1427460
  have hstable : (prefixWord ++ tailWord_1427460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427460).length < 2 ^ (prefixWord ++ tailWord_1427460).sum := by decide
  have hdescent : baseEnd_1427460 < baseStart_1427460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427485 : List Nat := [1, 4, 2, 2, 2, 1, 9]
def baseStart_1427485 : Nat := 118140960795 + 1427485 * 2 ^ 59
def prefixEnd_1427485 : Nat := 4983230072969 + 3 ^ 40 * 1427485 * 2
def baseEnd_1427485 : Nat := 36196836152269268744327

theorem tailTrace_1427485 : CollatzResearch.WordTrace tailWord_1427485 prefixEnd_1427485 36196836152269268744327 := by
  unfold tailWord_1427485
  simp only [CollatzResearch.WordTrace]
  refine ⟨52064655233473114873595909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34709770155648743249063939 52064655233473114873595909)
  ·
    refine ⟨9762122856276209038799233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52064655233473114873595909 9762122856276209038799233)
    ·
      refine ⟨7321592142207156779099425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9762122856276209038799233 7321592142207156779099425)
      ·
        refine ⟨5491194106655367584324569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7321592142207156779099425 5491194106655367584324569)
        ·
          refine ⟨4118395579991525688243427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491194106655367584324569 4118395579991525688243427)
          ·
            refine ⟨6177593369987288532365141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118395579991525688243427 6177593369987288532365141)
            ·
              refine ⟨36196836152269268744327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6177593369987288532365141 36196836152269268744327)
              ·
                rfl

theorem cell21_1427485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 9].length) (baseStart_1427485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427485 prefixEnd_1427485 := by exact prefixLift 1427485
  have htrace : WordTrace (prefixWord ++ tailWord_1427485) baseStart_1427485 baseEnd_1427485 := by
    simpa [prefixWord, tailWord_1427485, baseEnd_1427485] using wordTrace_append hprefix tailTrace_1427485
  have hstable : (prefixWord ++ tailWord_1427485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427485).length < 2 ^ (prefixWord ++ tailWord_1427485).sum := by decide
  have hdescent : baseEnd_1427485 < baseStart_1427485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427499 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_1427499 : Nat := 118140960795 + 1427499 * 2 ^ 59
def prefixEnd_1427499 : Nat := 4983230072969 + 3 ^ 40 * 1427499 * 2
def baseEnd_1427499 : Nat := 325774720361162505465581

theorem tailTrace_1427499 : CollatzResearch.WordTrace tailWord_1427499 prefixEnd_1427499 325774720361162505465581 := by
  unfold tailWord_1427499
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065165855422395264605551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34710110570281596843070367 52065165855422395264605551)
  ·
    refine ⟨78097748783133592896908327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52065165855422395264605551 78097748783133592896908327)
    ·
      refine ⟨117146623174700389345362491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78097748783133592896908327 117146623174700389345362491)
      ·
        refine ⟨175719934762050584018043737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117146623174700389345362491 175719934762050584018043737)
        ·
          refine ⟨131789951071537938013532803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175719934762050584018043737 131789951071537938013532803)
          ·
            refine ⟨197684926607306907020299205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131789951071537938013532803 197684926607306907020299205)
            ·
              refine ⟨37065923738870045066306101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197684926607306907020299205 37065923738870045066306101)
              ·
                refine ⟨3474930350519066724966197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37065923738870045066306101 3474930350519066724966197)
                ·
                  refine ⟨325774720361162505465581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474930350519066724966197 325774720361162505465581)
                  ·
                    rfl

theorem cell21_1427499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_1427499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427499 prefixEnd_1427499 := by exact prefixLift 1427499
  have htrace : WordTrace (prefixWord ++ tailWord_1427499) baseStart_1427499 baseEnd_1427499 := by
    simpa [prefixWord, tailWord_1427499, baseEnd_1427499] using wordTrace_append hprefix tailTrace_1427499
  have hstable : (prefixWord ++ tailWord_1427499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427499).length < 2 ^ (prefixWord ++ tailWord_1427499).sum := by decide
  have hdescent : baseEnd_1427499 < baseStart_1427499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427502 : List Nat := [4, 1, 3, 1, 1, 3, 2, 6]
def baseStart_1427502 : Nat := 118140960795 + 1427502 * 2 ^ 59
def prefixEnd_1427502 : Nat := 4983230072969 + 3 ^ 40 * 1427502 * 2
def baseEnd_1427502 : Nat := 108591801667345055638525

theorem tailTrace_1427502 : CollatzResearch.WordTrace tailWord_1427502 prefixEnd_1427502 108591801667345055638525 := by
  unfold tailWord_1427502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508159409301440847120595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34710183516274351184643173 6508159409301440847120595)
  ·
    refine ⟨9762239113952161270680893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508159409301440847120595 9762239113952161270680893)
    ·
      refine ⟨3660839667732060476505335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9762239113952161270680893 3660839667732060476505335)
      ·
        refine ⟨5491259501598090714758003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660839667732060476505335 5491259501598090714758003)
        ·
          refine ⟨8236889252397136072137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491259501598090714758003 8236889252397136072137005)
          ·
            refine ⟨3088833469648926027051377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8236889252397136072137005 3088833469648926027051377)
            ·
              refine ⟨2316625102236694520288533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088833469648926027051377 2316625102236694520288533)
              ·
                refine ⟨108591801667345055638525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2316625102236694520288533 108591801667345055638525)
                ·
                  rfl

theorem cell21_1427502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_1427502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427502 prefixEnd_1427502 := by exact prefixLift 1427502
  have htrace : WordTrace (prefixWord ++ tailWord_1427502) baseStart_1427502 baseEnd_1427502 := by
    simpa [prefixWord, tailWord_1427502, baseEnd_1427502] using wordTrace_append hprefix tailTrace_1427502
  have hstable : (prefixWord ++ tailWord_1427502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427502).length < 2 ^ (prefixWord ++ tailWord_1427502).sum := by decide
  have hdescent : baseEnd_1427502 < baseStart_1427502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427544 : List Nat := [2, 1, 2, 2, 1, 13]
def baseStart_1427544 : Nat := 118140960795 + 1427544 * 2 ^ 59
def prefixEnd_1427544 : Nat := 4983230072969 + 3 ^ 40 * 1427544 * 2
def baseEnd_1427544 : Nat := 12066110739787126933907

theorem tailTrace_1427544 : CollatzResearch.WordTrace tailWord_1427544 prefixEnd_1427544 12066110739787126933907 := by
  unfold tailWord_1427544
  simp only [CollatzResearch.WordTrace]
  refine ⟨26033403570129683974996843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34711204760172911966662457 26033403570129683974996843)
  ·
    refine ⟨39050105355194525962495265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26033403570129683974996843 39050105355194525962495265)
    ·
      refine ⟨29287579016395894471871449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39050105355194525962495265 29287579016395894471871449)
      ·
        refine ⟨21965684262296920853903587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29287579016395894471871449 21965684262296920853903587)
        ·
          refine ⟨32948526393445381280855381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21965684262296920853903587 32948526393445381280855381)
          ·
            refine ⟨12066110739787126933907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 32948526393445381280855381 12066110739787126933907)
            ·
              rfl

theorem cell21_1427544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 13].length) (baseStart_1427544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427544 prefixEnd_1427544 := by exact prefixLift 1427544
  have htrace : WordTrace (prefixWord ++ tailWord_1427544) baseStart_1427544 baseEnd_1427544 := by
    simpa [prefixWord, tailWord_1427544, baseEnd_1427544] using wordTrace_append hprefix tailTrace_1427544
  have hstable : (prefixWord ++ tailWord_1427544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427544).length < 2 ^ (prefixWord ++ tailWord_1427544).sum := by decide
  have hdescent : baseEnd_1427544 < baseStart_1427544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427575 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_1427575 : Nat := 118140960795 + 1427575 * 2 ^ 59
def prefixEnd_1427575 : Nat := 4983230072969 + 3 ^ 40 * 1427575 * 2
def baseEnd_1427575 : Nat := 325792064596603262198759

theorem tailTrace_1427575 : CollatzResearch.WordTrace tailWord_1427575 prefixEnd_1427575 325792064596603262198759 := by
  unfold tailWord_1427575
  simp only [CollatzResearch.WordTrace]
  refine ⟨52067937803147060244372179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34711958535431373496248119 52067937803147060244372179)
  ·
    refine ⟨78101906704720590366558269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52067937803147060244372179 78101906704720590366558269)
    ·
      refine ⟨29288215014270221387459351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78101906704720590366558269 29288215014270221387459351)
      ·
        refine ⟨43932322521405332081189027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29288215014270221387459351 43932322521405332081189027)
        ·
          refine ⟨65898483782107998121783541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43932322521405332081189027 65898483782107998121783541)
          ·
            refine ⟨6177982854572624823917207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65898483782107998121783541 6177982854572624823917207)
            ·
              refine ⟨9266974281858937235875811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177982854572624823917207 9266974281858937235875811)
              ·
                refine ⟨13900461422788405853813717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266974281858937235875811 13900461422788405853813717)
                ·
                  refine ⟨325792064596603262198759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13900461422788405853813717 325792064596603262198759)
                  ·
                    rfl

theorem cell21_1427575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_1427575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427575 prefixEnd_1427575 := by exact prefixLift 1427575
  have htrace : WordTrace (prefixWord ++ tailWord_1427575) baseStart_1427575 baseEnd_1427575 := by
    simpa [prefixWord, tailWord_1427575, baseEnd_1427575] using wordTrace_append hprefix tailTrace_1427575
  have hstable : (prefixWord ++ tailWord_1427575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427575).length < 2 ^ (prefixWord ++ tailWord_1427575).sum := by decide
  have hdescent : baseEnd_1427575 < baseStart_1427575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427716 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1427716 : Nat := 118140960795 + 1427716 * 2 ^ 59
def prefixEnd_1427716 : Nat := 4983230072969 + 3 ^ 40 * 1427716 * 2
def baseEnd_1427716 : Nat := 325824242717618350348471

theorem tailTrace_1427716 : CollatzResearch.WordTrace tailWord_1427716 prefixEnd_1427716 325824242717618350348471 := by
  unfold tailWord_1427716
  simp only [CollatzResearch.WordTrace]
  refine ⟨26036540247818120662627501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34715386997090827550170001 26036540247818120662627501)
  ·
    refine ⟨9763702592931795248485313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26036540247818120662627501 9763702592931795248485313)
    ·
      refine ⟨7322776944698846436363985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9763702592931795248485313 7322776944698846436363985)
      ·
        refine ⟨5492082708524134827272989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7322776944698846436363985 5492082708524134827272989)
        ·
          refine ⟨2059531015696550560227371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5492082708524134827272989 2059531015696550560227371)
          ·
            refine ⟨3089296523544825840341057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059531015696550560227371 3089296523544825840341057)
            ·
              refine ⟨2316972392658619380255793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089296523544825840341057 2316972392658619380255793)
              ·
                refine ⟨1737729294493964535191845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316972392658619380255793 1737729294493964535191845)
                ·
                  refine ⟨325824242717618350348471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737729294493964535191845 325824242717618350348471)
                  ·
                    rfl

theorem cell21_1427716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1427716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427716 prefixEnd_1427716 := by exact prefixLift 1427716
  have htrace : WordTrace (prefixWord ++ tailWord_1427716) baseStart_1427716 baseEnd_1427716 := by
    simpa [prefixWord, tailWord_1427716, baseEnd_1427716] using wordTrace_append hprefix tailTrace_1427716
  have hstable : (prefixWord ++ tailWord_1427716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427716).length < 2 ^ (prefixWord ++ tailWord_1427716).sum := by decide
  have hdescent : baseEnd_1427716 < baseStart_1427716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427744 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_1427744 : Nat := 118140960795 + 1427744 * 2 ^ 59
def prefixEnd_1427744 : Nat := 4983230072969 + 3 ^ 40 * 1427744 * 2
def baseEnd_1427744 : Nat := 325830632699096523881747

theorem tailTrace_1427744 : CollatzResearch.WordTrace tailWord_1427744 prefixEnd_1427744 325830632699096523881747 := by
  unfold tailWord_1427744
  simp only [CollatzResearch.WordTrace]
  refine ⟨26037050869767401053637143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34716067826356534738182857 26037050869767401053637143)
  ·
    refine ⟨39055576304651101580455715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26037050869767401053637143 39055576304651101580455715)
    ·
      refine ⟨58583364456976652370683573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39055576304651101580455715 58583364456976652370683573)
      ·
        refine ⟨5492190417841561159751585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58583364456976652370683573 5492190417841561159751585)
        ·
          refine ⟨4119142813381170869813689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5492190417841561159751585 4119142813381170869813689)
          ·
            refine ⟨3089357110035878152360267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4119142813381170869813689 3089357110035878152360267)
            ·
              refine ⟨4634035665053817228540401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089357110035878152360267 4634035665053817228540401)
              ·
                refine ⟨3475526748790362921405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4634035665053817228540401 3475526748790362921405301)
                ·
                  refine ⟨325830632699096523881747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475526748790362921405301 325830632699096523881747)
                  ·
                    rfl

theorem cell21_1427744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_1427744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427744 prefixEnd_1427744 := by exact prefixLift 1427744
  have htrace : WordTrace (prefixWord ++ tailWord_1427744) baseStart_1427744 baseEnd_1427744 := by
    simpa [prefixWord, tailWord_1427744, baseEnd_1427744] using wordTrace_append hprefix tailTrace_1427744
  have hstable : (prefixWord ++ tailWord_1427744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427744).length < 2 ^ (prefixWord ++ tailWord_1427744).sum := by decide
  have hdescent : baseEnd_1427744 < baseStart_1427744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427772 : List Nat := [2, 2, 2, 2, 1, 2, 10]
def baseStart_1427772 : Nat := 118140960795 + 1427772 * 2 ^ 59
def prefixEnd_1427772 : Nat := 4983230072969 + 3 ^ 40 * 1427772 * 2
def baseEnd_1427772 : Nat := 36204113631174966379447

theorem tailTrace_1427772 : CollatzResearch.WordTrace tailWord_1427772 prefixEnd_1427772 36204113631174966379447 := by
  unfold tailWord_1427772
  simp only [CollatzResearch.WordTrace]
  refine ⟨26037561491716681444646785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34716748655622241926195713 26037561491716681444646785)
  ·
    refine ⟨19528171118787511083485089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26037561491716681444646785 19528171118787511083485089)
    ·
      refine ⟨14646128339090633312613817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19528171118787511083485089 14646128339090633312613817)
      ·
        refine ⟨10984596254317974984460363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14646128339090633312613817 10984596254317974984460363)
        ·
          refine ⟨16476894381476962476690545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984596254317974984460363 16476894381476962476690545)
          ·
            refine ⟨12357670786107721857517909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16476894381476962476690545 12357670786107721857517909)
            ·
              refine ⟨36204113631174966379447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12357670786107721857517909 36204113631174966379447)
              ·
                rfl

theorem cell21_1427772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 10].length) (baseStart_1427772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427772 prefixEnd_1427772 := by exact prefixLift 1427772
  have htrace : WordTrace (prefixWord ++ tailWord_1427772) baseStart_1427772 baseEnd_1427772 := by
    simpa [prefixWord, tailWord_1427772, baseEnd_1427772] using wordTrace_append hprefix tailTrace_1427772
  have hstable : (prefixWord ++ tailWord_1427772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427772).length < 2 ^ (prefixWord ++ tailWord_1427772).sum := by decide
  have hdescent : baseEnd_1427772 < baseStart_1427772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427817 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1427817 : Nat := 118140960795 + 1427817 * 2 ^ 59
def prefixEnd_1427817 : Nat := 4983230072969 + 3 ^ 40 * 1427817 * 2
def baseEnd_1427817 : Nat := 325847292293664619164931

theorem tailTrace_1427817 : CollatzResearch.WordTrace tailWord_1427817 prefixEnd_1427817 325847292293664619164931 := by
  unfold tailWord_1427817
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076764268270335574681705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34717842845513557049787803 52076764268270335574681705)
  ·
    refine ⟨39057573201202751681011279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52076764268270335574681705 39057573201202751681011279)
    ·
      refine ⟨58586359801804127521516919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39057573201202751681011279 58586359801804127521516919)
      ·
        refine ⟨87879539702706191282275379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58586359801804127521516919 87879539702706191282275379)
        ·
          refine ⟨131819309554059286923413069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87879539702706191282275379 131819309554059286923413069)
          ·
            refine ⟨49432241082772232596279901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131819309554059286923413069 49432241082772232596279901)
            ·
              refine ⟨18537090406039587223604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49432241082772232596279901 18537090406039587223604963)
              ·
                refine ⟨27805635609059380835407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18537090406039587223604963 27805635609059380835407445)
                ·
                  refine ⟨325847292293664619164931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27805635609059380835407445 325847292293664619164931)
                  ·
                    rfl

theorem cell21_1427817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1427817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427817 prefixEnd_1427817 := by exact prefixLift 1427817
  have htrace : WordTrace (prefixWord ++ tailWord_1427817) baseStart_1427817 baseEnd_1427817 := by
    simpa [prefixWord, tailWord_1427817, baseEnd_1427817] using wordTrace_append hprefix tailTrace_1427817
  have hstable : (prefixWord ++ tailWord_1427817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427817).length < 2 ^ (prefixWord ++ tailWord_1427817).sum := by decide
  have hdescent : baseEnd_1427817 < baseStart_1427817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427851 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 4]
def baseStart_1427851 : Nat := 118140960795 + 1427851 * 2 ^ 59
def prefixEnd_1427851 : Nat := 4983230072969 + 3 ^ 40 * 1427851 * 2
def baseEnd_1427851 : Nat := 325855051556888115598195

theorem tailTrace_1427851 : CollatzResearch.WordTrace tailWord_1427851 prefixEnd_1427851 325855051556888115598195 := by
  unfold tailWord_1427851
  simp only [CollatzResearch.WordTrace]
  refine ⟨52078004350147159381419407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34718669566764772920946271 52078004350147159381419407)
  ·
    refine ⟨78117006525220739072129111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52078004350147159381419407 78117006525220739072129111)
    ·
      refine ⟨117175509787831108608193667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78117006525220739072129111 117175509787831108608193667)
      ·
        refine ⟨175763264681746662912290501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117175509787831108608193667 175763264681746662912290501)
        ·
          refine ⟨32955612127827499296054469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175763264681746662912290501 32955612127827499296054469)
          ·
            refine ⟨6179177273967656118010213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32955612127827499296054469 6179177273967656118010213)
            ·
              refine ⟨1158595738868935522126915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6179177273967656118010213 1158595738868935522126915)
              ·
                refine ⟨1737893608303403283190373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158595738868935522126915 1737893608303403283190373)
                ·
                  refine ⟨325855051556888115598195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737893608303403283190373 325855051556888115598195)
                  ·
                    rfl

theorem cell21_1427851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_1427851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427851 prefixEnd_1427851 := by exact prefixLift 1427851
  have htrace : WordTrace (prefixWord ++ tailWord_1427851) baseStart_1427851 baseEnd_1427851 := by
    simpa [prefixWord, tailWord_1427851, baseEnd_1427851] using wordTrace_append hprefix tailTrace_1427851
  have hstable : (prefixWord ++ tailWord_1427851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427851).length < 2 ^ (prefixWord ++ tailWord_1427851).sum := by decide
  have hdescent : baseEnd_1427851 < baseStart_1427851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427882 : List Nat := [3, 1, 6, 1, 10]
def baseStart_1427882 : Nat := 118140960795 + 1427882 * 2 ^ 59
def prefixEnd_1427882 : Nat := 4983230072969 + 3 ^ 40 * 1427882 * 2
def baseEnd_1427882 : Nat := 4022989212089369760265

theorem tailTrace_1427882 : CollatzResearch.WordTrace tailWord_1427882 prefixEnd_1427882 4022989212089369760265 := by
  unfold tailWord_1427882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13019783753258712918949475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34719423342023234450531933 13019783753258712918949475)
  ·
    refine ⟨19529675629888069378424213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13019783753258712918949475 19529675629888069378424213)
    ·
      refine ⟨915453545151003252113635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19529675629888069378424213 915453545151003252113635)
      ·
        refine ⟨1373180317726504878170453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915453545151003252113635 1373180317726504878170453)
        ·
          refine ⟨4022989212089369760265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1373180317726504878170453 4022989212089369760265)
          ·
            rfl

theorem cell21_1427882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 10].length) (baseStart_1427882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427882 prefixEnd_1427882 := by exact prefixLift 1427882
  have htrace : WordTrace (prefixWord ++ tailWord_1427882) baseStart_1427882 baseEnd_1427882 := by
    simpa [prefixWord, tailWord_1427882, baseEnd_1427882] using wordTrace_append hprefix tailTrace_1427882
  have hstable : (prefixWord ++ tailWord_1427882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427882).length < 2 ^ (prefixWord ++ tailWord_1427882).sum := by decide
  have hdescent : baseEnd_1427882 < baseStart_1427882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427941 : List Nat := [1, 3, 1, 5, 2, 1, 8]
def baseStart_1427941 : Nat := 118140960795 + 1427941 * 2 ^ 59
def prefixEnd_1427941 : Nat := 4983230072969 + 3 ^ 40 * 1427941 * 2
def baseEnd_1427941 : Nat := 36208398975896439899779

theorem tailTrace_1427941 : CollatzResearch.WordTrace tailWord_1427941 prefixEnd_1427941 36208398975896439899779 := by
  unfold tailWord_1427941
  simp only [CollatzResearch.WordTrace]
  refine ⟨52081286919821104752195677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34720857946547403168130451 52081286919821104752195677)
  ·
    refine ⟨19530482594932914282073379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52081286919821104752195677 19530482594932914282073379)
    ·
      refine ⟨29295723892399371423110069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19530482594932914282073379 29295723892399371423110069)
      ·
        refine ⟨2746474114912441070916569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29295723892399371423110069 2746474114912441070916569)
        ·
          refine ⟨2059855586184330803187427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746474114912441070916569 2059855586184330803187427)
          ·
            refine ⟨3089783379276496204781141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059855586184330803187427 3089783379276496204781141)
            ·
              refine ⟨36208398975896439899779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3089783379276496204781141 36208398975896439899779)
              ·
                rfl

theorem cell21_1427941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 8].length) (baseStart_1427941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427941 prefixEnd_1427941 := by exact prefixLift 1427941
  have htrace : WordTrace (prefixWord ++ tailWord_1427941) baseStart_1427941 baseEnd_1427941 := by
    simpa [prefixWord, tailWord_1427941, baseEnd_1427941] using wordTrace_append hprefix tailTrace_1427941
  have hstable : (prefixWord ++ tailWord_1427941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427941).length < 2 ^ (prefixWord ++ tailWord_1427941).sum := by decide
  have hdescent : baseEnd_1427941 < baseStart_1427941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427955 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_1427955 : Nat := 118140960795 + 1427955 * 2 ^ 59
def prefixEnd_1427955 : Nat := 4983230072969 + 3 ^ 40 * 1427955 * 2
def baseEnd_1427955 : Nat := 325878785773807045864649

theorem tailTrace_1427955 : CollatzResearch.WordTrace tailWord_1427955 prefixEnd_1427955 325878785773807045864649 := by
  unfold tailWord_1427955
  simp only [CollatzResearch.WordTrace]
  refine ⟨52081797541770385143205319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34721198361180256762136879 52081797541770385143205319)
  ·
    refine ⟨78122696312655577714807979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52081797541770385143205319 78122696312655577714807979)
    ·
      refine ⟨117184044468983366572211969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78122696312655577714807979 117184044468983366572211969)
      ·
        refine ⟨87888033351737524929158977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117184044468983366572211969 87888033351737524929158977)
        ·
          refine ⟨65916025013803143696869233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87888033351737524929158977 65916025013803143696869233)
          ·
            refine ⟨49437018760352357772651925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65916025013803143696869233 49437018760352357772651925)
            ·
              refine ⟨2317360254391516770593059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49437018760352357772651925 2317360254391516770593059)
              ·
                refine ⟨3476040381587275155889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317360254391516770593059 3476040381587275155889589)
                ·
                  refine ⟨325878785773807045864649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476040381587275155889589 325878785773807045864649)
                  ·
                    rfl

theorem cell21_1427955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_1427955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427955 prefixEnd_1427955 := by exact prefixLift 1427955
  have htrace : WordTrace (prefixWord ++ tailWord_1427955) baseStart_1427955 baseEnd_1427955 := by
    simpa [prefixWord, tailWord_1427955, baseEnd_1427955] using wordTrace_append hprefix tailTrace_1427955
  have hstable : (prefixWord ++ tailWord_1427955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427955).length < 2 ^ (prefixWord ++ tailWord_1427955).sum := by decide
  have hdescent : baseEnd_1427955 < baseStart_1427955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427972 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1427972 : Nat := 118140960795 + 1427972 * 2 ^ 59
def prefixEnd_1427972 : Nat := 4983230072969 + 3 ^ 40 * 1427972 * 2
def baseEnd_1427972 : Nat := 325882665405418794081281

theorem tailTrace_1427972 : CollatzResearch.WordTrace tailWord_1427972 prefixEnd_1427972 325882665405418794081281 := by
  unfold tailWord_1427972
  simp only [CollatzResearch.WordTrace]
  refine ⟨26041208791354398523287085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34721611721805864697716113 26041208791354398523287085)
  ·
    refine ⟨9765453296757899446232657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26041208791354398523287085 9765453296757899446232657)
    ·
      refine ⟨7324089972568424584674493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9765453296757899446232657 7324089972568424584674493)
      ·
        refine ⟨2746533739713159219252935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7324089972568424584674493 2746533739713159219252935)
        ·
          refine ⟨4119800609569738828879403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746533739713159219252935 4119800609569738828879403)
          ·
            refine ⟨6179700914354608243319105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119800609569738828879403 6179700914354608243319105)
            ·
              refine ⟨4634775685765956182489329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6179700914354608243319105 4634775685765956182489329)
              ·
                refine ⟨3476081764324467136866997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4634775685765956182489329 3476081764324467136866997)
                ·
                  refine ⟨325882665405418794081281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476081764324467136866997 325882665405418794081281)
                  ·
                    rfl

theorem cell21_1427972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1427972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427972 prefixEnd_1427972 := by exact prefixLift 1427972
  have htrace : WordTrace (prefixWord ++ tailWord_1427972) baseStart_1427972 baseEnd_1427972 := by
    simpa [prefixWord, tailWord_1427972, baseEnd_1427972] using wordTrace_append hprefix tailTrace_1427972
  have hstable : (prefixWord ++ tailWord_1427972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427972).length < 2 ^ (prefixWord ++ tailWord_1427972).sum := by decide
  have hdescent : baseEnd_1427972 < baseStart_1427972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1427975 : List Nat := [1, 1, 4, 3, 4, 1, 2, 5]
def baseStart_1427975 : Nat := 118140960795 + 1427975 * 2 ^ 59
def prefixEnd_1427975 : Nat := 4983230072969 + 3 ^ 40 * 1427975 * 2
def baseEnd_1427975 : Nat := 108627783348763818510425

theorem tailTrace_1427975 : CollatzResearch.WordTrace tailWord_1427975 prefixEnd_1427975 108627783348763818510425 := by
  unfold tailWord_1427975
  simp only [CollatzResearch.WordTrace]
  refine ⟨52082527001697928558933379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34721684667798619039288919 52082527001697928558933379)
  ·
    refine ⟨78123790502546892838400069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52082527001697928558933379 78123790502546892838400069)
    ·
      refine ⟨14648210719227542407200013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78123790502546892838400069 14648210719227542407200013)
      ·
        refine ⟨5493079019710328402700005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14648210719227542407200013 5493079019710328402700005)
        ·
          refine ⟨1029952316195686575506251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5493079019710328402700005 1029952316195686575506251)
          ·
            refine ⟨1544928474293529863259377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029952316195686575506251 1544928474293529863259377)
            ·
              refine ⟨1158696355720147397444533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544928474293529863259377 1158696355720147397444533)
              ·
                refine ⟨108627783348763818510425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158696355720147397444533 108627783348763818510425)
                ·
                  rfl

theorem cell21_1427975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].length) (baseStart_1427975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1427975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1427975 prefixEnd_1427975 := by exact prefixLift 1427975
  have htrace : WordTrace (prefixWord ++ tailWord_1427975) baseStart_1427975 baseEnd_1427975 := by
    simpa [prefixWord, tailWord_1427975, baseEnd_1427975] using wordTrace_append hprefix tailTrace_1427975
  have hstable : (prefixWord ++ tailWord_1427975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1427975).length < 2 ^ (prefixWord ++ tailWord_1427975).sum := by decide
  have hdescent : baseEnd_1427975 < baseStart_1427975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1427975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428065 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 3]
def baseStart_1428065 : Nat := 118140960795 + 1428065 * 2 ^ 59
def prefixEnd_1428065 : Nat := 4983230072969 + 3 ^ 40 * 1428065 * 2
def baseEnd_1428065 : Nat := 325903889272471299031091

theorem tailTrace_1428065 : CollatzResearch.WordTrace tailWord_1428065 prefixEnd_1428065 325903889272471299031091 := by
  unfold tailWord_1428065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52085809571371873929709649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34723873047581249286473099 52085809571371873929709649)
  ·
    refine ⟨39064357178528905447282237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52085809571371873929709649 39064357178528905447282237)
    ·
      refine ⟨14649133941948339542730839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39064357178528905447282237 14649133941948339542730839)
      ·
        refine ⟨21973700912922509314096259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649133941948339542730839 21973700912922509314096259)
        ·
          refine ⟨32960551369383763971144389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21973700912922509314096259 32960551369383763971144389)
          ·
            refine ⟨6180103381759455744589573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32960551369383763971144389 6180103381759455744589573)
            ·
              refine ⟨1158769384079897952110545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6180103381759455744589573 1158769384079897952110545)
              ·
                refine ⟨869077038059923464082909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158769384079897952110545 869077038059923464082909)
                ·
                  refine ⟨325903889272471299031091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869077038059923464082909 325903889272471299031091)
                  ·
                    rfl

theorem cell21_1428065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_1428065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428065 prefixEnd_1428065 := by exact prefixLift 1428065
  have htrace : WordTrace (prefixWord ++ tailWord_1428065) baseStart_1428065 baseEnd_1428065 := by
    simpa [prefixWord, tailWord_1428065, baseEnd_1428065] using wordTrace_append hprefix tailTrace_1428065
  have hstable : (prefixWord ++ tailWord_1428065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428065).length < 2 ^ (prefixWord ++ tailWord_1428065).sum := by decide
  have hdescent : baseEnd_1428065 < baseStart_1428065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428076 : List Nat := [2, 2, 1, 1, 3, 1, 5, 6]
def baseStart_1428076 : Nat := 118140960795 + 1428076 * 2 ^ 59
def prefixEnd_1428076 : Nat := 4983230072969 + 3 ^ 40 * 1428076 * 2
def baseEnd_1428076 : Nat := 108635466540779241449245

theorem tailTrace_1428076 : CollatzResearch.WordTrace tailWord_1428076 prefixEnd_1428076 108635466540779241449245 := by
  unfold tailWord_1428076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043105387166011404180041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34724140516221348538906721 26043105387166011404180041)
  ·
    refine ⟨19532329040374508553135031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26043105387166011404180041 19532329040374508553135031)
    ·
      refine ⟨29298493560561762829702547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19532329040374508553135031 29298493560561762829702547)
      ·
        refine ⟨43947740340842644244553821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29298493560561762829702547 43947740340842644244553821)
        ·
          refine ⟨16480402627815991591707683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43947740340842644244553821 16480402627815991591707683)
          ·
            refine ⟨24720603941723987387561525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16480402627815991591707683 24720603941723987387561525)
            ·
              refine ⟨2317556619536623817583893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24720603941723987387561525 2317556619536623817583893)
              ·
                refine ⟨108635466540779241449245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2317556619536623817583893 108635466540779241449245)
                ·
                  rfl

theorem cell21_1428076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_1428076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428076 prefixEnd_1428076 := by exact prefixLift 1428076
  have htrace : WordTrace (prefixWord ++ tailWord_1428076) baseStart_1428076 baseEnd_1428076 := by
    simpa [prefixWord, tailWord_1428076, baseEnd_1428076] using wordTrace_append hprefix tailTrace_1428076
  have hstable : (prefixWord ++ tailWord_1428076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428076).length < 2 ^ (prefixWord ++ tailWord_1428076).sum := by decide
  have hdescent : baseEnd_1428076 < baseStart_1428076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428121 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_1428121 : Nat := 118140960795 + 1428121 * 2 ^ 59
def prefixEnd_1428121 : Nat := 4983230072969 + 3 ^ 40 * 1428121 * 2
def baseEnd_1428121 : Nat := 325916669235427646097643

theorem tailTrace_1428121 : CollatzResearch.WordTrace tailWord_1428121 prefixEnd_1428121 325916669235427646097643 := by
  unfold tailWord_1428121
  simp only [CollatzResearch.WordTrace]
  refine ⟨52087852059168995493748217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34725234706112663662498811 52087852059168995493748217)
  ·
    refine ⟨39065889044376746620311163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52087852059168995493748217 39065889044376746620311163)
    ·
      refine ⟨58598833566565119930466745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39065889044376746620311163 58598833566565119930466745)
      ·
        refine ⟨43949125174923839947850059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58598833566565119930466745 43949125174923839947850059)
        ·
          refine ⟨65923687762385759921775089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43949125174923839947850059 65923687762385759921775089)
          ·
            refine ⟨49442765821789319941331317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65923687762385759921775089 49442765821789319941331317)
            ·
              refine ⟨4635259295792748744499811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49442765821789319941331317 4635259295792748744499811)
              ·
                refine ⟨6952888943689123116749717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635259295792748744499811 6952888943689123116749717)
                ·
                  refine ⟨325916669235427646097643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6952888943689123116749717 325916669235427646097643)
                  ·
                    rfl

theorem cell21_1428121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_1428121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428121 prefixEnd_1428121 := by exact prefixLift 1428121
  have htrace : WordTrace (prefixWord ++ tailWord_1428121) baseStart_1428121 baseEnd_1428121 := by
    simpa [prefixWord, tailWord_1428121, baseEnd_1428121] using wordTrace_append hprefix tailTrace_1428121
  have hstable : (prefixWord ++ tailWord_1428121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428121).length < 2 ^ (prefixWord ++ tailWord_1428121).sum := by decide
  have hdescent : baseEnd_1428121 < baseStart_1428121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428124 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1428124 : Nat := 118140960795 + 1428124 * 2 ^ 59
def prefixEnd_1428124 : Nat := 4983230072969 + 3 ^ 40 * 1428124 * 2
def baseEnd_1428124 : Nat := 325917353876300307547637

theorem tailTrace_1428124 : CollatzResearch.WordTrace tailWord_1428124 prefixEnd_1428124 325917353876300307547637 := by
  unfold tailWord_1428124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043980739079063503053713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34725307652105418004071617 26043980739079063503053713)
  ·
    refine ⟨19532985554309297627290285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26043980739079063503053713 19532985554309297627290285)
    ·
      refine ⟨7324869582865986610233857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19532985554309297627290285 7324869582865986610233857)
      ·
        refine ⟨5493652187149489957675393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324869582865986610233857 5493652187149489957675393)
        ·
          refine ⟨4120239140362117468256545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5493652187149489957675393 4120239140362117468256545)
          ·
            refine ⟨3090179355271588101192409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120239140362117468256545 3090179355271588101192409)
            ·
              refine ⟨2317634516453691075894307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090179355271588101192409 2317634516453691075894307)
              ·
                refine ⟨3476451774680536613841461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317634516453691075894307 3476451774680536613841461)
                ·
                  refine ⟨325917353876300307547637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476451774680536613841461 325917353876300307547637)
                  ·
                    rfl

theorem cell21_1428124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1428124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428124 prefixEnd_1428124 := by exact prefixLift 1428124
  have htrace : WordTrace (prefixWord ++ tailWord_1428124) baseStart_1428124 baseEnd_1428124 := by
    simpa [prefixWord, tailWord_1428124, baseEnd_1428124] using wordTrace_append hprefix tailTrace_1428124
  have hstable : (prefixWord ++ tailWord_1428124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428124).length < 2 ^ (prefixWord ++ tailWord_1428124).sum := by decide
  have hdescent : baseEnd_1428124 < baseStart_1428124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428183 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_1428183 : Nat := 118140960795 + 1428183 * 2 ^ 59
def prefixEnd_1428183 : Nat := 4983230072969 + 3 ^ 40 * 1428183 * 2
def baseEnd_1428183 : Nat := 325930818480129316064183

theorem tailTrace_1428183 : CollatzResearch.WordTrace tailWord_1428183 prefixEnd_1428183 325930818480129316064183 := by
  unfold tailWord_1428183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52090113384944380082505203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34726742256629586721670135 52090113384944380082505203)
  ·
    refine ⟨78135170077416570123757805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52090113384944380082505203 78135170077416570123757805)
    ·
      refine ⟨29300688779031213796409177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78135170077416570123757805 29300688779031213796409177)
      ·
        refine ⟨21975516584273410347306883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29300688779031213796409177 21975516584273410347306883)
        ·
          refine ⟨32963274876410115520960325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21975516584273410347306883 32963274876410115520960325)
          ·
            refine ⟨6180614039326896660180061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32963274876410115520960325 6180614039326896660180061)
            ·
              refine ⟨2317730264747586247567523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6180614039326896660180061 2317730264747586247567523)
              ·
                refine ⟨3476595397121379371351285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317730264747586247567523 3476595397121379371351285)
                ·
                  refine ⟨325930818480129316064183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476595397121379371351285 325930818480129316064183)
                  ·
                    rfl

theorem cell21_1428183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_1428183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428183 prefixEnd_1428183 := by exact prefixLift 1428183
  have htrace : WordTrace (prefixWord ++ tailWord_1428183) baseStart_1428183 baseEnd_1428183 := by
    simpa [prefixWord, tailWord_1428183, baseEnd_1428183] using wordTrace_append hprefix tailTrace_1428183
  have hstable : (prefixWord ++ tailWord_1428183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428183).length < 2 ^ (prefixWord ++ tailWord_1428183).sum := by decide
  have hdescent : baseEnd_1428183 < baseStart_1428183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428231 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_1428231 : Nat := 118140960795 + 1428231 * 2 ^ 59
def prefixEnd_1428231 : Nat := 4983230072969 + 3 ^ 40 * 1428231 * 2
def baseEnd_1428231 : Nat := 325941772734091899264085

theorem tailTrace_1428231 : CollatzResearch.WordTrace tailWord_1428231 prefixEnd_1428231 325941772734091899264085 := by
  unfold tailWord_1428231
  simp only [CollatzResearch.WordTrace]
  refine ⟨52091864088770484280252547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34727909392513656186835031 52091864088770484280252547)
  ·
    refine ⟨78137796133155726420378821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52091864088770484280252547 78137796133155726420378821)
    ·
      refine ⟨14650836774966698703821029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78137796133155726420378821 14650836774966698703821029)
      ·
        refine ⟨2747031895306256006966443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14650836774966698703821029 2747031895306256006966443)
        ·
          refine ⟨4120547842959384010449665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747031895306256006966443 4120547842959384010449665)
          ·
            refine ⟨3090410882219538007837249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120547842959384010449665 3090410882219538007837249)
            ·
              refine ⟨2317808161664653505877937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090410882219538007837249 2317808161664653505877937)
              ·
                refine ⟨1738356121248490129408453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317808161664653505877937 1738356121248490129408453)
                ·
                  refine ⟨325941772734091899264085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738356121248490129408453 325941772734091899264085)
                  ·
                    rfl

theorem cell21_1428231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_1428231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428231 prefixEnd_1428231 := by exact prefixLift 1428231
  have htrace : WordTrace (prefixWord ++ tailWord_1428231) baseStart_1428231 baseEnd_1428231 := by
    simpa [prefixWord, tailWord_1428231, baseEnd_1428231] using wordTrace_append hprefix tailTrace_1428231
  have hstable : (prefixWord ++ tailWord_1428231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428231).length < 2 ^ (prefixWord ++ tailWord_1428231).sum := by decide
  have hdescent : baseEnd_1428231 < baseStart_1428231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428273 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1428273 : Nat := 118140960795 + 1428273 * 2 ^ 59
def prefixEnd_1428273 : Nat := 4983230072969 + 3 ^ 40 * 1428273 * 2
def baseEnd_1428273 : Nat := 325951357706309159563999

theorem tailTrace_1428273 : CollatzResearch.WordTrace tailWord_1428273 prefixEnd_1428273 325951357706309159563999 := by
  unfold tailWord_1428273
  simp only [CollatzResearch.WordTrace]
  refine ⟨52093395954618325453281473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34728930636412216968854315 52093395954618325453281473)
  ·
    refine ⟨39070046965963744089961105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52093395954618325453281473 39070046965963744089961105)
    ·
      refine ⟨29302535224472808067470829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39070046965963744089961105 29302535224472808067470829)
      ·
        refine ⟨10988450709177303025301561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29302535224472808067470829 10988450709177303025301561)
        ·
          refine ⟨8241338031882977268976171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988450709177303025301561 8241338031882977268976171)
          ·
            refine ⟨12362007047824465903464257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241338031882977268976171 12362007047824465903464257)
            ·
              refine ⟨9271505285868349427598193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12362007047824465903464257 9271505285868349427598193)
              ·
                refine ⟨6953628964401262070698645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9271505285868349427598193 6953628964401262070698645)
                ·
                  refine ⟨325951357706309159563999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6953628964401262070698645 325951357706309159563999)
                  ·
                    rfl

theorem cell21_1428273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1428273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428273 prefixEnd_1428273 := by exact prefixLift 1428273
  have htrace : WordTrace (prefixWord ++ tailWord_1428273) baseStart_1428273 baseEnd_1428273 := by
    simpa [prefixWord, tailWord_1428273, baseEnd_1428273] using wordTrace_append hprefix tailTrace_1428273
  have hstable : (prefixWord ++ tailWord_1428273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428273).length < 2 ^ (prefixWord ++ tailWord_1428273).sum := by decide
  have hdescent : baseEnd_1428273 < baseStart_1428273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428349 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1428349 : Nat := 118140960795 + 1428349 * 2 ^ 59
def prefixEnd_1428349 : Nat := 4983230072969 + 3 ^ 40 * 1428349 * 2
def baseEnd_1428349 : Nat := 325968701941749916297177

theorem tailTrace_1428349 : CollatzResearch.WordTrace tailWord_1428349 prefixEnd_1428349 325968701941749916297177 := by
  unfold tailWord_1428349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52096167902342990433048101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34730778601561993622032067 52096167902342990433048101)
  ·
    refine ⟨9768031481689310706196519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52096167902342990433048101 9768031481689310706196519)
    ·
      refine ⟨14652047222533966059294779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768031481689310706196519 14652047222533966059294779)
      ·
        refine ⟨21978070833800949088942169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14652047222533966059294779 21978070833800949088942169)
        ·
          refine ⟨16483553125350711816706627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21978070833800949088942169 16483553125350711816706627)
          ·
            refine ⟨24725329688026067725059941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16483553125350711816706627 24725329688026067725059941)
            ·
              refine ⟨4635999316504887698448739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24725329688026067725059941 4635999316504887698448739)
              ·
                refine ⟨6953998974757331547673109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635999316504887698448739 6953998974757331547673109)
                ·
                  refine ⟨325968701941749916297177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6953998974757331547673109 325968701941749916297177)
                  ·
                    rfl

theorem cell21_1428349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1428349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428349 prefixEnd_1428349 := by exact prefixLift 1428349
  have htrace : WordTrace (prefixWord ++ tailWord_1428349) baseStart_1428349 baseEnd_1428349 := by
    simpa [prefixWord, tailWord_1428349, baseEnd_1428349] using wordTrace_append hprefix tailTrace_1428349
  have hstable : (prefixWord ++ tailWord_1428349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428349).length < 2 ^ (prefixWord ++ tailWord_1428349).sum := by decide
  have hdescent : baseEnd_1428349 < baseStart_1428349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428363 : List Nat := [1, 1, 1, 1, 4, 2, 3, 8]
def baseStart_1428363 : Nat := 118140960795 + 1428363 * 2 ^ 59
def prefixEnd_1428363 : Nat := 4983230072969 + 3 ^ 40 * 1428363 * 2
def baseEnd_1428363 : Nat := 108657298977496334354605

theorem tailTrace_1428363 : CollatzResearch.WordTrace tailWord_1428363 prefixEnd_1428363 108657298977496334354605 := by
  unfold tailWord_1428363
  simp only [CollatzResearch.WordTrace]
  refine ⟨52096678524292270824057743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34731119016194847216038495 52096678524292270824057743)
  ·
    refine ⟨78145017786438406236086615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52096678524292270824057743 78145017786438406236086615)
    ·
      refine ⟨117217526679657609354129923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78145017786438406236086615 117217526679657609354129923)
      ·
        refine ⟨175826290019486414031194885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117217526679657609354129923 175826290019486414031194885)
        ·
          refine ⟨32967429378653702630849041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175826290019486414031194885 32967429378653702630849041)
          ·
            refine ⟨24725572033990276973136781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32967429378653702630849041 24725572033990276973136781)
            ·
              refine ⟨9272089512746353864926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24725572033990276973136781 9272089512746353864926293)
              ·
                refine ⟨108657298977496334354605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9272089512746353864926293 108657298977496334354605)
                ·
                  rfl

theorem cell21_1428363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_1428363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428363 prefixEnd_1428363 := by exact prefixLift 1428363
  have htrace : WordTrace (prefixWord ++ tailWord_1428363) baseStart_1428363 baseEnd_1428363 := by
    simpa [prefixWord, tailWord_1428363, baseEnd_1428363] using wordTrace_append hprefix tailTrace_1428363
  have hstable : (prefixWord ++ tailWord_1428363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428363).length < 2 ^ (prefixWord ++ tailWord_1428363).sum := by decide
  have hdescent : baseEnd_1428363 < baseStart_1428363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428397 : List Nat := [1, 5, 2, 3, 1, 9]
def baseStart_1428397 : Nat := 118140960795 + 1428397 * 2 ^ 59
def prefixEnd_1428397 : Nat := 4983230072969 + 3 ^ 40 * 1428397 * 2
def baseEnd_1428397 : Nat := 12073320599841203685077

theorem tailTrace_1428397 : CollatzResearch.WordTrace tailWord_1428397 prefixEnd_1428397 12073320599841203685077 := by
  unfold tailWord_1428397
  simp only [CollatzResearch.WordTrace]
  refine ⟨52097918606169094630795445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34731945737446063087196963 52097918606169094630795445)
  ·
    refine ⟨4884179869328352621637073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52097918606169094630795445 4884179869328352621637073)
    ·
      refine ⟨3663134901996264466227805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4884179869328352621637073 3663134901996264466227805)
      ·
        refine ⟨1373675588248599174835427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3663134901996264466227805 1373675588248599174835427)
        ·
          refine ⟨2060513382372898762253141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373675588248599174835427 2060513382372898762253141)
          ·
            refine ⟨12073320599841203685077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2060513382372898762253141 12073320599841203685077)
            ·
              rfl

theorem cell21_1428397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 9].length) (baseStart_1428397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428397 prefixEnd_1428397 := by exact prefixLift 1428397
  have htrace : WordTrace (prefixWord ++ tailWord_1428397) baseStart_1428397 baseEnd_1428397 := by
    simpa [prefixWord, tailWord_1428397, baseEnd_1428397] using wordTrace_append hprefix tailTrace_1428397
  have hstable : (prefixWord ++ tailWord_1428397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428397).length < 2 ^ (prefixWord ++ tailWord_1428397).sum := by decide
  have hdescent : baseEnd_1428397 < baseStart_1428397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428445 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1428445 : Nat := 118140960795 + 1428445 * 2 ^ 59
def prefixEnd_1428445 : Nat := 4983230072969 + 3 ^ 40 * 1428445 * 2
def baseEnd_1428445 : Nat := 325990610449675082696981

theorem tailTrace_1428445 : CollatzResearch.WordTrace tailWord_1428445 prefixEnd_1428445 325990610449675082696981 := by
  unfold tailWord_1428445
  simp only [CollatzResearch.WordTrace]
  refine ⟨52099669309995198828542789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34733112873330132552361859 52099669309995198828542789)
  ·
    refine ⟨9768687995624099780351773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52099669309995198828542789 9768687995624099780351773)
    ·
      refine ⟨3663257998359037417631915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9768687995624099780351773 3663257998359037417631915)
      ·
        refine ⟨5494886997538556126447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663257998359037417631915 5494886997538556126447873)
        ·
          refine ⟨4121165248153917094835905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5494886997538556126447873 4121165248153917094835905)
          ·
            refine ⟨3090873936115437821126929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121165248153917094835905 3090873936115437821126929)
            ·
              refine ⟨2318155452086578365845197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090873936115437821126929 2318155452086578365845197)
              ·
                refine ⟨869308294532466887191949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318155452086578365845197 869308294532466887191949)
                ·
                  refine ⟨325990610449675082696981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869308294532466887191949 325990610449675082696981)
                  ·
                    rfl

theorem cell21_1428445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1428445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428445 prefixEnd_1428445 := by exact prefixLift 1428445
  have htrace : WordTrace (prefixWord ++ tailWord_1428445) baseStart_1428445 baseEnd_1428445 := by
    simpa [prefixWord, tailWord_1428445, baseEnd_1428445] using wordTrace_append hprefix tailTrace_1428445
  have hstable : (prefixWord ++ tailWord_1428445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428445).length < 2 ^ (prefixWord ++ tailWord_1428445).sum := by decide
  have hdescent : baseEnd_1428445 < baseStart_1428445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428501 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1428501 : Nat := 118140960795 + 1428501 * 2 ^ 59
def prefixEnd_1428501 : Nat := 4983230072969 + 3 ^ 40 * 1428501 * 2
def baseEnd_1428501 : Nat := 326003390412631429763533

theorem tailTrace_1428501 : CollatzResearch.WordTrace tailWord_1428501 prefixEnd_1428501 326003390412631429763533 := by
  unfold tailWord_1428501
  simp only [CollatzResearch.WordTrace]
  refine ⟨52101711797792320392581357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34734474531861546928387571 52101711797792320392581357)
  ·
    refine ⟨19538141924172120147218009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52101711797792320392581357 19538141924172120147218009)
    ·
      refine ⟨14653606443129090110413507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19538141924172120147218009 14653606443129090110413507)
      ·
        refine ⟨21980409664693635165620261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653606443129090110413507 21980409664693635165620261)
        ·
          refine ⟨4121326812130056593553799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21980409664693635165620261 4121326812130056593553799)
          ·
            refine ⟨6181990218195084890330699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121326812130056593553799 6181990218195084890330699)
            ·
              refine ⟨9272985327292627335496049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181990218195084890330699 9272985327292627335496049)
              ·
                refine ⟨6954738995469470501622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9272985327292627335496049 6954738995469470501622037)
                ·
                  refine ⟨326003390412631429763533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6954738995469470501622037 326003390412631429763533)
                  ·
                    rfl

theorem cell21_1428501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1428501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428501 prefixEnd_1428501 := by exact prefixLift 1428501
  have htrace : WordTrace (prefixWord ++ tailWord_1428501) baseStart_1428501 baseEnd_1428501 := by
    simpa [prefixWord, tailWord_1428501, baseEnd_1428501] using wordTrace_append hprefix tailTrace_1428501
  have hstable : (prefixWord ++ tailWord_1428501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428501).length < 2 ^ (prefixWord ++ tailWord_1428501).sum := by decide
  have hdescent : baseEnd_1428501 < baseStart_1428501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428504 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_1428504 : Nat := 118140960795 + 1428504 * 2 ^ 59
def prefixEnd_1428504 : Nat := 4983230072969 + 3 ^ 40 * 1428504 * 2
def baseEnd_1428504 : Nat := 326004075053504091213527

theorem tailTrace_1428504 : CollatzResearch.WordTrace tailWord_1428504 prefixEnd_1428504 326004075053504091213527 := by
  unfold tailWord_1428504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26050910608390725952470283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34734547477854301269960377 26050910608390725952470283)
  ·
    refine ⟨39076365912586088928705425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26050910608390725952470283 39076365912586088928705425)
    ·
      refine ⟨29307274434439566696529069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39076365912586088928705425 29307274434439566696529069)
      ·
        refine ⟨10990227912914837511198401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29307274434439566696529069 10990227912914837511198401)
        ·
          refine ⟨8242670934686128133398801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990227912914837511198401 8242670934686128133398801)
          ·
            refine ⟨6182003201014596100049101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8242670934686128133398801 6182003201014596100049101)
            ·
              refine ⟨2318251200380473537518413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6182003201014596100049101 2318251200380473537518413)
              ·
                refine ⟨869344200142677576569405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318251200380473537518413 869344200142677576569405)
                ·
                  refine ⟨326004075053504091213527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869344200142677576569405 326004075053504091213527)
                  ·
                    rfl

theorem cell21_1428504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_1428504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428504 prefixEnd_1428504 := by exact prefixLift 1428504
  have htrace : WordTrace (prefixWord ++ tailWord_1428504) baseStart_1428504 baseEnd_1428504 := by
    simpa [prefixWord, tailWord_1428504, baseEnd_1428504] using wordTrace_append hprefix tailTrace_1428504
  have hstable : (prefixWord ++ tailWord_1428504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428504).length < 2 ^ (prefixWord ++ tailWord_1428504).sum := by decide
  have hdescent : baseEnd_1428504 < baseStart_1428504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428515 : List Nat := [1, 1, 1, 4, 3, 2, 9]
def baseStart_1428515 : Nat := 118140960795 + 1428515 * 2 ^ 59
def prefixEnd_1428515 : Nat := 4983230072969 + 3 ^ 40 * 1428515 * 2
def baseEnd_1428515 : Nat := 36222953933707835170019

theorem tailTrace_1428515 : CollatzResearch.WordTrace tailWord_1428515 prefixEnd_1428515 36222953933707835170019 := by
  unfold tailWord_1428515
  simp only [CollatzResearch.WordTrace]
  refine ⟨52102222419741600783590999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34734814946494400522393999 52102222419741600783590999)
  ·
    refine ⟨78153333629612401175386499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52102222419741600783590999 78153333629612401175386499)
    ·
      refine ⟨117230000444418601763079749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78153333629612401175386499 117230000444418601763079749)
      ·
        refine ⟨21980625083328487830577453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117230000444418601763079749 21980625083328487830577453)
        ·
          refine ⟨8242734406248182936466545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21980625083328487830577453 8242734406248182936466545)
          ·
            refine ⟨6182050804686137202349909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8242734406248182936466545 6182050804686137202349909)
            ·
              refine ⟨36222953933707835170019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6182050804686137202349909 36222953933707835170019)
              ·
                rfl

theorem cell21_1428515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_1428515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428515 prefixEnd_1428515 := by exact prefixLift 1428515
  have htrace : WordTrace (prefixWord ++ tailWord_1428515) baseStart_1428515 baseEnd_1428515 := by
    simpa [prefixWord, tailWord_1428515, baseEnd_1428515] using wordTrace_append hprefix tailTrace_1428515
  have hstable : (prefixWord ++ tailWord_1428515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428515).length < 2 ^ (prefixWord ++ tailWord_1428515).sum := by decide
  have hdescent : baseEnd_1428515 < baseStart_1428515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428560 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_1428560 : Nat := 118140960795 + 1428560 * 2 ^ 59
def prefixEnd_1428560 : Nat := 4983230072969 + 3 ^ 40 * 1428560 * 2
def baseEnd_1428560 : Nat := 326016855016460438280079

theorem tailTrace_1428560 : CollatzResearch.WordTrace tailWord_1428560 prefixEnd_1428560 326016855016460438280079 := by
  unfold tailWord_1428560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051931852289286734489567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34735909136385715645986089 26051931852289286734489567)
  ·
    refine ⟨39077897778433930101734351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26051931852289286734489567 39077897778433930101734351)
    ·
      refine ⟨58616846667650895152601527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39077897778433930101734351 58616846667650895152601527)
      ·
        refine ⟨87925270001476342728902291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58616846667650895152601527 87925270001476342728902291)
        ·
          refine ⟨131887905002214514093353437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87925270001476342728902291 131887905002214514093353437)
          ·
            refine ⟨49457964375830442785007539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131887905002214514093353437 49457964375830442785007539)
            ·
              refine ⟨74186946563745664177511309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49457964375830442785007539 74186946563745664177511309)
              ·
                refine ⟨27820104961404624066566741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74186946563745664177511309 27820104961404624066566741)
                ·
                  refine ⟨326016855016460438280079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27820104961404624066566741 326016855016460438280079)
                  ·
                    rfl

theorem cell21_1428560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_1428560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428560 prefixEnd_1428560 := by exact prefixLift 1428560
  have htrace : WordTrace (prefixWord ++ tailWord_1428560) baseStart_1428560 baseEnd_1428560 := by
    simpa [prefixWord, tailWord_1428560, baseEnd_1428560] using wordTrace_append hprefix tailTrace_1428560
  have hstable : (prefixWord ++ tailWord_1428560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428560).length < 2 ^ (prefixWord ++ tailWord_1428560).sum := by decide
  have hdescent : baseEnd_1428560 < baseStart_1428560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428566 : List Nat := [5, 2, 2, 1, 3, 8]
def baseStart_1428566 : Nat := 118140960795 + 1428566 * 2 ^ 59
def prefixEnd_1428566 : Nat := 4983230072969 + 3 ^ 40 * 1428566 * 2
def baseEnd_1428566 : Nat := 12074749048081694858521

theorem tailTrace_1428566 : CollatzResearch.WordTrace tailWord_1428566 prefixEnd_1428566 12074749048081694858521 := by
  unfold tailWord_1428566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256505158909802280856097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34736055028371224329131701 3256505158909802280856097)
  ·
    refine ⟨2442378869182351710642073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3256505158909802280856097 2442378869182351710642073)
    ·
      refine ⟨1831784151886763782981555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2442378869182351710642073 1831784151886763782981555)
      ·
        refine ⟨2747676227830145674472333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831784151886763782981555 2747676227830145674472333)
        ·
          refine ⟨1030378585436304627927125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2747676227830145674472333 1030378585436304627927125)
          ·
            refine ⟨12074749048081694858521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1030378585436304627927125 12074749048081694858521)
            ·
              rfl

theorem cell21_1428566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 8].length) (baseStart_1428566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428566 prefixEnd_1428566 := by exact prefixLift 1428566
  have htrace : WordTrace (prefixWord ++ tailWord_1428566) baseStart_1428566 baseEnd_1428566 := by
    simpa [prefixWord, tailWord_1428566, baseEnd_1428566] using wordTrace_append hprefix tailTrace_1428566
  have hstable : (prefixWord ++ tailWord_1428566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428566).length < 2 ^ (prefixWord ++ tailWord_1428566).sum := by decide
  have hdescent : baseEnd_1428566 < baseStart_1428566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428577 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_1428577 : Nat := 118140960795 + 1428577 * 2 ^ 59
def prefixEnd_1428577 : Nat := 4983230072969 + 3 ^ 40 * 1428577 * 2
def baseEnd_1428577 : Nat := 326020734648072186496711

theorem tailTrace_1428577 : CollatzResearch.WordTrace tailWord_1428577 prefixEnd_1428577 326020734648072186496711 := by
  unfold tailWord_1428577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52104483745516985372347985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34736322497011323581565323 52104483745516985372347985)
  ·
    refine ⟨39078362809137739029260989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52104483745516985372347985 39078362809137739029260989)
    ·
      refine ⟨14654386053426652135972871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39078362809137739029260989 14654386053426652135972871)
      ·
        refine ⟨21981579080139978203959307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14654386053426652135972871 21981579080139978203959307)
        ·
          refine ⟨32972368620209967305938961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21981579080139978203959307 32972368620209967305938961)
          ·
            refine ⟨24729276465157475479454221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32972368620209967305938961 24729276465157475479454221)
            ·
              refine ⟨9273478674434053304795333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24729276465157475479454221 9273478674434053304795333)
              ·
                refine ⟨1738777251456384994649125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9273478674434053304795333 1738777251456384994649125)
                ·
                  refine ⟨326020734648072186496711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1738777251456384994649125 326020734648072186496711)
                  ·
                    rfl

theorem cell21_1428577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_1428577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428577 prefixEnd_1428577 := by exact prefixLift 1428577
  have htrace : WordTrace (prefixWord ++ tailWord_1428577) baseStart_1428577 baseEnd_1428577 := by
    simpa [prefixWord, tailWord_1428577, baseEnd_1428577] using wordTrace_append hprefix tailTrace_1428577
  have hstable : (prefixWord ++ tailWord_1428577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428577).length < 2 ^ (prefixWord ++ tailWord_1428577).sum := by decide
  have hdescent : baseEnd_1428577 < baseStart_1428577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428673 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 3]
def baseStart_1428673 : Nat := 118140960795 + 1428673 * 2 ^ 59
def prefixEnd_1428673 : Nat := 4983230072969 + 3 ^ 40 * 1428673 * 2
def baseEnd_1428673 : Nat := 326042643155997352896515

theorem tailTrace_1428673 : CollatzResearch.WordTrace tailWord_1428673 prefixEnd_1428673 326042643155997352896515 := by
  unfold tailWord_1428673
  simp only [CollatzResearch.WordTrace]
  refine ⟨52107985153169193767842673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34738656768779462511895115 52107985153169193767842673)
  ·
    refine ⟨39080988864876895325882005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52107985153169193767842673 39080988864876895325882005)
    ·
      refine ⟨1831921353041104468400719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39080988864876895325882005 1831921353041104468400719)
      ·
        refine ⟨2747882029561656702601079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831921353041104468400719 2747882029561656702601079)
        ·
          refine ⟨4121823044342485053901619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747882029561656702601079 4121823044342485053901619)
          ·
            refine ⟨6182734566513727580852429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121823044342485053901619 6182734566513727580852429)
            ·
              refine ⟨2318525462442647842819661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6182734566513727580852429 2318525462442647842819661)
              ·
                refine ⟨869447048415992941057373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318525462442647842819661 869447048415992941057373)
                ·
                  refine ⟨326042643155997352896515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869447048415992941057373 326042643155997352896515)
                  ·
                    rfl

theorem cell21_1428673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_1428673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428673 prefixEnd_1428673 := by exact prefixLift 1428673
  have htrace : WordTrace (prefixWord ++ tailWord_1428673) baseStart_1428673 baseEnd_1428673 := by
    simpa [prefixWord, tailWord_1428673, baseEnd_1428673] using wordTrace_append hprefix tailTrace_1428673
  have hstable : (prefixWord ++ tailWord_1428673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428673).length < 2 ^ (prefixWord ++ tailWord_1428673).sum := by decide
  have hdescent : baseEnd_1428673 < baseStart_1428673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428701 : List Nat := [1, 4, 3, 2, 2, 1, 2, 6]
def baseStart_1428701 : Nat := 118140960795 + 1428701 * 2 ^ 59
def prefixEnd_1428701 : Nat := 4983230072969 + 3 ^ 40 * 1428701 * 2
def baseEnd_1428701 : Nat := 108683011045825175476597

theorem tailTrace_1428701 : CollatzResearch.WordTrace tailWord_1428701 prefixEnd_1428701 108683011045825175476597 := by
  unfold tailWord_1428701
  simp only [CollatzResearch.WordTrace]
  refine ⟨52109006397067754549861957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34739337598045169699907971 52109006397067754549861957)
  ·
    refine ⟨9770438699450203978099117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52109006397067754549861957 9770438699450203978099117)
    ·
      refine ⟨3663914512293826491787169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9770438699450203978099117 3663914512293826491787169)
      ·
        refine ⟨2747935884220369868840377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3663914512293826491787169 2747935884220369868840377)
        ·
          refine ⟨2060951913165277401630283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2747935884220369868840377 2060951913165277401630283)
          ·
            refine ⟨3091427869747916102445425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060951913165277401630283 3091427869747916102445425)
            ·
              refine ⟨2318570902310937076834069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091427869747916102445425 2318570902310937076834069)
              ·
                refine ⟨108683011045825175476597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2318570902310937076834069 108683011045825175476597)
                ·
                  rfl

theorem cell21_1428701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_1428701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428701 prefixEnd_1428701 := by exact prefixLift 1428701
  have htrace : WordTrace (prefixWord ++ tailWord_1428701) baseStart_1428701 baseEnd_1428701 := by
    simpa [prefixWord, tailWord_1428701, baseEnd_1428701] using wordTrace_append hprefix tailTrace_1428701
  have hstable : (prefixWord ++ tailWord_1428701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428701).length < 2 ^ (prefixWord ++ tailWord_1428701).sum := by decide
  have hdescent : baseEnd_1428701 < baseStart_1428701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428760 : List Nat := [2, 1, 2, 3, 1, 5, 1, 6]
def baseStart_1428760 : Nat := 118140960795 + 1428760 * 2 ^ 59
def prefixEnd_1428760 : Nat := 4983230072969 + 3 ^ 40 * 1428760 * 2
def baseEnd_1428760 : Nat := 108687499247101511648779

theorem tailTrace_1428760 : CollatzResearch.WordTrace tailWord_1428760 prefixEnd_1428760 108687499247101511648779 := by
  unfold tailWord_1428760
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055579151927003813129867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34740772202569338417506489 26055579151927003813129867)
  ·
    refine ⟨39083368727890505719694801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26055579151927003813129867 39083368727890505719694801)
    ·
      refine ⟨29312526545917879289771101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39083368727890505719694801 29312526545917879289771101)
      ·
        refine ⟨10992197454719204733664163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29312526545917879289771101 10992197454719204733664163)
        ·
          refine ⟨16488296182078807100496245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10992197454719204733664163 16488296182078807100496245)
          ·
            refine ⟨1545777767069888165671523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16488296182078807100496245 1545777767069888165671523)
            ·
              refine ⟨2318666650604832248507285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545777767069888165671523 2318666650604832248507285)
              ·
                refine ⟨108687499247101511648779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2318666650604832248507285 108687499247101511648779)
                ·
                  rfl

theorem cell21_1428760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_1428760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428760 prefixEnd_1428760 := by exact prefixLift 1428760
  have htrace : WordTrace (prefixWord ++ tailWord_1428760) baseStart_1428760 baseEnd_1428760 := by
    simpa [prefixWord, tailWord_1428760, baseEnd_1428760] using wordTrace_append hprefix tailTrace_1428760
  have hstable : (prefixWord ++ tailWord_1428760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428760).length < 2 ^ (prefixWord ++ tailWord_1428760).sum := by decide
  have hdescent : baseEnd_1428760 < baseStart_1428760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428836 : List Nat := [2, 3, 1, 1, 3, 2, 4, 5]
def baseStart_1428836 : Nat := 118140960795 + 1428836 * 2 ^ 59
def prefixEnd_1428836 : Nat := 4983230072969 + 3 ^ 40 * 1428836 * 2
def baseEnd_1428836 : Nat := 108693280658915097226505

theorem tailTrace_1428836 : CollatzResearch.WordTrace tailWord_1428836 prefixEnd_1428836 108693280658915097226505 := by
  unfold tailWord_1428836
  simp only [CollatzResearch.WordTrace]
  refine ⟨26056965125789336303013181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34742620167719115070684241 26056965125789336303013181)
  ·
    refine ⟨9771361922171001113629943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26056965125789336303013181 9771361922171001113629943)
    ·
      refine ⟨14657042883256501670444915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771361922171001113629943 14657042883256501670444915)
      ·
        refine ⟨21985564324884752505667373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657042883256501670444915 21985564324884752505667373)
        ·
          refine ⟨8244586621831782189625265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21985564324884752505667373 8244586621831782189625265)
          ·
            refine ⟨6183439966373836642218949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8244586621831782189625265 6183439966373836642218949)
            ·
              refine ⟨1159394993695094370416053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6183439966373836642218949 1159394993695094370416053)
              ·
                refine ⟨108693280658915097226505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159394993695094370416053 108693280658915097226505)
                ·
                  rfl

theorem cell21_1428836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_1428836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428836 prefixEnd_1428836 := by exact prefixLift 1428836
  have htrace : WordTrace (prefixWord ++ tailWord_1428836) baseStart_1428836 baseEnd_1428836 := by
    simpa [prefixWord, tailWord_1428836, baseEnd_1428836] using wordTrace_append hprefix tailTrace_1428836
  have hstable : (prefixWord ++ tailWord_1428836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428836).length < 2 ^ (prefixWord ++ tailWord_1428836).sum := by decide
  have hdescent : baseEnd_1428836 < baseStart_1428836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428842 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_1428842 : Nat := 118140960795 + 1428842 * 2 ^ 59
def prefixEnd_1428842 : Nat := 4983230072969 + 3 ^ 40 * 1428842 * 2
def baseEnd_1428842 : Nat := 326081211258490614579503

theorem tailTrace_1428842 : CollatzResearch.WordTrace tailWord_1428842 prefixEnd_1428842 326081211258490614579503 := by
  unfold tailWord_1428842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028537272389233907686195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34742766059704623753829853 13028537272389233907686195)
  ·
    refine ⟨19542805908583850861529293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13028537272389233907686195 19542805908583850861529293)
    ·
      refine ⟨7328552215718944073073485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19542805908583850861529293 7328552215718944073073485)
      ·
        refine ⟨2748207080894604027402557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7328552215718944073073485 2748207080894604027402557)
        ·
          refine ⟨1030577655335476510275959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2748207080894604027402557 1030577655335476510275959)
          ·
            refine ⟨1545866483003214765413939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030577655335476510275959 1545866483003214765413939)
            ·
              refine ⟨2318799724504822148120909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545866483003214765413939 2318799724504822148120909)
              ·
                refine ⟨869549896689308305545341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318799724504822148120909 869549896689308305545341)
                ·
                  refine ⟨326081211258490614579503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869549896689308305545341 326081211258490614579503)
                  ·
                    rfl

theorem cell21_1428842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_1428842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428842 prefixEnd_1428842 := by exact prefixLift 1428842
  have htrace : WordTrace (prefixWord ++ tailWord_1428842) baseStart_1428842 baseEnd_1428842 := by
    simpa [prefixWord, tailWord_1428842, baseEnd_1428842] using wordTrace_append hprefix tailTrace_1428842
  have hstable : (prefixWord ++ tailWord_1428842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428842).length < 2 ^ (prefixWord ++ tailWord_1428842).sum := by decide
  have hdescent : baseEnd_1428842 < baseStart_1428842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428853 : List Nat := [1, 3, 4, 1, 4, 1, 7]
def baseStart_1428853 : Nat := 118140960795 + 1428853 * 2 ^ 59
def prefixEnd_1428853 : Nat := 4983230072969 + 3 ^ 40 * 1428853 * 2
def baseEnd_1428853 : Nat := 36231524623150782210683

theorem tailTrace_1428853 : CollatzResearch.WordTrace tailWord_1428853 prefixEnd_1428853 36231524623150782210683 := by
  unfold tailWord_1428853
  simp only [CollatzResearch.WordTrace]
  refine ⟨52114550292517084509395213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34743033528344723006263475 52114550292517084509395213)
  ·
    refine ⟨19542956359693906691023205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52114550292517084509395213 19542956359693906691023205)
    ·
      refine ⟨3664304317442607504566851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19542956359693906691023205 3664304317442607504566851)
      ·
        refine ⟨5496456476163911256850277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664304317442607504566851 5496456476163911256850277)
        ·
          refine ⟨1030585589280733360659427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5496456476163911256850277 1030585589280733360659427)
          ·
            refine ⟨1545878383921100040989141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030585589280733360659427 1545878383921100040989141)
            ·
              refine ⟨36231524623150782210683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1545878383921100040989141 36231524623150782210683)
              ·
                rfl

theorem cell21_1428853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 7].length) (baseStart_1428853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428853 prefixEnd_1428853 := by exact prefixLift 1428853
  have htrace : WordTrace (prefixWord ++ tailWord_1428853) baseStart_1428853 baseEnd_1428853 := by
    simpa [prefixWord, tailWord_1428853, baseEnd_1428853] using wordTrace_append hprefix tailTrace_1428853
  have hstable : (prefixWord ++ tailWord_1428853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428853).length < 2 ^ (prefixWord ++ tailWord_1428853).sum := by decide
  have hdescent : baseEnd_1428853 < baseStart_1428853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428867 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_1428867 : Nat := 118140960795 + 1428867 * 2 ^ 59
def prefixEnd_1428867 : Nat := 4983230072969 + 3 ^ 40 * 1428867 * 2
def baseEnd_1428867 : Nat := 326086916599096126662785

theorem tailTrace_1428867 : CollatzResearch.WordTrace tailWord_1428867 prefixEnd_1428867 326086916599096126662785 := by
  unfold tailWord_1428867
  simp only [CollatzResearch.WordTrace]
  refine ⟨52115060914466364900404855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34743373942977576600269903 52115060914466364900404855)
  ·
    refine ⟨78172591371699547350607283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52115060914466364900404855 78172591371699547350607283)
    ·
      refine ⟨117258887057549321025910925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78172591371699547350607283 117258887057549321025910925)
      ·
        refine ⟨43972082646580995384716597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117258887057549321025910925 43972082646580995384716597)
        ·
          refine ⟨4122382748116968317317181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43972082646580995384716597 4122382748116968317317181)
          ·
            refine ⟨1545893530543863118993943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4122382748116968317317181 1545893530543863118993943)
            ·
              refine ⟨2318840295815794678490915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545893530543863118993943 2318840295815794678490915)
              ·
                refine ⟨3478260443723692017736373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318840295815794678490915 3478260443723692017736373)
                ·
                  refine ⟨326086916599096126662785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478260443723692017736373 326086916599096126662785)
                  ·
                    rfl

theorem cell21_1428867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_1428867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428867 prefixEnd_1428867 := by exact prefixLift 1428867
  have htrace : WordTrace (prefixWord ++ tailWord_1428867) baseStart_1428867 baseEnd_1428867 := by
    simpa [prefixWord, tailWord_1428867, baseEnd_1428867] using wordTrace_append hprefix tailTrace_1428867
  have hstable : (prefixWord ++ tailWord_1428867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428867).length < 2 ^ (prefixWord ++ tailWord_1428867).sum := by decide
  have hdescent : baseEnd_1428867 < baseStart_1428867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428895 : List Nat := [1, 1, 2, 5, 1, 2, 2, 7]
def baseStart_1428895 : Nat := 118140960795 + 1428895 * 2 ^ 59
def prefixEnd_1428895 : Nat := 4983230072969 + 3 ^ 40 * 1428895 * 2
def baseEnd_1428895 : Nat := 108697768860191433398687

theorem tailTrace_1428895 : CollatzResearch.WordTrace tailWord_1428895 prefixEnd_1428895 108697768860191433398687 := by
  unfold tailWord_1428895
  simp only [CollatzResearch.WordTrace]
  refine ⟨52116082158364925682424139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34744054772243283788282759 52116082158364925682424139)
  ·
    refine ⟨78174123237547388523636209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52116082158364925682424139 78174123237547388523636209)
    ·
      refine ⟨58630592428160541392727157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78174123237547388523636209 58630592428160541392727157)
      ·
        refine ⟨5496618040140050755568171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58630592428160541392727157 5496618040140050755568171)
        ·
          refine ⟨8244927060210076133352257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496618040140050755568171 8244927060210076133352257)
          ·
            refine ⟨6183695295157557100014193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8244927060210076133352257 6183695295157557100014193)
            ·
              refine ⟨4637771471368167825010645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183695295157557100014193 4637771471368167825010645)
              ·
                refine ⟨108697768860191433398687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4637771471368167825010645 108697768860191433398687)
                ·
                  rfl

theorem cell21_1428895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_1428895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428895 prefixEnd_1428895 := by exact prefixLift 1428895
  have htrace : WordTrace (prefixWord ++ tailWord_1428895) baseStart_1428895 baseEnd_1428895 := by
    simpa [prefixWord, tailWord_1428895, baseEnd_1428895] using wordTrace_append hprefix tailTrace_1428895
  have hstable : (prefixWord ++ tailWord_1428895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428895).length < 2 ^ (prefixWord ++ tailWord_1428895).sum := by decide
  have hdescent : baseEnd_1428895 < baseStart_1428895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1428926 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1428926 : Nat := 118140960795 + 1428926 * 2 ^ 59
def prefixEnd_1428926 : Nat := 4983230072969 + 3 ^ 40 * 1428926 * 2
def baseEnd_1428926 : Nat := 326100381202925135179331

theorem tailTrace_1428926 : CollatzResearch.WordTrace tailWord_1428926 prefixEnd_1428926 326100381202925135179331 := by
  unfold tailWord_1428926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514651602656577247100329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34744808547501745317868421 6514651602656577247100329)
  ·
    refine ⟨4885988701992432935325247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6514651602656577247100329 4885988701992432935325247)
    ·
      refine ⟨7328983052988649402987871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885988701992432935325247 7328983052988649402987871)
      ·
        refine ⟨10993474579482974104481807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7328983052988649402987871 10993474579482974104481807)
        ·
          refine ⟨16490211869224461156722711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10993474579482974104481807 16490211869224461156722711)
          ·
            refine ⟨24735317803836691735084067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16490211869224461156722711 24735317803836691735084067)
            ·
              refine ⟨37102976705755037602626101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24735317803836691735084067 37102976705755037602626101)
              ·
                refine ⟨3478404066164534775246197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37102976705755037602626101 3478404066164534775246197)
                ·
                  refine ⟨326100381202925135179331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478404066164534775246197 326100381202925135179331)
                  ·
                    rfl

theorem cell21_1428926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1428926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1428926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1428926 prefixEnd_1428926 := by exact prefixLift 1428926
  have htrace : WordTrace (prefixWord ++ tailWord_1428926) baseStart_1428926 baseEnd_1428926 := by
    simpa [prefixWord, tailWord_1428926, baseEnd_1428926] using wordTrace_append hprefix tailTrace_1428926
  have hstable : (prefixWord ++ tailWord_1428926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1428926).length < 2 ^ (prefixWord ++ tailWord_1428926).sum := by decide
  have hdescent : baseEnd_1428926 < baseStart_1428926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1428926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429002 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1429002 : Nat := 118140960795 + 1429002 * 2 ^ 59
def prefixEnd_1429002 : Nat := 4983230072969 + 3 ^ 40 * 1429002 * 2
def baseEnd_1429002 : Nat := 326117725438365891912509

theorem tailTrace_1429002 : CollatzResearch.WordTrace tailWord_1429002 prefixEnd_1429002 326117725438365891912509 := by
  unfold tailWord_1429002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029996192244320739142315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34746656512651521971046173 13029996192244320739142315)
  ·
    refine ⟨19544994288366481108713473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13029996192244320739142315 19544994288366481108713473)
    ·
      refine ⟨14658745716274860831535105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19544994288366481108713473 14658745716274860831535105)
      ·
        refine ⟨10994059287206145623651329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14658745716274860831535105 10994059287206145623651329)
        ·
          refine ⟨8245544465404609217738497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10994059287206145623651329 8245544465404609217738497)
          ·
            refine ⟨6184158349053456913303873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8245544465404609217738497 6184158349053456913303873)
            ·
              refine ⟨4638118761790092684977905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184158349053456913303873 4638118761790092684977905)
              ·
                refine ⟨3478589071342569513733429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638118761790092684977905 3478589071342569513733429)
                ·
                  refine ⟨326117725438365891912509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478589071342569513733429 326117725438365891912509)
                  ·
                    rfl

theorem cell21_1429002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1429002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429002 prefixEnd_1429002 := by exact prefixLift 1429002
  have htrace : WordTrace (prefixWord ++ tailWord_1429002) baseStart_1429002 baseEnd_1429002 := by
    simpa [prefixWord, tailWord_1429002, baseEnd_1429002] using wordTrace_append hprefix tailTrace_1429002
  have hstable : (prefixWord ++ tailWord_1429002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429002).length < 2 ^ (prefixWord ++ tailWord_1429002).sum := by decide
  have hdescent : baseEnd_1429002 < baseStart_1429002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429047 : List Nat := [1, 1, 3, 1, 2, 5, 2, 6]
def baseStart_1429047 : Nat := 118140960795 + 1429047 * 2 ^ 59
def prefixEnd_1429047 : Nat := 4983230072969 + 3 ^ 40 * 1429047 * 2
def baseEnd_1429047 : Nat := 108709331683818604554139

theorem tailTrace_1429047 : CollatzResearch.WordTrace tailWord_1429047 prefixEnd_1429047 108709331683818604554139 := by
  unfold tailWord_1429047
  simp only [CollatzResearch.WordTrace]
  refine ⟨52121626053814255641957395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34747750702542837094638263 52121626053814255641957395)
  ·
    refine ⟨78182439080721383462936093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52121626053814255641957395 78182439080721383462936093)
    ·
      refine ⟨29318414655270518798601035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78182439080721383462936093 29318414655270518798601035)
      ·
        refine ⟨43977621982905778197901553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29318414655270518798601035 43977621982905778197901553)
        ·
          refine ⟨32983216487179333648426165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43977621982905778197901553 32983216487179333648426165)
          ·
            refine ⟨3092176545673062529539953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32983216487179333648426165 3092176545673062529539953)
            ·
              refine ⟨2319132409254796897154965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092176545673062529539953 2319132409254796897154965)
              ·
                refine ⟨108709331683818604554139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2319132409254796897154965 108709331683818604554139)
                ·
                  rfl

theorem cell21_1429047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_1429047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429047 prefixEnd_1429047 := by exact prefixLift 1429047
  have htrace : WordTrace (prefixWord ++ tailWord_1429047) baseStart_1429047 baseEnd_1429047 := by
    simpa [prefixWord, tailWord_1429047, baseEnd_1429047] using wordTrace_append hprefix tailTrace_1429047
  have hstable : (prefixWord ++ tailWord_1429047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429047).length < 2 ^ (prefixWord ++ tailWord_1429047).sum := by decide
  have hdescent : baseEnd_1429047 < baseStart_1429047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429061 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1429061 : Nat := 118140960795 + 1429061 * 2 ^ 59
def prefixEnd_1429061 : Nat := 4983230072969 + 3 ^ 40 * 1429061 * 2
def baseEnd_1429061 : Nat := 326131190042194900429055

theorem tailTrace_1429061 : CollatzResearch.WordTrace tailWord_1429061 prefixEnd_1429061 326131190042194900429055 := by
  unfold tailWord_1429061
  simp only [CollatzResearch.WordTrace]
  refine ⟨52122136675763536032967037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34748091117175690688644691 52122136675763536032967037)
  ·
    refine ⟨19545801253411326012362639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52122136675763536032967037 19545801253411326012362639)
    ·
      refine ⟨29318701880116989018543959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19545801253411326012362639 29318701880116989018543959)
      ·
        refine ⟨43978052820175483527815939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29318701880116989018543959 43978052820175483527815939)
        ·
          refine ⟨65967079230263225291723909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43978052820175483527815939 65967079230263225291723909)
          ·
            refine ⟨12368827355674354742198233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65967079230263225291723909 12368827355674354742198233)
            ·
              refine ⟨9276620516755766056648675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12368827355674354742198233 9276620516755766056648675)
              ·
                refine ⟨13914930775133649084973013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276620516755766056648675 13914930775133649084973013)
                ·
                  refine ⟨326131190042194900429055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13914930775133649084973013 326131190042194900429055)
                  ·
                    rfl

theorem cell21_1429061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1429061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429061 prefixEnd_1429061 := by exact prefixLift 1429061
  have htrace : WordTrace (prefixWord ++ tailWord_1429061) baseStart_1429061 baseEnd_1429061 := by
    simpa [prefixWord, tailWord_1429061, baseEnd_1429061] using wordTrace_append hprefix tailTrace_1429061
  have hstable : (prefixWord ++ tailWord_1429061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429061).length < 2 ^ (prefixWord ++ tailWord_1429061).sum := by decide
  have hdescent : baseEnd_1429061 < baseStart_1429061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429140 : List Nat := [2, 4, 2, 2, 2, 1, 8]
def baseStart_1429140 : Nat := 118140960795 + 1429140 * 2 ^ 59
def prefixEnd_1429140 : Nat := 4983230072969 + 3 ^ 40 * 1429140 * 2
def baseEnd_1429140 : Nat := 36238802102056479845803

theorem tailTrace_1429140 : CollatzResearch.WordTrace tailWord_1429140 prefixEnd_1429140 36238802102056479845803 := by
  unfold tailWord_1429140
  simp only [CollatzResearch.WordTrace]
  refine ⟨26062509021238666262546437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34750012028318221683395249 26062509021238666262546437)
  ·
    refine ⟨4886720441482249924227457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26062509021238666262546437 4886720441482249924227457)
    ·
      refine ⟨3665040331111687443170593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4886720441482249924227457 3665040331111687443170593)
      ·
        refine ⟨2748780248333765582377945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665040331111687443170593 2748780248333765582377945)
        ·
          refine ⟨2061585186250324186783459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748780248333765582377945 2061585186250324186783459)
          ·
            refine ⟨3092377779375486280175189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061585186250324186783459 3092377779375486280175189)
            ·
              refine ⟨36238802102056479845803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3092377779375486280175189 36238802102056479845803)
              ·
                rfl

theorem cell21_1429140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 8].length) (baseStart_1429140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429140 prefixEnd_1429140 := by exact prefixLift 1429140
  have htrace : WordTrace (prefixWord ++ tailWord_1429140) baseStart_1429140 baseEnd_1429140 := by
    simpa [prefixWord, tailWord_1429140, baseEnd_1429140] using wordTrace_append hprefix tailTrace_1429140
  have hstable : (prefixWord ++ tailWord_1429140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429140).length < 2 ^ (prefixWord ++ tailWord_1429140).sum := by decide
  have hdescent : baseEnd_1429140 < baseStart_1429140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429168 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_1429168 : Nat := 118140960795 + 1429168 * 2 ^ 59
def prefixEnd_1429168 : Nat := 4983230072969 + 3 ^ 40 * 1429168 * 2
def baseEnd_1429168 : Nat := 326155608899986492145503

theorem tailTrace_1429168 : CollatzResearch.WordTrace tailWord_1429168 prefixEnd_1429168 326155608899986492145503 := by
  unfold tailWord_1429168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063019643187946653556079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34750692857583928871408105 26063019643187946653556079)
  ·
    refine ⟨39094529464781919980334119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26063019643187946653556079 39094529464781919980334119)
    ·
      refine ⟨58641794197172879970501179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39094529464781919980334119 58641794197172879970501179)
      ·
        refine ⟨87962691295759319955751769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58641794197172879970501179 87962691295759319955751769)
        ·
          refine ⟨65972018471819489966813827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87962691295759319955751769 65972018471819489966813827)
          ·
            refine ⟨98958027707729234950220741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65972018471819489966813827 98958027707729234950220741)
            ·
              refine ⟨18554630195199231553166389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98958027707729234950220741 18554630195199231553166389)
              ·
                refine ⟨1739496580799927958109349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18554630195199231553166389 1739496580799927958109349)
                ·
                  refine ⟨326155608899986492145503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739496580799927958109349 326155608899986492145503)
                  ·
                    rfl

theorem cell21_1429168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_1429168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429168 prefixEnd_1429168 := by exact prefixLift 1429168
  have htrace : WordTrace (prefixWord ++ tailWord_1429168) baseStart_1429168 baseEnd_1429168 := by
    simpa [prefixWord, tailWord_1429168, baseEnd_1429168] using wordTrace_append hprefix tailTrace_1429168
  have hstable : (prefixWord ++ tailWord_1429168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429168).length < 2 ^ (prefixWord ++ tailWord_1429168).sum := by decide
  have hdescent : baseEnd_1429168 < baseStart_1429168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429174 : List Nat := [5, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1429174 : Nat := 118140960795 + 1429174 * 2 ^ 59
def prefixEnd_1429174 : Nat := 4983230072969 + 3 ^ 40 * 1429174 * 2
def baseEnd_1429174 : Nat := 108718992727243938348497

theorem tailTrace_1429174 : CollatzResearch.WordTrace tailWord_1429174 prefixEnd_1429174 108718992727243938348497 := by
  unfold tailWord_1429174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257891132772134770739411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34750838749569437554553717 3257891132772134770739411)
  ·
    refine ⟨4886836699158202156109117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257891132772134770739411 4886836699158202156109117)
    ·
      refine ⟨1832563762184325808540919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4886836699158202156109117 1832563762184325808540919)
      ·
        refine ⟨2748845643276488712811379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832563762184325808540919 2748845643276488712811379)
        ·
          refine ⟨4123268464914733069217069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748845643276488712811379 4123268464914733069217069)
          ·
            refine ⟨1546225674343024900956401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4123268464914733069217069 1546225674343024900956401)
            ·
              refine ⟨1159669255757268675717301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546225674343024900956401 1159669255757268675717301)
              ·
                refine ⟨108718992727243938348497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159669255757268675717301 108718992727243938348497)
                ·
                  rfl

theorem cell21_1429174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1429174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429174 prefixEnd_1429174 := by exact prefixLift 1429174
  have htrace : WordTrace (prefixWord ++ tailWord_1429174) baseStart_1429174 baseEnd_1429174 := by
    simpa [prefixWord, tailWord_1429174, baseEnd_1429174] using wordTrace_append hprefix tailTrace_1429174
  have hstable : (prefixWord ++ tailWord_1429174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429174).length < 2 ^ (prefixWord ++ tailWord_1429174).sum := by decide
  have hdescent : baseEnd_1429174 < baseStart_1429174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429219 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 4]
def baseStart_1429219 : Nat := 118140960795 + 1429219 * 2 ^ 59
def prefixEnd_1429219 : Nat := 4983230072969 + 3 ^ 40 * 1429219 * 2
def baseEnd_1429219 : Nat := 326167247794821736795399

theorem tailTrace_1429219 : CollatzResearch.WordTrace tailWord_1429219 prefixEnd_1429219 326167247794821736795399 := by
  unfold tailWord_1429219
  simp only [CollatzResearch.WordTrace]
  refine ⟨52127899409191129017218711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34751932939460752678145807 52127899409191129017218711)
  ·
    refine ⟨78191849113786693525828067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52127899409191129017218711 78191849113786693525828067)
    ·
      refine ⟨117287773670680040288742101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78191849113786693525828067 117287773670680040288742101)
      ·
        refine ⟨2748932195406563444267393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 117287773670680040288742101 2748932195406563444267393)
        ·
          refine ⟨2061699146554922583200545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748932195406563444267393 2061699146554922583200545)
          ·
            refine ⟨1546274359916191937400409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061699146554922583200545 1546274359916191937400409)
            ·
              refine ⟨1159705769937143953050307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546274359916191937400409 1159705769937143953050307)
              ·
                refine ⟨1739558654905715929575461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159705769937143953050307 1739558654905715929575461)
                ·
                  refine ⟨326167247794821736795399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739558654905715929575461 326167247794821736795399)
                  ·
                    rfl

theorem cell21_1429219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_1429219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429219 prefixEnd_1429219 := by exact prefixLift 1429219
  have htrace : WordTrace (prefixWord ++ tailWord_1429219) baseStart_1429219 baseEnd_1429219 := by
    simpa [prefixWord, tailWord_1429219, baseEnd_1429219] using wordTrace_append hprefix tailTrace_1429219
  have hstable : (prefixWord ++ tailWord_1429219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429219).length < 2 ^ (prefixWord ++ tailWord_1429219).sum := by decide
  have hdescent : baseEnd_1429219 < baseStart_1429219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429258 : List Nat := [3, 1, 2, 2, 1, 12]
def baseStart_1429258 : Nat := 118140960795 + 1429258 * 2 ^ 59
def prefixEnd_1429258 : Nat := 4983230072969 + 3 ^ 40 * 1429258 * 2
def baseEnd_1429258 : Nat := 12080598078746901320197

theorem tailTrace_1429258 : CollatzResearch.WordTrace tailWord_1429258 prefixEnd_1429258 12080598078746901320197 := by
  unfold tailWord_1429258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032330464012459669472107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34752881237366559118592285 13032330464012459669472107)
  ·
    refine ⟨19548495696018689504208161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032330464012459669472107 19548495696018689504208161)
    ·
      refine ⟨14661371772014017128156121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19548495696018689504208161 14661371772014017128156121)
      ·
        refine ⟨10996028829010512846117091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14661371772014017128156121 10996028829010512846117091)
        ·
          refine ⟨16494043243515769269175637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10996028829010512846117091 16494043243515769269175637)
          ·
            refine ⟨12080598078746901320197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16494043243515769269175637 12080598078746901320197)
            ·
              rfl

theorem cell21_1429258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 12].length) (baseStart_1429258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429258 prefixEnd_1429258 := by exact prefixLift 1429258
  have htrace : WordTrace (prefixWord ++ tailWord_1429258) baseStart_1429258 baseEnd_1429258 := by
    simpa [prefixWord, tailWord_1429258, baseEnd_1429258] using wordTrace_append hprefix tailTrace_1429258
  have hstable : (prefixWord ++ tailWord_1429258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429258).length < 2 ^ (prefixWord ++ tailWord_1429258).sum := by decide
  have hdescent : baseEnd_1429258 < baseStart_1429258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429320 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1429320 : Nat := 118140960795 + 1429320 * 2 ^ 59
def prefixEnd_1429320 : Nat := 4983230072969 + 3 ^ 40 * 1429320 * 2
def baseEnd_1429320 : Nat := 326190297370868005611859

theorem tailTrace_1429320 : CollatzResearch.WordTrace tailWord_1429320 prefixEnd_1429320 326190297370868005611859 := by
  unfold tailWord_1429320
  simp only [CollatzResearch.WordTrace]
  refine ⟨26065791590912611633322707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34754388787883482177763609 26065791590912611633322707)
  ·
    refine ⟨39098687386368917449984061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26065791590912611633322707 39098687386368917449984061)
    ·
      refine ⟨14662007769888344043744023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39098687386368917449984061 14662007769888344043744023)
      ·
        refine ⟨21993011654832516065616035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14662007769888344043744023 21993011654832516065616035)
        ·
          refine ⟨32989517482248774098424053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21993011654832516065616035 32989517482248774098424053)
          ·
            refine ⟨3092767263960822571727255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32989517482248774098424053 3092767263960822571727255)
            ·
              refine ⟨4639150895941233857590883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092767263960822571727255 4639150895941233857590883)
              ·
                refine ⟨6958726343911850786386325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639150895941233857590883 6958726343911850786386325)
                ·
                  refine ⟨326190297370868005611859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6958726343911850786386325 326190297370868005611859)
                  ·
                    rfl

theorem cell21_1429320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1429320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429320 prefixEnd_1429320 := by exact prefixLift 1429320
  have htrace : WordTrace (prefixWord ++ tailWord_1429320) baseStart_1429320 baseEnd_1429320 := by
    simpa [prefixWord, tailWord_1429320, baseEnd_1429320] using wordTrace_append hprefix tailTrace_1429320
  have hstable : (prefixWord ++ tailWord_1429320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429320).length < 2 ^ (prefixWord ++ tailWord_1429320).sum := by decide
  have hdescent : baseEnd_1429320 < baseStart_1429320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429337 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 4]
def baseStart_1429337 : Nat := 118140960795 + 1429337 * 2 ^ 59
def prefixEnd_1429337 : Nat := 4983230072969 + 3 ^ 40 * 1429337 * 2
def baseEnd_1429337 : Nat := 326194177002479753828491

theorem tailTrace_1429337 : CollatzResearch.WordTrace tailWord_1429337 prefixEnd_1429337 326194177002479753828491 := by
  unfold tailWord_1429337
  simp only [CollatzResearch.WordTrace]
  refine ⟨52132203222763635170014265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34754802148509090113342843 52132203222763635170014265)
  ·
    refine ⟨39099152417072726377510699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52132203222763635170014265 39099152417072726377510699)
    ·
      refine ⟨58648728625609089566266049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39099152417072726377510699 58648728625609089566266049)
      ·
        refine ⟨43986546469206817174699537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58648728625609089566266049 43986546469206817174699537)
        ·
          refine ⟨32989909851905112881024653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43986546469206817174699537 32989909851905112881024653)
          ·
            refine ⟨12371216194464417330384245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32989909851905112881024653 12371216194464417330384245)
            ·
              refine ⟨1159801518231039124723523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12371216194464417330384245 1159801518231039124723523)
              ·
                refine ⟨1739702277346558687085285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159801518231039124723523 1739702277346558687085285)
                ·
                  refine ⟨326194177002479753828491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1739702277346558687085285 326194177002479753828491)
                  ·
                    rfl

theorem cell21_1429337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_1429337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429337 prefixEnd_1429337 := by exact prefixLift 1429337
  have htrace : WordTrace (prefixWord ++ tailWord_1429337) baseStart_1429337 baseEnd_1429337 := by
    simpa [prefixWord, tailWord_1429337, baseEnd_1429337] using wordTrace_append hprefix tailTrace_1429337
  have hstable : (prefixWord ++ tailWord_1429337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429337).length < 2 ^ (prefixWord ++ tailWord_1429337).sum := by decide
  have hdescent : baseEnd_1429337 < baseStart_1429337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429475 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 3]
def baseStart_1429475 : Nat := 118140960795 + 1429475 * 2 ^ 59
def prefixEnd_1429475 : Nat := 4983230072969 + 3 ^ 40 * 1429475 * 2
def baseEnd_1429475 : Nat := 326225670482622180528209

theorem tailTrace_1429475 : CollatzResearch.WordTrace tailWord_1429475 prefixEnd_1429475 326225670482622180528209 := by
  unfold tailWord_1429475
  simp only [CollatzResearch.WordTrace]
  refine ⟨52137236496263684738537879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34758157664175789825691919 52137236496263684738537879)
  ·
    refine ⟨78205854744395527107806819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52137236496263684738537879 78205854744395527107806819)
    ·
      refine ⟨117308782116593290661710229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78205854744395527107806819 117308782116593290661710229)
      ·
        refine ⟨5498849161715310499767667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117308782116593290661710229 5498849161715310499767667)
        ·
          refine ⟨8248273742572965749651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498849161715310499767667 8248273742572965749651501)
          ·
            refine ⟨3093102653464862156119313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8248273742572965749651501 3093102653464862156119313)
            ·
              refine ⟨2319826990098646617089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093102653464862156119313 2319826990098646617089485)
              ·
                refine ⟨869935121286992481408557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319826990098646617089485 869935121286992481408557)
                ·
                  refine ⟨326225670482622180528209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 869935121286992481408557 326225670482622180528209)
                  ·
                    rfl

theorem cell21_1429475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 3].length) (baseStart_1429475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429475 prefixEnd_1429475 := by exact prefixLift 1429475
  have htrace : WordTrace (prefixWord ++ tailWord_1429475) baseStart_1429475 baseEnd_1429475 := by
    simpa [prefixWord, tailWord_1429475, baseEnd_1429475] using wordTrace_append hprefix tailTrace_1429475
  have hstable : (prefixWord ++ tailWord_1429475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429475).length < 2 ^ (prefixWord ++ tailWord_1429475).sum := by decide
  have hdescent : baseEnd_1429475 < baseStart_1429475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429602 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1429602 : Nat := 118140960795 + 1429602 * 2 ^ 59
def prefixEnd_1429602 : Nat := 4983230072969 + 3 ^ 40 * 1429602 * 2
def baseEnd_1429602 : Nat := 326254653612898181911283

theorem tailTrace_1429602 : CollatzResearch.WordTrace tailWord_1429602 prefixEnd_1429602 326254653612898181911283 := by
  unfold tailWord_1429602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035467141700896357102765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34761245711202390285607373 13035467141700896357102765)
  ·
    refine ⟨4888300178137836133913537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13035467141700896357102765 4888300178137836133913537)
    ·
      refine ⟨3666225133603377100435153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4888300178137836133913537 3666225133603377100435153)
      ·
        refine ⟨2749668850202532825326365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666225133603377100435153 2749668850202532825326365)
        ·
          refine ⟨1031125818825949809497387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2749668850202532825326365 1031125818825949809497387)
          ·
            refine ⟨1546688728238924714246081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031125818825949809497387 1546688728238924714246081)
            ·
              refine ⟨1160016546179193535684561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546688728238924714246081 1160016546179193535684561)
              ·
                refine ⟨870012409634395151763421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160016546179193535684561 870012409634395151763421)
                ·
                  refine ⟨326254653612898181911283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870012409634395151763421 326254653612898181911283)
                  ·
                    rfl

theorem cell21_1429602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1429602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429602 prefixEnd_1429602 := by exact prefixLift 1429602
  have htrace : WordTrace (prefixWord ++ tailWord_1429602) baseStart_1429602 baseEnd_1429602 := by
    simpa [prefixWord, tailWord_1429602, baseEnd_1429602] using wordTrace_append hprefix tailTrace_1429602
  have hstable : (prefixWord ++ tailWord_1429602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429602).length < 2 ^ (prefixWord ++ tailWord_1429602).sum := by decide
  have hdescent : baseEnd_1429602 < baseStart_1429602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429658 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_1429658 : Nat := 118140960795 + 1429658 * 2 ^ 59
def prefixEnd_1429658 : Nat := 4983230072969 + 3 ^ 40 * 1429658 * 2
def baseEnd_1429658 : Nat := 326267433575854528977835

theorem tailTrace_1429658 : CollatzResearch.WordTrace tailWord_1429658 prefixEnd_1429658 326267433575854528977835 := by
  unfold tailWord_1429658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035977763650176748112407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34762607369733804661633085 13035977763650176748112407)
  ·
    refine ⟨19553966645475265122168611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035977763650176748112407 19553966645475265122168611)
    ·
      refine ⟨29330949968212897683252917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553966645475265122168611 29330949968212897683252917)
      ·
        refine ⟨2749776559519959157804961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29330949968212897683252917 2749776559519959157804961)
        ·
          refine ⟨2062332419639969368353721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2749776559519959157804961 2062332419639969368353721)
          ·
            refine ⟨1546749314729977026265291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062332419639969368353721 1546749314729977026265291)
            ·
              refine ⟨2320123972094965539397937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546749314729977026265291 2320123972094965539397937)
              ·
                refine ⟨1740092979071224154548453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320123972094965539397937 1740092979071224154548453)
                ·
                  refine ⟨326267433575854528977835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740092979071224154548453 326267433575854528977835)
                  ·
                    rfl

theorem cell21_1429658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_1429658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429658 prefixEnd_1429658 := by exact prefixLift 1429658
  have htrace : WordTrace (prefixWord ++ tailWord_1429658) baseStart_1429658 baseEnd_1429658 := by
    simpa [prefixWord, tailWord_1429658, baseEnd_1429658] using wordTrace_append hprefix tailTrace_1429658
  have hstable : (prefixWord ++ tailWord_1429658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429658).length < 2 ^ (prefixWord ++ tailWord_1429658).sum := by decide
  have hdescent : baseEnd_1429658 < baseStart_1429658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429669 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1429669 : Nat := 118140960795 + 1429669 * 2 ^ 59
def prefixEnd_1429669 : Nat := 4983230072969 + 3 ^ 40 * 1429669 * 2
def baseEnd_1429669 : Nat := 326269943925720954294479

theorem tailTrace_1429669 : CollatzResearch.WordTrace tailWord_1429669 prefixEnd_1429669 326269943925720954294479 := by
  unfold tailWord_1429669
  simp only [CollatzResearch.WordTrace]
  refine ⟨52144312257560855871100061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34762874838373903914066707 52144312257560855871100061)
  ·
    refine ⟨19554117096585320951662523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52144312257560855871100061 19554117096585320951662523)
    ·
      refine ⟨29331175644877981427493785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19554117096585320951662523 29331175644877981427493785)
      ·
        refine ⟨21998381733658486070620339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29331175644877981427493785 21998381733658486070620339)
        ·
          refine ⟨32997572600487729105930509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21998381733658486070620339 32997572600487729105930509)
          ·
            refine ⟨12374089725182898414723941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32997572600487729105930509 12374089725182898414723941)
            ·
              refine ⟨2320141823471793452760739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12374089725182898414723941 2320141823471793452760739)
              ·
                refine ⟨3480212735207690179141109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320141823471793452760739 3480212735207690179141109)
                ·
                  refine ⟨326269943925720954294479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480212735207690179141109 326269943925720954294479)
                  ·
                    rfl

theorem cell21_1429669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1429669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429669 prefixEnd_1429669 := by exact prefixLift 1429669
  have htrace : WordTrace (prefixWord ++ tailWord_1429669) baseStart_1429669 baseEnd_1429669 := by
    simpa [prefixWord, tailWord_1429669, baseEnd_1429669] using wordTrace_append hprefix tailTrace_1429669
  have hstable : (prefixWord ++ tailWord_1429669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429669).length < 2 ^ (prefixWord ++ tailWord_1429669).sum := by decide
  have hdescent : baseEnd_1429669 < baseStart_1429669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429700 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1429700 : Nat := 118140960795 + 1429700 * 2 ^ 59
def prefixEnd_1429700 : Nat := 4983230072969 + 3 ^ 40 * 1429700 * 2
def baseEnd_1429700 : Nat := 326277018548071789277749

theorem tailTrace_1429700 : CollatzResearch.WordTrace tailWord_1429700 prefixEnd_1429700 326277018548071789277749 := by
  unfold tailWord_1429700
  simp only [CollatzResearch.WordTrace]
  refine ⟨26072721460224274082739277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34763628613632365443652369 26072721460224274082739277)
  ·
    refine ⟨9777270547584102781027229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26072721460224274082739277 9777270547584102781027229)
    ·
      refine ⟨3666476455344038542885211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9777270547584102781027229 3666476455344038542885211)
      ·
        refine ⟨5499714683016057814327817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666476455344038542885211 5499714683016057814327817)
        ·
          refine ⟨4124786012262043360745863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499714683016057814327817 4124786012262043360745863)
          ·
            refine ⟨6187179018393065041118795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124786012262043360745863 6187179018393065041118795)
            ·
              refine ⟨9280768527589597561678193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6187179018393065041118795 9280768527589597561678193)
              ·
                refine ⟨6960576395692198171258645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9280768527589597561678193 6960576395692198171258645)
                ·
                  refine ⟨326277018548071789277749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6960576395692198171258645 326277018548071789277749)
                  ·
                    rfl

theorem cell21_1429700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1429700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429700 prefixEnd_1429700 := by exact prefixLift 1429700
  have htrace : WordTrace (prefixWord ++ tailWord_1429700) baseStart_1429700 baseEnd_1429700 := by
    simpa [prefixWord, tailWord_1429700, baseEnd_1429700] using wordTrace_append hprefix tailTrace_1429700
  have hstable : (prefixWord ++ tailWord_1429700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429700).length < 2 ^ (prefixWord ++ tailWord_1429700).sum := by decide
  have hdescent : baseEnd_1429700 < baseStart_1429700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429714 : List Nat := [3, 2, 2, 2, 1, 2, 9]
def baseStart_1429714 : Nat := 118140960795 + 1429714 * 2 ^ 59
def prefixEnd_1429714 : Nat := 4983230072969 + 3 ^ 40 * 1429714 * 2
def baseEnd_1429714 : Nat := 36253357059867875116043

theorem tailTrace_1429714 : CollatzResearch.WordTrace tailWord_1429714 prefixEnd_1429714 36253357059867875116043 := by
  unfold tailWord_1429714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036488385599457139122049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34763969028265219037658797 13036488385599457139122049)
  ·
    refine ⟨9777366289199592854341537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13036488385599457139122049 9777366289199592854341537)
    ·
      refine ⟨7333024716899694640756153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9777366289199592854341537 7333024716899694640756153)
      ·
        refine ⟨5499768537674770980567115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7333024716899694640756153 5499768537674770980567115)
        ·
          refine ⟨8249652806512156470850673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499768537674770980567115 8249652806512156470850673)
          ·
            refine ⟨6187239604884117353138005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8249652806512156470850673 6187239604884117353138005)
            ·
              refine ⟨36253357059867875116043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6187239604884117353138005 36253357059867875116043)
              ·
                rfl

theorem cell21_1429714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 9].length) (baseStart_1429714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429714 prefixEnd_1429714 := by exact prefixLift 1429714
  have htrace : WordTrace (prefixWord ++ tailWord_1429714) baseStart_1429714 baseEnd_1429714 := by
    simpa [prefixWord, tailWord_1429714, baseEnd_1429714] using wordTrace_append hprefix tailTrace_1429714
  have hstable : (prefixWord ++ tailWord_1429714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429714).length < 2 ^ (prefixWord ++ tailWord_1429714).sum := by decide
  have hdescent : baseEnd_1429714 < baseStart_1429714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429804 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1429804 : Nat := 118140960795 + 1429804 * 2 ^ 59
def prefixEnd_1429804 : Nat := 4983230072969 + 3 ^ 40 * 1429804 * 2
def baseEnd_1429804 : Nat := 326300752764990719544203

theorem tailTrace_1429804 : CollatzResearch.WordTrace tailWord_1429804 prefixEnd_1429804 326300752764990719544203 := by
  unfold tailWord_1429804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074618056035886963632233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34766157408047849284842977 26074618056035886963632233)
  ·
    refine ⟨19555963542026915222724175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26074618056035886963632233 19555963542026915222724175)
    ·
      refine ⟨29333945313040372834086263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19555963542026915222724175 29333945313040372834086263)
      ·
        refine ⟨44000917969560559251129395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29333945313040372834086263 44000917969560559251129395)
        ·
          refine ⟨66001376954340838876694093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44000917969560559251129395 66001376954340838876694093)
          ·
            refine ⟨24750516357877814578760285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66001376954340838876694093 24750516357877814578760285)
            ·
              refine ⟨9281443634204180467035107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24750516357877814578760285 9281443634204180467035107)
              ·
                refine ⟨13922165451306270700552661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281443634204180467035107 13922165451306270700552661)
                ·
                  refine ⟨326300752764990719544203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13922165451306270700552661 326300752764990719544203)
                  ·
                    rfl

theorem cell21_1429804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1429804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429804 prefixEnd_1429804 := by exact prefixLift 1429804
  have htrace : WordTrace (prefixWord ++ tailWord_1429804) baseStart_1429804 baseEnd_1429804 := by
    simpa [prefixWord, tailWord_1429804, baseEnd_1429804] using wordTrace_append hprefix tailTrace_1429804
  have hstable : (prefixWord ++ tailWord_1429804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429804).length < 2 ^ (prefixWord ++ tailWord_1429804).sum := by decide
  have hdescent : baseEnd_1429804 < baseStart_1429804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429835 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_1429835 : Nat := 118140960795 + 1429835 * 2 ^ 59
def prefixEnd_1429835 : Nat := 4983230072969 + 3 ^ 40 * 1429835 * 2
def baseEnd_1429835 : Nat := 326307827387341554527473

theorem tailTrace_1429835 : CollatzResearch.WordTrace tailWord_1429835 prefixEnd_1429835 326307827387341554527473 := by
  unfold tailWord_1429835
  simp only [CollatzResearch.WordTrace]
  refine ⟨52150366774959466221642959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34766911183306310814428639 52150366774959466221642959)
  ·
    refine ⟨78225550162439199332464439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52150366774959466221642959 78225550162439199332464439)
    ·
      refine ⟨117338325243658798998696659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78225550162439199332464439 117338325243658798998696659)
      ·
        refine ⟨176007487865488198498044989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117338325243658798998696659 176007487865488198498044989)
        ·
          refine ⟨66002807949558074436766871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176007487865488198498044989 66002807949558074436766871)
          ·
            refine ⟨99004211924337111655150307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66002807949558074436766871 99004211924337111655150307)
            ·
              refine ⟨148506317886505667482725461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99004211924337111655150307 148506317886505667482725461)
              ·
                refine ⟨1740308412732488290813189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 148506317886505667482725461 1740308412732488290813189)
                ·
                  refine ⟨326307827387341554527473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740308412732488290813189 326307827387341554527473)
                  ·
                    rfl

theorem cell21_1429835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_1429835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429835 prefixEnd_1429835 := by exact prefixLift 1429835
  have htrace : WordTrace (prefixWord ++ tailWord_1429835) baseStart_1429835 baseEnd_1429835 := by
    simpa [prefixWord, tailWord_1429835, baseEnd_1429835] using wordTrace_append hprefix tailTrace_1429835
  have hstable : (prefixWord ++ tailWord_1429835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429835).length < 2 ^ (prefixWord ++ tailWord_1429835).sum := by decide
  have hdescent : baseEnd_1429835 < baseStart_1429835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429849 : List Nat := [1, 2, 1, 2, 2, 2, 1, 10]
def baseStart_1429849 : Nat := 118140960795 + 1429849 * 2 ^ 59
def prefixEnd_1429849 : Nat := 4983230072969 + 3 ^ 40 * 1429849 * 2
def baseEnd_1429849 : Nat := 108770340792693547098037

theorem tailTrace_1429849 : CollatzResearch.WordTrace tailWord_1429849 prefixEnd_1429849 108770340792693547098037 := by
  unfold tailWord_1429849
  simp only [CollatzResearch.WordTrace]
  refine ⟨52150877396908746612652601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34767251597939164408435067 52150877396908746612652601)
  ·
    refine ⟨39113158047681559959489451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52150877396908746612652601 39113158047681559959489451)
    ·
      refine ⟨58669737071522339939234177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39113158047681559959489451 58669737071522339939234177)
      ·
        refine ⟨44002302803641754954425633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58669737071522339939234177 44002302803641754954425633)
        ·
          refine ⟨33001727102731316215819225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44002302803641754954425633 33001727102731316215819225)
          ·
            refine ⟨24751295327048487161864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33001727102731316215819225 24751295327048487161864419)
            ·
              refine ⟨37126942990572730742796629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24751295327048487161864419 37126942990572730742796629)
              ·
                refine ⟨108770340792693547098037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37126942990572730742796629 108770340792693547098037)
                ·
                  rfl

theorem cell21_1429849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_1429849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429849 prefixEnd_1429849 := by exact prefixLift 1429849
  have htrace : WordTrace (prefixWord ++ tailWord_1429849) baseStart_1429849 baseEnd_1429849 := by
    simpa [prefixWord, tailWord_1429849, baseEnd_1429849] using wordTrace_append hprefix tailTrace_1429849
  have hstable : (prefixWord ++ tailWord_1429849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429849).length < 2 ^ (prefixWord ++ tailWord_1429849).sum := by decide
  have hdescent : baseEnd_1429849 < baseStart_1429849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429897 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_1429897 : Nat := 118140960795 + 1429897 * 2 ^ 59
def prefixEnd_1429897 : Nat := 4983230072969 + 3 ^ 40 * 1429897 * 2
def baseEnd_1429897 : Nat := 326321976632043224494013

theorem tailTrace_1429897 : CollatzResearch.WordTrace tailWord_1429897 prefixEnd_1429897 326321976632043224494013 := by
  unfold tailWord_1429897
  simp only [CollatzResearch.WordTrace]
  refine ⟨52152628100734850810399945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34768418733823233873599963 52152628100734850810399945)
  ·
    refine ⟨39114471075551138107799959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52152628100734850810399945 39114471075551138107799959)
    ·
      refine ⟨58671706613326707161699939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39114471075551138107799959 58671706613326707161699939)
      ·
        refine ⟨88007559919990060742549909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58671706613326707161699939 88007559919990060742549909)
        ·
          refine ⟨4125354371249534097307027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88007559919990060742549909 4125354371249534097307027)
          ·
            refine ⟨6188031556874301145960541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125354371249534097307027 6188031556874301145960541)
            ·
              refine ⟨2320511833827862929735203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6188031556874301145960541 2320511833827862929735203)
              ·
                refine ⟨3480767750741794394602805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320511833827862929735203 3480767750741794394602805)
                ·
                  refine ⟨326321976632043224494013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480767750741794394602805 326321976632043224494013)
                  ·
                    rfl

theorem cell21_1429897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_1429897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429897 prefixEnd_1429897 := by exact prefixLift 1429897
  have htrace : WordTrace (prefixWord ++ tailWord_1429897) baseStart_1429897 baseEnd_1429897 := by
    simpa [prefixWord, tailWord_1429897, baseEnd_1429897] using wordTrace_append hprefix tailTrace_1429897
  have hstable : (prefixWord ++ tailWord_1429897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429897).length < 2 ^ (prefixWord ++ tailWord_1429897).sum := by decide
  have hdescent : baseEnd_1429897 < baseStart_1429897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429925 : List Nat := [1, 3, 1, 2, 1, 1, 3, 9]
def baseStart_1429925 : Nat := 118140960795 + 1429925 * 2 ^ 59
def prefixEnd_1429925 : Nat := 4983230072969 + 3 ^ 40 * 1429925 * 2
def baseEnd_1429925 : Nat := 108776122204507132675763

theorem tailTrace_1429925 : CollatzResearch.WordTrace tailWord_1429925 prefixEnd_1429925 108776122204507132675763 := by
  unfold tailWord_1429925
  simp only [CollatzResearch.WordTrace]
  refine ⟨52153649344633411592419229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34769099563088941061612819 52153649344633411592419229)
  ·
    refine ⟨19557618504237529347157211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52153649344633411592419229 19557618504237529347157211)
    ·
      refine ⟨29336427756356294020735817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19557618504237529347157211 29336427756356294020735817)
      ·
        refine ⟨22002320817267220515551863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29336427756356294020735817 22002320817267220515551863)
        ·
          refine ⟨33003481225900830773327795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22002320817267220515551863 33003481225900830773327795)
          ·
            refine ⟨49505221838851246159991693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33003481225900830773327795 49505221838851246159991693)
            ·
              refine ⟨18564458189569217309996885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49505221838851246159991693 18564458189569217309996885)
              ·
                refine ⟨108776122204507132675763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18564458189569217309996885 108776122204507132675763)
                ·
                  rfl

theorem cell21_1429925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_1429925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429925 prefixEnd_1429925 := by exact prefixLift 1429925
  have htrace : WordTrace (prefixWord ++ tailWord_1429925) baseStart_1429925 baseEnd_1429925 := by
    simpa [prefixWord, tailWord_1429925, baseEnd_1429925] using wordTrace_append hprefix tailTrace_1429925
  have hstable : (prefixWord ++ tailWord_1429925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429925).length < 2 ^ (prefixWord ++ tailWord_1429925).sum := by decide
  have hdescent : baseEnd_1429925 < baseStart_1429925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429948 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1429948 : Nat := 118140960795 + 1429948 * 2 ^ 59
def prefixEnd_1429948 : Nat := 4983230072969 + 3 ^ 40 * 1429948 * 2
def baseEnd_1429948 : Nat := 326333615526878469143909

theorem tailTrace_1429948 : CollatzResearch.WordTrace tailWord_1429948 prefixEnd_1429948 326333615526878469143909 := by
  unfold tailWord_1429948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077244111775043260253249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34769658815700057680337665 26077244111775043260253249)
  ·
    refine ⟨19557933083831282445189937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26077244111775043260253249 19557933083831282445189937)
    ·
      refine ⟨14668449812873461833892453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19557933083831282445189937 14668449812873461833892453)
      ·
        refine ⟨2750334339913774093854835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14668449812873461833892453 2750334339913774093854835)
        ·
          refine ⟨4125501509870661140782253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750334339913774093854835 4125501509870661140782253)
          ·
            refine ⟨1547063066201497927793345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4125501509870661140782253 1547063066201497927793345)
            ·
              refine ⟨1160297299651123445845009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547063066201497927793345 1160297299651123445845009)
              ·
                refine ⟨870222974738342584383757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160297299651123445845009 870222974738342584383757)
                ·
                  refine ⟨326333615526878469143909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870222974738342584383757 326333615526878469143909)
                  ·
                    rfl

theorem cell21_1429948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1429948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429948 prefixEnd_1429948 := by exact prefixLift 1429948
  have htrace : WordTrace (prefixWord ++ tailWord_1429948) baseStart_1429948 baseEnd_1429948 := by
    simpa [prefixWord, tailWord_1429948, baseEnd_1429948] using wordTrace_append hprefix tailTrace_1429948
  have hstable : (prefixWord ++ tailWord_1429948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429948).length < 2 ^ (prefixWord ++ tailWord_1429948).sum := by decide
  have hdescent : baseEnd_1429948 < baseStart_1429948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1429973 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1429973 : Nat := 118140960795 + 1429973 * 2 ^ 59
def prefixEnd_1429973 : Nat := 4983230072969 + 3 ^ 40 * 1429973 * 2
def baseEnd_1429973 : Nat := 326339320867483981227191

theorem tailTrace_1429973 : CollatzResearch.WordTrace tailWord_1429973 prefixEnd_1429973 326339320867483981227191 := by
  unfold tailWord_1429973
  simp only [CollatzResearch.WordTrace]
  refine ⟨52155400048459515790166573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34770266698973010526777715 52155400048459515790166573)
  ·
    refine ⟨19558275018172318421312465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52155400048459515790166573 19558275018172318421312465)
    ·
      refine ⟨14668706263629238815984349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19558275018172318421312465 14668706263629238815984349)
      ·
        refine ⟨5500764848860964555994131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14668706263629238815984349 5500764848860964555994131)
        ·
          refine ⟨8251147273291446833991197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500764848860964555994131 8251147273291446833991197)
          ·
            refine ⟨3094180227484292562746699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8251147273291446833991197 3094180227484292562746699)
            ·
              refine ⟨4641270341226438844120049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094180227484292562746699 4641270341226438844120049)
              ·
                refine ⟨3480952755919829133090037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641270341226438844120049 3480952755919829133090037)
                ·
                  refine ⟨326339320867483981227191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3480952755919829133090037 326339320867483981227191)
                  ·
                    rfl

theorem cell21_1429973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1429973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1429973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1429973 prefixEnd_1429973 := by exact prefixLift 1429973
  have htrace : WordTrace (prefixWord ++ tailWord_1429973) baseStart_1429973 baseEnd_1429973 := by
    simpa [prefixWord, tailWord_1429973, baseEnd_1429973] using wordTrace_append hprefix tailTrace_1429973
  have hstable : (prefixWord ++ tailWord_1429973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1429973).length < 2 ^ (prefixWord ++ tailWord_1429973).sum := by decide
  have hdescent : baseEnd_1429973 < baseStart_1429973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1429973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430001 : List Nat := [1, 2, 2, 2, 3, 1, 10]
def baseStart_1430001 : Nat := 118140960795 + 1430001 * 2 ^ 59
def prefixEnd_1430001 : Nat := 4983230072969 + 3 ^ 40 * 1430001 * 2
def baseEnd_1430001 : Nat := 36260634538773572751163

theorem tailTrace_1430001 : CollatzResearch.WordTrace tailWord_1430001 prefixEnd_1430001 36260634538773572751163 := by
  unfold tailWord_1430001
  simp only [CollatzResearch.WordTrace]
  refine ⟨52156421292358076572185857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34770947528238717714790571 52156421292358076572185857)
  ·
    refine ⟨39117315969268557429139393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52156421292358076572185857 39117315969268557429139393)
    ·
      refine ⟨29337986976951418071854545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39117315969268557429139393 29337986976951418071854545)
      ·
        refine ⟨22003490232713563553890909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29337986976951418071854545 22003490232713563553890909)
        ·
          refine ⟨8251308837267586332709091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22003490232713563553890909 8251308837267586332709091)
          ·
            refine ⟨12376963255901379499063637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251308837267586332709091 12376963255901379499063637)
            ·
              refine ⟨36260634538773572751163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12376963255901379499063637 36260634538773572751163)
              ·
                rfl

theorem cell21_1430001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 10].length) (baseStart_1430001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430001 prefixEnd_1430001 := by exact prefixLift 1430001
  have htrace : WordTrace (prefixWord ++ tailWord_1430001) baseStart_1430001 baseEnd_1430001 := by
    simpa [prefixWord, tailWord_1430001, baseEnd_1430001] using wordTrace_append hprefix tailTrace_1430001
  have hstable : (prefixWord ++ tailWord_1430001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430001).length < 2 ^ (prefixWord ++ tailWord_1430001).sum := by decide
  have hdescent : baseEnd_1430001 < baseStart_1430001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430052 : List Nat := [2, 3, 1, 5, 2, 1, 7]
def baseStart_1430052 : Nat := 118140960795 + 1430052 * 2 ^ 59
def prefixEnd_1430052 : Nat := 4983230072969 + 3 ^ 40 * 1430052 * 2
def baseEnd_1430052 : Nat := 36261927749310822156707

theorem tailTrace_1430052 : CollatzResearch.WordTrace tailWord_1430052 prefixEnd_1430052 36261927749310822156707 := by
  unfold tailWord_1430052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26079140707586656141146205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34772187610115541521528273 26079140707586656141146205)
  ·
    refine ⟨9779677765344996052929827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26079140707586656141146205 9779677765344996052929827)
    ·
      refine ⟨14669516648017494079394741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9779677765344996052929827 14669516648017494079394741)
      ·
        refine ⟨1375267185751640069943257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14669516648017494079394741 1375267185751640069943257)
        ·
          refine ⟨1031450389313730052457443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375267185751640069943257 1031450389313730052457443)
          ·
            refine ⟨1547175583970595078686165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031450389313730052457443 1547175583970595078686165)
            ·
              refine ⟨36261927749310822156707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1547175583970595078686165 36261927749310822156707)
              ·
                rfl

theorem cell21_1430052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 7].length) (baseStart_1430052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430052 prefixEnd_1430052 := by exact prefixLift 1430052
  have htrace : WordTrace (prefixWord ++ tailWord_1430052) baseStart_1430052 baseEnd_1430052 := by
    simpa [prefixWord, tailWord_1430052, baseEnd_1430052] using wordTrace_append hprefix tailTrace_1430052
  have hstable : (prefixWord ++ tailWord_1430052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430052).length < 2 ^ (prefixWord ++ tailWord_1430052).sum := by decide
  have hdescent : baseEnd_1430052 < baseStart_1430052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430080 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_1430080 : Nat := 118140960795 + 1430080 * 2 ^ 59
def prefixEnd_1430080 : Nat := 4983230072969 + 3 ^ 40 * 1430080 * 2
def baseEnd_1430080 : Nat := 326363739725275572943639

theorem tailTrace_1430080 : CollatzResearch.WordTrace tailWord_1430080 prefixEnd_1430080 326363739725275572943639 := by
  unfold tailWord_1430080
  simp only [CollatzResearch.WordTrace]
  refine ⟨26079651329535936532155847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34772868439381248709541129 26079651329535936532155847)
  ·
    refine ⟨39119476994303904798233771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26079651329535936532155847 39119476994303904798233771)
    ·
      refine ⟨58679215491455857197350657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39119476994303904798233771 58679215491455857197350657)
      ·
        refine ⟨44009411618591892898012993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58679215491455857197350657 44009411618591892898012993)
        ·
          refine ⟨33007058713943919673509745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44009411618591892898012993 33007058713943919673509745)
          ·
            refine ⟨24755294035457939755132309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33007058713943919673509745 24755294035457939755132309)
            ·
              refine ⟨1160404407912090926021827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24755294035457939755132309 1160404407912090926021827)
              ·
                refine ⟨1740606611868136389032741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160404407912090926021827 1740606611868136389032741)
                ·
                  refine ⟨326363739725275572943639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740606611868136389032741 326363739725275572943639)
                  ·
                    rfl

theorem cell21_1430080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_1430080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430080 prefixEnd_1430080 := by exact prefixLift 1430080
  have htrace : WordTrace (prefixWord ++ tailWord_1430080) baseStart_1430080 baseEnd_1430080 := by
    simpa [prefixWord, tailWord_1430080, baseEnd_1430080] using wordTrace_append hprefix tailTrace_1430080
  have hstable : (prefixWord ++ tailWord_1430080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430080).length < 2 ^ (prefixWord ++ tailWord_1430080).sum := by decide
  have hdescent : baseEnd_1430080 < baseStart_1430080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430114 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1430114 : Nat := 118140960795 + 1430114 * 2 ^ 59
def prefixEnd_1430114 : Nat := 4983230072969 + 3 ^ 40 * 1430114 * 2
def baseEnd_1430114 : Nat := 326371498988499069376903

theorem tailTrace_1430114 : CollatzResearch.WordTrace tailWord_1430114 prefixEnd_1430114 326371498988499069376903 := by
  unfold tailWord_1430114
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040135685237174217762349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34773695160632464580699597 13040135685237174217762349)
  ·
    refine ⟨4890050881963940331660881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13040135685237174217762349 4890050881963940331660881)
    ·
      refine ⟨3667538161472955248745661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4890050881963940331660881 3667538161472955248745661)
      ·
        refine ⟨1375326810552358218279623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3667538161472955248745661 1375326810552358218279623)
        ·
          refine ⟨2062990215828537327419435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375326810552358218279623 2062990215828537327419435)
          ·
            refine ⟨3094485323742805991129153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062990215828537327419435 3094485323742805991129153)
            ·
              refine ⟨2320863992807104493346865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094485323742805991129153 2320863992807104493346865)
              ·
                refine ⟨1740647994605328370010149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2320863992807104493346865 1740647994605328370010149)
                ·
                  refine ⟨326371498988499069376903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740647994605328370010149 326371498988499069376903)
                  ·
                    rfl

theorem cell21_1430114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1430114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430114 prefixEnd_1430114 := by exact prefixLift 1430114
  have htrace : WordTrace (prefixWord ++ tailWord_1430114) baseStart_1430114 baseEnd_1430114 := by
    simpa [prefixWord, tailWord_1430114, baseEnd_1430114] using wordTrace_append hprefix tailTrace_1430114
  have hstable : (prefixWord ++ tailWord_1430114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430114).length < 2 ^ (prefixWord ++ tailWord_1430114).sum := by decide
  have hdescent : baseEnd_1430114 < baseStart_1430114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430190 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1430190 : Nat := 118140960795 + 1430190 * 2 ^ 59
def prefixEnd_1430190 : Nat := 4983230072969 + 3 ^ 40 * 1430190 * 2
def baseEnd_1430190 : Nat := 326388843223939826110081

theorem tailTrace_1430190 : CollatzResearch.WordTrace tailWord_1430190 prefixEnd_1430190 326388843223939826110081 := by
  unfold tailWord_1430190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520414336084170231352003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34775543125782241233877349 6520414336084170231352003)
  ·
    refine ⟨9780621504126255347028005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6520414336084170231352003 9780621504126255347028005)
    ·
      refine ⟨1833866532023672877567751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9780621504126255347028005 1833866532023672877567751)
      ·
        refine ⟨2750799798035509316351627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833866532023672877567751 2750799798035509316351627)
        ·
          refine ⟨4126199697053263974527441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750799798035509316351627 4126199697053263974527441)
          ·
            refine ⟨3094649772789947980895581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4126199697053263974527441 3094649772789947980895581)
            ·
              refine ⟨1160493664796230492835843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094649772789947980895581 1160493664796230492835843)
              ·
                refine ⟨1740740497194345739253765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160493664796230492835843 1740740497194345739253765)
                ·
                  refine ⟨326388843223939826110081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740740497194345739253765 326388843223939826110081)
                  ·
                    rfl

theorem cell21_1430190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1430190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430190 prefixEnd_1430190 := by exact prefixLift 1430190
  have htrace : WordTrace (prefixWord ++ tailWord_1430190) baseStart_1430190 baseEnd_1430190 := by
    simpa [prefixWord, tailWord_1430190, baseEnd_1430190] using wordTrace_append hprefix tailTrace_1430190
  have hstable : (prefixWord ++ tailWord_1430190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430190).length < 2 ^ (prefixWord ++ tailWord_1430190).sum := by decide
  have hdescent : baseEnd_1430190 < baseStart_1430190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430218 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1430218 : Nat := 118140960795 + 1430218 * 2 ^ 59
def prefixEnd_1430218 : Nat := 4983230072969 + 3 ^ 40 * 1430218 * 2
def baseEnd_1430218 : Nat := 326395233205417999643357

theorem tailTrace_1430218 : CollatzResearch.WordTrace tailWord_1430218 prefixEnd_1430218 326395233205417999643357 := by
  unfold tailWord_1430218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041083983142980658208827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34776223955047948421890205 13041083983142980658208827)
  ·
    refine ⟨19561625974714470987313241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041083983142980658208827 19561625974714470987313241)
    ·
      refine ⟨14671219481035853240484931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19561625974714470987313241 14671219481035853240484931)
      ·
        refine ⟨22006829221553779860727397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14671219481035853240484931 22006829221553779860727397)
        ·
          refine ⟨4126280479041333723886387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22006829221553779860727397 4126280479041333723886387)
          ·
            refine ⟨6189420718562000585829581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126280479041333723886387 6189420718562000585829581)
            ·
              refine ⟨2321032769460750219686093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6189420718562000585829581 2321032769460750219686093)
              ·
                refine ⟨870387288547781332382285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2321032769460750219686093 870387288547781332382285)
                ·
                  refine ⟨326395233205417999643357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870387288547781332382285 326395233205417999643357)
                  ·
                    rfl

theorem cell21_1430218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1430218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430218 prefixEnd_1430218 := by exact prefixLift 1430218
  have htrace : WordTrace (prefixWord ++ tailWord_1430218) baseStart_1430218 baseEnd_1430218 := by
    simpa [prefixWord, tailWord_1430218, baseEnd_1430218] using wordTrace_append hprefix tailTrace_1430218
  have hstable : (prefixWord ++ tailWord_1430218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430218).length < 2 ^ (prefixWord ++ tailWord_1430218).sum := by decide
  have hdescent : baseEnd_1430218 < baseStart_1430218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430291 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_1430291 : Nat := 118140960795 + 1430291 * 2 ^ 59
def prefixEnd_1430291 : Nat := 4983230072969 + 3 ^ 40 * 1430291 * 2
def baseEnd_1430291 : Nat := 326411892799986094926541

theorem tailTrace_1430291 : CollatzResearch.WordTrace tailWord_1430291 prefixEnd_1430291 326411892799986094926541 := by
  unfold tailWord_1430291
  simp only [CollatzResearch.WordTrace]
  refine ⟨52166998461307456100242727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34777998974204970733495151 52166998461307456100242727)
  ·
    refine ⟨78250497691961184150364091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52166998461307456100242727 78250497691961184150364091)
    ·
      refine ⟨117375746537941776225546137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78250497691961184150364091 117375746537941776225546137)
      ·
        refine ⟨88031809903456332169159603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117375746537941776225546137 88031809903456332169159603)
        ·
          refine ⟨132047714855184498253739405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88031809903456332169159603 132047714855184498253739405)
          ·
            refine ⟨49517893070694186845152277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132047714855184498253739405 49517893070694186845152277)
            ·
              refine ⟨2321151237688790008366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49517893070694186845152277 2321151237688790008366513)
              ·
                refine ⟨1740863428266592506274885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321151237688790008366513 1740863428266592506274885)
                ·
                  refine ⟨326411892799986094926541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1740863428266592506274885 326411892799986094926541)
                  ·
                    rfl

theorem cell21_1430291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_1430291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430291 prefixEnd_1430291 := by exact prefixLift 1430291
  have htrace : WordTrace (prefixWord ++ tailWord_1430291) baseStart_1430291 baseEnd_1430291 := by
    simpa [prefixWord, tailWord_1430291, baseEnd_1430291] using wordTrace_append hprefix tailTrace_1430291
  have hstable : (prefixWord ++ tailWord_1430291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430291).length < 2 ^ (prefixWord ++ tailWord_1430291).sum := by decide
  have hdescent : baseEnd_1430291 < baseStart_1430291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430322 : List Nat := [3, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1430322 : Nat := 118140960795 + 1430322 * 2 ^ 59
def prefixEnd_1430322 : Nat := 4983230072969 + 3 ^ 40 * 1430322 * 2
def baseEnd_1430322 : Nat := 108806322474112309969937

theorem tailTrace_1430322 : CollatzResearch.WordTrace tailWord_1430322 prefixEnd_1430322 108806322474112309969937 := by
  unfold tailWord_1430322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042032281048787098655305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34778752749463432263080813 13042032281048787098655305)
  ·
    refine ⟨9781524210786590323991479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13042032281048787098655305 9781524210786590323991479)
    ·
      refine ⟨14672286316179885485987219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9781524210786590323991479 14672286316179885485987219)
      ·
        refine ⟨22008429474269828228980829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14672286316179885485987219 22008429474269828228980829)
        ·
          refine ⟨8253161052851185585867811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22008429474269828228980829 8253161052851185585867811)
          ·
            refine ⟨12379741579276778378801717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8253161052851185585867811 12379741579276778378801717)
            ·
              refine ⟨1160600773057197973012661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12379741579276778378801717 1160600773057197973012661)
              ·
                refine ⟨108806322474112309969937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160600773057197973012661 108806322474112309969937)
                ·
                  rfl

theorem cell21_1430322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1430322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430322 prefixEnd_1430322 := by exact prefixLift 1430322
  have htrace : WordTrace (prefixWord ++ tailWord_1430322) baseStart_1430322 baseEnd_1430322 := by
    simpa [prefixWord, tailWord_1430322, baseEnd_1430322] using wordTrace_append hprefix tailTrace_1430322
  have hstable : (prefixWord ++ tailWord_1430322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430322).length < 2 ^ (prefixWord ++ tailWord_1430322).sum := by decide
  have hdescent : baseEnd_1430322 < baseStart_1430322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430353 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_1430353 : Nat := 118140960795 + 1430353 * 2 ^ 59
def prefixEnd_1430353 : Nat := 4983230072969 + 3 ^ 40 * 1430353 * 2
def baseEnd_1430353 : Nat := 326426042044687764893081

theorem tailTrace_1430353 : CollatzResearch.WordTrace tailWord_1430353 prefixEnd_1430353 326426042044687764893081 := by
  unfold tailWord_1430353
  simp only [CollatzResearch.WordTrace]
  refine ⟨52169259787082840688999713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34779506524721893792666475 52169259787082840688999713)
  ·
    refine ⟨39126944840312130516749785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52169259787082840688999713 39126944840312130516749785)
    ·
      refine ⟨29345208630234097887562339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39126944840312130516749785 29345208630234097887562339)
      ·
        refine ⟨44017812945351146831343509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29345208630234097887562339 44017812945351146831343509)
        ·
          refine ⟨2063334981813335007719227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44017812945351146831343509 2063334981813335007719227)
          ·
            refine ⟨3095002472720002511578841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063334981813335007719227 3095002472720002511578841)
            ·
              refine ⟨2321251854540001883684131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095002472720002511578841 2321251854540001883684131)
              ·
                refine ⟨3481877781810002825526197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321251854540001883684131 3481877781810002825526197)
                ·
                  refine ⟨326426042044687764893081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3481877781810002825526197 326426042044687764893081)
                  ·
                    rfl

theorem cell21_1430353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_1430353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430353 prefixEnd_1430353 := by exact prefixLift 1430353
  have htrace : WordTrace (prefixWord ++ tailWord_1430353) baseStart_1430353 baseEnd_1430353 := by
    simpa [prefixWord, tailWord_1430353, baseEnd_1430353] using wordTrace_append hprefix tailTrace_1430353
  have hstable : (prefixWord ++ tailWord_1430353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430353).length < 2 ^ (prefixWord ++ tailWord_1430353).sum := by decide
  have hdescent : baseEnd_1430353 < baseStart_1430353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430395 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_1430395 : Nat := 118140960795 + 1430395 * 2 ^ 59
def prefixEnd_1430395 : Nat := 4983230072969 + 3 ^ 40 * 1430395 * 2
def baseEnd_1430395 : Nat := 326435627016905025192995

theorem tailTrace_1430395 : CollatzResearch.WordTrace tailWord_1430395 prefixEnd_1430395 326435627016905025192995 := by
  unfold tailWord_1430395
  simp only [CollatzResearch.WordTrace]
  refine ⟨52170791652930681862028639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34780527768620454574685759 52170791652930681862028639)
  ·
    refine ⟨78256187479396022793042959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52170791652930681862028639 78256187479396022793042959)
    ·
      refine ⟨117384281219094034189564439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78256187479396022793042959 117384281219094034189564439)
      ·
        refine ⟨176076421828641051284346659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117384281219094034189564439 176076421828641051284346659)
        ·
          refine ⟨264114632742961576926519989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176076421828641051284346659 264114632742961576926519989)
          ·
            refine ⟨24760746819652647836861249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264114632742961576926519989 24760746819652647836861249)
            ·
              refine ⟨18570560114739485877645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24760746819652647836861249 18570560114739485877645937)
              ·
                refine ⟨13927920086054614408234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570560114739485877645937 13927920086054614408234453)
                ·
                  refine ⟨326435627016905025192995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13927920086054614408234453 326435627016905025192995)
                  ·
                    rfl

theorem cell21_1430395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_1430395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430395 prefixEnd_1430395 := by exact prefixLift 1430395
  have htrace : WordTrace (prefixWord ++ tailWord_1430395) baseStart_1430395 baseEnd_1430395 := by
    simpa [prefixWord, tailWord_1430395, baseEnd_1430395] using wordTrace_append hprefix tailTrace_1430395
  have hstable : (prefixWord ++ tailWord_1430395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430395).length < 2 ^ (prefixWord ++ tailWord_1430395).sum := by decide
  have hdescent : baseEnd_1430395 < baseStart_1430395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430412 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1430412 : Nat := 118140960795 + 1430412 * 2 ^ 59
def prefixEnd_1430412 : Nat := 4983230072969 + 3 ^ 40 * 1430412 * 2
def baseEnd_1430412 : Nat := 326439506648516773409627

theorem tailTrace_1430412 : CollatzResearch.WordTrace tailWord_1430412 prefixEnd_1430412 326439506648516773409627 := by
  unfold tailWord_1430412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085705846934546882698745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34780941129246062510264993 26085705846934546882698745)
  ·
    refine ⟨19564279385200910162024059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26085705846934546882698745 19564279385200910162024059)
    ·
      refine ⟨29346419077801365243036089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19564279385200910162024059 29346419077801365243036089)
      ·
        refine ⟨22009814308351023932277067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29346419077801365243036089 22009814308351023932277067)
        ·
          refine ⟨33014721462526535898415601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22009814308351023932277067 33014721462526535898415601)
          ·
            refine ⟨24761041096894901923811701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33014721462526535898415601 24761041096894901923811701)
            ·
              refine ⟨2321347602833897055357347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24761041096894901923811701 2321347602833897055357347)
              ·
                refine ⟨3482021404250845583036021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321347602833897055357347 3482021404250845583036021)
                ·
                  refine ⟨326439506648516773409627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482021404250845583036021 326439506648516773409627)
                  ·
                    rfl

theorem cell21_1430412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1430412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430412 prefixEnd_1430412 := by exact prefixLift 1430412
  have htrace : WordTrace (prefixWord ++ tailWord_1430412) baseStart_1430412 baseEnd_1430412 := by
    simpa [prefixWord, tailWord_1430412, baseEnd_1430412] using wordTrace_append hprefix tailTrace_1430412
  have hstable : (prefixWord ++ tailWord_1430412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430412).length < 2 ^ (prefixWord ++ tailWord_1430412).sum := by decide
  have hdescent : baseEnd_1430412 < baseStart_1430412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430418 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1430418 : Nat := 118140960795 + 1430418 * 2 ^ 59
def prefixEnd_1430418 : Nat := 4983230072969 + 3 ^ 40 * 1430418 * 2
def baseEnd_1430418 : Nat := 326440875930262096309615

theorem tailTrace_1430418 : CollatzResearch.WordTrace tailWord_1430418 prefixEnd_1430418 326440875930262096309615 := by
  unfold tailWord_1430418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042907632961839197528977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34781087021231571193410605 13042907632961839197528977)
  ·
    refine ⟨9782180724721379398146733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13042907632961839197528977 9782180724721379398146733)
    ·
      refine ⟨3668317771770517274305025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9782180724721379398146733 3668317771770517274305025)
      ·
        refine ⟨2751238328827887955728769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3668317771770517274305025 2751238328827887955728769)
        ·
          refine ⟨2063428746620915966796577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2751238328827887955728769 2063428746620915966796577)
          ·
            refine ⟨1547571559965686975097433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063428746620915966796577 1547571559965686975097433)
            ·
              refine ⟨1160678669974265231323075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547571559965686975097433 1160678669974265231323075)
              ·
                refine ⟨1741018004961397846984613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160678669974265231323075 1741018004961397846984613)
                ·
                  refine ⟨326440875930262096309615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741018004961397846984613 326440875930262096309615)
                  ·
                    rfl

theorem cell21_1430418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1430418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430418 prefixEnd_1430418 := by exact prefixLift 1430418
  have htrace : WordTrace (prefixWord ++ tailWord_1430418) baseStart_1430418 baseEnd_1430418 := by
    simpa [prefixWord, tailWord_1430418, baseEnd_1430418] using wordTrace_append hprefix tailTrace_1430418
  have hstable : (prefixWord ++ tailWord_1430418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430418).length < 2 ^ (prefixWord ++ tailWord_1430418).sum := by decide
  have hdescent : baseEnd_1430418 < baseStart_1430418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430488 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_1430488 : Nat := 118140960795 + 1430488 * 2 ^ 59
def prefixEnd_1430488 : Nat := 4983230072969 + 3 ^ 40 * 1430488 * 2
def baseEnd_1430488 : Nat := 326456850883957530142805

theorem tailTrace_1430488 : CollatzResearch.WordTrace tailWord_1430488 prefixEnd_1430488 326456850883957530142805 := by
  unfold tailWord_1430488
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087091820796879372582059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34782789094395839163442745 26087091820796879372582059)
  ·
    refine ⟨39130637731195319058873089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26087091820796879372582059 39130637731195319058873089)
    ·
      refine ⟨29347978298396489294154817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39130637731195319058873089 29347978298396489294154817)
      ·
        refine ⟨22010983723797366970616113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29347978298396489294154817 22010983723797366970616113)
        ·
          refine ⟨16508237792848025227962085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22010983723797366970616113 16508237792848025227962085)
          ·
            refine ⟨3095294586159004730242891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16508237792848025227962085 3095294586159004730242891)
            ·
              refine ⟨4642941879238507095364337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3095294586159004730242891 4642941879238507095364337)
              ·
                refine ⟨3482206409428880321523253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4642941879238507095364337 3482206409428880321523253)
                ·
                  refine ⟨326456850883957530142805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482206409428880321523253 326456850883957530142805)
                  ·
                    rfl

theorem cell21_1430488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_1430488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430488 prefixEnd_1430488 := by exact prefixLift 1430488
  have htrace : WordTrace (prefixWord ++ tailWord_1430488) baseStart_1430488 baseEnd_1430488 := by
    simpa [prefixWord, tailWord_1430488, baseEnd_1430488] using wordTrace_append hprefix tailTrace_1430488
  have hstable : (prefixWord ++ tailWord_1430488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430488).length < 2 ^ (prefixWord ++ tailWord_1430488).sum := by decide
  have hdescent : baseEnd_1430488 < baseStart_1430488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430536 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_1430536 : Nat := 118140960795 + 1430536 * 2 ^ 59
def prefixEnd_1430536 : Nat := 4983230072969 + 3 ^ 40 * 1430536 * 2
def baseEnd_1430536 : Nat := 326467805137920113342707

theorem tailTrace_1430536 : CollatzResearch.WordTrace tailWord_1430536 prefixEnd_1430536 326467805137920113342707 := by
  unfold tailWord_1430536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087967172709931471455731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34783956230279908628607641 26087967172709931471455731)
  ·
    refine ⟨39131950759064897207183597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26087967172709931471455731 39131950759064897207183597)
    ·
      refine ⟨14674481534649336452693849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39131950759064897207183597 14674481534649336452693849)
      ·
        refine ⟨11005861150987002339520387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14674481534649336452693849 11005861150987002339520387)
        ·
          refine ⟨16508791726480503509280581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005861150987002339520387 16508791726480503509280581)
          ·
            refine ⟨3095398448715094407990109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16508791726480503509280581 3095398448715094407990109)
            ·
              refine ⟨1160774418268160402996291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3095398448715094407990109 1160774418268160402996291)
              ·
                refine ⟨1741161627402240604494437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160774418268160402996291 1741161627402240604494437)
                ·
                  refine ⟨326467805137920113342707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741161627402240604494437 326467805137920113342707)
                  ·
                    rfl

theorem cell21_1430536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_1430536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430536 prefixEnd_1430536 := by exact prefixLift 1430536
  have htrace : WordTrace (prefixWord ++ tailWord_1430536) baseStart_1430536 baseEnd_1430536 := by
    simpa [prefixWord, tailWord_1430536, baseEnd_1430536] using wordTrace_append hprefix tailTrace_1430536
  have hstable : (prefixWord ++ tailWord_1430536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430536).length < 2 ^ (prefixWord ++ tailWord_1430536).sum := by decide
  have hdescent : baseEnd_1430536 < baseStart_1430536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430578 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1430578 : Nat := 118140960795 + 1430578 * 2 ^ 59
def prefixEnd_1430578 : Nat := 4983230072969 + 3 ^ 40 * 1430578 * 2
def baseEnd_1430578 : Nat := 326477390110137373642621

theorem tailTrace_1430578 : CollatzResearch.WordTrace tailWord_1430578 prefixEnd_1430578 326477390110137373642621 := by
  unfold tailWord_1430578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13044366552816926028985097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34784977474178469410626925 13044366552816926028985097)
  ·
    refine ⟨9783274914612694521738823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13044366552816926028985097 9783274914612694521738823)
    ·
      refine ⟨14674912371919041782608235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9783274914612694521738823 14674912371919041782608235)
      ·
        refine ⟨22012368557878562673912353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674912371919041782608235 22012368557878562673912353)
        ·
          refine ⟨16509276418408922005434265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22012368557878562673912353 16509276418408922005434265)
          ·
            refine ⟨12381957313806691504075699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16509276418408922005434265 12381957313806691504075699)
            ·
              refine ⟨18572935970710037256113549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12381957313806691504075699 18572935970710037256113549)
              ·
                refine ⟨6964850989016263971042581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18572935970710037256113549 6964850989016263971042581)
                ·
                  refine ⟨326477390110137373642621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6964850989016263971042581 326477390110137373642621)
                  ·
                    rfl

theorem cell21_1430578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1430578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430578 prefixEnd_1430578 := by exact prefixLift 1430578
  have htrace : WordTrace (prefixWord ++ tailWord_1430578) baseStart_1430578 baseEnd_1430578 := by
    simpa [prefixWord, tailWord_1430578, baseEnd_1430578] using wordTrace_append hprefix tailTrace_1430578
  have hstable : (prefixWord ++ tailWord_1430578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430578).length < 2 ^ (prefixWord ++ tailWord_1430578).sum := by decide
  have hdescent : baseEnd_1430578 < baseStart_1430578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430632 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_1430632 : Nat := 118140960795 + 1430632 * 2 ^ 59
def prefixEnd_1430632 : Nat := 4983230072969 + 3 ^ 40 * 1430632 * 2
def baseEnd_1430632 : Nat := 326489713645845279742511

theorem tailTrace_1430632 : CollatzResearch.WordTrace tailWord_1430632 prefixEnd_1430632 326489713645845279742511 := by
  unfold tailWord_1430632
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089717876536035669203075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34786290502048047558937433 26089717876536035669203075)
  ·
    refine ⟨39134576814804053503804613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26089717876536035669203075 39134576814804053503804613)
    ·
      refine ⟨7337733152775760031963365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39134576814804053503804613 7337733152775760031963365)
      ·
        refine ⟨1375824966145455005993131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7337733152775760031963365 1375824966145455005993131)
        ·
          refine ⟨2063737449218182508989697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375824966145455005993131 2063737449218182508989697)
          ·
            refine ⟨1547803086913636881742273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063737449218182508989697 1547803086913636881742273)
            ·
              refine ⟨1160852315185227661306705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547803086913636881742273 1160852315185227661306705)
              ·
                refine ⟨870639236388920745980029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160852315185227661306705 870639236388920745980029)
                ·
                  refine ⟨326489713645845279742511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870639236388920745980029 326489713645845279742511)
                  ·
                    rfl

theorem cell21_1430632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_1430632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430632 prefixEnd_1430632 := by exact prefixLift 1430632
  have htrace : WordTrace (prefixWord ++ tailWord_1430632) baseStart_1430632 baseEnd_1430632 := by
    simpa [prefixWord, tailWord_1430632, baseEnd_1430632] using wordTrace_append hprefix tailTrace_1430632
  have hstable : (prefixWord ++ tailWord_1430632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430632).length < 2 ^ (prefixWord ++ tailWord_1430632).sum := by decide
  have hdescent : baseEnd_1430632 < baseStart_1430632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430668 : List Nat := [2, 2, 1, 2, 1, 1, 1, 11]
def baseStart_1430668 : Nat := 118140960795 + 1430668 * 2 ^ 59
def prefixEnd_1430668 : Nat := 4983230072969 + 3 ^ 40 * 1430668 * 2
def baseEnd_1430668 : Nat := 108832643112105739047479

theorem tailTrace_1430668 : CollatzResearch.WordTrace tailWord_1430668 prefixEnd_1430668 108832643112105739047479 := by
  unfold tailWord_1430668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26090374390470824743358329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34787165853961099657811105 26090374390470824743358329)
  ·
    refine ⟨19567780792853118557518747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26090374390470824743358329 19567780792853118557518747)
    ·
      refine ⟨29351671189279677836278121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19567780792853118557518747 29351671189279677836278121)
      ·
        refine ⟨22013753391959758377208591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29351671189279677836278121 22013753391959758377208591)
        ·
          refine ⟨33020630087939637565812887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22013753391959758377208591 33020630087939637565812887)
          ·
            refine ⟨49530945131909456348719331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33020630087939637565812887 49530945131909456348719331)
            ·
              refine ⟨74296417697864184523078997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49530945131909456348719331 74296417697864184523078997)
              ·
                refine ⟨108832643112105739047479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74296417697864184523078997 108832643112105739047479)
                ·
                  rfl

theorem cell21_1430668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_1430668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430668 prefixEnd_1430668 := by exact prefixLift 1430668
  have htrace : WordTrace (prefixWord ++ tailWord_1430668) baseStart_1430668 baseEnd_1430668 := by
    simpa [prefixWord, tailWord_1430668, baseEnd_1430668] using wordTrace_append hprefix tailTrace_1430668
  have hstable : (prefixWord ++ tailWord_1430668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430668).length < 2 ^ (prefixWord ++ tailWord_1430668).sum := by decide
  have hdescent : baseEnd_1430668 < baseStart_1430668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430674 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1430674 : Nat := 118140960795 + 1430674 * 2 ^ 59
def prefixEnd_1430674 : Nat := 4983230072969 + 3 ^ 40 * 1430674 * 2
def baseEnd_1430674 : Nat := 326499298618062540042425

theorem tailTrace_1430674 : CollatzResearch.WordTrace tailWord_1430674 prefixEnd_1430674 326499298618062540042425 := by
  unfold tailWord_1430674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045241904729978127858769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34787311745946608340956717 13045241904729978127858769)
  ·
    refine ⟨9783931428547483595894077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13045241904729978127858769 9783931428547483595894077)
    ·
      refine ⟨3668974285705306348460279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9783931428547483595894077 3668974285705306348460279)
      ·
        refine ⟨5503461428557959522690419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3668974285705306348460279 5503461428557959522690419)
        ·
          refine ⟨8255192142836939284035629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503461428557959522690419 8255192142836939284035629)
          ·
            refine ⟨3095697053563852231513361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8255192142836939284035629 3095697053563852231513361)
            ·
              refine ⟨2321772790172889173635021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3095697053563852231513361 2321772790172889173635021)
              ·
                refine ⟨870664796314833440113133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2321772790172889173635021 870664796314833440113133)
                ·
                  refine ⟨326499298618062540042425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870664796314833440113133 326499298618062540042425)
                  ·
                    rfl

theorem cell21_1430674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1430674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430674 prefixEnd_1430674 := by exact prefixLift 1430674
  have htrace : WordTrace (prefixWord ++ tailWord_1430674) baseStart_1430674 baseEnd_1430674 := by
    simpa [prefixWord, tailWord_1430674, baseEnd_1430674] using wordTrace_append hprefix tailTrace_1430674
  have hstable : (prefixWord ++ tailWord_1430674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430674).length < 2 ^ (prefixWord ++ tailWord_1430674).sum := by decide
  have hdescent : baseEnd_1430674 < baseStart_1430674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430716 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1430716 : Nat := 118140960795 + 1430716 * 2 ^ 59
def prefixEnd_1430716 : Nat := 4983230072969 + 3 ^ 40 * 1430716 * 2
def baseEnd_1430716 : Nat := 326508883590279800342339

theorem tailTrace_1430716 : CollatzResearch.WordTrace tailWord_1430716 prefixEnd_1430716 326508883590279800342339 := by
  unfold tailWord_1430716
  simp only [CollatzResearch.WordTrace]
  refine ⟨26091249742383876842232001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34788332989845169122976001 26091249742383876842232001)
  ·
    refine ⟨19568437306787907631674001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26091249742383876842232001 19568437306787907631674001)
    ·
      refine ⟨14676327980090930723755501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19568437306787907631674001 14676327980090930723755501)
      ·
        refine ⟨5503622992534099021408313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14676327980090930723755501 5503622992534099021408313)
        ·
          refine ⟨4127717244400574266056235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5503622992534099021408313 4127717244400574266056235)
          ·
            refine ⟨6191575866600861399084353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127717244400574266056235 6191575866600861399084353)
            ·
              refine ⟨4643681899950646049313265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6191575866600861399084353 4643681899950646049313265)
              ·
                refine ⟨3482761424962984536984949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4643681899950646049313265 3482761424962984536984949)
                ·
                  refine ⟨326508883590279800342339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3482761424962984536984949 326508883590279800342339)
                  ·
                    rfl

theorem cell21_1430716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1430716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430716 prefixEnd_1430716 := by exact prefixLift 1430716
  have htrace : WordTrace (prefixWord ++ tailWord_1430716) baseStart_1430716 baseEnd_1430716 := by
    simpa [prefixWord, tailWord_1430716, baseEnd_1430716] using wordTrace_append hprefix tailTrace_1430716
  have hstable : (prefixWord ++ tailWord_1430716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430716).length < 2 ^ (prefixWord ++ tailWord_1430716).sum := by decide
  have hdescent : baseEnd_1430716 < baseStart_1430716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430730 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1430730 : Nat := 118140960795 + 1430730 * 2 ^ 59
def prefixEnd_1430730 : Nat := 4983230072969 + 3 ^ 40 * 1430730 * 2
def baseEnd_1430730 : Nat := 326512078581018887108977

theorem tailTrace_1430730 : CollatzResearch.WordTrace tailWord_1430730 prefixEnd_1430730 326512078581018887108977 := by
  unfold tailWord_1430730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045752526679258518868411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34788673404478022716982429 13045752526679258518868411)
  ·
    refine ⟨19568628790018887778302617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13045752526679258518868411 19568628790018887778302617)
    ·
      refine ⟨14676471592514165833726963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19568628790018887778302617 14676471592514165833726963)
      ·
        refine ⟨22014707388771248750590445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14676471592514165833726963 22014707388771248750590445)
        ·
          refine ⟨8255515270789218281471417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22014707388771248750590445 8255515270789218281471417)
          ·
            refine ⟨6191636453091913711103563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8255515270789218281471417 6191636453091913711103563)
            ·
              refine ⟨9287454679637870566655345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191636453091913711103563 9287454679637870566655345)
              ·
                refine ⟨6965591009728402924991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9287454679637870566655345 6965591009728402924991509)
                ·
                  refine ⟨326512078581018887108977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6965591009728402924991509 326512078581018887108977)
                  ·
                    rfl

theorem cell21_1430730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1430730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430730 prefixEnd_1430730 := by exact prefixLift 1430730
  have htrace : WordTrace (prefixWord ++ tailWord_1430730) baseStart_1430730 baseEnd_1430730 := by
    simpa [prefixWord, tailWord_1430730, baseEnd_1430730] using wordTrace_append hprefix tailTrace_1430730
  have hstable : (prefixWord ++ tailWord_1430730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430730).length < 2 ^ (prefixWord ++ tailWord_1430730).sum := by decide
  have hdescent : baseEnd_1430730 < baseStart_1430730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430764 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1430764 : Nat := 118140960795 + 1430764 * 2 ^ 59
def prefixEnd_1430764 : Nat := 4983230072969 + 3 ^ 40 * 1430764 * 2
def baseEnd_1430764 : Nat := 326519837844242383542241

theorem tailTrace_1430764 : CollatzResearch.WordTrace tailWord_1430764 prefixEnd_1430764 326519837844242383542241 := by
  unfold tailWord_1430764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26092125094296928941105673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34789500125729238588140897 26092125094296928941105673)
  ·
    refine ⟨19569093820722696705829255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26092125094296928941105673 19569093820722696705829255)
    ·
      refine ⟨29353640731084045058743883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19569093820722696705829255 29353640731084045058743883)
      ·
        refine ⟨44030461096626067588115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29353640731084045058743883 44030461096626067588115825)
        ·
          refine ⟨33022845822469550691086869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44030461096626067588115825 33022845822469550691086869)
          ·
            refine ⟨1547945897928260188644697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33022845822469550691086869 1547945897928260188644697)
            ·
              refine ⟨1160959423446195141483523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547945897928260188644697 1160959423446195141483523)
              ·
                refine ⟨1741439135169292712225285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160959423446195141483523 1741439135169292712225285)
                ·
                  refine ⟨326519837844242383542241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741439135169292712225285 326519837844242383542241)
                  ·
                    rfl

theorem cell21_1430764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1430764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430764 prefixEnd_1430764 := by exact prefixLift 1430764
  have htrace : WordTrace (prefixWord ++ tailWord_1430764) baseStart_1430764 baseEnd_1430764 := by
    simpa [prefixWord, tailWord_1430764, baseEnd_1430764] using wordTrace_append hprefix tailTrace_1430764
  have hstable : (prefixWord ++ tailWord_1430764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430764).length < 2 ^ (prefixWord ++ tailWord_1430764).sum := by decide
  have hdescent : baseEnd_1430764 < baseStart_1430764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430868 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1430868 : Nat := 118140960795 + 1430868 * 2 ^ 59
def prefixEnd_1430868 : Nat := 4983230072969 + 3 ^ 40 * 1430868 * 2
def baseEnd_1430868 : Nat := 326543572061161313808695

theorem tailTrace_1430868 : CollatzResearch.WordTrace tailWord_1430868 prefixEnd_1430868 326543572061161313808695 := by
  unfold tailWord_1430868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26094021690108541821998629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34792028920144722429331505 26094021690108541821998629)
  ·
    refine ⟨4892629066895351591624743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26094021690108541821998629 4892629066895351591624743)
    ·
      refine ⟨7338943600343027387437115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892629066895351591624743 7338943600343027387437115)
      ·
        refine ⟨11008415400514541081155673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7338943600343027387437115 11008415400514541081155673)
        ·
          refine ⟨8256311550385905810866755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11008415400514541081155673 8256311550385905810866755)
          ·
            refine ⟨12384467325578858716300133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256311550385905810866755 12384467325578858716300133)
            ·
              refine ⟨2322087623546036009306275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12384467325578858716300133 2322087623546036009306275)
              ·
                refine ⟨3483131435319054013959413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322087623546036009306275 3483131435319054013959413)
                ·
                  refine ⟨326543572061161313808695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483131435319054013959413 326543572061161313808695)
                  ·
                    rfl

theorem cell21_1430868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1430868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430868 prefixEnd_1430868 := by exact prefixLift 1430868
  have htrace : WordTrace (prefixWord ++ tailWord_1430868) baseStart_1430868 baseEnd_1430868 := by
    simpa [prefixWord, tailWord_1430868, baseEnd_1430868] using wordTrace_append hprefix tailTrace_1430868
  have hstable : (prefixWord ++ tailWord_1430868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430868).length < 2 ^ (prefixWord ++ tailWord_1430868).sum := by decide
  have hdescent : baseEnd_1430868 < baseStart_1430868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430896 : List Nat := [2, 1, 1, 1, 4, 2, 3, 7]
def baseStart_1430896 : Nat := 118140960795 + 1430896 * 2 ^ 59
def prefixEnd_1430896 : Nat := 4983230072969 + 3 ^ 40 * 1430896 * 2
def baseEnd_1430896 : Nat := 108849987347546495780657

theorem tailTrace_1430896 : CollatzResearch.WordTrace tailWord_1430896 prefixEnd_1430896 108849987347546495780657 := by
  unfold tailWord_1430896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26094532312057822213008271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34792709749410429617344361 26094532312057822213008271)
  ·
    refine ⟨39141798468086733319512407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26094532312057822213008271 39141798468086733319512407)
    ·
      refine ⟨58712697702130099979268611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39141798468086733319512407 58712697702130099979268611)
      ·
        refine ⟨88069046553195149968902917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58712697702130099979268611 88069046553195149968902917)
        ·
          refine ⟨16512946228724090619169297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88069046553195149968902917 16512946228724090619169297)
          ·
            refine ⟨12384709671543067964376973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16512946228724090619169297 12384709671543067964376973)
            ·
              refine ⟨4644266126828650486641365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12384709671543067964376973 4644266126828650486641365)
              ·
                refine ⟨108849987347546495780657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4644266126828650486641365 108849987347546495780657)
                ·
                  rfl

theorem cell21_1430896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_1430896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430896 prefixEnd_1430896 := by exact prefixLift 1430896
  have htrace : WordTrace (prefixWord ++ tailWord_1430896) baseStart_1430896 baseEnd_1430896 := by
    simpa [prefixWord, tailWord_1430896, baseEnd_1430896] using wordTrace_append hprefix tailTrace_1430896
  have hstable : (prefixWord ++ tailWord_1430896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430896).length < 2 ^ (prefixWord ++ tailWord_1430896).sum := by decide
  have hdescent : baseEnd_1430896 < baseStart_1430896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1430972 : List Nat := [2, 2, 2, 4, 11]
def baseStart_1430972 : Nat := 118140960795 + 1430972 * 2 ^ 59
def prefixEnd_1430972 : Nat := 4983230072969 + 3 ^ 40 * 1430972 * 2
def baseEnd_1430972 : Nat := 4031695139235558568829

theorem tailTrace_1430972 : CollatzResearch.WordTrace tailWord_1430972 prefixEnd_1430972 4031695139235558568829 := by
  unfold tailWord_1430972
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095918285920154702891585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34794557714560206270522113 26095918285920154702891585)
  ·
    refine ⟨19571938714440116027168689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26095918285920154702891585 19571938714440116027168689)
    ·
      refine ⟨14678954035830087020376517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19571938714440116027168689 14678954035830087020376517)
      ·
        refine ⟨2752303881718141316320597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14678954035830087020376517 2752303881718141316320597)
        ·
          refine ⟨4031695139235558568829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2752303881718141316320597 4031695139235558568829)
          ·
            rfl

theorem cell21_1430972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 11].length) (baseStart_1430972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1430972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1430972 prefixEnd_1430972 := by exact prefixLift 1430972
  have htrace : WordTrace (prefixWord ++ tailWord_1430972) baseStart_1430972 baseEnd_1430972 := by
    simpa [prefixWord, tailWord_1430972, baseEnd_1430972] using wordTrace_append hprefix tailTrace_1430972
  have hstable : (prefixWord ++ tailWord_1430972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1430972).length < 2 ^ (prefixWord ++ tailWord_1430972).sum := by decide
  have hdescent : baseEnd_1430972 < baseStart_1430972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1430972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431096 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1431096 : Nat := 118140960795 + 1431096 * 2 ^ 59
def prefixEnd_1431096 : Nat := 4983230072969 + 3 ^ 40 * 1431096 * 2
def baseEnd_1431096 : Nat := 326595604767483584008229

theorem tailTrace_1431096 : CollatzResearch.WordTrace tailWord_1431096 prefixEnd_1431096 326595604767483584008229 := by
  unfold tailWord_1431096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098179611695539291648571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34797572815594052388864761 26098179611695539291648571)
  ·
    refine ⟨39147269417543308937472857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26098179611695539291648571 39147269417543308937472857)
    ·
      refine ⟨29360452063157481703104643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39147269417543308937472857 29360452063157481703104643)
      ·
        refine ⟨44040678094736222554656965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29360452063157481703104643 44040678094736222554656965)
        ·
          refine ⟨8257627142763041728998181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44040678094736222554656965 8257627142763041728998181)
          ·
            refine ⟨1548305089268070324187159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8257627142763041728998181 1548305089268070324187159)
            ·
              refine ⟨2322457633902105486280739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548305089268070324187159 2322457633902105486280739)
              ·
                refine ⟨3483686450853158229421109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322457633902105486280739 3483686450853158229421109)
                ·
                  refine ⟨326595604767483584008229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483686450853158229421109 326595604767483584008229)
                  ·
                    rfl

theorem cell21_1431096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1431096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431096 prefixEnd_1431096 := by exact prefixLift 1431096
  have htrace : WordTrace (prefixWord ++ tailWord_1431096) baseStart_1431096 baseEnd_1431096 := by
    simpa [prefixWord, tailWord_1431096, baseEnd_1431096] using wordTrace_append hprefix tailTrace_1431096
  have hstable : (prefixWord ++ tailWord_1431096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431096).length < 2 ^ (prefixWord ++ tailWord_1431096).sum := by decide
  have hdescent : baseEnd_1431096 < baseStart_1431096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431124 : List Nat := [2, 4, 1, 1, 1, 2, 1, 9]
def baseStart_1431124 : Nat := 118140960795 + 1431124 * 2 ^ 59
def prefixEnd_1431124 : Nat := 4983230072969 + 3 ^ 40 * 1431124 * 2
def baseEnd_1431124 : Nat := 108867331582987252513835

theorem tailTrace_1431124 : CollatzResearch.WordTrace tailWord_1431124 prefixEnd_1431124 108867331582987252513835 := by
  unfold tailWord_1431124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098690233644819682658213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34798253644859759576877617 26098690233644819682658213)
  ·
    refine ⟨4893504418808403690498415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26098690233644819682658213 4893504418808403690498415)
    ·
      refine ⟨7340256628212605535747623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893504418808403690498415 7340256628212605535747623)
      ·
        refine ⟨11010384942318908303621435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340256628212605535747623 11010384942318908303621435)
        ·
          refine ⟨16515577413478362455432153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010384942318908303621435 16515577413478362455432153)
          ·
            refine ⟨12386683060108771841574115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16515577413478362455432153 12386683060108771841574115)
            ·
              refine ⟨18580024590163157762361173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386683060108771841574115 18580024590163157762361173)
              ·
                refine ⟨108867331582987252513835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18580024590163157762361173 108867331582987252513835)
                ·
                  rfl

theorem cell21_1431124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_1431124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431124 prefixEnd_1431124 := by exact prefixLift 1431124
  have htrace : WordTrace (prefixWord ++ tailWord_1431124) baseStart_1431124 baseEnd_1431124 := by
    simpa [prefixWord, tailWord_1431124, baseEnd_1431124] using wordTrace_append hprefix tailTrace_1431124
  have hstable : (prefixWord ++ tailWord_1431124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431124).length < 2 ^ (prefixWord ++ tailWord_1431124).sum := by decide
  have hdescent : baseEnd_1431124 < baseStart_1431124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431158 : List Nat := [5, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1431158 : Nat := 118140960795 + 1431158 * 2 ^ 59
def prefixEnd_1431158 : Nat := 4983230072969 + 3 ^ 40 * 1431158 * 2
def baseEnd_1431158 : Nat := 108869918004061751324923

theorem tailTrace_1431158 : CollatzResearch.WordTrace tailWord_1431158 prefixEnd_1431158 108869918004061751324923 := by
  unfold tailWord_1431158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262413784322903948253383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34799080366110975448036085 3262413784322903948253383)
  ·
    refine ⟨4893620676484355922380075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262413784322903948253383 4893620676484355922380075)
    ·
      refine ⟨7340431014726533883570113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893620676484355922380075 7340431014726533883570113)
      ·
        refine ⟨5505323261044900412677585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7340431014726533883570113 5505323261044900412677585)
        ·
          refine ⟨4128992445783675309508189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5505323261044900412677585 4128992445783675309508189)
          ·
            refine ⟨1548372167168878241065571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4128992445783675309508189 1548372167168878241065571)
            ·
              refine ⟨2322558250753317361598357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548372167168878241065571 2322558250753317361598357)
              ·
                refine ⟨108869918004061751324923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2322558250753317361598357 108869918004061751324923)
                ·
                  rfl

theorem cell21_1431158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1431158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431158 prefixEnd_1431158 := by exact prefixLift 1431158
  have htrace : WordTrace (prefixWord ++ tailWord_1431158) baseStart_1431158 baseEnd_1431158 := by
    simpa [prefixWord, tailWord_1431158, baseEnd_1431158] using wordTrace_append hprefix tailTrace_1431158
  have hstable : (prefixWord ++ tailWord_1431158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431158).length < 2 ^ (prefixWord ++ tailWord_1431158).sum := by decide
  have hdescent : baseEnd_1431158 < baseStart_1431158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431172 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1431172 : Nat := 118140960795 + 1431172 * 2 ^ 59
def prefixEnd_1431172 : Nat := 4983230072969 + 3 ^ 40 * 1431172 * 2
def baseEnd_1431172 : Nat := 326612949002924340741407

theorem tailTrace_1431172 : CollatzResearch.WordTrace tailWord_1431172 prefixEnd_1431172 326612949002924340741407 := by
  unfold tailWord_1431172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26099565585557871781531885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34799420780743829042042513 26099565585557871781531885)
  ·
    refine ⟨9787337094584201918074457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26099565585557871781531885 9787337094584201918074457)
    ·
      refine ⟨7340502820938151438555843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9787337094584201918074457 7340502820938151438555843)
      ·
        refine ⟨11010754231407227157833765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340502820938151438555843 11010754231407227157833765)
        ·
          refine ⟨2064516418388855092093831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11010754231407227157833765 2064516418388855092093831)
          ·
            refine ⟨3096774627583282638140747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064516418388855092093831 3096774627583282638140747)
            ·
              refine ⟨4645161941374923957211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096774627583282638140747 4645161941374923957211121)
              ·
                refine ⟨3483871456031192967908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645161941374923957211121 3483871456031192967908341)
                ·
                  refine ⟨326612949002924340741407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3483871456031192967908341 326612949002924340741407)
                  ·
                    rfl

theorem cell21_1431172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1431172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431172 prefixEnd_1431172 := by exact prefixLift 1431172
  have htrace : WordTrace (prefixWord ++ tailWord_1431172) baseStart_1431172 baseEnd_1431172 := by
    simpa [prefixWord, tailWord_1431172, baseEnd_1431172] using wordTrace_append hprefix tailTrace_1431172
  have hstable : (prefixWord ++ tailWord_1431172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431172).length < 2 ^ (prefixWord ++ tailWord_1431172).sum := by decide
  have hdescent : baseEnd_1431172 < baseStart_1431172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431200 : List Nat := [2, 1, 1, 4, 3, 2, 8]
def baseStart_1431200 : Nat := 118140960795 + 1431200 * 2 ^ 59
def prefixEnd_1431200 : Nat := 4983230072969 + 3 ^ 40 * 1431200 * 2
def baseEnd_1431200 : Nat := 36291037664933612697187

theorem tailTrace_1431200 : CollatzResearch.WordTrace tailWord_1431200 prefixEnd_1431200 36291037664933612697187 := by
  unfold tailWord_1431200
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100076207507152172541527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34800101610009536230055369 26100076207507152172541527)
  ·
    refine ⟨39150114311260728258812291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26100076207507152172541527 39150114311260728258812291)
    ·
      refine ⟨58725171466891092388218437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39150114311260728258812291 58725171466891092388218437)
      ·
        refine ⟨11010969650042079822790957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58725171466891092388218437 11010969650042079822790957)
        ·
          refine ⟨4129113618765779933546609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11010969650042079822790957 4129113618765779933546609)
          ·
            refine ⟨3096835214074334950159957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4129113618765779933546609 3096835214074334950159957)
            ·
              refine ⟨36291037664933612697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3096835214074334950159957 36291037664933612697187)
              ·
                rfl

theorem cell21_1431200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 8].length) (baseStart_1431200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431200 prefixEnd_1431200 := by exact prefixLift 1431200
  have htrace : WordTrace (prefixWord ++ tailWord_1431200) baseStart_1431200 baseEnd_1431200 := by
    simpa [prefixWord, tailWord_1431200, baseEnd_1431200] using wordTrace_append hprefix tailTrace_1431200
  have hstable : (prefixWord ++ tailWord_1431200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431200).length < 2 ^ (prefixWord ++ tailWord_1431200).sum := by decide
  have hdescent : baseEnd_1431200 < baseStart_1431200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431265 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 5]
def baseStart_1431265 : Nat := 118140960795 + 1431265 * 2 ^ 59
def prefixEnd_1431265 : Nat := 4983230072969 + 3 ^ 40 * 1431265 * 2
def baseEnd_1431265 : Nat := 326634172869976845691217

theorem tailTrace_1431265 : CollatzResearch.WordTrace tailWord_1431265 prefixEnd_1431265 326634172869976845691217 := by
  unfold tailWord_1431265
  simp only [CollatzResearch.WordTrace]
  refine ⟨52202523159778820446199249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34801682106519213630799499 52202523159778820446199249)
  ·
    refine ⟨39151892369834115334649437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52202523159778820446199249 39151892369834115334649437)
    ·
      refine ⟨14681959638687793250493539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39151892369834115334649437 14681959638687793250493539)
      ·
        refine ⟨22022939458031689875740309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14681959638687793250493539 22022939458031689875740309)
        ·
          refine ⟨1032325287095235462925327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22022939458031689875740309 1032325287095235462925327)
          ·
            refine ⟨1548487930642853194387991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032325287095235462925327 1548487930642853194387991)
            ·
              refine ⟨2322731895964279791581987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548487930642853194387991 2322731895964279791581987)
              ·
                refine ⟨3484097843946419687372981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322731895964279791581987 3484097843946419687372981)
                ·
                  refine ⟨326634172869976845691217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3484097843946419687372981 326634172869976845691217)
                  ·
                    rfl

theorem cell21_1431265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_1431265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431265 prefixEnd_1431265 := by exact prefixLift 1431265
  have htrace : WordTrace (prefixWord ++ tailWord_1431265) baseStart_1431265 baseEnd_1431265 := by
    simpa [prefixWord, tailWord_1431265, baseEnd_1431265] using wordTrace_append hprefix tailTrace_1431265
  have hstable : (prefixWord ++ tailWord_1431265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431265).length < 2 ^ (prefixWord ++ tailWord_1431265).sum := by decide
  have hdescent : baseEnd_1431265 < baseStart_1431265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431290 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1431290 : Nat := 118140960795 + 1431290 * 2 ^ 59
def prefixEnd_1431290 : Nat := 4983230072969 + 3 ^ 40 * 1431290 * 2
def baseEnd_1431290 : Nat := 326639878210582357774499

theorem tailTrace_1431290 : CollatzResearch.WordTrace tailWord_1431290 prefixEnd_1431290 326639878210582357774499 := by
  unfold tailWord_1431290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13050858746172062428964831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34802289989792166477239549 13050858746172062428964831)
  ·
    refine ⟨19576288119258093643447247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13050858746172062428964831 19576288119258093643447247)
    ·
      refine ⟨29364432178887140465170871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19576288119258093643447247 29364432178887140465170871)
      ·
        refine ⟨44046648268330710697756307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29364432178887140465170871 44046648268330710697756307)
        ·
          refine ⟨66069972402496066046634461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44046648268330710697756307 66069972402496066046634461)
          ·
            refine ⟨24776239650936024767487923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66069972402496066046634461 24776239650936024767487923)
            ·
              refine ⟨37164359476404037151231885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24776239650936024767487923 37164359476404037151231885)
              ·
                refine ⟨13936634803651513931711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37164359476404037151231885 13936634803651513931711957)
                ·
                  refine ⟨326639878210582357774499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13936634803651513931711957 326639878210582357774499)
                  ·
                    rfl

theorem cell21_1431290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1431290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431290 prefixEnd_1431290 := by exact prefixLift 1431290
  have htrace : WordTrace (prefixWord ++ tailWord_1431290) baseStart_1431290 baseEnd_1431290 := by
    simpa [prefixWord, tailWord_1431290, baseEnd_1431290] using wordTrace_append hprefix tailTrace_1431290
  have hstable : (prefixWord ++ tailWord_1431290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431290).length < 2 ^ (prefixWord ++ tailWord_1431290).sum := by decide
  have hdescent : baseEnd_1431290 < baseStart_1431290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431324 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_1431324 : Nat := 118140960795 + 1431324 * 2 ^ 59
def prefixEnd_1431324 : Nat := 4983230072969 + 3 ^ 40 * 1431324 * 2
def baseEnd_1431324 : Nat := 326647637473805854207763

theorem tailTrace_1431324 : CollatzResearch.WordTrace tailWord_1431324 prefixEnd_1431324 326647637473805854207763 := by
  unfold tailWord_1431324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26102337533282536761298513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34803116711043382348398017 26102337533282536761298513)
  ·
    refine ⟨19576753149961902570973885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26102337533282536761298513 19576753149961902570973885)
    ·
      refine ⟨7341282431235713464115207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19576753149961902570973885 7341282431235713464115207)
      ·
        refine ⟨11011923646853570196172811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7341282431235713464115207 11011923646853570196172811)
        ·
          refine ⟨16517885470280355294259217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011923646853570196172811 16517885470280355294259217)
          ·
            refine ⟨12388414102710266470694413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16517885470280355294259217 12388414102710266470694413)
            ·
              refine ⟨4645655288516349926510405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12388414102710266470694413 4645655288516349926510405)
              ·
                refine ⟨871060366596815611220701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4645655288516349926510405 871060366596815611220701)
                ·
                  refine ⟨326647637473805854207763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871060366596815611220701 326647637473805854207763)
                  ·
                    rfl

theorem cell21_1431324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_1431324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431324 prefixEnd_1431324 := by exact prefixLift 1431324
  have htrace : WordTrace (prefixWord ++ tailWord_1431324) baseStart_1431324 baseEnd_1431324 := by
    simpa [prefixWord, tailWord_1431324, baseEnd_1431324] using wordTrace_append hprefix tailTrace_1431324
  have hstable : (prefixWord ++ tailWord_1431324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431324).length < 2 ^ (prefixWord ++ tailWord_1431324).sum := by decide
  have hdescent : baseEnd_1431324 < baseStart_1431324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431372 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1431372 : Nat := 118140960795 + 1431372 * 2 ^ 59
def prefixEnd_1431372 : Nat := 4983230072969 + 3 ^ 40 * 1431372 * 2
def baseEnd_1431372 : Nat := 326658591727768437407665

theorem tailTrace_1431372 : CollatzResearch.WordTrace tailWord_1431372 prefixEnd_1431372 326658591727768437407665 := by
  unfold tailWord_1431372
  simp only [CollatzResearch.WordTrace]
  refine ⟨26103212885195588860172185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34804283846927451813562913 26103212885195588860172185)
  ·
    refine ⟨19577409663896691645129139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26103212885195588860172185 19577409663896691645129139)
    ·
      refine ⟨29366114495845037467693709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19577409663896691645129139 29366114495845037467693709)
      ·
        refine ⟨11012292935941889050385141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29366114495845037467693709 11012292935941889050385141)
        ·
          refine ⟨1032402462744552098473607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11012292935941889050385141 1032402462744552098473607)
          ·
            refine ⟨1548603694116828147710411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032402462744552098473607 1548603694116828147710411)
            ·
              refine ⟨2322905541175242221565617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548603694116828147710411 2322905541175242221565617)
              ·
                refine ⟨1742179155881431666174213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322905541175242221565617 1742179155881431666174213)
                ·
                  refine ⟨326658591727768437407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742179155881431666174213 326658591727768437407665)
                  ·
                    rfl

theorem cell21_1431372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1431372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431372 prefixEnd_1431372 := by exact prefixLift 1431372
  have htrace : WordTrace (prefixWord ++ tailWord_1431372) baseStart_1431372 baseEnd_1431372 := by
    simpa [prefixWord, tailWord_1431372, baseEnd_1431372] using wordTrace_append hprefix tailTrace_1431372
  have hstable : (prefixWord ++ tailWord_1431372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431372).length < 2 ^ (prefixWord ++ tailWord_1431372).sum := by decide
  have hdescent : baseEnd_1431372 < baseStart_1431372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431434 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_1431434 : Nat := 118140960795 + 1431434 * 2 ^ 59
def prefixEnd_1431434 : Nat := 4983230072969 + 3 ^ 40 * 1431434 * 2
def baseEnd_1431434 : Nat := 326672740972470107374205

theorem tailTrace_1431434 : CollatzResearch.WordTrace tailWord_1431434 prefixEnd_1431434 326672740972470107374205 := by
  unfold tailWord_1431434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052171774041640577275339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34805791397444374872734237 13052171774041640577275339)
  ·
    refine ⟨19578257661062460865913009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13052171774041640577275339 19578257661062460865913009)
    ·
      refine ⟨14683693245796845649434757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19578257661062460865913009 14683693245796845649434757)
      ·
        refine ⟨2753192483586908559269017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14683693245796845649434757 2753192483586908559269017)
        ·
          refine ⟨2064894362690181419451763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753192483586908559269017 2064894362690181419451763)
          ·
            refine ⟨3097341544035272129177645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064894362690181419451763 3097341544035272129177645)
            ·
              refine ⟨1161503079013227048441617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3097341544035272129177645 1161503079013227048441617)
              ·
                refine ⟨871127309259920286331213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161503079013227048441617 871127309259920286331213)
                ·
                  refine ⟨326672740972470107374205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871127309259920286331213 326672740972470107374205)
                  ·
                    rfl

theorem cell21_1431434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_1431434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431434 prefixEnd_1431434 := by exact prefixLift 1431434
  have htrace : WordTrace (prefixWord ++ tailWord_1431434) baseStart_1431434 baseEnd_1431434 := by
    simpa [prefixWord, tailWord_1431434, baseEnd_1431434] using wordTrace_append hprefix tailTrace_1431434
  have hstable : (prefixWord ++ tailWord_1431434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431434).length < 2 ^ (prefixWord ++ tailWord_1431434).sum := by decide
  have hdescent : baseEnd_1431434 < baseStart_1431434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431563 : List Nat := [1, 1, 1, 1, 6, 1, 2, 8]
def baseStart_1431563 : Nat := 118140960795 + 1431563 * 2 ^ 59
def prefixEnd_1431563 : Nat := 4983230072969 + 3 ^ 40 * 1431563 * 2
def baseEnd_1431563 : Nat := 108900726843331516574647

theorem tailTrace_1431563 : CollatzResearch.WordTrace tailWord_1431563 prefixEnd_1431563 108900726843331516574647 := by
  unfold tailWord_1431563
  simp only [CollatzResearch.WordTrace]
  refine ⟨52213392112699217340547343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34808928075132811560364895 52213392112699217340547343)
  ·
    refine ⟨78320088169048826010821015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52213392112699217340547343 78320088169048826010821015)
    ·
      refine ⟨117480132253573239016231523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78320088169048826010821015 117480132253573239016231523)
      ·
        refine ⟨176220198380359858524347285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117480132253573239016231523 176220198380359858524347285)
        ·
          refine ⟨8260321799079368368328779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176220198380359858524347285 8260321799079368368328779)
          ·
            refine ⟨12390482698619052552493169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260321799079368368328779 12390482698619052552493169)
            ·
              refine ⟨9292862023964289414369877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12390482698619052552493169 9292862023964289414369877)
              ·
                refine ⟨108900726843331516574647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9292862023964289414369877 108900726843331516574647)
                ·
                  rfl

theorem cell21_1431563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_1431563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431563 prefixEnd_1431563 := by exact prefixLift 1431563
  have htrace : WordTrace (prefixWord ++ tailWord_1431563) baseStart_1431563 baseEnd_1431563 := by
    simpa [prefixWord, tailWord_1431563, baseEnd_1431563] using wordTrace_append hprefix tailTrace_1431563
  have hstable : (prefixWord ++ tailWord_1431563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431563).length < 2 ^ (prefixWord ++ tailWord_1431563).sum := by decide
  have hdescent : baseEnd_1431563 < baseStart_1431563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431572 : List Nat := [2, 4, 3, 2, 2, 1, 2, 5]
def baseStart_1431572 : Nat := 118140960795 + 1431572 * 2 ^ 59
def prefixEnd_1431572 : Nat := 4983230072969 + 3 ^ 40 * 1431572 * 2
def baseEnd_1431572 : Nat := 108901411484204178024641

theorem tailTrace_1431572 : CollatzResearch.WordTrace tailWord_1431572 prefixEnd_1431572 108901411484204178024641 := by
  unfold tailWord_1431572
  simp only [CollatzResearch.WordTrace]
  refine ⟨26106860184833305938812485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34809146913111074585083313 26106860184833305938812485)
  ·
    refine ⟨4895036284656244863527341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26106860184833305938812485 4895036284656244863527341)
    ·
      refine ⟨1835638606746091823822753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4895036284656244863527341 1835638606746091823822753)
      ·
        refine ⟨1376728955059568867867065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1835638606746091823822753 1376728955059568867867065)
        ·
          refine ⟨1032546716294676650900299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376728955059568867867065 1032546716294676650900299)
          ·
            refine ⟨1548820074442014976350449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032546716294676650900299 1548820074442014976350449)
            ·
              refine ⟨1161615055831511232262837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548820074442014976350449 1161615055831511232262837)
              ·
                refine ⟨108901411484204178024641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1161615055831511232262837 108901411484204178024641)
                ·
                  rfl

theorem cell21_1431572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_1431572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431572 prefixEnd_1431572 := by exact prefixLift 1431572
  have htrace : WordTrace (prefixWord ++ tailWord_1431572) baseStart_1431572 baseEnd_1431572 := by
    simpa [prefixWord, tailWord_1431572, baseEnd_1431572] using wordTrace_append hprefix tailTrace_1431572
  have hstable : (prefixWord ++ tailWord_1431572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431572).length < 2 ^ (prefixWord ++ tailWord_1431572).sum := by decide
  have hdescent : baseEnd_1431572 < baseStart_1431572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431580 : List Nat := [2, 2, 3, 1, 3, 2, 1, 7]
def baseStart_1431580 : Nat := 118140960795 + 1431580 * 2 ^ 59
def prefixEnd_1431580 : Nat := 4983230072969 + 3 ^ 40 * 1431580 * 2
def baseEnd_1431580 : Nat := 108902020053868765980191

theorem tailTrace_1431580 : CollatzResearch.WordTrace tailWord_1431580 prefixEnd_1431580 108902020053868765980191 := by
  unfold tailWord_1431580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107006076818814621958097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34809341435758419495944129 26107006076818814621958097)
  ·
    refine ⟨19580254557614110966468573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26107006076818814621958097 19580254557614110966468573)
    ·
      refine ⟨7342595459105291612425715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19580254557614110966468573 7342595459105291612425715)
      ·
        refine ⟨11013893188657937418638573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342595459105291612425715 11013893188657937418638573)
        ·
          refine ⟨4130209945746726531989465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11013893188657937418638573 4130209945746726531989465)
          ·
            refine ⟨3097657459310044898992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130209945746726531989465 3097657459310044898992099)
            ·
              refine ⟨4646486188965067348488149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097657459310044898992099 4646486188965067348488149)
              ·
                refine ⟨108902020053868765980191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4646486188965067348488149 108902020053868765980191)
                ·
                  rfl

theorem cell21_1431580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_1431580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431580 prefixEnd_1431580 := by exact prefixLift 1431580
  have htrace : WordTrace (prefixWord ++ tailWord_1431580) baseStart_1431580 baseEnd_1431580 := by
    simpa [prefixWord, tailWord_1431580, baseEnd_1431580] using wordTrace_append hprefix tailTrace_1431580
  have hstable : (prefixWord ++ tailWord_1431580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431580).length < 2 ^ (prefixWord ++ tailWord_1431580).sum := by decide
  have hdescent : baseEnd_1431580 < baseStart_1431580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431625 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_1431625 : Nat := 118140960795 + 1431625 * 2 ^ 59
def prefixEnd_1431625 : Nat := 4983230072969 + 3 ^ 40 * 1431625 * 2
def baseEnd_1431625 : Nat := 326716329774696219690481

theorem tailTrace_1431625 : CollatzResearch.WordTrace tailWord_1431625 prefixEnd_1431625 326716329774696219690481 := by
  unfold tailWord_1431625
  simp only [CollatzResearch.WordTrace]
  refine ⟨52215653438474601929304329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34810435625649734619536219 52215653438474601929304329)
  ·
    refine ⟨39161740078855951446978247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52215653438474601929304329 39161740078855951446978247)
    ·
      refine ⟨58742610118283927170467371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39161740078855951446978247 58742610118283927170467371)
      ·
        refine ⟨88113915177425890755701057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58742610118283927170467371 88113915177425890755701057)
        ·
          refine ⟨66085436383069418066775793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88113915177425890755701057 66085436383069418066775793)
          ·
            refine ⟨49564077287302063550081845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66085436383069418066775793 49564077287302063550081845)
            ·
              refine ⟨4646632245684568457820173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49564077287302063550081845 4646632245684568457820173)
              ·
                refine ⟨1742487092131713171682565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4646632245684568457820173 1742487092131713171682565)
                ·
                  refine ⟨326716329774696219690481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742487092131713171682565 326716329774696219690481)
                  ·
                    rfl

theorem cell21_1431625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_1431625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431625 prefixEnd_1431625 := by exact prefixLift 1431625
  have htrace : WordTrace (prefixWord ++ tailWord_1431625) baseStart_1431625 baseEnd_1431625 := by
    simpa [prefixWord, tailWord_1431625, baseEnd_1431625] using wordTrace_append hprefix tailTrace_1431625
  have hstable : (prefixWord ++ tailWord_1431625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431625).length < 2 ^ (prefixWord ++ tailWord_1431625).sum := by decide
  have hdescent : baseEnd_1431625 < baseStart_1431625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431639 : List Nat := [1, 1, 3, 2, 2, 1, 4, 7]
def baseStart_1431639 : Nat := 118140960795 + 1431639 * 2 ^ 59
def prefixEnd_1431639 : Nat := 4983230072969 + 3 ^ 40 * 1431639 * 2
def baseEnd_1431639 : Nat := 108906508255145102152373

theorem tailTrace_1431639 : CollatzResearch.WordTrace tailWord_1431639 prefixEnd_1431639 108906508255145102152373 := by
  unfold tailWord_1431639
  simp only [CollatzResearch.WordTrace]
  refine ⟨52216164060423882320313971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34810776040282588213542647 52216164060423882320313971)
  ·
    refine ⟨78324246090635823480470957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52216164060423882320313971 78324246090635823480470957)
    ·
      refine ⟨29371592283988433805176609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78324246090635823480470957 29371592283988433805176609)
      ·
        refine ⟨22028694212991325353882457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29371592283988433805176609 22028694212991325353882457)
        ·
          refine ⟨16521520659743494015411843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22028694212991325353882457 16521520659743494015411843)
          ·
            refine ⟨24782280989615241023117765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16521520659743494015411843 24782280989615241023117765)
            ·
              refine ⟨4646677685552857691834581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24782280989615241023117765 4646677685552857691834581)
              ·
                refine ⟨108906508255145102152373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4646677685552857691834581 108906508255145102152373)
                ·
                  rfl

theorem cell21_1431639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_1431639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431639 prefixEnd_1431639 := by exact prefixLift 1431639
  have htrace : WordTrace (prefixWord ++ tailWord_1431639) baseStart_1431639 baseEnd_1431639 := by
    simpa [prefixWord, tailWord_1431639, baseEnd_1431639] using wordTrace_append hprefix tailTrace_1431639
  have hstable : (prefixWord ++ tailWord_1431639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431639).length < 2 ^ (prefixWord ++ tailWord_1431639).sum := by decide
  have hdescent : baseEnd_1431639 < baseStart_1431639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431777 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_1431777 : Nat := 118140960795 + 1431777 * 2 ^ 59
def prefixEnd_1431777 : Nat := 4983230072969 + 3 ^ 40 * 1431777 * 2
def baseEnd_1431777 : Nat := 326751018245577733156837

theorem tailTrace_1431777 : CollatzResearch.WordTrace tailWord_1431777 prefixEnd_1431777 326751018245577733156837 := by
  unfold tailWord_1431777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52221197333923931888837585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34814131555949287925891723 52221197333923931888837585)
  ·
    refine ⟨39165898000442948916628189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52221197333923931888837585 39165898000442948916628189)
    ·
      refine ⟨14687211750166105843735571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39165898000442948916628189 14687211750166105843735571)
      ·
        refine ⟨22030817625249158765603357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14687211750166105843735571 22030817625249158765603357)
        ·
          refine ⟨8261556609468434537101259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22030817625249158765603357 8261556609468434537101259)
          ·
            refine ⟨12392334914202651805651889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261556609468434537101259 12392334914202651805651889)
            ·
              refine ⟨9294251185651988854238917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12392334914202651805651889 9294251185651988854238917)
              ·
                refine ⟨1742672097309747910169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9294251185651988854238917 1742672097309747910169797)
                ·
                  refine ⟨326751018245577733156837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742672097309747910169797 326751018245577733156837)
                  ·
                    rfl

theorem cell21_1431777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_1431777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431777 prefixEnd_1431777 := by exact prefixLift 1431777
  have htrace : WordTrace (prefixWord ++ tailWord_1431777) baseStart_1431777 baseEnd_1431777 := by
    simpa [prefixWord, tailWord_1431777, baseEnd_1431777] using wordTrace_append hprefix tailTrace_1431777
  have hstable : (prefixWord ++ tailWord_1431777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431777).length < 2 ^ (prefixWord ++ tailWord_1431777).sum := by decide
  have hdescent : baseEnd_1431777 < baseStart_1431777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431791 : List Nat := [1, 1, 2, 1, 6, 1, 1, 8]
def baseStart_1431791 : Nat := 118140960795 + 1431791 * 2 ^ 59
def prefixEnd_1431791 : Nat := 4983230072969 + 3 ^ 40 * 1431791 * 2
def baseEnd_1431791 : Nat := 108918071078772273307825

theorem tailTrace_1431791 : CollatzResearch.WordTrace tailWord_1431791 prefixEnd_1431791 108918071078772273307825 := by
  unfold tailWord_1431791
  simp only [CollatzResearch.WordTrace]
  refine ⟨52221707955873212279847227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34814471970582141519898151 52221707955873212279847227)
  ·
    refine ⟨78332561933809818419770841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52221707955873212279847227 78332561933809818419770841)
    ·
      refine ⟨58749421450357363814828131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78332561933809818419770841 58749421450357363814828131)
      ·
        refine ⟨88124132175536045722242197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58749421450357363814828131 88124132175536045722242197)
        ·
          refine ⟨4130818695728252143230103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88124132175536045722242197 4130818695728252143230103)
          ·
            refine ⟨6196228043592378214845155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130818695728252143230103 6196228043592378214845155)
            ·
              refine ⟨9294342065388567322267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196228043592378214845155 9294342065388567322267733)
              ·
                refine ⟨108918071078772273307825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9294342065388567322267733 108918071078772273307825)
                ·
                  rfl

theorem cell21_1431791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_1431791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431791 prefixEnd_1431791 := by exact prefixLift 1431791
  have htrace : WordTrace (prefixWord ++ tailWord_1431791) baseStart_1431791 baseEnd_1431791 := by
    simpa [prefixWord, tailWord_1431791, baseEnd_1431791] using wordTrace_append hprefix tailTrace_1431791
  have hstable : (prefixWord ++ tailWord_1431791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431791).length < 2 ^ (prefixWord ++ tailWord_1431791).sum := by decide
  have hdescent : baseEnd_1431791 < baseStart_1431791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431794 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1431794 : Nat := 118140960795 + 1431794 * 2 ^ 59
def prefixEnd_1431794 : Nat := 4983230072969 + 3 ^ 40 * 1431794 * 2
def baseEnd_1431794 : Nat := 326754897877189481373469

theorem tailTrace_1431794 : CollatzResearch.WordTrace tailWord_1431794 prefixEnd_1431794 326754897877189481373469 := by
  unfold tailWord_1431794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13055454343715585948051609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34814544916574895861470957 13055454343715585948051609)
  ·
    refine ⟨9791590757786689461038707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13055454343715585948051609 9791590757786689461038707)
    ·
      refine ⟨14687386136680034191558061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9791590757786689461038707 14687386136680034191558061)
      ·
        refine ⟨5507769801255012821834273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14687386136680034191558061 5507769801255012821834273)
        ·
          refine ⟨4130827350941259616375705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507769801255012821834273 4130827350941259616375705)
          ·
            refine ⟨3098120513205944712281779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130827350941259616375705 3098120513205944712281779)
            ·
              refine ⟨4647180769808917068422669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098120513205944712281779 4647180769808917068422669)
              ·
                refine ⟨1742692788678343900658501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4647180769808917068422669 1742692788678343900658501)
                ·
                  refine ⟨326754897877189481373469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742692788678343900658501 326754897877189481373469)
                  ·
                    rfl

theorem cell21_1431794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1431794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431794 prefixEnd_1431794 := by exact prefixLift 1431794
  have htrace : WordTrace (prefixWord ++ tailWord_1431794) baseStart_1431794 baseEnd_1431794 := by
    simpa [prefixWord, tailWord_1431794, baseEnd_1431794] using wordTrace_append hprefix tailTrace_1431794
  have hstable : (prefixWord ++ tailWord_1431794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431794).length < 2 ^ (prefixWord ++ tailWord_1431794).sum := by decide
  have hdescent : baseEnd_1431794 < baseStart_1431794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431873 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 3]
def baseStart_1431873 : Nat := 118140960795 + 1431873 * 2 ^ 59
def prefixEnd_1431873 : Nat := 4983230072969 + 3 ^ 40 * 1431873 * 2
def baseEnd_1431873 : Nat := 326772926753502899556641

theorem tailTrace_1431873 : CollatzResearch.WordTrace tailWord_1431873 prefixEnd_1431873 326772926753502899556641 := by
  unfold tailWord_1431873
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224698741576140284332273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34816465827717426856221515 52224698741576140284332273)
  ·
    refine ⟨39168524056182105213249205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52224698741576140284332273 39168524056182105213249205)
    ·
      refine ⟨3672049130267072363742113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39168524056182105213249205 3672049130267072363742113)
      ·
        refine ⟨2754036847700304272806585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3672049130267072363742113 2754036847700304272806585)
        ·
          refine ⟨2065527635775228204604939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754036847700304272806585 2065527635775228204604939)
          ·
            refine ⟨3098291453662842306907409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065527635775228204604939 3098291453662842306907409)
            ·
              refine ⟨2323718590247131730180557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098291453662842306907409 2323718590247131730180557)
              ·
                refine ⟨871394471342674398817709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323718590247131730180557 871394471342674398817709)
                ·
                  refine ⟨326772926753502899556641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871394471342674398817709 326772926753502899556641)
                  ·
                    rfl

theorem cell21_1431873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_1431873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431873 prefixEnd_1431873 := by exact prefixLift 1431873
  have htrace : WordTrace (prefixWord ++ tailWord_1431873) baseStart_1431873 baseEnd_1431873 := by
    simpa [prefixWord, tailWord_1431873, baseEnd_1431873] using wordTrace_append hprefix tailTrace_1431873
  have hstable : (prefixWord ++ tailWord_1431873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431873).length < 2 ^ (prefixWord ++ tailWord_1431873).sum := by decide
  have hdescent : baseEnd_1431873 < baseStart_1431873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431881 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_1431881 : Nat := 118140960795 + 1431881 * 2 ^ 59
def prefixEnd_1431881 : Nat := 4983230072969 + 3 ^ 40 * 1431881 * 2
def baseEnd_1431881 : Nat := 326774752462496663423291

theorem tailTrace_1431881 : CollatzResearch.WordTrace tailWord_1431881 prefixEnd_1431881 326774752462496663423291 := by
  unfold tailWord_1431881
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224990525547157650623497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34816660350364771767082331 52224990525547157650623497)
  ·
    refine ⟨39168742894160368237967623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52224990525547157650623497 39168742894160368237967623)
    ·
      refine ⟨58753114341240552356951435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39168742894160368237967623 58753114341240552356951435)
      ·
        refine ⟨88129671511860828535427153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58753114341240552356951435 88129671511860828535427153)
        ·
          refine ⟨66097253633895621401570365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88129671511860828535427153 66097253633895621401570365)
          ·
            refine ⟨24786470112710858025588887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66097253633895621401570365 24786470112710858025588887)
            ·
              refine ⟨37179705169066287038383331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24786470112710858025588887 37179705169066287038383331)
              ·
                refine ⟨55769557753599430557574997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37179705169066287038383331 55769557753599430557574997)
                ·
                  refine ⟨326774752462496663423291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55769557753599430557574997 326774752462496663423291)
                  ·
                    rfl

theorem cell21_1431881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_1431881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431881 prefixEnd_1431881 := by exact prefixLift 1431881
  have htrace : WordTrace (prefixWord ++ tailWord_1431881) baseStart_1431881 baseEnd_1431881 := by
    simpa [prefixWord, tailWord_1431881, baseEnd_1431881] using wordTrace_append hprefix tailTrace_1431881
  have hstable : (prefixWord ++ tailWord_1431881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431881).length < 2 ^ (prefixWord ++ tailWord_1431881).sum := by decide
  have hdescent : baseEnd_1431881 < baseStart_1431881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1431960 : List Nat := [2, 1, 2, 5, 1, 2, 2, 6]
def baseStart_1431960 : Nat := 118140960795 + 1431960 * 2 ^ 59
def prefixEnd_1431960 : Nat := 4983230072969 + 3 ^ 40 * 1431960 * 2
def baseEnd_1431960 : Nat := 108930927112936693868821

theorem tailTrace_1431960 : CollatzResearch.WordTrace tailWord_1431960 prefixEnd_1431960 108930927112936693868821 := by
  unfold tailWord_1431960
  simp only [CollatzResearch.WordTrace]
  refine ⟨26113935946130477071374667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34818581261507302761832889 26113935946130477071374667)
  ·
    refine ⟨39170903919195715607062001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26113935946130477071374667 39170903919195715607062001)
    ·
      refine ⟨29378177939396786705296501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39170903919195715607062001 29378177939396786705296501)
      ·
        refine ⟨2754204181818448753621547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29378177939396786705296501 2754204181818448753621547)
        ·
          refine ⟨4131306272727673130432321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2754204181818448753621547 4131306272727673130432321)
          ·
            refine ⟨3098479704545754847824241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131306272727673130432321 3098479704545754847824241)
            ·
              refine ⟨2323859778409316135868181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098479704545754847824241 2323859778409316135868181)
              ·
                refine ⟨108930927112936693868821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2323859778409316135868181 108930927112936693868821)
                ·
                  rfl

theorem cell21_1431960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_1431960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1431960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1431960 prefixEnd_1431960 := by exact prefixLift 1431960
  have htrace : WordTrace (prefixWord ++ tailWord_1431960) baseStart_1431960 baseEnd_1431960 := by
    simpa [prefixWord, tailWord_1431960, baseEnd_1431960] using wordTrace_append hprefix tailTrace_1431960
  have hstable : (prefixWord ++ tailWord_1431960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1431960).length < 2 ^ (prefixWord ++ tailWord_1431960).sum := by decide
  have hdescent : baseEnd_1431960 < baseStart_1431960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1431960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432008 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_1432008 : Nat := 118140960795 + 1432008 * 2 ^ 59
def prefixEnd_1432008 : Nat := 4983230072969 + 3 ^ 40 * 1432008 * 2
def baseEnd_1432008 : Nat := 326803735592772664806365

theorem tailTrace_1432008 : CollatzResearch.WordTrace tailWord_1432008 prefixEnd_1432008 326803735592772664806365 := by
  unfold tailWord_1432008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114811298043529170248339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34819748397391372226997785 26114811298043529170248339)
  ·
    refine ⟨39172216947065293755372509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26114811298043529170248339 39172216947065293755372509)
    ·
      refine ⟨14689581355149485158264691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39172216947065293755372509 14689581355149485158264691)
      ·
        refine ⟨22034372032724227737397037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14689581355149485158264691 22034372032724227737397037)
        ·
          refine ⟨8262889512271585401523889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22034372032724227737397037 8262889512271585401523889)
          ·
            refine ⟨6197167134203689051142917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8262889512271585401523889 6197167134203689051142917)
            ·
              refine ⟨1161968837663191697089297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6197167134203689051142917 1161968837663191697089297)
              ·
                refine ⟨871476628247393772816973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161968837663191697089297 871476628247393772816973)
                ·
                  refine ⟨326803735592772664806365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871476628247393772816973 326803735592772664806365)
                  ·
                    rfl

theorem cell21_1432008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_1432008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432008 prefixEnd_1432008 := by exact prefixLift 1432008
  have htrace : WordTrace (prefixWord ++ tailWord_1432008) baseStart_1432008 baseEnd_1432008 := by
    simpa [prefixWord, tailWord_1432008, baseEnd_1432008] using wordTrace_append hprefix tailTrace_1432008
  have hstable : (prefixWord ++ tailWord_1432008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432008).length < 2 ^ (prefixWord ++ tailWord_1432008).sum := by decide
  have hdescent : baseEnd_1432008 < baseStart_1432008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432022 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1432022 : Nat := 118140960795 + 1432022 * 2 ^ 59
def prefixEnd_1432022 : Nat := 4983230072969 + 3 ^ 40 * 1432022 * 2
def baseEnd_1432022 : Nat := 326806930583511751573003

theorem tailTrace_1432022 : CollatzResearch.WordTrace tailWord_1432022 prefixEnd_1432022 326806930583511751573003 := by
  unfold tailWord_1432022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264383326127271170719145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34820088812024225821004213 3264383326127271170719145)
  ·
    refine ⟨2448287494595453378039359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3264383326127271170719145 2448287494595453378039359)
    ·
      refine ⟨3672431241893180067059039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448287494595453378039359 3672431241893180067059039)
      ·
        refine ⟨5508646862839770100588559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672431241893180067059039 5508646862839770100588559)
        ·
          refine ⟨8262970294259655150882839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508646862839770100588559 8262970294259655150882839)
          ·
            refine ⟨12394455441389482726324259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262970294259655150882839 12394455441389482726324259)
            ·
              refine ⟨18591683162084224089486389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394455441389482726324259 18591683162084224089486389)
              ·
                refine ⟨1742970296445396008389349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18591683162084224089486389 1742970296445396008389349)
                ·
                  refine ⟨326806930583511751573003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1742970296445396008389349 326806930583511751573003)
                  ·
                    rfl

theorem cell21_1432022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1432022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432022 prefixEnd_1432022 := by exact prefixLift 1432022
  have htrace : WordTrace (prefixWord ++ tailWord_1432022) baseStart_1432022 baseEnd_1432022 := by
    simpa [prefixWord, tailWord_1432022, baseEnd_1432022] using wordTrace_append hprefix tailTrace_1432022
  have hstable : (prefixWord ++ tailWord_1432022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432022).length < 2 ^ (prefixWord ++ tailWord_1432022).sum := by decide
  have hdescent : baseEnd_1432022 < baseStart_1432022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432132 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1432132 : Nat := 118140960795 + 1432132 * 2 ^ 59
def prefixEnd_1432132 : Nat := 4983230072969 + 3 ^ 40 * 1432132 * 2
def baseEnd_1432132 : Nat := 326832034082176004739445

theorem tailTrace_1432132 : CollatzResearch.WordTrace tailWord_1432132 prefixEnd_1432132 326832034082176004739445 := by
  unfold tailWord_1432132
  simp only [CollatzResearch.WordTrace]
  refine ⟨26117072623818913759005325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34822763498425218345340433 26117072623818913759005325)
  ·
    refine ⟨9793902233932092659626997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26117072623818913759005325 9793902233932092659626997)
    ·
      refine ⟨918178334431133686840031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9793902233932092659626997 918178334431133686840031)
      ·
        refine ⟨1377267501646700530260047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918178334431133686840031 1377267501646700530260047)
        ·
          refine ⟨2065901252470050795390071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377267501646700530260047 2065901252470050795390071)
          ·
            refine ⟨3098851878705076193085107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065901252470050795390071 3098851878705076193085107)
            ·
              refine ⟨4648277818057614289627661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098851878705076193085107 4648277818057614289627661)
              ·
                refine ⟨1743104181771605358610373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4648277818057614289627661 1743104181771605358610373)
                ·
                  refine ⟨326832034082176004739445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743104181771605358610373 326832034082176004739445)
                  ·
                    rfl

theorem cell21_1432132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1432132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432132 prefixEnd_1432132 := by exact prefixLift 1432132
  have htrace : WordTrace (prefixWord ++ tailWord_1432132) baseStart_1432132 baseEnd_1432132 := by
    simpa [prefixWord, tailWord_1432132, baseEnd_1432132] using wordTrace_append hprefix tailTrace_1432132
  have hstable : (prefixWord ++ tailWord_1432132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432132).length < 2 ^ (prefixWord ++ tailWord_1432132).sum := by decide
  have hdescent : baseEnd_1432132 < baseStart_1432132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432174 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1432174 : Nat := 118140960795 + 1432174 * 2 ^ 59
def prefixEnd_1432174 : Nat := 4983230072969 + 3 ^ 40 * 1432174 * 2
def baseEnd_1432174 : Nat := 326841619054393265039359

theorem tailTrace_1432174 : CollatzResearch.WordTrace tailWord_1432174 prefixEnd_1432174 326841619054393265039359 := by
  unfold tailWord_1432174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529459639185708586379947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34823784742323779127359717 6529459639185708586379947)
  ·
    refine ⟨9794189458778562879569921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6529459639185708586379947 9794189458778562879569921)
    ·
      refine ⟨7345642094083922159677441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9794189458778562879569921 7345642094083922159677441)
      ·
        refine ⟨5509231570562941619758081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7345642094083922159677441 5509231570562941619758081)
        ·
          refine ⟨4131923677922206214818561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5509231570562941619758081 4131923677922206214818561)
          ·
            refine ⟨3098942758441654661113921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131923677922206214818561 3098942758441654661113921)
            ·
              refine ⟨2324207068831240995835441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098942758441654661113921 2324207068831240995835441)
              ·
                refine ⟨1743155301623430746876581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324207068831240995835441 1743155301623430746876581)
                ·
                  refine ⟨326841619054393265039359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743155301623430746876581 326841619054393265039359)
                  ·
                    rfl

theorem cell21_1432174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1432174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432174 prefixEnd_1432174 := by exact prefixLift 1432174
  have htrace : WordTrace (prefixWord ++ tailWord_1432174) baseStart_1432174 baseEnd_1432174 := by
    simpa [prefixWord, tailWord_1432174, baseEnd_1432174] using wordTrace_append hprefix tailTrace_1432174
  have hstable : (prefixWord ++ tailWord_1432174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432174).length < 2 ^ (prefixWord ++ tailWord_1432174).sum := by decide
  have hdescent : baseEnd_1432174 < baseStart_1432174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432216 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_1432216 : Nat := 118140960795 + 1432216 * 2 ^ 59
def prefixEnd_1432216 : Nat := 4983230072969 + 3 ^ 40 * 1432216 * 2
def baseEnd_1432216 : Nat := 326851204026610525339273

theorem tailTrace_1432216 : CollatzResearch.WordTrace tailWord_1432216 prefixEnd_1432216 326851204026610525339273 := by
  unfold tailWord_1432216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118604489666754932034251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34824805986222339909379001 26118604489666754932034251)
  ·
    refine ⟨39177906734500132398051377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26118604489666754932034251 39177906734500132398051377)
    ·
      refine ⟨29383430050875099298538533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39177906734500132398051377 29383430050875099298538533)
      ·
        refine ⟨5509393134539081118475975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29383430050875099298538533 5509393134539081118475975)
        ·
          refine ⟨8264089701808621677713963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509393134539081118475975 8264089701808621677713963)
          ·
            refine ⟨12396134552712932516570945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264089701808621677713963 12396134552712932516570945)
            ·
              refine ⟨9297100914534699387428209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396134552712932516570945 9297100914534699387428209)
              ·
                refine ⟨6972825685901024540571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297100914534699387428209 6972825685901024540571157)
                ·
                  refine ⟨326851204026610525339273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6972825685901024540571157 326851204026610525339273)
                  ·
                    rfl

theorem cell21_1432216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_1432216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432216 prefixEnd_1432216 := by exact prefixLift 1432216
  have htrace : WordTrace (prefixWord ++ tailWord_1432216) baseStart_1432216 baseEnd_1432216 := by
    simpa [prefixWord, tailWord_1432216, baseEnd_1432216] using wordTrace_append hprefix tailTrace_1432216
  have hstable : (prefixWord ++ tailWord_1432216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432216).length < 2 ^ (prefixWord ++ tailWord_1432216).sum := by decide
  have hdescent : baseEnd_1432216 < baseStart_1432216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432264 : List Nat := [2, 1, 3, 1, 2, 5, 2, 5]
def baseStart_1432264 : Nat := 118140960795 + 1432264 * 2 ^ 59
def prefixEnd_1432264 : Nat := 4983230072969 + 3 ^ 40 * 1432264 * 2
def baseEnd_1432264 : Nat := 108954052760191036179725

theorem tailTrace_1432264 : CollatzResearch.WordTrace tailWord_1432264 prefixEnd_1432264 108954052760191036179725 := by
  unfold tailWord_1432264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26119479841579807030907923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34825973122106409374543897 26119479841579807030907923)
  ·
    refine ⟨39179219762369710546361885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26119479841579807030907923 39179219762369710546361885)
    ·
      refine ⟨14692207410888641454885707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39179219762369710546361885 14692207410888641454885707)
      ·
        refine ⟨22038311116332962182328561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14692207410888641454885707 22038311116332962182328561)
        ·
          refine ⟨16528733337249721636746421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22038311116332962182328561 16528733337249721636746421)
          ·
            refine ⟨1549568750367161403444977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16528733337249721636746421 1549568750367161403444977)
            ·
              refine ⟨1162176562775371052583733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549568750367161403444977 1162176562775371052583733)
              ·
                refine ⟨108954052760191036179725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1162176562775371052583733 108954052760191036179725)
                ·
                  rfl

theorem cell21_1432264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_1432264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432264 prefixEnd_1432264 := by exact prefixLift 1432264
  have htrace : WordTrace (prefixWord ++ tailWord_1432264) baseStart_1432264 baseEnd_1432264 := by
    simpa [prefixWord, tailWord_1432264, baseEnd_1432264] using wordTrace_append hprefix tailTrace_1432264
  have hstable : (prefixWord ++ tailWord_1432264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432264).length < 2 ^ (prefixWord ++ tailWord_1432264).sum := by decide
  have hdescent : baseEnd_1432264 < baseStart_1432264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432292 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1432292 : Nat := 118140960795 + 1432292 * 2 ^ 59
def prefixEnd_1432292 : Nat := 4983230072969 + 3 ^ 40 * 1432292 * 2
def baseEnd_1432292 : Nat := 326868548262051282072451

theorem tailTrace_1432292 : CollatzResearch.WordTrace tailWord_1432292 prefixEnd_1432292 326868548262051282072451 := by
  unfold tailWord_1432292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26119990463529087421917565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34826653951372116562556753 26119990463529087421917565)
  ·
    refine ⟨9794996423823407783219087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26119990463529087421917565 9794996423823407783219087)
    ·
      refine ⟨14692494635735111674828631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9794996423823407783219087 14692494635735111674828631)
      ·
        refine ⟨22038741953602667512242947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14692494635735111674828631 22038741953602667512242947)
        ·
          refine ⟨33058112930404001268364421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22038741953602667512242947 33058112930404001268364421)
          ·
            refine ⟨6198396174450750237818329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33058112930404001268364421 6198396174450750237818329)
            ·
              refine ⟨4648797130838062678363747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198396174450750237818329 4648797130838062678363747)
              ·
                refine ⟨6973195696257094017545621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648797130838062678363747 6973195696257094017545621)
                ·
                  refine ⟨326868548262051282072451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6973195696257094017545621 326868548262051282072451)
                  ·
                    rfl

theorem cell21_1432292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1432292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432292 prefixEnd_1432292 := by exact prefixLift 1432292
  have htrace : WordTrace (prefixWord ++ tailWord_1432292) baseStart_1432292 baseEnd_1432292 := by
    simpa [prefixWord, tailWord_1432292, baseEnd_1432292] using wordTrace_append hprefix tailTrace_1432292
  have hstable : (prefixWord ++ tailWord_1432292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432292).length < 2 ^ (prefixWord ++ tailWord_1432292).sum := by decide
  have hdescent : baseEnd_1432292 < baseStart_1432292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432450 : List Nat := [3, 4, 2, 2, 2, 1, 7]
def baseStart_1432450 : Nat := 118140960795 + 1432450 * 2 ^ 59
def prefixEnd_1432450 : Nat := 4983230072969 + 3 ^ 40 * 1432450 * 2
def baseEnd_1432450 : Nat := 36322734001630902048755

theorem tailTrace_1432450 : CollatzResearch.WordTrace tailWord_1432450 prefixEnd_1432450 36322734001630902048755 := by
  unfold tailWord_1432450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061435915121441957021701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34830495773657178552057869 13061435915121441957021701)
  ·
    refine ⟨2449019234085270366941569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13061435915121441957021701 2449019234085270366941569)
    ·
      refine ⟨1836764425563952775206177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449019234085270366941569 1836764425563952775206177)
      ·
        refine ⟨1377573319172964581404633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1836764425563952775206177 1377573319172964581404633)
        ·
          refine ⟨1033179989379723436053475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377573319172964581404633 1033179989379723436053475)
          ·
            refine ⟨1549769984069585154080213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033179989379723436053475 1549769984069585154080213)
            ·
              refine ⟨36322734001630902048755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1549769984069585154080213 36322734001630902048755)
              ·
                rfl

theorem cell21_1432450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 7].length) (baseStart_1432450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432450 prefixEnd_1432450 := by exact prefixLift 1432450
  have htrace : WordTrace (prefixWord ++ tailWord_1432450) baseStart_1432450 baseEnd_1432450 := by
    simpa [prefixWord, tailWord_1432450, baseEnd_1432450] using wordTrace_append hprefix tailTrace_1432450
  have hstable : (prefixWord ++ tailWord_1432450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432450).length < 2 ^ (prefixWord ++ tailWord_1432450).sum := by decide
  have hdescent : baseEnd_1432450 < baseStart_1432450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432503 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_1432503 : Nat := 118140960795 + 1432503 * 2 ^ 59
def prefixEnd_1432503 : Nat := 4983230072969 + 3 ^ 40 * 1432503 * 2
def baseEnd_1432503 : Nat := 326916701336761804055353

theorem tailTrace_1432503 : CollatzResearch.WordTrace tailWord_1432503 prefixEnd_1432503 326916701336761804055353 := by
  unfold tailWord_1432503
  simp only [CollatzResearch.WordTrace]
  refine ⟨52247676729293757879766163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34831784486195838586510775 52247676729293757879766163)
  ·
    refine ⟨78371515093940636819649245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52247676729293757879766163 78371515093940636819649245)
    ·
      refine ⟨29389318160227738807368467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78371515093940636819649245 29389318160227738807368467)
      ·
        refine ⟨44083977240341608211052701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29389318160227738807368467 44083977240341608211052701)
        ·
          refine ⟨16531491465128103079144763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44083977240341608211052701 16531491465128103079144763)
          ·
            refine ⟨24797237197692154618717145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16531491465128103079144763 24797237197692154618717145)
            ·
              refine ⟨18597927898269115964037859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24797237197692154618717145 18597927898269115964037859)
              ·
                refine ⟨27896891847403673946056789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597927898269115964037859 27896891847403673946056789)
                ·
                  refine ⟨326916701336761804055353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27896891847403673946056789 326916701336761804055353)
                  ·
                    rfl

theorem cell21_1432503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_1432503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432503 prefixEnd_1432503 := by exact prefixLift 1432503
  have htrace : WordTrace (prefixWord ++ tailWord_1432503) baseStart_1432503 baseEnd_1432503 := by
    simpa [prefixWord, tailWord_1432503, baseEnd_1432503] using wordTrace_append hprefix tailTrace_1432503
  have hstable : (prefixWord ++ tailWord_1432503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432503).length < 2 ^ (prefixWord ++ tailWord_1432503).sum := by decide
  have hdescent : baseEnd_1432503 < baseStart_1432503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432506 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1432506 : Nat := 118140960795 + 1432506 * 2 ^ 59
def prefixEnd_1432506 : Nat := 4983230072969 + 3 ^ 40 * 1432506 * 2
def baseEnd_1432506 : Nat := 326917385977634465505347

theorem tailTrace_1432506 : CollatzResearch.WordTrace tailWord_1432506 prefixEnd_1432506 326917385977634465505347 := by
  unfold tailWord_1432506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061946537070722348031343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34831857432188592928083581 13061946537070722348031343)
  ·
    refine ⟨19592919805606083522047015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13061946537070722348031343 19592919805606083522047015)
    ·
      refine ⟨29389379708409125283070523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19592919805606083522047015 29389379708409125283070523)
      ·
        refine ⟨44084069562613687924605785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29389379708409125283070523 44084069562613687924605785)
        ·
          refine ⟨33063052171960265943454339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44084069562613687924605785 33063052171960265943454339)
          ·
            refine ⟨49594578257940398915181509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33063052171960265943454339 49594578257940398915181509)
            ·
              refine ⟨9298983423363824796596533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49594578257940398915181509 9298983423363824796596533)
              ·
                refine ⟨871779695940358574680925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9298983423363824796596533 871779695940358574680925)
                ·
                  refine ⟨326917385977634465505347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871779695940358574680925 326917385977634465505347)
                  ·
                    rfl

theorem cell21_1432506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1432506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432506 prefixEnd_1432506 := by exact prefixLift 1432506
  have htrace : WordTrace (prefixWord ++ tailWord_1432506) baseStart_1432506 baseEnd_1432506 := by
    simpa [prefixWord, tailWord_1432506, baseEnd_1432506] using wordTrace_append hprefix tailTrace_1432506
  have hstable : (prefixWord ++ tailWord_1432506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432506).length < 2 ^ (prefixWord ++ tailWord_1432506).sum := by decide
  have hdescent : baseEnd_1432506 < baseStart_1432506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432523 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 3]
def baseStart_1432523 : Nat := 118140960795 + 1432523 * 2 ^ 59
def prefixEnd_1432523 : Nat := 4983230072969 + 3 ^ 40 * 1432523 * 2
def baseEnd_1432523 : Nat := 326921265609246213721979

theorem tailTrace_1432523 : CollatzResearch.WordTrace tailWord_1432523 prefixEnd_1432523 326921265609246213721979 := by
  unfold tailWord_1432523
  simp only [CollatzResearch.WordTrace]
  refine ⟨52248406189221301295494223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34832270792814200863662815 52248406189221301295494223)
  ·
    refine ⟨78372609283831951943241335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52248406189221301295494223 78372609283831951943241335)
    ·
      refine ⟨117558913925747927914862003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78372609283831951943241335 117558913925747927914862003)
      ·
        refine ⟨176338370888621891872293005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117558913925747927914862003 176338370888621891872293005)
        ·
          refine ⟨66126889083233209452109877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176338370888621891872293005 66126889083233209452109877)
          ·
            refine ⟨6199395851553113386135301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66126889083233209452109877 6199395851553113386135301)
            ·
              refine ⟨1162386722166208759900369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6199395851553113386135301 1162386722166208759900369)
              ·
                refine ⟨871790041624656569925277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162386722166208759900369 871790041624656569925277)
                ·
                  refine ⟨326921265609246213721979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871790041624656569925277 326921265609246213721979)
                  ·
                    rfl

theorem cell21_1432523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].length) (baseStart_1432523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432523 prefixEnd_1432523 := by exact prefixLift 1432523
  have htrace : WordTrace (prefixWord ++ tailWord_1432523) baseStart_1432523 baseEnd_1432523 := by
    simpa [prefixWord, tailWord_1432523, baseEnd_1432523] using wordTrace_append hprefix tailTrace_1432523
  have hstable : (prefixWord ++ tailWord_1432523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432523).length < 2 ^ (prefixWord ++ tailWord_1432523).sum := by decide
  have hdescent : baseEnd_1432523 < baseStart_1432523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432686 : List Nat := [4, 1, 2, 2, 1, 11]
def baseStart_1432686 : Nat := 118140960795 + 1432686 * 2 ^ 59
def prefixEnd_1432686 : Nat := 4983230072969 + 3 ^ 40 * 1432686 * 2
def baseEnd_1432686 : Nat := 12109572756666450092777

theorem tailTrace_1432686 : CollatzResearch.WordTrace tailWord_1432686 prefixEnd_1432686 12109572756666450092777 := by
  unfold tailWord_1432686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531793910953847516709739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34836234191753853422451941 6531793910953847516709739)
  ·
    refine ⟨9797690866430771275064609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6531793910953847516709739 9797690866430771275064609)
    ·
      refine ⟨7348268149823078456298457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9797690866430771275064609 7348268149823078456298457)
      ·
        refine ⟨5511201112367308842223843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7348268149823078456298457 5511201112367308842223843)
        ·
          refine ⟨8266801668550963263335765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511201112367308842223843 8266801668550963263335765)
          ·
            refine ⟨12109572756666450092777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8266801668550963263335765 12109572756666450092777)
            ·
              rfl

theorem cell21_1432686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 11].length) (baseStart_1432686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432686 prefixEnd_1432686 := by exact prefixLift 1432686
  have htrace : WordTrace (prefixWord ++ tailWord_1432686) baseStart_1432686 baseEnd_1432686 := by
    simpa [prefixWord, tailWord_1432686, baseEnd_1432686] using wordTrace_append hprefix tailTrace_1432686
  have hstable : (prefixWord ++ tailWord_1432686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432686).length < 2 ^ (prefixWord ++ tailWord_1432686).sum := by decide
  have hdescent : baseEnd_1432686 < baseStart_1432686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432810 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1432810 : Nat := 118140960795 + 1432810 * 2 ^ 59
def prefixEnd_1432810 : Nat := 4983230072969 + 3 ^ 40 * 1432810 * 2
def baseEnd_1432810 : Nat := 326986762919397492438059

theorem tailTrace_1432810 : CollatzResearch.WordTrace tailWord_1432810 prefixEnd_1432810 326986762919397492438059 := by
  unfold tailWord_1432810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064718484795387327797971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34839249292787699540794589 13064718484795387327797971)
  ·
    refine ⟨19597077727193080991696957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13064718484795387327797971 19597077727193080991696957)
    ·
      refine ⟨7348904147697405371886359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19597077727193080991696957 7348904147697405371886359)
      ·
        refine ⟨11023356221546108057829539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348904147697405371886359 11023356221546108057829539)
        ·
          refine ⟨16535034332319162086744309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023356221546108057829539 16535034332319162086744309)
          ·
            refine ⟨1550159468654921445632279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16535034332319162086744309 1550159468654921445632279)
            ·
              refine ⟨2325239202982382168448419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550159468654921445632279 2325239202982382168448419)
              ·
                refine ⟨3487858804473573252672629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325239202982382168448419 3487858804473573252672629)
                ·
                  refine ⟨326986762919397492438059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3487858804473573252672629 326986762919397492438059)
                  ·
                    rfl

theorem cell21_1432810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1432810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432810 prefixEnd_1432810 := by exact prefixLift 1432810
  have htrace : WordTrace (prefixWord ++ tailWord_1432810) baseStart_1432810 baseEnd_1432810 := by
    simpa [prefixWord, tailWord_1432810, baseEnd_1432810] using wordTrace_append hprefix tailTrace_1432810
  have hstable : (prefixWord ++ tailWord_1432810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432810).length < 2 ^ (prefixWord ++ tailWord_1432810).sum := by decide
  have hdescent : baseEnd_1432810 < baseStart_1432810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1432917 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1432917 : Nat := 118140960795 + 1432917 * 2 ^ 59
def prefixEnd_1432917 : Nat := 4983230072969 + 3 ^ 40 * 1432917 * 2
def baseEnd_1432917 : Nat := 327011181777189084154507

theorem tailTrace_1432917 : CollatzResearch.WordTrace tailWord_1432917 prefixEnd_1432917 327011181777189084154507 := by
  unfold tailWord_1432917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52262776549793906585337005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34841851033195937723558003 52262776549793906585337005)
  ·
    refine ⟨19598541206172714969501377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52262776549793906585337005 19598541206172714969501377)
    ·
      refine ⟨14698905904629536227126033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19598541206172714969501377 14698905904629536227126033)
      ·
        refine ⟨11024179428472152170344525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14698905904629536227126033 11024179428472152170344525)
        ·
          refine ⟨4134067285677057063879197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11024179428472152170344525 4134067285677057063879197)
          ·
            refine ⟨1550275232128896398954699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4134067285677057063879197 1550275232128896398954699)
            ·
              refine ⟨2325412848193344598432049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550275232128896398954699 2325412848193344598432049)
              ·
                refine ⟨1744059636145008448824037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325412848193344598432049 1744059636145008448824037)
                ·
                  refine ⟨327011181777189084154507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744059636145008448824037 327011181777189084154507)
                  ·
                    rfl

theorem cell21_1432917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1432917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1432917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1432917 prefixEnd_1432917 := by exact prefixLift 1432917
  have htrace : WordTrace (prefixWord ++ tailWord_1432917) baseStart_1432917 baseEnd_1432917 := by
    simpa [prefixWord, tailWord_1432917, baseEnd_1432917] using wordTrace_append hprefix tailTrace_1432917
  have hstable : (prefixWord ++ tailWord_1432917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1432917).length < 2 ^ (prefixWord ++ tailWord_1432917).sum := by decide
  have hdescent : baseEnd_1432917 < baseStart_1432917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1432917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433004 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1433004 : Nat := 118140960795 + 1433004 * 2 ^ 59
def prefixEnd_1433004 : Nat := 4983230072969 + 3 ^ 40 * 1433004 * 2
def baseEnd_1433004 : Nat := 327031036362496266204329

theorem tailTrace_1433004 : CollatzResearch.WordTrace tailWord_1433004 prefixEnd_1433004 327031036362496266204329 := by
  unfold tailWord_1433004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26132974850239360221877033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34843966466985813629169377 26132974850239360221877033)
  ·
    refine ⟨19599731137679520166407775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26132974850239360221877033 19599731137679520166407775)
    ·
      refine ⟨29399596706519280249611663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19599731137679520166407775 29399596706519280249611663)
      ·
        refine ⟨44099395059778920374417495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29399596706519280249611663 44099395059778920374417495)
        ·
          refine ⟨66149092589668380561626243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44099395059778920374417495 66149092589668380561626243)
          ·
            refine ⟨99223638884502570842439365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66149092589668380561626243 99223638884502570842439365)
            ·
              refine ⟨18604432290844232032957381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99223638884502570842439365 18604432290844232032957381)
              ·
                refine ⟨3488331054533293506179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18604432290844232032957381 3488331054533293506179509)
                ·
                  refine ⟨327031036362496266204329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488331054533293506179509 327031036362496266204329)
                  ·
                    rfl

theorem cell21_1433004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1433004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433004 prefixEnd_1433004 := by exact prefixLift 1433004
  have htrace : WordTrace (prefixWord ++ tailWord_1433004) baseStart_1433004 baseEnd_1433004 := by
    simpa [prefixWord, tailWord_1433004, baseEnd_1433004] using wordTrace_append hprefix tailTrace_1433004
  have hstable : (prefixWord ++ tailWord_1433004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433004).length < 2 ^ (prefixWord ++ tailWord_1433004).sum := by decide
  have hdescent : baseEnd_1433004 < baseStart_1433004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433035 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_1433035 : Nat := 118140960795 + 1433035 * 2 ^ 59
def prefixEnd_1433035 : Nat := 4983230072969 + 3 ^ 40 * 1433035 * 2
def baseEnd_1433035 : Nat := 327038110984847101187599

theorem tailTrace_1433035 : CollatzResearch.WordTrace tailWord_1433035 prefixEnd_1433035 327038110984847101187599 := by
  unfold tailWord_1433035
  simp only [CollatzResearch.WordTrace]
  refine ⟨52267080363366412738132559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34844720242244275158755039 52267080363366412738132559)
  ·
    refine ⟨78400620545049619107198839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52267080363366412738132559 78400620545049619107198839)
    ·
      refine ⟨117600930817574428660798259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78400620545049619107198839 117600930817574428660798259)
      ·
        refine ⟨176401396226361642991197389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117600930817574428660798259 176401396226361642991197389)
        ·
          refine ⟨66150523584885616121699021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176401396226361642991197389 66150523584885616121699021)
          ·
            refine ⟨24806446344332106045637133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66150523584885616121699021 24806446344332106045637133)
            ·
              refine ⟨9302417379124539767113925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24806446344332106045637133 9302417379124539767113925)
              ·
                refine ⟨1744203258585851206333861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9302417379124539767113925 1744203258585851206333861)
                ·
                  refine ⟨327038110984847101187599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744203258585851206333861 327038110984847101187599)
                  ·
                    rfl

theorem cell21_1433035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_1433035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433035 prefixEnd_1433035 := by exact prefixLift 1433035
  have htrace : WordTrace (prefixWord ++ tailWord_1433035) baseStart_1433035 baseEnd_1433035 := by
    simpa [prefixWord, tailWord_1433035, baseEnd_1433035] using wordTrace_append hprefix tailTrace_1433035
  have hstable : (prefixWord ++ tailWord_1433035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433035).length < 2 ^ (prefixWord ++ tailWord_1433035).sum := by decide
  have hdescent : baseEnd_1433035 < baseStart_1433035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433097 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 3]
def baseStart_1433097 : Nat := 118140960795 + 1433097 * 2 ^ 59
def prefixEnd_1433097 : Nat := 4983230072969 + 3 ^ 40 * 1433097 * 2
def baseEnd_1433097 : Nat := 327052260229548771154139

theorem tailTrace_1433097 : CollatzResearch.WordTrace tailWord_1433097 prefixEnd_1433097 327052260229548771154139 := by
  unfold tailWord_1433097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52269341689141797326889545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34846227792761198217926363 52269341689141797326889545)
  ·
    refine ⟨39202006266856347995167159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52269341689141797326889545 39202006266856347995167159)
    ·
      refine ⟨58803009400284521992750739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39202006266856347995167159 58803009400284521992750739)
      ·
        refine ⟨88204514100426782989126109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58803009400284521992750739 88204514100426782989126109)
        ·
          refine ⟨33076692787660043620922291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88204514100426782989126109 33076692787660043620922291)
          ·
            refine ⟨49615039181490065431383437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33076692787660043620922291 49615039181490065431383437)
            ·
              refine ⟨18605639693058774536768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49615039181490065431383437 18605639693058774536768789)
              ·
                refine ⟨872139360612130056411037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18605639693058774536768789 872139360612130056411037)
                ·
                  refine ⟨327052260229548771154139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872139360612130056411037 327052260229548771154139)
                  ·
                    rfl

theorem cell21_1433097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_1433097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433097 prefixEnd_1433097 := by exact prefixLift 1433097
  have htrace : WordTrace (prefixWord ++ tailWord_1433097) baseStart_1433097 baseEnd_1433097 := by
    simpa [prefixWord, tailWord_1433097, baseEnd_1433097] using wordTrace_append hprefix tailTrace_1433097
  have hstable : (prefixWord ++ tailWord_1433097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433097).length < 2 ^ (prefixWord ++ tailWord_1433097).sum := by decide
  have hdescent : baseEnd_1433097 < baseStart_1433097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433277 : List Nat := [1, 4, 1, 2, 1, 2, 2, 8]
def baseStart_1433277 : Nat := 118140960795 + 1433277 * 2 ^ 59
def prefixEnd_1433277 : Nat := 4983230072969 + 3 ^ 40 * 1433277 * 2
def baseEnd_1433277 : Nat := 109031112893969486051257

theorem tailTrace_1433277 : CollatzResearch.WordTrace tailWord_1433277 prefixEnd_1433277 109031112893969486051257 := by
  unfold tailWord_1433277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52275906828489688068442085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34850604552326458712294723 52275906828489688068442085)
  ·
    refine ⟨9801732530341816512832891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52275906828489688068442085 9801732530341816512832891)
    ·
      refine ⟨14702598795512724769249337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9801732530341816512832891 14702598795512724769249337)
      ·
        refine ⟨11026949096634543576937003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14702598795512724769249337 11026949096634543576937003)
        ·
          refine ⟨16540423644951815365405505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026949096634543576937003 16540423644951815365405505)
          ·
            refine ⟨12405317733713861524054129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16540423644951815365405505 12405317733713861524054129)
            ·
              refine ⟨9303988300285396143040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12405317733713861524054129 9303988300285396143040597)
              ·
                refine ⟨109031112893969486051257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9303988300285396143040597 109031112893969486051257)
                ·
                  rfl

theorem cell21_1433277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_1433277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433277 prefixEnd_1433277 := by exact prefixLift 1433277
  have htrace : WordTrace (prefixWord ++ tailWord_1433277) baseStart_1433277 baseEnd_1433277 := by
    simpa [prefixWord, tailWord_1433277, baseEnd_1433277] using wordTrace_append hprefix tailTrace_1433277
  have hstable : (prefixWord ++ tailWord_1433277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433277).length < 2 ^ (prefixWord ++ tailWord_1433277).sum := by decide
  have hdescent : baseEnd_1433277 < baseStart_1433277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433280 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1433280 : Nat := 118140960795 + 1433280 * 2 ^ 59
def prefixEnd_1433280 : Nat := 4983230072969 + 3 ^ 40 * 1433280 * 2
def baseEnd_1433280 : Nat := 327094023322781119603765

theorem tailTrace_1433280 : CollatzResearch.WordTrace tailWord_1433280 prefixEnd_1433280 327094023322781119603765 := by
  unfold tailWord_1433280
  simp only [CollatzResearch.WordTrace]
  refine ⟨26138008123739409790400647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34850677498319213053867529 26138008123739409790400647)
  ·
    refine ⟨39207012185609114685600971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26138008123739409790400647 39207012185609114685600971)
    ·
      refine ⟨58810518278413672028401457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39207012185609114685600971 58810518278413672028401457)
      ·
        refine ⟨44107888708810254021301093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58810518278413672028401457 44107888708810254021301093)
        ·
          refine ⟨8270229132901922628993955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44107888708810254021301093 8270229132901922628993955)
          ·
            refine ⟨12405343699352883943490933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270229132901922628993955 12405343699352883943490933)
            ·
              refine ⟨1163000971814332869702275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12405343699352883943490933 1163000971814332869702275)
              ·
                refine ⟨1744501457721499304553413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163000971814332869702275 1744501457721499304553413)
                ·
                  refine ⟨327094023322781119603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744501457721499304553413 327094023322781119603765)
                  ·
                    rfl

theorem cell21_1433280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1433280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433280 prefixEnd_1433280 := by exact prefixLift 1433280
  have htrace : WordTrace (prefixWord ++ tailWord_1433280) baseStart_1433280 baseEnd_1433280 := by
    simpa [prefixWord, tailWord_1433280, baseEnd_1433280] using wordTrace_append hprefix tailTrace_1433280
  have hstable : (prefixWord ++ tailWord_1433280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433280).length < 2 ^ (prefixWord ++ tailWord_1433280).sum := by decide
  have hdescent : baseEnd_1433280 < baseStart_1433280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433325 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1433325 : Nat := 118140960795 + 1433325 * 2 ^ 59
def prefixEnd_1433325 : Nat := 4983230072969 + 3 ^ 40 * 1433325 * 2
def baseEnd_1433325 : Nat := 327104292935871041353673

theorem tailTrace_1433325 : CollatzResearch.WordTrace tailWord_1433325 prefixEnd_1433325 327104292935871041353673 := by
  unfold tailWord_1433325
  simp only [CollatzResearch.WordTrace]
  refine ⟨52277657532315792266189429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34851771688210528177459619 52277657532315792266189429)
  ·
    refine ⟨4901030393654605524955259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52277657532315792266189429 4901030393654605524955259)
    ·
      refine ⟨7351545590481908287432889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901030393654605524955259 7351545590481908287432889)
      ·
        refine ⟨5513659192861431215574667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7351545590481908287432889 5513659192861431215574667)
        ·
          refine ⟨8270488789292146823362001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513659192861431215574667 8270488789292146823362001)
          ·
            refine ⟨6202866591969110117521501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8270488789292146823362001 6202866591969110117521501)
            ·
              refine ⟨2326074971988416294070563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6202866591969110117521501 2326074971988416294070563)
              ·
                refine ⟨3489112457982624441105845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326074971988416294070563 3489112457982624441105845)
                ·
                  refine ⟨327104292935871041353673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3489112457982624441105845 327104292935871041353673)
                  ·
                    rfl

theorem cell21_1433325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1433325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433325 prefixEnd_1433325 := by exact prefixLift 1433325
  have htrace : WordTrace (prefixWord ++ tailWord_1433325) baseStart_1433325 baseEnd_1433325 := by
    simpa [prefixWord, tailWord_1433325, baseEnd_1433325] using wordTrace_append hprefix tailTrace_1433325
  have hstable : (prefixWord ++ tailWord_1433325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433325).length < 2 ^ (prefixWord ++ tailWord_1433325).sum := by decide
  have hdescent : baseEnd_1433325 < baseStart_1433325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433429 : List Nat := [1, 3, 2, 2, 2, 3, 8]
def baseStart_1433429 : Nat := 118140960795 + 1433429 * 2 ^ 59
def prefixEnd_1433429 : Nat := 4983230072969 + 3 ^ 40 * 1433429 * 2
def baseEnd_1433429 : Nat := 36347558572532219068903

theorem tailTrace_1433429 : CollatzResearch.WordTrace tailWord_1433429 prefixEnd_1433429 36347558572532219068903 := by
  unfold tailWord_1433429
  simp only [CollatzResearch.WordTrace]
  refine ⟨52281450723939018027975341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34854300482626012018650227 52281450723939018027975341)
  ·
    refine ⟨19605544021477131760490753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52281450723939018027975341 19605544021477131760490753)
    ·
      refine ⟨14704158016107848820368065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19605544021477131760490753 14704158016107848820368065)
      ·
        refine ⟨11028118512080886615276049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14704158016107848820368065 11028118512080886615276049)
        ·
          refine ⟨8271088884060664961457037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11028118512080886615276049 8271088884060664961457037)
          ·
            refine ⟨3101658331522749360546389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8271088884060664961457037 3101658331522749360546389)
            ·
              refine ⟨36347558572532219068903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3101658331522749360546389 36347558572532219068903)
              ·
                rfl

theorem cell21_1433429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 8].length) (baseStart_1433429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433429 prefixEnd_1433429 := by exact prefixLift 1433429
  have htrace : WordTrace (prefixWord ++ tailWord_1433429) baseStart_1433429 baseEnd_1433429 := by
    simpa [prefixWord, tailWord_1433429, baseEnd_1433429] using wordTrace_append hprefix tailTrace_1433429
  have hstable : (prefixWord ++ tailWord_1433429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433429).length < 2 ^ (prefixWord ++ tailWord_1433429).sum := by decide
  have hdescent : baseEnd_1433429 < baseStart_1433429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433508 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1433508 : Nat := 118140960795 + 1433508 * 2 ^ 59
def prefixEnd_1433508 : Nat := 4983230072969 + 3 ^ 40 * 1433508 * 2
def baseEnd_1433508 : Nat := 327146056029103389803299

theorem tailTrace_1433508 : CollatzResearch.WordTrace tailWord_1433508 prefixEnd_1433508 327146056029103389803299 := by
  unfold tailWord_1433508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142166045326407260050589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34856221393768543013400785 26142166045326407260050589)
  ·
    refine ⟨9803312266997402722518971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26142166045326407260050589 9803312266997402722518971)
    ·
      refine ⟨14704968400496104083778457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9803312266997402722518971 14704968400496104083778457)
      ·
        refine ⟨11028726300372078062833843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14704968400496104083778457 11028726300372078062833843)
        ·
          refine ⟨16543089450558117094250765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028726300372078062833843 16543089450558117094250765)
          ·
            refine ⟨6203658543959293910344037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16543089450558117094250765 6203658543959293910344037)
            ·
              refine ⟨1163185976992367608189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6203658543959293910344037 1163185976992367608189507)
              ·
                refine ⟨1744778965488551412284261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163185976992367608189507 1744778965488551412284261)
                ·
                  refine ⟨327146056029103389803299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744778965488551412284261 327146056029103389803299)
                  ·
                    rfl

theorem cell21_1433508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1433508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433508 prefixEnd_1433508 := by exact prefixLift 1433508
  have htrace : WordTrace (prefixWord ++ tailWord_1433508) baseStart_1433508 baseEnd_1433508 := by
    simpa [prefixWord, tailWord_1433508, baseEnd_1433508] using wordTrace_append hprefix tailTrace_1433508
  have hstable : (prefixWord ++ tailWord_1433508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433508).length < 2 ^ (prefixWord ++ tailWord_1433508).sum := by decide
  have hdescent : baseEnd_1433508 < baseStart_1433508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433519 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_1433519 : Nat := 118140960795 + 1433519 * 2 ^ 59
def prefixEnd_1433519 : Nat := 4983230072969 + 3 ^ 40 * 1433519 * 2
def baseEnd_1433519 : Nat := 327148566378969815119943

theorem tailTrace_1433519 : CollatzResearch.WordTrace tailWord_1433519 prefixEnd_1433519 327148566378969815119943 := by
  unfold tailWord_1433519
  simp only [CollatzResearch.WordTrace]
  refine ⟨52284733293612963398751611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34856488862408642265834407 52284733293612963398751611)
  ·
    refine ⟨78427099940419445098127417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52284733293612963398751611 78427099940419445098127417)
    ·
      refine ⟨58820324955314583823595563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78427099940419445098127417 58820324955314583823595563)
      ·
        refine ⟨88230487432971875735393345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58820324955314583823595563 88230487432971875735393345)
        ·
          refine ⟨66172865574728906801545009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88230487432971875735393345 66172865574728906801545009)
          ·
            refine ⟨49629649181046680101158757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66172865574728906801545009 49629649181046680101158757)
            ·
              refine ⟨9305559221446252518967267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49629649181046680101158757 9305559221446252518967267)
              ·
                refine ⟨13958338832169378778450901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9305559221446252518967267 13958338832169378778450901)
                ·
                  refine ⟨327148566378969815119943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13958338832169378778450901 327148566378969815119943)
                  ·
                    rfl

theorem cell21_1433519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_1433519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433519 prefixEnd_1433519 := by exact prefixLift 1433519
  have htrace : WordTrace (prefixWord ++ tailWord_1433519) baseStart_1433519 baseEnd_1433519 := by
    simpa [prefixWord, tailWord_1433519, baseEnd_1433519] using wordTrace_append hprefix tailTrace_1433519
  have hstable : (prefixWord ++ tailWord_1433519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433519).length < 2 ^ (prefixWord ++ tailWord_1433519).sum := by decide
  have hdescent : baseEnd_1433519 < baseStart_1433519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433567 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_1433567 : Nat := 118140960795 + 1433567 * 2 ^ 59
def prefixEnd_1433567 : Nat := 4983230072969 + 3 ^ 40 * 1433567 * 2
def baseEnd_1433567 : Nat := 327159520632932398319845

theorem tailTrace_1433567 : CollatzResearch.WordTrace tailWord_1433567 prefixEnd_1433567 327159520632932398319845 := by
  unfold tailWord_1433567
  simp only [CollatzResearch.WordTrace]
  refine ⟨52286483997439067596498955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34857655998292711730999303 52286483997439067596498955)
  ·
    refine ⟨78429725996158601394748433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52286483997439067596498955 78429725996158601394748433)
    ·
      refine ⟨58822294497118951046061325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78429725996158601394748433 58822294497118951046061325)
      ·
        refine ⟨22058360436419606642272997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58822294497118951046061325 22058360436419606642272997)
        ·
          refine ⟨4135942581828676245426187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22058360436419606642272997 4135942581828676245426187)
          ·
            refine ⟨6203913872743014368139281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135942581828676245426187 6203913872743014368139281)
            ·
              refine ⟨4652935404557260776104461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203913872743014368139281 4652935404557260776104461)
              ·
                refine ⟨1744850776708972791039173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4652935404557260776104461 1744850776708972791039173)
                ·
                  refine ⟨327159520632932398319845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744850776708972791039173 327159520632932398319845)
                  ·
                    rfl

theorem cell21_1433567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_1433567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433567 prefixEnd_1433567 := by exact prefixLift 1433567
  have htrace : WordTrace (prefixWord ++ tailWord_1433567) baseStart_1433567 baseEnd_1433567 := by
    simpa [prefixWord, tailWord_1433567, baseEnd_1433567] using wordTrace_append hprefix tailTrace_1433567
  have hstable : (prefixWord ++ tailWord_1433567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433567).length < 2 ^ (prefixWord ++ tailWord_1433567).sum := by decide
  have hdescent : baseEnd_1433567 < baseStart_1433567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433570 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1433570 : Nat := 118140960795 + 1433570 * 2 ^ 59
def prefixEnd_1433570 : Nat := 4983230072969 + 3 ^ 40 * 1433570 * 2
def baseEnd_1433570 : Nat := 327160205273805059769839

theorem tailTrace_1433570 : CollatzResearch.WordTrace tailWord_1433570 prefixEnd_1433570 327160205273805059769839 := by
  unfold tailWord_1433570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071648354107049777214541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34857728944285466072572109 13071648354107049777214541)
  ·
    refine ⟨4901868132790143666455453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13071648354107049777214541 4901868132790143666455453)
    ·
      refine ⟨1838200549796303874920795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4901868132790143666455453 1838200549796303874920795)
      ·
        refine ⟨2757300824694455812381193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838200549796303874920795 2757300824694455812381193)
        ·
          refine ⟨2067975618520841859285895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757300824694455812381193 2067975618520841859285895)
          ·
            refine ⟨3101963427781262788928843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067975618520841859285895 3101963427781262788928843)
            ·
              refine ⟨4652945141671894183393265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101963427781262788928843 4652945141671894183393265)
              ·
                refine ⟨3489708856253920637544949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652945141671894183393265 3489708856253920637544949)
                ·
                  refine ⟨327160205273805059769839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3489708856253920637544949 327160205273805059769839)
                  ·
                    rfl

theorem cell21_1433570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1433570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433570 prefixEnd_1433570 := by exact prefixLift 1433570
  have htrace : WordTrace (prefixWord ++ tailWord_1433570) baseStart_1433570 baseEnd_1433570 := by
    simpa [prefixWord, tailWord_1433570, baseEnd_1433570] using wordTrace_append hprefix tailTrace_1433570
  have hstable : (prefixWord ++ tailWord_1433570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433570).length < 2 ^ (prefixWord ++ tailWord_1433570).sum := by decide
  have hdescent : baseEnd_1433570 < baseStart_1433570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433598 : List Nat := [4, 2, 2, 2, 1, 2, 8]
def baseStart_1433598 : Nat := 118140960795 + 1433598 * 2 ^ 59
def prefixEnd_1433598 : Nat := 4983230072969 + 3 ^ 40 * 1433598 * 2
def baseEnd_1433598 : Nat := 36351843917253692589235

theorem tailTrace_1433598 : CollatzResearch.WordTrace tailWord_1433598 prefixEnd_1433598 36351843917253692589235 := by
  unfold tailWord_1433598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535951832540844986359681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34858409773551173260584965 6535951832540844986359681)
  ·
    refine ⟨4901963874405633739769761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6535951832540844986359681 4901963874405633739769761)
    ·
      refine ⟨3676472905804225304827321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4901963874405633739769761 3676472905804225304827321)
      ·
        refine ⟨2757354679353168978620491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3676472905804225304827321 2757354679353168978620491)
        ·
          refine ⟨4136032019029753467930737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757354679353168978620491 4136032019029753467930737)
          ·
            refine ⟨3102024014272315100948053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4136032019029753467930737 3102024014272315100948053)
            ·
              refine ⟨36351843917253692589235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3102024014272315100948053 36351843917253692589235)
              ·
                rfl

theorem cell21_1433598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 8].length) (baseStart_1433598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433598 prefixEnd_1433598 := by exact prefixLift 1433598
  have htrace : WordTrace (prefixWord ++ tailWord_1433598) baseStart_1433598 baseEnd_1433598 := by
    simpa [prefixWord, tailWord_1433598, baseEnd_1433598] using wordTrace_append hprefix tailTrace_1433598
  have hstable : (prefixWord ++ tailWord_1433598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433598).length < 2 ^ (prefixWord ++ tailWord_1433598).sum := by decide
  have hdescent : baseEnd_1433598 < baseStart_1433598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433612 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1433612 : Nat := 118140960795 + 1433612 * 2 ^ 59
def prefixEnd_1433612 : Nat := 4983230072969 + 3 ^ 40 * 1433612 * 2
def baseEnd_1433612 : Nat := 327169790246022320069753

theorem tailTrace_1433612 : CollatzResearch.WordTrace tailWord_1433612 prefixEnd_1433612 327169790246022320069753 := by
  unfold tailWord_1433612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26144062641138020140943545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34858750188184026854591393 26144062641138020140943545)
  ·
    refine ⟨19608046980853515105707659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26144062641138020140943545 19608046980853515105707659)
    ·
      refine ⟨29412070471280272658561489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19608046980853515105707659 29412070471280272658561489)
      ·
        refine ⟨22059052853460204493921117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29412070471280272658561489 22059052853460204493921117)
        ·
          refine ⟨8272144820047576685220419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22059052853460204493921117 8272144820047576685220419)
          ·
            refine ⟨12408217230071365027830629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272144820047576685220419 12408217230071365027830629)
            ·
              refine ⟨2326540730638380942718243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12408217230071365027830629 2326540730638380942718243)
              ·
                refine ⟨3489811095957571414077365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326540730638380942718243 3489811095957571414077365)
                ·
                  refine ⟨327169790246022320069753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3489811095957571414077365 327169790246022320069753)
                  ·
                    rfl

theorem cell21_1433612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1433612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433612 prefixEnd_1433612 := by exact prefixLift 1433612
  have htrace : WordTrace (prefixWord ++ tailWord_1433612) baseStart_1433612 baseEnd_1433612 := by
    simpa [prefixWord, tailWord_1433612, baseEnd_1433612] using wordTrace_append hprefix tailTrace_1433612
  have hstable : (prefixWord ++ tailWord_1433612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433612).length < 2 ^ (prefixWord ++ tailWord_1433612).sum := by decide
  have hdescent : baseEnd_1433612 < baseStart_1433612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433646 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1433646 : Nat := 118140960795 + 1433646 * 2 ^ 59
def prefixEnd_1433646 : Nat := 4983230072969 + 3 ^ 40 * 1433646 * 2
def baseEnd_1433646 : Nat := 327177549509245816503017

theorem tailTrace_1433646 : CollatzResearch.WordTrace tailWord_1433646 prefixEnd_1433646 327177549509245816503017 := by
  unfold tailWord_1433646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536170670519108011078099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34859576909435242725749861 6536170670519108011078099)
  ·
    refine ⟨9804256005778662016617149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6536170670519108011078099 9804256005778662016617149)
    ·
      refine ⟨3676596002166998256231431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9804256005778662016617149 3676596002166998256231431)
      ·
        refine ⟨5514894003250497384347147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676596002166998256231431 5514894003250497384347147)
        ·
          refine ⟨8272341004875746076520721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514894003250497384347147 8272341004875746076520721)
          ·
            refine ⟨6204255753656809557390541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8272341004875746076520721 6204255753656809557390541)
            ·
              refine ⟨2326595907621303584021453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6204255753656809557390541 2326595907621303584021453)
              ·
                refine ⟨872473465357988844008045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326595907621303584021453 872473465357988844008045)
                ·
                  refine ⟨327177549509245816503017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872473465357988844008045 327177549509245816503017)
                  ·
                    rfl

theorem cell21_1433646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1433646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433646 prefixEnd_1433646 := by exact prefixLift 1433646
  have htrace : WordTrace (prefixWord ++ tailWord_1433646) baseStart_1433646 baseEnd_1433646 := by
    simpa [prefixWord, tailWord_1433646, baseEnd_1433646] using wordTrace_append hprefix tailTrace_1433646
  have hstable : (prefixWord ++ tailWord_1433646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433646).length < 2 ^ (prefixWord ++ tailWord_1433646).sum := by decide
  have hdescent : baseEnd_1433646 < baseStart_1433646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433719 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_1433719 : Nat := 118140960795 + 1433719 * 2 ^ 59
def prefixEnd_1433719 : Nat := 4983230072969 + 3 ^ 40 * 1433719 * 2
def baseEnd_1433719 : Nat := 327194209103813911786201

theorem tailTrace_1433719 : CollatzResearch.WordTrace tailWord_1433719 prefixEnd_1433719 327194209103813911786201 := by
  unfold tailWord_1433719
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292027892888397556032211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34861351928592265037354807 52292027892888397556032211)
  ·
    refine ⟨78438041839332596334048317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52292027892888397556032211 78438041839332596334048317)
    ·
      refine ⟨29414265689749723625268119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78438041839332596334048317 29414265689749723625268119)
      ·
        refine ⟨44121398534624585437902179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29414265689749723625268119 44121398534624585437902179)
        ·
          refine ⟨66182097801936878156853269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44121398534624585437902179 66182097801936878156853269)
          ·
            refine ⟨3102285834465791163602497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66182097801936878156853269 3102285834465791163602497)
            ·
              refine ⟨2326714375849343372701873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102285834465791163602497 2326714375849343372701873)
              ·
                refine ⟨1745035781887007529526405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326714375849343372701873 1745035781887007529526405)
                ·
                  refine ⟨327194209103813911786201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745035781887007529526405 327194209103813911786201)
                  ·
                    rfl

theorem cell21_1433719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_1433719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433719 prefixEnd_1433719 := by exact prefixLift 1433719
  have htrace : WordTrace (prefixWord ++ tailWord_1433719) baseStart_1433719 baseEnd_1433719 := by
    simpa [prefixWord, tailWord_1433719, baseEnd_1433719] using wordTrace_append hprefix tailTrace_1433719
  have hstable : (prefixWord ++ tailWord_1433719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433719).length < 2 ^ (prefixWord ++ tailWord_1433719).sum := by decide
  have hdescent : baseEnd_1433719 < baseStart_1433719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433733 : List Nat := [1, 3, 1, 1, 5, 1, 3, 6]
def baseStart_1433733 : Nat := 118140960795 + 1433733 * 2 ^ 59
def prefixEnd_1433733 : Nat := 4983230072969 + 3 ^ 40 * 1433733 * 2
def baseEnd_1433733 : Nat := 109065801364850999517613

theorem tailTrace_1433733 : CollatzResearch.WordTrace tailWord_1433733 prefixEnd_1433733 109065801364850999517613 := by
  unfold tailWord_1433733
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292538514837677947041853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34861692343225118631361235 52292538514837677947041853)
  ·
    refine ⟨19609701943064129230140695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52292538514837677947041853 19609701943064129230140695)
    ·
      refine ⟨29414552914596193845211043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19609701943064129230140695 29414552914596193845211043)
      ·
        refine ⟨44121829371894290767816565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29414552914596193845211043 44121829371894290767816565)
        ·
          refine ⟨4136421503615089759482803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44121829371894290767816565 4136421503615089759482803)
          ·
            refine ⟨6204632255422634639224205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136421503615089759482803 6204632255422634639224205)
            ·
              refine ⟨2326737095783487989709077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6204632255422634639224205 2326737095783487989709077)
              ·
                refine ⟨109065801364850999517613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2326737095783487989709077 109065801364850999517613)
                ·
                  rfl

theorem cell21_1433733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_1433733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433733 prefixEnd_1433733 := by exact prefixLift 1433733
  have htrace : WordTrace (prefixWord ++ tailWord_1433733) baseStart_1433733 baseEnd_1433733 := by
    simpa [prefixWord, tailWord_1433733, baseEnd_1433733] using wordTrace_append hprefix tailTrace_1433733
  have hstable : (prefixWord ++ tailWord_1433733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433733).length < 2 ^ (prefixWord ++ tailWord_1433733).sum := by decide
  have hdescent : baseEnd_1433733 < baseStart_1433733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433770 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_1433770 : Nat := 118140960795 + 1433770 * 2 ^ 59
def prefixEnd_1433770 : Nat := 4983230072969 + 3 ^ 40 * 1433770 * 2
def baseEnd_1433770 : Nat := 327205847998649156436097

theorem tailTrace_1433770 : CollatzResearch.WordTrace tailWord_1433770 prefixEnd_1433770 327205847998649156436097 := by
  unfold tailWord_1433770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073472003925908316534691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34862592010469088844092509 13073472003925908316534691)
  ·
    refine ⟨19610208005888862474802037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13073472003925908316534691 19610208005888862474802037)
    ·
      refine ⟨1838457000552080857012691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19610208005888862474802037 1838457000552080857012691)
      ·
        refine ⟨2757685500828121285519037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838457000552080857012691 2757685500828121285519037)
        ·
          refine ⟨1034132062810545482069639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2757685500828121285519037 1034132062810545482069639)
          ·
            refine ⟨1551198094215818223104459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034132062810545482069639 1551198094215818223104459)
            ·
              refine ⟨2326797141323727334656689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551198094215818223104459 2326797141323727334656689)
              ·
                refine ⟨1745097855992795500992517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326797141323727334656689 1745097855992795500992517)
                ·
                  refine ⟨327205847998649156436097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745097855992795500992517 327205847998649156436097)
                  ·
                    rfl

theorem cell21_1433770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_1433770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433770 prefixEnd_1433770 := by exact prefixLift 1433770
  have htrace : WordTrace (prefixWord ++ tailWord_1433770) baseStart_1433770 baseEnd_1433770 := by
    simpa [prefixWord, tailWord_1433770, baseEnd_1433770] using wordTrace_append hprefix tailTrace_1433770
  have hstable : (prefixWord ++ tailWord_1433770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433770).length < 2 ^ (prefixWord ++ tailWord_1433770).sum := by decide
  have hdescent : baseEnd_1433770 < baseStart_1433770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433778 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1433778 : Nat := 118140960795 + 1433778 * 2 ^ 59
def prefixEnd_1433778 : Nat := 4983230072969 + 3 ^ 40 * 1433778 * 2
def baseEnd_1433778 : Nat := 327207673707642920302747

theorem tailTrace_1433778 : CollatzResearch.WordTrace tailWord_1433778 prefixEnd_1433778 327207673707642920302747 := by
  unfold tailWord_1433778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073544949918662658107497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34862786533116433754953325 13073544949918662658107497)
  ·
    refine ⟨9805158712438996993580623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13073544949918662658107497 9805158712438996993580623)
    ·
      refine ⟨14707738068658495490370935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9805158712438996993580623 14707738068658495490370935)
      ·
        refine ⟨22061607102987743235556403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707738068658495490370935 22061607102987743235556403)
        ·
          refine ⟨33092410654481614853334605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22061607102987743235556403 33092410654481614853334605)
          ·
            refine ⟨12409653995430605570000477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33092410654481614853334605 12409653995430605570000477)
            ·
              refine ⟨4653620248286477088750179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12409653995430605570000477 4653620248286477088750179)
              ·
                refine ⟨6980430372429715633125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653620248286477088750179 6980430372429715633125269)
                ·
                  refine ⟨327207673707642920302747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6980430372429715633125269 327207673707642920302747)
                  ·
                    rfl

theorem cell21_1433778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1433778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433778 prefixEnd_1433778 := by exact prefixLift 1433778
  have htrace : WordTrace (prefixWord ++ tailWord_1433778) baseStart_1433778 baseEnd_1433778 := by
    simpa [prefixWord, tailWord_1433778, baseEnd_1433778] using wordTrace_append hprefix tailTrace_1433778
  have hstable : (prefixWord ++ tailWord_1433778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433778).length < 2 ^ (prefixWord ++ tailWord_1433778).sum := by decide
  have hdescent : baseEnd_1433778 < baseStart_1433778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433809 : List Nat := [1, 2, 2, 1, 2, 2, 6, 5]
def baseStart_1433809 : Nat := 118140960795 + 1433809 * 2 ^ 59
def prefixEnd_1433809 : Nat := 4983230072969 + 3 ^ 40 * 1433809 * 2
def baseEnd_1433809 : Nat := 109071582776664585095339

theorem tailTrace_1433809 : CollatzResearch.WordTrace tailWord_1433809 prefixEnd_1433809 109071582776664585095339 := by
  unfold tailWord_1433809
  simp only [CollatzResearch.WordTrace]
  refine ⟨52295310462562342926808481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34863540308374895284538987 52295310462562342926808481)
  ·
    refine ⟨39221482846921757195106361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52295310462562342926808481 39221482846921757195106361)
    ·
      refine ⟨29416112135191317896329771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39221482846921757195106361 29416112135191317896329771)
      ·
        refine ⟨44124168202786976844494657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416112135191317896329771 44124168202786976844494657)
        ·
          refine ⟨33093126152090232633370993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44124168202786976844494657 33093126152090232633370993)
          ·
            refine ⟨24819844614067674475028245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33093126152090232633370993 24819844614067674475028245)
            ·
              refine ⟨1163430216284422241016949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24819844614067674475028245 1163430216284422241016949)
              ·
                refine ⟨109071582776664585095339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1163430216284422241016949 109071582776664585095339)
                ·
                  rfl

theorem cell21_1433809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].length) (baseStart_1433809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433809 prefixEnd_1433809 := by exact prefixLift 1433809
  have htrace : WordTrace (prefixWord ++ tailWord_1433809) baseStart_1433809 baseEnd_1433809 := by
    simpa [prefixWord, tailWord_1433809, baseEnd_1433809] using wordTrace_append hprefix tailTrace_1433809
  have hstable : (prefixWord ++ tailWord_1433809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433809).length < 2 ^ (prefixWord ++ tailWord_1433809).sum := by decide
  have hdescent : baseEnd_1433809 < baseStart_1433809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433840 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_1433840 : Nat := 118140960795 + 1433840 * 2 ^ 59
def prefixEnd_1433840 : Nat := 4983230072969 + 3 ^ 40 * 1433840 * 2
def baseEnd_1433840 : Nat := 327221822952344590269287

theorem tailTrace_1433840 : CollatzResearch.WordTrace tailWord_1433840 prefixEnd_1433840 327221822952344590269287 := by
  unfold tailWord_1433840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148220562725017610593487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34864294083633356814124649 26148220562725017610593487)
  ·
    refine ⟨39222330844087526415890231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26148220562725017610593487 39222330844087526415890231)
    ·
      refine ⟨58833496266131289623835347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39222330844087526415890231 58833496266131289623835347)
      ·
        refine ⟨88250244399196934435753021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58833496266131289623835347 88250244399196934435753021)
        ·
          refine ⟨33093841649698850413407383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88250244399196934435753021 33093841649698850413407383)
          ·
            refine ⟨49640762474548275620111075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33093841649698850413407383 49640762474548275620111075)
            ·
              refine ⟨74461143711822413430166613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49640762474548275620111075 74461143711822413430166613)
              ·
                refine ⟨872591527872918907384765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74461143711822413430166613 872591527872918907384765)
                ·
                  refine ⟨327221822952344590269287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872591527872918907384765 327221822952344590269287)
                  ·
                    rfl

theorem cell21_1433840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_1433840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433840 prefixEnd_1433840 := by exact prefixLift 1433840
  have htrace : WordTrace (prefixWord ++ tailWord_1433840) baseStart_1433840 baseEnd_1433840 := by
    simpa [prefixWord, tailWord_1433840, baseEnd_1433840] using wordTrace_append hprefix tailTrace_1433840
  have hstable : (prefixWord ++ tailWord_1433840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433840).length < 2 ^ (prefixWord ++ tailWord_1433840).sum := by decide
  have hdescent : baseEnd_1433840 < baseStart_1433840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
