import V185TrunkScan23Chunk1086

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6435863 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6435863 : Nat := 118140960795 + 6435863 * 2 ^ 59
def prefixEnd_6435863 : Nat := 4983230072969 + 3 ^ 40 * 6435863 * 2
def baseEnd_6435863 : Nat := 3304691145487258390114511

theorem tailTrace_6435863 : CollatzResearch.WordTrace tailWord_6435863 prefixEnd_6435863 3304691145487258390114511 := by
  unfold tailWord_6435863
  simp only [CollatzResearch.WordTrace]
  refine ⟨234735207882974983737080243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156490138588649989158053495 234735207882974983737080243)
  ·
    refine ⟨352102811824462475605620365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234735207882974983737080243 352102811824462475605620365)
    ·
      refine ⟨132038554434173428352107637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352102811824462475605620365 132038554434173428352107637)
      ·
        refine ⟨12378614478203758908010091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132038554434173428352107637 12378614478203758908010091)
        ·
          refine ⟨18567921717305638362015137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378614478203758908010091 18567921717305638362015137)
          ·
            refine ⟨13925941287979228771511353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18567921717305638362015137 13925941287979228771511353)
            ·
              refine ⟨10444455965984421578633515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13925941287979228771511353 10444455965984421578633515)
              ·
                refine ⟨15666683948976632367950273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10444455965984421578633515 15666683948976632367950273)
                ·
                  refine ⟨11750012961732474275962705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15666683948976632367950273 11750012961732474275962705)
                  ·
                    refine ⟨8812509721299355706972029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11750012961732474275962705 8812509721299355706972029)
                    ·
                      refine ⟨3304691145487258390114511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812509721299355706972029 3304691145487258390114511)
                      ·
                        rfl

theorem cell23_6435863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6435863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435863 prefixEnd_6435863 := by exact prefixLift 6435863
  have htrace : WordTrace (prefixWord ++ tailWord_6435863) baseStart_6435863 baseEnd_6435863 := by
    simpa [prefixWord, tailWord_6435863, baseEnd_6435863] using wordTrace_append hprefix tailTrace_6435863
  have hstable : (prefixWord ++ tailWord_6435863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435863).length < 2 ^ (prefixWord ++ tailWord_6435863).sum := by decide
  have hdescent : baseEnd_6435863 < baseStart_6435863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435909 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_6435909 : Nat := 118140960795 + 6435909 * 2 ^ 59
def prefixEnd_6435909 : Nat := 4983230072969 + 3 ^ 40 * 6435909 * 2
def baseEnd_6435909 : Nat := 1101571588532455070046433

theorem tailTrace_6435909 : CollatzResearch.WordTrace tailWord_6435909 prefixEnd_6435909 1101571588532455070046433 := by
  unfold tailWord_6435909
  simp only [CollatzResearch.WordTrace]
  refine ⟨234736885640808333593254781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156491257093872222395503187 234736885640808333593254781)
  ·
    refine ⟨88026332115303125097470543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234736885640808333593254781 88026332115303125097470543)
    ·
      refine ⟨132039498172954687646205815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88026332115303125097470543 132039498172954687646205815)
      ·
        refine ⟨198059247259432031469308723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132039498172954687646205815 198059247259432031469308723)
        ·
          refine ⟨297088870889148047203963085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198059247259432031469308723 297088870889148047203963085)
          ·
            refine ⟨111408326583430517701486157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297088870889148047203963085 111408326583430517701486157)
            ·
              refine ⟨41778122468786444138057309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111408326583430517701486157 41778122468786444138057309)
              ·
                refine ⟨15666795925794916551771491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41778122468786444138057309 15666795925794916551771491)
                ·
                  refine ⟨23500193888692374827657237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15666795925794916551771491 23500193888692374827657237)
                  ·
                    refine ⟨1101571588532455070046433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23500193888692374827657237 1101571588532455070046433)
                    ·
                      rfl

theorem cell23_6435909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_6435909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435909 prefixEnd_6435909 := by exact prefixLift 6435909
  have htrace : WordTrace (prefixWord ++ tailWord_6435909) baseStart_6435909 baseEnd_6435909 := by
    simpa [prefixWord, tailWord_6435909, baseEnd_6435909] using wordTrace_append hprefix tailTrace_6435909
  have hstable : (prefixWord ++ tailWord_6435909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435909).length < 2 ^ (prefixWord ++ tailWord_6435909).sum := by decide
  have hdescent : baseEnd_6435909 < baseStart_6435909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435910 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6435910 : Nat := 118140960795 + 6435910 * 2 ^ 59
def prefixEnd_6435910 : Nat := 4983230072969 + 3 ^ 40 * 6435910 * 2
def baseEnd_6435910 : Nat := 3304715279078019706226795

theorem tailTrace_6435910 : CollatzResearch.WordTrace tailWord_6435910 prefixEnd_6435910 3304715279078019706226795 := by
  unfold tailWord_6435910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335528816056397211376287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156491281409203140509360789 7335528816056397211376287)
  ·
    refine ⟨11003293224084595817064431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7335528816056397211376287 11003293224084595817064431)
    ·
      refine ⟨16504939836126893725596647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11003293224084595817064431 16504939836126893725596647)
      ·
        refine ⟨24757409754190340588394971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16504939836126893725596647 24757409754190340588394971)
        ·
          refine ⟨37136114631285510882592457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24757409754190340588394971 37136114631285510882592457)
          ·
            refine ⟨27852085973464133161944343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37136114631285510882592457 27852085973464133161944343)
            ·
              refine ⟨41778128960196199742916515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27852085973464133161944343 41778128960196199742916515)
              ·
                refine ⟨62667193440294299614374773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41778128960196199742916515 62667193440294299614374773)
                ·
                  refine ⟨5875049385027590588847635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62667193440294299614374773 5875049385027590588847635)
                  ·
                    refine ⟨8812574077541385883271453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875049385027590588847635 8812574077541385883271453)
                    ·
                      refine ⟨3304715279078019706226795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812574077541385883271453 3304715279078019706226795)
                      ·
                        rfl

theorem cell23_6435910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6435910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435910 prefixEnd_6435910 := by exact prefixLift 6435910
  have htrace : WordTrace (prefixWord ++ tailWord_6435910) baseStart_6435910 baseEnd_6435910 := by
    simpa [prefixWord, tailWord_6435910, baseEnd_6435910] using wordTrace_append hprefix tailTrace_6435910
  have hstable : (prefixWord ++ tailWord_6435910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435910).length < 2 ^ (prefixWord ++ tailWord_6435910).sum := by decide
  have hdescent : baseEnd_6435910 < baseStart_6435910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6435916 : Nat := 118140960795 + 6435916 * 2 ^ 59
def prefixEnd_6435916 : Nat := 4983230072969 + 3 ^ 40 * 6435916 * 2
def baseEnd_6435916 : Nat := 3304718359961946682751767

theorem tailTrace_6435916 : CollatzResearch.WordTrace tailWord_6435916 prefixEnd_6435916 3304718359961946682751767 := by
  unfold tailWord_6435916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117368570475891486894379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156491427301188649192506401 117368570475891486894379801)
  ·
    refine ⟨88026427856918615170784851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117368570475891486894379801 88026427856918615170784851)
    ·
      refine ⟨132039641785377922756177277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88026427856918615170784851 132039641785377922756177277)
      ·
        refine ⟨49514865669516721033566479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132039641785377922756177277 49514865669516721033566479)
        ·
          refine ⟨74272298504275081550349719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49514865669516721033566479 74272298504275081550349719)
          ·
            refine ⟨111408447756412622325524579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74272298504275081550349719 111408447756412622325524579)
            ·
              refine ⟨167112671634618933488286869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111408447756412622325524579 167112671634618933488286869)
              ·
                refine ⟨7833406482872762507263447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167112671634618933488286869 7833406482872762507263447)
                ·
                  refine ⟨11750109724309143760895171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833406482872762507263447 11750109724309143760895171)
                  ·
                    refine ⟨17625164586463715641342757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11750109724309143760895171 17625164586463715641342757)
                    ·
                      refine ⟨3304718359961946682751767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17625164586463715641342757 3304718359961946682751767)
                      ·
                        rfl

theorem cell23_6435916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6435916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435916 prefixEnd_6435916 := by exact prefixLift 6435916
  have htrace : WordTrace (prefixWord ++ tailWord_6435916) baseStart_6435916 baseEnd_6435916 := by
    simpa [prefixWord, tailWord_6435916, baseEnd_6435916] using wordTrace_append hprefix tailTrace_6435916
  have hstable : (prefixWord ++ tailWord_6435916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435916).length < 2 ^ (prefixWord ++ tailWord_6435916).sum := by decide
  have hdescent : baseEnd_6435916 < baseStart_6435916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435929 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_6435929 : Nat := 118140960795 + 6435929 * 2 ^ 59
def prefixEnd_6435929 : Nat := 4983230072969 + 3 ^ 40 * 6435929 * 2
def baseEnd_6435929 : Nat := 3304725035210455131889207

theorem tailTrace_6435929 : CollatzResearch.WordTrace tailWord_6435929 prefixEnd_6435929 3304725035210455131889207 := by
  unfold tailWord_6435929
  simp only [CollatzResearch.WordTrace]
  refine ⟨234737615100735877008982841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156491743400490584672655227 234737615100735877008982841)
  ·
    refine ⟨176053211325551907756737131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234737615100735877008982841 176053211325551907756737131)
    ·
      refine ⟨264079816988327861635105697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176053211325551907756737131 264079816988327861635105697)
      ·
        refine ⟨198059862741245896226329273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264079816988327861635105697 198059862741245896226329273)
        ·
          refine ⟨148544897055934422169746955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198059862741245896226329273 148544897055934422169746955)
          ·
            refine ⟨222817345583901633254620433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148544897055934422169746955 222817345583901633254620433)
            ·
              refine ⟨167113009187926224940965325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222817345583901633254620433 167113009187926224940965325)
              ·
                refine ⟨62667378445472334352861997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167113009187926224940965325 62667378445472334352861997)
                ·
                  refine ⟨23500266917052125382323249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62667378445472334352861997 23500266917052125382323249)
                  ·
                    refine ⟨17625200187789094036742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23500266917052125382323249 17625200187789094036742437)
                    ·
                      refine ⟨3304725035210455131889207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17625200187789094036742437 3304725035210455131889207)
                      ·
                        rfl

theorem cell23_6435929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_6435929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435929 prefixEnd_6435929 := by exact prefixLift 6435929
  have htrace : WordTrace (prefixWord ++ tailWord_6435929) baseStart_6435929 baseEnd_6435929 := by
    simpa [prefixWord, tailWord_6435929, baseEnd_6435929] using wordTrace_append hprefix tailTrace_6435929
  have hstable : (prefixWord ++ tailWord_6435929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435929).length < 2 ^ (prefixWord ++ tailWord_6435929).sum := by decide
  have hdescent : baseEnd_6435929 < baseStart_6435929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435943 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 2, 4]
def baseStart_6435943 : Nat := 118140960795 + 6435943 * 2 ^ 59
def prefixEnd_6435943 : Nat := 4983230072969 + 3 ^ 40 * 6435943 * 2
def baseEnd_6435943 : Nat := 1101577407979872692371381

theorem tailTrace_6435943 : CollatzResearch.WordTrace tailWord_6435943 prefixEnd_6435943 1101577407979872692371381 := by
  unfold tailWord_6435943
  simp only [CollatzResearch.WordTrace]
  refine ⟨234738125722685157399992483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156492083815123438266661655 234738125722685157399992483)
  ·
    refine ⟨352107188584027736099988725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234738125722685157399992483 352107188584027736099988725)
    ·
      refine ⟨33010048929752600259373943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352107188584027736099988725 33010048929752600259373943)
      ·
        refine ⟨49515073394628900389060915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33010048929752600259373943 49515073394628900389060915)
        ·
          refine ⟨74272610091943350583591373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49515073394628900389060915 74272610091943350583591373)
          ·
            refine ⟨27852228784478756468846765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74272610091943350583591373 27852228784478756468846765)
            ·
              refine ⟨10444585794179533675817537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27852228784478756468846765 10444585794179533675817537)
              ·
                refine ⟨7833439345634650256863153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10444585794179533675817537 7833439345634650256863153)
                ·
                  refine ⟨5875079509225987692647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833439345634650256863153 5875079509225987692647365)
                  ·
                    refine ⟨1101577407979872692371381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5875079509225987692647365 1101577407979872692371381)
                    ·
                      rfl

theorem cell23_6435943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_6435943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435943 prefixEnd_6435943 := by exact prefixLift 6435943
  have htrace : WordTrace (prefixWord ++ tailWord_6435943) baseStart_6435943 baseEnd_6435943 := by
    simpa [prefixWord, tailWord_6435943, baseEnd_6435943] using wordTrace_append hprefix tailTrace_6435943
  have hstable : (prefixWord ++ tailWord_6435943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435943).length < 2 ^ (prefixWord ++ tailWord_6435943).sum := by decide
  have hdescent : baseEnd_6435943 < baseStart_6435943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435950 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6435950 : Nat := 118140960795 + 6435950 * 2 ^ 59
def prefixEnd_6435950 : Nat := 4983230072969 + 3 ^ 40 * 6435950 * 2
def baseEnd_6435950 : Nat := 3304735818304199549726611

theorem tailTrace_6435950 : CollatzResearch.WordTrace tailWord_6435950 prefixEnd_6435950 3304735818304199549726611 := by
  unfold tailWord_6435950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342297629207474699437163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156492254022439865063664869 29342297629207474699437163)
  ·
    refine ⟨44013446443811212049155745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29342297629207474699437163 44013446443811212049155745)
    ·
      refine ⟨33010084832858409036866809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44013446443811212049155745 33010084832858409036866809)
      ·
        refine ⟨24757563624643806777650107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33010084832858409036866809 24757563624643806777650107)
        ·
          refine ⟨37136345436965710166475161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24757563624643806777650107 37136345436965710166475161)
          ·
            refine ⟨27852259077724282624856371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37136345436965710166475161 27852259077724282624856371)
            ·
              refine ⟨41778388616586423937284557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27852259077724282624856371 41778388616586423937284557)
              ·
                refine ⟨15666895731219908976481709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41778388616586423937284557 15666895731219908976481709)
                ·
                  refine ⟨5875085899207465866180641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15666895731219908976481709 5875085899207465866180641)
                  ·
                    refine ⟨4406314424405599399635481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5875085899207465866180641 4406314424405599399635481)
                    ·
                      refine ⟨3304735818304199549726611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406314424405599399635481 3304735818304199549726611)
                      ·
                        rfl

theorem cell23_6435950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6435950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435950 prefixEnd_6435950 := by exact prefixLift 6435950
  have htrace : WordTrace (prefixWord ++ tailWord_6435950) baseStart_6435950 baseEnd_6435950 := by
    simpa [prefixWord, tailWord_6435950, baseEnd_6435950] using wordTrace_append hprefix tailTrace_6435950
  have hstable : (prefixWord ++ tailWord_6435950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435950).length < 2 ^ (prefixWord ++ tailWord_6435950).sum := by decide
  have hdescent : baseEnd_6435950 < baseStart_6435950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435973 : List Nat := [1, 3, 1, 1, 6, 2, 2, 7]
def baseStart_6435973 : Nat := 118140960795 + 6435973 * 2 ^ 59
def prefixEnd_6435973 : Nat := 4983230072969 + 3 ^ 40 * 6435973 * 2
def baseEnd_6435973 : Nat := 122398060309601961471815

theorem tailTrace_6435973 : CollatzResearch.WordTrace tailWord_6435973 prefixEnd_6435973 122398060309601961471815 := by
  unfold tailWord_6435973
  simp only [CollatzResearch.WordTrace]
  refine ⟨234739219912576472523584573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156492813275050981682389715 234739219912576472523584573)
  ·
    refine ⟨88027207467216177196344215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234739219912576472523584573 88027207467216177196344215)
    ·
      refine ⟨132040811200824265794516323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88027207467216177196344215 132040811200824265794516323)
      ·
        refine ⟨198061216801236398691774485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132040811200824265794516323 198061216801236398691774485)
        ·
          refine ⟨9284119537557956188676929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198061216801236398691774485 9284119537557956188676929)
          ·
            refine ⟨6963089653168467141507697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9284119537557956188676929 6963089653168467141507697)
            ·
              refine ⟨5222317239876350356130773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6963089653168467141507697 5222317239876350356130773)
              ·
                refine ⟨122398060309601961471815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5222317239876350356130773 122398060309601961471815)
                ·
                  rfl

theorem cell23_6435973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 7].length) (baseStart_6435973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435973 prefixEnd_6435973 := by exact prefixLift 6435973
  have htrace : WordTrace (prefixWord ++ tailWord_6435973) baseStart_6435973 baseEnd_6435973 := by
    simpa [prefixWord, tailWord_6435973, baseEnd_6435973] using wordTrace_append hprefix tailTrace_6435973
  have hstable : (prefixWord ++ tailWord_6435973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435973).length < 2 ^ (prefixWord ++ tailWord_6435973).sum := by decide
  have hdescent : baseEnd_6435973 < baseStart_6435973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436017 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6436017 : Nat := 118140960795 + 6436017 * 2 ^ 59
def prefixEnd_6436017 : Nat := 4983230072969 + 3 ^ 40 * 6436017 * 2
def baseEnd_6436017 : Nat := 3304770221508050787588803

theorem tailTrace_6436017 : CollatzResearch.WordTrace tailWord_6436017 prefixEnd_6436017 3304770221508050787588803 := by
  unfold tailWord_6436017
  simp only [CollatzResearch.WordTrace]
  refine ⟨234740824724417068038186305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156493883149611378692124203 234740824724417068038186305)
  ·
    refine ⟨176055618543312801028639729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234740824724417068038186305 176055618543312801028639729)
    ·
      refine ⟨132041713907484600771479797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176055618543312801028639729 132041713907484600771479797)
      ·
        refine ⟨12378910678826681322326231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132041713907484600771479797 12378910678826681322326231)
        ·
          refine ⟨18568366018240021983489347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378910678826681322326231 18568366018240021983489347)
          ·
            refine ⟨27852549027360032975234021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568366018240021983489347 27852549027360032975234021)
            ·
              refine ⟨5222352942630006182856379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27852549027360032975234021 5222352942630006182856379)
              ·
                refine ⟨7833529413945009274284569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222352942630006182856379 7833529413945009274284569)
                ·
                  refine ⟨5875147060458756955713427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833529413945009274284569 5875147060458756955713427)
                  ·
                    refine ⟨8812720590688135433570141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875147060458756955713427 8812720590688135433570141)
                    ·
                      refine ⟨3304770221508050787588803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812720590688135433570141 3304770221508050787588803)
                      ·
                        rfl

theorem cell23_6436017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6436017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436017 prefixEnd_6436017 := by exact prefixLift 6436017
  have htrace : WordTrace (prefixWord ++ tailWord_6436017) baseStart_6436017 baseEnd_6436017 := by
    simpa [prefixWord, tailWord_6436017, baseEnd_6436017] using wordTrace_append hprefix tailTrace_6436017
  have hstable : (prefixWord ++ tailWord_6436017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436017).length < 2 ^ (prefixWord ++ tailWord_6436017).sum := by decide
  have hdescent : baseEnd_6436017 < baseStart_6436017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436023 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_6436023 : Nat := 118140960795 + 6436023 * 2 ^ 59
def prefixEnd_6436023 : Nat := 4983230072969 + 3 ^ 40 * 6436023 * 2
def baseEnd_6436023 : Nat := 3304773302391977764113775

theorem tailTrace_6436023 : CollatzResearch.WordTrace tailWord_6436023 prefixEnd_6436023 3304773302391977764113775 := by
  unfold tailWord_6436023
  simp only [CollatzResearch.WordTrace]
  refine ⟨234741043562395331062904723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156494029041596887375269815 234741043562395331062904723)
  ·
    refine ⟨352111565343592996594357085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234741043562395331062904723 352111565343592996594357085)
    ·
      refine ⟨132041837003847373722883907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352111565343592996594357085 132041837003847373722883907)
      ·
        refine ⟨198062755505771060584325861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132041837003847373722883907 198062755505771060584325861)
        ·
          refine ⟨37136766657332073859561099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198062755505771060584325861 37136766657332073859561099)
          ·
            refine ⟨55705149985998110789341649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37136766657332073859561099 55705149985998110789341649)
            ·
              refine ⟨41778862489498583092006237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55705149985998110789341649 41778862489498583092006237)
              ·
                refine ⟨15667073433561968659502339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41778862489498583092006237 15667073433561968659502339)
                ·
                  refine ⟨23500610150342952989253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15667073433561968659502339 23500610150342952989253509)
                  ·
                    refine ⟨4406364403189303685485033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23500610150342952989253509 4406364403189303685485033)
                    ·
                      refine ⟨3304773302391977764113775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406364403189303685485033 3304773302391977764113775)
                      ·
                        rfl

theorem cell23_6436023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_6436023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436023 prefixEnd_6436023 := by exact prefixLift 6436023
  have htrace : WordTrace (prefixWord ++ tailWord_6436023) baseStart_6436023 baseEnd_6436023 := by
    simpa [prefixWord, tailWord_6436023, baseEnd_6436023] using wordTrace_append hprefix tailTrace_6436023
  have hstable : (prefixWord ++ tailWord_6436023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436023).length < 2 ^ (prefixWord ++ tailWord_6436023).sum := by decide
  have hdescent : baseEnd_6436023 < baseStart_6436023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436113 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_6436113 : Nat := 118140960795 + 6436113 * 2 ^ 59
def prefixEnd_6436113 : Nat := 4983230072969 + 3 ^ 40 * 6436113 * 2
def baseEnd_6436113 : Nat := 3304819515650882411988361

theorem tailTrace_6436113 : CollatzResearch.WordTrace tailWord_6436113 prefixEnd_6436113 3304819515650882411988361 := by
  unfold tailWord_6436113
  simp only [CollatzResearch.WordTrace]
  refine ⟨234744326132069276433680993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156496217421379517622453995 234744326132069276433680993)
  ·
    refine ⟨176058244599051957325260745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234744326132069276433680993 176058244599051957325260745)
    ·
      refine ⟨132043683449288967993945559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176058244599051957325260745 132043683449288967993945559)
      ·
        refine ⟨198065525173933451990918339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132043683449288967993945559 198065525173933451990918339)
        ·
          refine ⟨297098287760900177986377509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198065525173933451990918339 297098287760900177986377509)
          ·
            refine ⟨55705928955168783372445783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297098287760900177986377509 55705928955168783372445783)
            ·
              refine ⟨83558893432753175058668675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55705928955168783372445783 83558893432753175058668675)
              ·
                refine ⟨125338340149129762588003013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83558893432753175058668675 125338340149129762588003013)
                ·
                  refine ⟨23500938777961830485250565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125338340149129762588003013 23500938777961830485250565)
                  ·
                    refine ⟨4406426020867843215984481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23500938777961830485250565 4406426020867843215984481)
                    ·
                      refine ⟨3304819515650882411988361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406426020867843215984481 3304819515650882411988361)
                      ·
                        rfl

theorem cell23_6436113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_6436113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436113 prefixEnd_6436113 := by exact prefixLift 6436113
  have htrace : WordTrace (prefixWord ++ tailWord_6436113) baseStart_6436113 baseEnd_6436113 := by
    simpa [prefixWord, tailWord_6436113, baseEnd_6436113] using wordTrace_append hprefix tailTrace_6436113
  have hstable : (prefixWord ++ tailWord_6436113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436113).length < 2 ^ (prefixWord ++ tailWord_6436113).sum := by decide
  have hdescent : baseEnd_6436113 < baseStart_6436113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436133 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_6436133 : Nat := 118140960795 + 6436133 * 2 ^ 59
def prefixEnd_6436133 : Nat := 4983230072969 + 3 ^ 40 * 6436133 * 2
def baseEnd_6436133 : Nat := 3304829785263972333738269

theorem tailTrace_6436133 : CollatzResearch.WordTrace tailWord_6436133 prefixEnd_6436133 3304829785263972333738269 := by
  unfold tailWord_6436133
  simp only [CollatzResearch.WordTrace]
  refine ⟨234745055591996819849409053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156496703727997879899606035 234745055591996819849409053)
  ·
    refine ⟨88029395846998807443528395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234745055591996819849409053 88029395846998807443528395)
    ·
      refine ⟨132044093770498211165292593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88029395846998807443528395 132044093770498211165292593)
      ·
        refine ⟨99033070327873658373969445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132044093770498211165292593 99033070327873658373969445)
        ·
          refine ⟨18568700686476310945119271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99033070327873658373969445 18568700686476310945119271)
          ·
            refine ⟨27853051029714466417678907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568700686476310945119271 27853051029714466417678907)
            ·
              refine ⟨41779576544571699626518361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27853051029714466417678907 41779576544571699626518361)
              ·
                refine ⟨31334682408428774719888771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41779576544571699626518361 31334682408428774719888771)
                ·
                  refine ⟨47002023612643162079833157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31334682408428774719888771 47002023612643162079833157)
                  ·
                    refine ⟨8812879427370592889968717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47002023612643162079833157 8812879427370592889968717)
                    ·
                      refine ⟨3304829785263972333738269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812879427370592889968717 3304829785263972333738269)
                      ·
                        rfl

theorem cell23_6436133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_6436133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436133 prefixEnd_6436133 := by exact prefixLift 6436133
  have htrace : WordTrace (prefixWord ++ tailWord_6436133) baseStart_6436133 baseEnd_6436133 := by
    simpa [prefixWord, tailWord_6436133, baseEnd_6436133] using wordTrace_append hprefix tailTrace_6436133
  have hstable : (prefixWord ++ tailWord_6436133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436133).length < 2 ^ (prefixWord ++ tailWord_6436133).sum := by decide
  have hdescent : baseEnd_6436133 < baseStart_6436133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436200 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_6436200 : Nat := 118140960795 + 6436200 * 2 ^ 59
def prefixEnd_6436200 : Nat := 4983230072969 + 3 ^ 40 * 6436200 * 2
def baseEnd_6436200 : Nat := 1101621396155941190533487

theorem tailTrace_6436200 : CollatzResearch.WordTrace tailWord_6436200 prefixEnd_6436200 1101621396155941190533487 := by
  unfold tailWord_6436200
  simp only [CollatzResearch.WordTrace]
  refine ⟨117373749641377045146049027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156498332855169393528065369 117373749641377045146049027)
  ·
    refine ⟨176060624462065567719073541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117373749641377045146049027 176060624462065567719073541)
    ·
      refine ⟨33011367086637293947326289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176060624462065567719073541 33011367086637293947326289)
      ·
        refine ⟨24758525314977970460494717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33011367086637293947326289 24758525314977970460494717)
        ·
          refine ⟨9284446993116738922685519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24758525314977970460494717 9284446993116738922685519)
          ·
            refine ⟨13926670489675108384028279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9284446993116738922685519 13926670489675108384028279)
            ·
              refine ⟨20890005734512662576042419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13926670489675108384028279 20890005734512662576042419)
              ·
                refine ⟨31335008601768993864063629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20890005734512662576042419 31335008601768993864063629)
                ·
                  refine ⟨11750628225663372699023861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31335008601768993864063629 11750628225663372699023861)
                  ·
                    refine ⟨1101621396155941190533487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11750628225663372699023861 1101621396155941190533487)
                    ·
                      rfl

theorem cell23_6436200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_6436200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436200 prefixEnd_6436200 := by exact prefixLift 6436200
  have htrace : WordTrace (prefixWord ++ tailWord_6436200) baseStart_6436200 baseEnd_6436200 := by
    simpa [prefixWord, tailWord_6436200, baseEnd_6436200] using wordTrace_append hprefix tailTrace_6436200
  have hstable : (prefixWord ++ tailWord_6436200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436200).length < 2 ^ (prefixWord ++ tailWord_6436200).sum := by decide
  have hdescent : baseEnd_6436200 < baseStart_6436200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436216 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_6436216 : Nat := 118140960795 + 6436216 * 2 ^ 59
def prefixEnd_6436216 : Nat := 4983230072969 + 3 ^ 40 * 6436216 * 2
def baseEnd_6436216 : Nat := 3304872404158295509000387

theorem tailTrace_6436216 : CollatzResearch.WordTrace tailWord_6436216 prefixEnd_6436216 3304872404158295509000387 := by
  unfold tailWord_6436216
  simp only [CollatzResearch.WordTrace]
  refine ⟨117374041425348062512340251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156498721900464083349787001 117374041425348062512340251)
  ·
    refine ⟨176061062138022093768510377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117374041425348062512340251 176061062138022093768510377)
    ·
      refine ⟨132045796603516570326382783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176061062138022093768510377 132045796603516570326382783)
      ·
        refine ⟨198068694905274855489574175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132045796603516570326382783 198068694905274855489574175)
        ·
          refine ⟨297103042357912283234361263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198068694905274855489574175 297103042357912283234361263)
          ·
            refine ⟨445654563536868424851541895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297103042357912283234361263 445654563536868424851541895)
            ·
              refine ⟨668481845305302637277312843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445654563536868424851541895 668481845305302637277312843)
              ·
                refine ⟨1002722767957953955915969265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668481845305302637277312843 1002722767957953955915969265)
                ·
                  refine ⟨752042075968465466936976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002722767957953955915969265 752042075968465466936976949)
                  ·
                    refine ⟨70503944622043637525341589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 752042075968465466936976949 70503944622043637525341589)
                    ·
                      refine ⟨3304872404158295509000387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70503944622043637525341589 3304872404158295509000387)
                      ·
                        rfl

theorem cell23_6436216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_6436216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436216 prefixEnd_6436216 := by exact prefixLift 6436216
  have htrace : WordTrace (prefixWord ++ tailWord_6436216) baseStart_6436216 baseEnd_6436216 := by
    simpa [prefixWord, tailWord_6436216, baseEnd_6436216] using wordTrace_append hprefix tailTrace_6436216
  have hstable : (prefixWord ++ tailWord_6436216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436216).length < 2 ^ (prefixWord ++ tailWord_6436216).sum := by decide
  have hdescent : baseEnd_6436216 < baseStart_6436216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436223 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_6436223 : Nat := 118140960795 + 6436223 * 2 ^ 59
def prefixEnd_6436223 : Nat := 4983230072969 + 3 ^ 40 * 6436223 * 2
def baseEnd_6436223 : Nat := 3304875998522876981612855

theorem tailTrace_6436223 : CollatzResearch.WordTrace tailWord_6436223 prefixEnd_6436223 3304875998522876981612855 := by
  unfold tailWord_6436223
  simp only [CollatzResearch.WordTrace]
  refine ⟨234748338161670765220185323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156498892107780510146790215 234748338161670765220185323)
  ·
    refine ⟨352122507242506147830277985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234748338161670765220185323 352122507242506147830277985)
    ·
      refine ⟨264091880431879610872708489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352122507242506147830277985 264091880431879610872708489)
      ·
        refine ⟨198068910323909708154531367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264091880431879610872708489 198068910323909708154531367)
        ·
          refine ⟨297103365485864562231797051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198068910323909708154531367 297103365485864562231797051)
          ·
            refine ⟨445655048228796843347695577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297103365485864562231797051 445655048228796843347695577)
            ·
              refine ⟨334241286171597632510771683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445655048228796843347695577 334241286171597632510771683)
              ·
                refine ⟨501361929257396448766157525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334241286171597632510771683 501361929257396448766157525)
                ·
                  refine ⟨11750670216970229267956817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 501361929257396448766157525 11750670216970229267956817)
                  ·
                    refine ⟨8813002662727671950967613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11750670216970229267956817 8813002662727671950967613)
                    ·
                      refine ⟨3304875998522876981612855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813002662727671950967613 3304875998522876981612855)
                      ·
                        rfl

theorem cell23_6436223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_6436223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436223 prefixEnd_6436223 := by exact prefixLift 6436223
  have htrace : WordTrace (prefixWord ++ tailWord_6436223) baseStart_6436223 baseEnd_6436223 := by
    simpa [prefixWord, tailWord_6436223, baseEnd_6436223] using wordTrace_append hprefix tailTrace_6436223
  have hstable : (prefixWord ++ tailWord_6436223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436223).length < 2 ^ (prefixWord ++ tailWord_6436223).sum := by decide
  have hdescent : baseEnd_6436223 < baseStart_6436223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436231 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_6436231 : Nat := 118140960795 + 6436231 * 2 ^ 59
def prefixEnd_6436231 : Nat := 4983230072969 + 3 ^ 40 * 6436231 * 2
def baseEnd_6436231 : Nat := 3304880106368112950312819

theorem tailTrace_6436231 : CollatzResearch.WordTrace tailWord_6436231 prefixEnd_6436231 3304880106368112950312819 := by
  unfold tailWord_6436231
  simp only [CollatzResearch.WordTrace]
  refine ⟨234748629945641782586476547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156499086630427855057651031 234748629945641782586476547)
  ·
    refine ⟨352122944918462673879714821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234748629945641782586476547 352122944918462673879714821)
    ·
      refine ⟨66023052172211751352446529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352122944918462673879714821 66023052172211751352446529)
      ·
        refine ⟨49517289129158813514334897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66023052172211751352446529 49517289129158813514334897)
        ·
          refine ⟨37137966846869110135751173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49517289129158813514334897 37137966846869110135751173)
          ·
            refine ⟨6963368783787958150453345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37137966846869110135751173 6963368783787958150453345)
            ·
              refine ⟨5222526587840968612840009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6963368783787958150453345 5222526587840968612840009)
              ·
                refine ⟨3916894940880726459630007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222526587840968612840009 3916894940880726459630007)
                ·
                  refine ⟨5875342411321089689445011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916894940880726459630007 5875342411321089689445011)
                  ·
                    refine ⟨8813013616981634534167517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875342411321089689445011 8813013616981634534167517)
                    ·
                      refine ⟨3304880106368112950312819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813013616981634534167517 3304880106368112950312819)
                      ·
                        rfl

theorem cell23_6436231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_6436231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436231 prefixEnd_6436231 := by exact prefixLift 6436231
  have htrace : WordTrace (prefixWord ++ tailWord_6436231) baseStart_6436231 baseEnd_6436231 := by
    simpa [prefixWord, tailWord_6436231, baseEnd_6436231] using wordTrace_append hprefix tailTrace_6436231
  have hstable : (prefixWord ++ tailWord_6436231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436231).length < 2 ^ (prefixWord ++ tailWord_6436231).sum := by decide
  have hdescent : baseEnd_6436231 < baseStart_6436231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436250 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6436250 : Nat := 118140960795 + 6436250 * 2 ^ 59
def prefixEnd_6436250 : Nat := 4983230072969 + 3 ^ 40 * 6436250 * 2
def baseEnd_6436250 : Nat := 3304889862500548375975231

theorem tailTrace_6436250 : CollatzResearch.WordTrace tailWord_6436250 prefixEnd_6436250 3304889862500548375975231 := by
  unfold tailWord_6436250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58687330733143237207854551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156499548621715299220945469 58687330733143237207854551)
  ·
    refine ⟨88030996099714855811781827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58687330733143237207854551 88030996099714855811781827)
    ·
      refine ⟨132046494149572283717672741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88030996099714855811781827 132046494149572283717672741)
      ·
        refine ⟨24758717653044803197063639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132046494149572283717672741 24758717653044803197063639)
        ·
          refine ⟨37138076479567204795595459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24758717653044803197063639 37138076479567204795595459)
          ·
            refine ⟨55707114719350807193393189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37138076479567204795595459 55707114719350807193393189)
            ·
              refine ⟨10445084009878276348761223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55707114719350807193393189 10445084009878276348761223)
              ·
                refine ⟨15667626014817414523141835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10445084009878276348761223 15667626014817414523141835)
                ·
                  refine ⟨23501439022226121784712753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15667626014817414523141835 23501439022226121784712753)
                  ·
                    refine ⟨17626079266669591338534565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23501439022226121784712753 17626079266669591338534565)
                    ·
                      refine ⟨3304889862500548375975231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17626079266669591338534565 3304889862500548375975231)
                      ·
                        rfl

theorem cell23_6436250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6436250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436250 prefixEnd_6436250 := by exact prefixLift 6436250
  have htrace : WordTrace (prefixWord ++ tailWord_6436250) baseStart_6436250 baseEnd_6436250 := by
    simpa [prefixWord, tailWord_6436250, baseEnd_6436250] using wordTrace_append hprefix tailTrace_6436250
  have hstable : (prefixWord ++ tailWord_6436250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436250).length < 2 ^ (prefixWord ++ tailWord_6436250).sum := by decide
  have hdescent : baseEnd_6436250 < baseStart_6436250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436303 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 6]
def baseStart_6436303 : Nat := 118140960795 + 6436303 * 2 ^ 59
def prefixEnd_6436303 : Nat := 4983230072969 + 3 ^ 40 * 6436303 * 2
def baseEnd_6436303 : Nat := 1101639025658412222870829

theorem tailTrace_6436303 : CollatzResearch.WordTrace tailWord_6436303 prefixEnd_6436303 1101639025658412222870829 := by
  unfold tailWord_6436303
  simp only [CollatzResearch.WordTrace]
  refine ⟨234751256001380938883097563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156500837334253959255398375 234751256001380938883097563)
  ·
    refine ⟨352126884002071408324646345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234751256001380938883097563 352126884002071408324646345)
    ·
      refine ⟨264095163001553556243484759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352126884002071408324646345 264095163001553556243484759)
      ·
        refine ⟨396142744502330334365227139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264095163001553556243484759 396142744502330334365227139)
        ·
          refine ⟨594214116753495501547840709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396142744502330334365227139 594214116753495501547840709)
          ·
            refine ⟨111415146891280406540220133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 594214116753495501547840709 111415146891280406540220133)
            ·
              refine ⟨20890340042115076226291275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111415146891280406540220133 20890340042115076226291275)
              ·
                refine ⟨31335510063172614339436913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20890340042115076226291275 31335510063172614339436913)
                ·
                  refine ⟨23501632547379460754577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31335510063172614339436913 23501632547379460754577685)
                  ·
                    refine ⟨1101639025658412222870829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23501632547379460754577685 1101639025658412222870829)
                    ·
                      rfl

theorem cell23_6436303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_6436303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436303 prefixEnd_6436303 := by exact prefixLift 6436303
  have htrace : WordTrace (prefixWord ++ tailWord_6436303) baseStart_6436303 baseEnd_6436303 := by
    simpa [prefixWord, tailWord_6436303, baseEnd_6436303] using wordTrace_append hprefix tailTrace_6436303
  have hstable : (prefixWord ++ tailWord_6436303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436303).length < 2 ^ (prefixWord ++ tailWord_6436303).sum := by decide
  have hdescent : baseEnd_6436303 < baseStart_6436303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436314 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_6436314 : Nat := 118140960795 + 6436314 * 2 ^ 59
def prefixEnd_6436314 : Nat := 4983230072969 + 3 ^ 40 * 6436314 * 2
def baseEnd_6436314 : Nat := 3304922725262436125574937

theorem tailTrace_6436314 : CollatzResearch.WordTrace tailWord_6436314 prefixEnd_6436314 3304922725262436125574937 := by
  unfold tailWord_6436314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58687914301085271940436999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156501104802894058507831997 58687914301085271940436999)
  ·
    refine ⟨88031871451627907910655499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58687914301085271940436999 88031871451627907910655499)
    ·
      refine ⟨132047807177441861865983249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88031871451627907910655499 132047807177441861865983249)
      ·
        refine ⟨99035855383081396399487437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132047807177441861865983249 99035855383081396399487437)
        ·
          refine ⟨37138445768655523649807789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99035855383081396399487437 37138445768655523649807789)
          ·
            refine ⟨13926917163245821368677921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37138445768655523649807789 13926917163245821368677921)
            ·
              refine ⟨10445187872434366026508441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13926917163245821368677921 10445187872434366026508441)
              ·
                refine ⟨7833890904325774519881331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445187872434366026508441 7833890904325774519881331)
                ·
                  refine ⟨11750836356488661779821997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833890904325774519881331 11750836356488661779821997)
                  ·
                    refine ⟨4406563633683248167433249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11750836356488661779821997 4406563633683248167433249)
                    ·
                      refine ⟨3304922725262436125574937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406563633683248167433249 3304922725262436125574937)
                      ·
                        rfl

theorem cell23_6436314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_6436314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436314 prefixEnd_6436314 := by exact prefixLift 6436314
  have htrace : WordTrace (prefixWord ++ tailWord_6436314) baseStart_6436314 baseEnd_6436314 := by
    simpa [prefixWord, tailWord_6436314, baseEnd_6436314] using wordTrace_append hprefix tailTrace_6436314
  have hstable : (prefixWord ++ tailWord_6436314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436314).length < 2 ^ (prefixWord ++ tailWord_6436314).sum := by decide
  have hdescent : baseEnd_6436314 < baseStart_6436314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436360 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_6436360 : Nat := 118140960795 + 6436360 * 2 ^ 59
def prefixEnd_6436360 : Nat := 4983230072969 + 3 ^ 40 * 6436360 * 2
def baseEnd_6436360 : Nat := 3304946345372542945599725

theorem tailTrace_6436360 : CollatzResearch.WordTrace tailWord_6436360 prefixEnd_6436360 3304946345372542945599725 := by
  unfold tailWord_6436360
  simp only [CollatzResearch.WordTrace]
  refine ⟨117376667481087218808961267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156502223308116291745281689 117376667481087218808961267)
  ·
    refine ⟨176065001221630828213441901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117376667481087218808961267 176065001221630828213441901)
    ·
      refine ⟨66024375458111560580040713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176065001221630828213441901 66024375458111560580040713)
      ·
        refine ⟨49518281593583670435030535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66024375458111560580040713 49518281593583670435030535)
        ·
          refine ⟨74277422390375505652545803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49518281593583670435030535 74277422390375505652545803)
          ·
            refine ⟨111416133585563258478818705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74277422390375505652545803 111416133585563258478818705)
            ·
              refine ⟨83562100189172443859114029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111416133585563258478818705 83562100189172443859114029)
              ·
                refine ⟨31335787570939666447167761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83562100189172443859114029 31335787570939666447167761)
                ·
                  refine ⟨23501840678204749835375821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31335787570939666447167761 23501840678204749835375821)
                  ·
                    refine ⟨8813190254326781188265933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23501840678204749835375821 8813190254326781188265933)
                    ·
                      refine ⟨3304946345372542945599725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813190254326781188265933 3304946345372542945599725)
                      ·
                        rfl

theorem cell23_6436360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_6436360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436360 prefixEnd_6436360 := by exact prefixLift 6436360
  have htrace : WordTrace (prefixWord ++ tailWord_6436360) baseStart_6436360 baseEnd_6436360 := by
    simpa [prefixWord, tailWord_6436360, baseEnd_6436360] using wordTrace_append hprefix tailTrace_6436360
  have hstable : (prefixWord ++ tailWord_6436360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436360).length < 2 ^ (prefixWord ++ tailWord_6436360).sum := by decide
  have hdescent : baseEnd_6436360 < baseStart_6436360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436365 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6436365 : Nat := 118140960795 + 6436365 * 2 ^ 59
def prefixEnd_6436365 : Nat := 4983230072969 + 3 ^ 40 * 6436365 * 2
def baseEnd_6436365 : Nat := 3304948912775815426037203

theorem tailTrace_6436365 : CollatzResearch.WordTrace tailWord_6436365 prefixEnd_6436365 3304948912775815426037203 := by
  unfold tailWord_6436365
  simp only [CollatzResearch.WordTrace]
  refine ⟨234753517327156323471854549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156502344884770882314569699 234753517327156323471854549)
  ·
    refine ⟨5502035562355226331371591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 234753517327156323471854549 5502035562355226331371591)
    ·
      refine ⟨8253053343532839497057387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502035562355226331371591 8253053343532839497057387)
      ·
        refine ⟨12379580015299259245586081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253053343532839497057387 12379580015299259245586081)
        ·
          refine ⟨9284685011474444434189561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12379580015299259245586081 9284685011474444434189561)
          ·
            refine ⟨6963513758605833325642171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9284685011474444434189561 6963513758605833325642171)
            ·
              refine ⟨10445270637908749988463257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963513758605833325642171 10445270637908749988463257)
              ·
                refine ⟨7833952978431562491347443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445270637908749988463257 7833952978431562491347443)
                ·
                  refine ⟨11750929467647343737021165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833952978431562491347443 11750929467647343737021165)
                  ·
                    refine ⟨4406598550367753901382937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11750929467647343737021165 4406598550367753901382937)
                    ·
                      refine ⟨3304948912775815426037203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406598550367753901382937 3304948912775815426037203)
                      ·
                        rfl

theorem cell23_6436365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6436365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436365 prefixEnd_6436365 := by exact prefixLift 6436365
  have htrace : WordTrace (prefixWord ++ tailWord_6436365) baseStart_6436365 baseEnd_6436365 := by
    simpa [prefixWord, tailWord_6436365, baseEnd_6436365] using wordTrace_append hprefix tailTrace_6436365
  have hstable : (prefixWord ++ tailWord_6436365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436365).length < 2 ^ (prefixWord ++ tailWord_6436365).sum := by decide
  have hdescent : baseEnd_6436365 < baseStart_6436365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436382 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6436382 : Nat := 118140960795 + 6436382 * 2 ^ 59
def prefixEnd_6436382 : Nat := 4983230072969 + 3 ^ 40 * 6436382 * 2
def baseEnd_6436382 : Nat := 3304957641946941859524625

theorem tailTrace_6436382 : CollatzResearch.WordTrace tailWord_6436382 prefixEnd_6436382 3304957641946941859524625 := by
  unfold tailWord_6436382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344267171011841921902925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156502758245396490250148933 29344267171011841921902925)
  ·
    refine ⟨11004100189129440720713597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29344267171011841921902925 11004100189129440720713597)
    ·
      refine ⟨4126537570923540270267599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11004100189129440720713597 4126537570923540270267599)
      ·
        refine ⟨6189806356385310405401399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126537570923540270267599 6189806356385310405401399)
        ·
          refine ⟨9284709534577965608102099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189806356385310405401399 9284709534577965608102099)
          ·
            refine ⟨13927064301866948412153149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9284709534577965608102099 13927064301866948412153149)
            ·
              refine ⟨5222649113200105654557431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13927064301866948412153149 5222649113200105654557431)
              ·
                refine ⟨7833973669800158481836147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222649113200105654557431 7833973669800158481836147)
                ·
                  refine ⟨11750960504700237722754221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833973669800158481836147 11750960504700237722754221)
                  ·
                    refine ⟨4406610189262589146032833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11750960504700237722754221 4406610189262589146032833)
                    ·
                      refine ⟨3304957641946941859524625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406610189262589146032833 3304957641946941859524625)
                      ·
                        rfl

theorem cell23_6436382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6436382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436382 prefixEnd_6436382 := by exact prefixLift 6436382
  have htrace : WordTrace (prefixWord ++ tailWord_6436382) baseStart_6436382 baseEnd_6436382 := by
    simpa [prefixWord, tailWord_6436382, baseEnd_6436382] using wordTrace_append hprefix tailTrace_6436382
  have hstable : (prefixWord ++ tailWord_6436382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436382).length < 2 ^ (prefixWord ++ tailWord_6436382).sum := by decide
  have hdescent : baseEnd_6436382 < baseStart_6436382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436434 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_6436434 : Nat := 118140960795 + 6436434 * 2 ^ 59
def prefixEnd_6436434 : Nat := 4983230072969 + 3 ^ 40 * 6436434 * 2
def baseEnd_6436434 : Nat := 3304984342940975656074385

theorem tailTrace_6436434 : CollatzResearch.WordTrace tailWord_6436434 prefixEnd_6436434 3304984342940975656074385 := by
  unfold tailWord_6436434
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689008490976587064029089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156504022642604232170744237 58689008490976587064029089)
  ·
    refine ⟨44016756368232440298021817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58689008490976587064029089 44016756368232440298021817)
    ·
      refine ⟨33012567276174330223516363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44016756368232440298021817 33012567276174330223516363)
      ·
        refine ⟨49518850914261495335274545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33012567276174330223516363 49518850914261495335274545)
        ·
          refine ⟨37139138185696121501455909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49518850914261495335274545 37139138185696121501455909)
          ·
            refine ⟨6963588409818022781522983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37139138185696121501455909 6963588409818022781522983)
            ·
              refine ⟨10445382614727034172284475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963588409818022781522983 10445382614727034172284475)
              ·
                refine ⟨15668073922090551258426713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10445382614727034172284475 15668073922090551258426713)
                ·
                  refine ⟨11751055441567913443820035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15668073922090551258426713 11751055441567913443820035)
                  ·
                    refine ⟨17626583162351870165730053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11751055441567913443820035 17626583162351870165730053)
                    ·
                      refine ⟨3304984342940975656074385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17626583162351870165730053 3304984342940975656074385)
                      ·
                        rfl

theorem cell23_6436434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_6436434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436434 prefixEnd_6436434 := by exact prefixLift 6436434
  have htrace : WordTrace (prefixWord ++ tailWord_6436434) baseStart_6436434 baseEnd_6436434 := by
    simpa [prefixWord, tailWord_6436434, baseEnd_6436434] using wordTrace_append hprefix tailTrace_6436434
  have hstable : (prefixWord ++ tailWord_6436434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436434).length < 2 ^ (prefixWord ++ tailWord_6436434).sum := by decide
  have hdescent : baseEnd_6436434 < baseStart_6436434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436487 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 1, 5]
def baseStart_6436487 : Nat := 118140960795 + 6436487 * 2 ^ 59
def prefixEnd_6436487 : Nat := 4983230072969 + 3 ^ 40 * 6436487 * 2
def baseEnd_6436487 : Nat := 1101670519138554649570547

theorem tailTrace_6436487 : CollatzResearch.WordTrace tailWord_6436487 prefixEnd_6436487 1101670519138554649570547 := by
  unfold tailWord_6436487
  simp only [CollatzResearch.WordTrace]
  refine ⟨234757967032714338307795715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156505311355142892205197143 234757967032714338307795715)
  ·
    refine ⟨352136950549071507461693573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234757967032714338307795715 352136950549071507461693573)
    ·
      refine ⟨66025678227950907649067545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352136950549071507461693573 66025678227950907649067545)
      ·
        refine ⟨49519258670963180736800659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66025678227950907649067545 49519258670963180736800659)
        ·
          refine ⟨74278888006444771105200989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49519258670963180736800659 74278888006444771105200989)
          ·
            refine ⟨27854583002416789164450371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74278888006444771105200989 27854583002416789164450371)
            ·
              refine ⟨41781874503625183746675557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27854583002416789164450371 41781874503625183746675557)
              ·
                refine ⟨7834101469429721952501667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41781874503625183746675557 7834101469429721952501667)
                ·
                  refine ⟨11751152204144582928752501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834101469429721952501667 11751152204144582928752501)
                  ·
                    refine ⟨1101670519138554649570547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11751152204144582928752501 1101670519138554649570547)
                    ·
                      rfl

theorem cell23_6436487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_6436487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436487 prefixEnd_6436487 := by exact prefixLift 6436487
  have htrace : WordTrace (prefixWord ++ tailWord_6436487) baseStart_6436487 baseEnd_6436487 := by
    simpa [prefixWord, tailWord_6436487, baseEnd_6436487] using wordTrace_append hprefix tailTrace_6436487
  have hstable : (prefixWord ++ tailWord_6436487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436487).length < 2 ^ (prefixWord ++ tailWord_6436487).sum := by decide
  have hdescent : baseEnd_6436487 < baseStart_6436487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436494 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6436494 : Nat := 118140960795 + 6436494 * 2 ^ 59
def prefixEnd_6436494 : Nat := 4983230072969 + 3 ^ 40 * 6436494 * 2
def baseEnd_6436494 : Nat := 3305015151780245421324109

theorem tailTrace_6436494 : CollatzResearch.WordTrace tailWord_6436494 prefixEnd_6436494 3305015151780245421324109 := by
  unfold tailWord_6436494
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344777792961122312912567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156505481562459319002200357 29344777792961122312912567)
  ·
    refine ⟨44017166689441683469368851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29344777792961122312912567 44017166689441683469368851)
    ·
      refine ⟨66025750034162525204053277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44017166689441683469368851 66025750034162525204053277)
      ·
        refine ⟨24759656262810946951519979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66025750034162525204053277 24759656262810946951519979)
        ·
          refine ⟨37139484394216420427279969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24759656262810946951519979 37139484394216420427279969)
          ·
            refine ⟨27854613295662315320459977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37139484394216420427279969 27854613295662315320459977)
            ·
              refine ⟨20890959971746736490344983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27854613295662315320459977 20890959971746736490344983)
              ·
                refine ⟨31336439957620104735517475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20890959971746736490344983 31336439957620104735517475)
                ·
                  refine ⟨47004659936430157103276213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31336439957620104735517475 47004659936430157103276213)
                  ·
                    refine ⟨4406686869040327228432145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47004659936430157103276213 4406686869040327228432145)
                    ·
                      refine ⟨3305015151780245421324109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406686869040327228432145 3305015151780245421324109)
                      ·
                        rfl

theorem cell23_6436494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6436494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436494 prefixEnd_6436494 := by exact prefixLift 6436494
  have htrace : WordTrace (prefixWord ++ tailWord_6436494) baseStart_6436494 baseEnd_6436494 := by
    simpa [prefixWord, tailWord_6436494, baseEnd_6436494] using wordTrace_append hprefix tailTrace_6436494
  have hstable : (prefixWord ++ tailWord_6436494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436494).length < 2 ^ (prefixWord ++ tailWord_6436494).sum := by decide
  have hdescent : baseEnd_6436494 < baseStart_6436494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436517 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_6436517 : Nat := 118140960795 + 6436517 * 2 ^ 59
def prefixEnd_6436517 : Nat := 4983230072969 + 3 ^ 40 * 6436517 * 2
def baseEnd_6436517 : Nat := 1101675653945099610445501

theorem tailTrace_6436517 : CollatzResearch.WordTrace tailWord_6436517 prefixEnd_6436517 1101675653945099610445501 := by
  unfold tailWord_6436517
  simp only [CollatzResearch.WordTrace]
  refine ⟨234759061222605653431387805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156506040815070435620925203 234759061222605653431387805)
  ·
    refine ⟨88034647958477120036770427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234759061222605653431387805 88034647958477120036770427)
    ·
      refine ⟨132051971937715680055155641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88034647958477120036770427 132051971937715680055155641)
      ·
        refine ⟨99038978953286760041366731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132051971937715680055155641 99038978953286760041366731)
        ·
          refine ⟨148558468429930140062050097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99038978953286760041366731 148558468429930140062050097)
          ·
            refine ⟨111418851322447605046537573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148558468429930140062050097 111418851322447605046537573)
            ·
              refine ⟨20891034622958925946225795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111418851322447605046537573 20891034622958925946225795)
              ·
                refine ⟨31336551934438388919338693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20891034622958925946225795 31336551934438388919338693)
                ·
                  refine ⟨5875603487707197922376005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31336551934438388919338693 5875603487707197922376005)
                  ·
                    refine ⟨1101675653945099610445501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5875603487707197922376005 1101675653945099610445501)
                    ·
                      rfl

theorem cell23_6436517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_6436517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436517 prefixEnd_6436517 := by exact prefixLift 6436517
  have htrace : WordTrace (prefixWord ++ tailWord_6436517) baseStart_6436517 baseEnd_6436517 := by
    simpa [prefixWord, tailWord_6436517, baseEnd_6436517] using wordTrace_append hprefix tailTrace_6436517
  have hstable : (prefixWord ++ tailWord_6436517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436517).length < 2 ^ (prefixWord ++ tailWord_6436517).sum := by decide
  have hdescent : baseEnd_6436517 < baseStart_6436517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436527 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_6436527 : Nat := 118140960795 + 6436527 * 2 ^ 59
def prefixEnd_6436527 : Nat := 4983230072969 + 3 ^ 40 * 6436527 * 2
def baseEnd_6436527 : Nat := 3305032096641843792211457

theorem tailTrace_6436527 : CollatzResearch.WordTrace tailWord_6436527 prefixEnd_6436527 3305032096641843792211457 := by
  unfold tailWord_6436527
  simp only [CollatzResearch.WordTrace]
  refine ⟨234759425952569425139251835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156506283968379616759501223 234759425952569425139251835)
  ·
    refine ⟨352139138928854137708877753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234759425952569425139251835 352139138928854137708877753)
    ·
      refine ⟨264104354196640603281658315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352139138928854137708877753 264104354196640603281658315)
      ·
        refine ⟨396156531294960904922487473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264104354196640603281658315 396156531294960904922487473)
        ·
          refine ⟨297117398471220678691865605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396156531294960904922487473 297117398471220678691865605)
          ·
            refine ⟨55709512213353877254724801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297117398471220678691865605 55709512213353877254724801)
            ·
              refine ⟨41782134160015407941043601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55709512213353877254724801 41782134160015407941043601)
              ·
                refine ⟨31336600620011555955782701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41782134160015407941043601 31336600620011555955782701)
                ·
                  refine ⟨11751225232504333483418513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31336600620011555955782701 11751225232504333483418513)
                  ·
                    refine ⟨8813418924378250112563885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11751225232504333483418513 8813418924378250112563885)
                    ·
                      refine ⟨3305032096641843792211457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813418924378250112563885 3305032096641843792211457)
                      ·
                        rfl

theorem cell23_6436527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_6436527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436527 prefixEnd_6436527 := by exact prefixLift 6436527
  have htrace : WordTrace (prefixWord ++ tailWord_6436527) baseStart_6436527 baseEnd_6436527 := by
    simpa [prefixWord, tailWord_6436527, baseEnd_6436527] using wordTrace_append hprefix tailTrace_6436527
  have hstable : (prefixWord ++ tailWord_6436527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436527).length < 2 ^ (prefixWord ++ tailWord_6436527).sum := by decide
  have hdescent : baseEnd_6436527 < baseStart_6436527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436530 : List Nat := [3, 2, 1, 1, 1, 2, 3, 10]
def baseStart_6436530 : Nat := 118140960795 + 6436530 * 2 ^ 59
def prefixEnd_6436530 : Nat := 4983230072969 + 3 ^ 40 * 6436530 * 2
def baseEnd_6436530 : Nat := 122408653225326195573109

theorem tailTrace_6436530 : CollatzResearch.WordTrace tailWord_6436530 prefixEnd_6436530 122408653225326195573109 := by
  unfold tailWord_6436530
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689883842889639162902761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156506356914372371101074029 58689883842889639162902761)
  ·
    refine ⟨44017412882167229372177071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58689883842889639162902761 44017412882167229372177071)
    ·
      refine ⟨66026119323250844058265607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44017412882167229372177071 66026119323250844058265607)
      ·
        refine ⟨99039178984876266087398411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66026119323250844058265607 99039178984876266087398411)
        ·
          refine ⟨148558768477314399131097617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99039178984876266087398411 148558768477314399131097617)
          ·
            refine ⟨111419076357985799348323213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148558768477314399131097617 111419076357985799348323213)
            ·
              refine ⟨41782153634244674755621205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111419076357985799348323213 41782153634244674755621205)
              ·
                refine ⟨122408653225326195573109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41782153634244674755621205 122408653225326195573109)
                ·
                  rfl

theorem cell23_6436530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_6436530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436530 prefixEnd_6436530 := by exact prefixLift 6436530
  have htrace : WordTrace (prefixWord ++ tailWord_6436530) baseStart_6436530 baseEnd_6436530 := by
    simpa [prefixWord, tailWord_6436530, baseEnd_6436530] using wordTrace_append hprefix tailTrace_6436530
  have hstable : (prefixWord ++ tailWord_6436530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436530).length < 2 ^ (prefixWord ++ tailWord_6436530).sum := by decide
  have hdescent : baseEnd_6436530 < baseStart_6436530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436554 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_6436554 : Nat := 118140960795 + 6436554 * 2 ^ 59
def prefixEnd_6436554 : Nat := 4983230072969 + 3 ^ 40 * 6436554 * 2
def baseEnd_6436554 : Nat := 3305045960619515186573833

theorem tailTrace_6436554 : CollatzResearch.WordTrace tailWord_6436554 prefixEnd_6436554 3305045960619515186573833 := by
  unfold tailWord_6436554
  simp only [CollatzResearch.WordTrace]
  refine ⟨58690102680867902187621179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156506940482314405833656477 58690102680867902187621179)
  ·
    refine ⟨88035154021301853281431769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58690102680867902187621179 88035154021301853281431769)
    ·
      refine ⟨66026365515976389961073827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88035154021301853281431769 66026365515976389961073827)
      ·
        refine ⟨99039548273964584941610741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66026365515976389961073827 99039548273964584941610741)
        ·
          refine ⟨9284957650684179838276007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99039548273964584941610741 9284957650684179838276007)
          ·
            refine ⟨13927436476026269757414011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9284957650684179838276007 13927436476026269757414011)
            ·
              refine ⟨20891154714039404636121017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13927436476026269757414011 20891154714039404636121017)
              ·
                refine ⟨15668366035529553477090763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20891154714039404636121017 15668366035529553477090763)
                ·
                  refine ⟨23502549053294330215636145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15668366035529553477090763 23502549053294330215636145)
                  ·
                    refine ⟨17626911789970747661727109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23502549053294330215636145 17626911789970747661727109)
                    ·
                      refine ⟨3305045960619515186573833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17626911789970747661727109 3305045960619515186573833)
                      ·
                        rfl

theorem cell23_6436554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_6436554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436554 prefixEnd_6436554 := by exact prefixLift 6436554
  have htrace : WordTrace (prefixWord ++ tailWord_6436554) baseStart_6436554 baseEnd_6436554 := by
    simpa [prefixWord, tailWord_6436554, baseEnd_6436554] using wordTrace_append hprefix tailTrace_6436554
  have hstable : (prefixWord ++ tailWord_6436554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436554).length < 2 ^ (prefixWord ++ tailWord_6436554).sum := by decide
  have hdescent : baseEnd_6436554 < baseStart_6436554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436558 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_6436558 : Nat := 118140960795 + 6436558 * 2 ^ 59
def prefixEnd_6436558 : Nat := 4983230072969 + 3 ^ 40 * 6436558 * 2
def baseEnd_6436558 : Nat := 3305048014542133170923815

theorem tailTrace_6436558 : CollatzResearch.WordTrace tailWord_6436558 prefixEnd_6436558 3305048014542133170923815 := by
  unfold tailWord_6436558
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345069576932139679203791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156507037743638078289086885 29345069576932139679203791)
  ·
    refine ⟨44017604365398209518805687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29345069576932139679203791 44017604365398209518805687)
    ·
      refine ⟨66026406548097314278208531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44017604365398209518805687 66026406548097314278208531)
      ·
        refine ⟨99039609822145971417312797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66026406548097314278208531 99039609822145971417312797)
        ·
          refine ⟨37139853683304739281492299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99039609822145971417312797 37139853683304739281492299)
          ·
            refine ⟨55709780524957108922238449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37139853683304739281492299 55709780524957108922238449)
            ·
              refine ⟨41782335393717831691678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55709780524957108922238449 41782335393717831691678837)
              ·
                refine ⟨3917093943161046721094891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41782335393717831691678837 3917093943161046721094891)
                ·
                  refine ⟨5875640914741570081642337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917093943161046721094891 5875640914741570081642337)
                  ·
                    refine ⟨4406730686056177561231753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5875640914741570081642337 4406730686056177561231753)
                    ·
                      refine ⟨3305048014542133170923815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406730686056177561231753 3305048014542133170923815)
                      ·
                        rfl

theorem cell23_6436558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_6436558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436558 prefixEnd_6436558 := by exact prefixLift 6436558
  have htrace : WordTrace (prefixWord ++ tailWord_6436558) baseStart_6436558 baseEnd_6436558 := by
    simpa [prefixWord, tailWord_6436558, baseEnd_6436558] using wordTrace_append hprefix tailTrace_6436558
  have hstable : (prefixWord ++ tailWord_6436558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436558).length < 2 ^ (prefixWord ++ tailWord_6436558).sum := by decide
  have hdescent : baseEnd_6436558 < baseStart_6436558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436561 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_6436561 : Nat := 118140960795 + 6436561 * 2 ^ 59
def prefixEnd_6436561 : Nat := 4983230072969 + 3 ^ 40 * 6436561 * 2
def baseEnd_6436561 : Nat := 3305049554984096659186301

theorem tailTrace_6436561 : CollatzResearch.WordTrace tailWord_6436561 prefixEnd_6436561 3305049554984096659186301 := by
  unfold tailWord_6436561
  simp only [CollatzResearch.WordTrace]
  refine ⟨234760666034446248945989537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156507110689630832630659691 234760666034446248945989537)
  ·
    refine ⟨176070499525834686709492153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234760666034446248945989537 176070499525834686709492153)
    ·
      refine ⟨132052874644376015032119115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176070499525834686709492153 132052874644376015032119115)
      ·
        refine ⟨198079311966564022548178673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132052874644376015032119115 198079311966564022548178673)
        ·
          refine ⟨148559483974923016911134005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198079311966564022548178673 148559483974923016911134005)
          ·
            refine ⟨13927451622649032835418813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148559483974923016911134005 13927451622649032835418813)
            ·
              refine ⟨5222794358493387313282055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13927451622649032835418813 5222794358493387313282055)
              ·
                refine ⟨7834191537740080969923083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222794358493387313282055 7834191537740080969923083)
                ·
                  refine ⟨11751287306610121454884625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834191537740080969923083 11751287306610121454884625)
                  ·
                    refine ⟨8813465479957591091163469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11751287306610121454884625 8813465479957591091163469)
                    ·
                      refine ⟨3305049554984096659186301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813465479957591091163469 3305049554984096659186301)
                      ·
                        rfl

theorem cell23_6436561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_6436561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436561 prefixEnd_6436561 := by exact prefixLift 6436561
  have htrace : WordTrace (prefixWord ++ tailWord_6436561) baseStart_6436561 baseEnd_6436561 := by
    simpa [prefixWord, tailWord_6436561, baseEnd_6436561] using wordTrace_append hprefix tailTrace_6436561
  have hstable : (prefixWord ++ tailWord_6436561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436561).length < 2 ^ (prefixWord ++ tailWord_6436561).sum := by decide
  have hdescent : baseEnd_6436561 < baseStart_6436561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436618 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_6436618 : Nat := 118140960795 + 6436618 * 2 ^ 59
def prefixEnd_6436618 : Nat := 4983230072969 + 3 ^ 40 * 6436618 * 2
def baseEnd_6436618 : Nat := 3305078823381402936173539

theorem tailTrace_6436618 : CollatzResearch.WordTrace tailWord_6436618 prefixEnd_6436618 3305078823381402936173539 := by
  unfold tailWord_6436618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58690686248809936920203627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156508496663493165120543005 58690686248809936920203627)
  ·
    refine ⟨88036029373214905380305441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58690686248809936920203627 88036029373214905380305441)
    ·
      refine ⟨66027022029911179035229081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88036029373214905380305441 66027022029911179035229081)
      ·
        refine ⟨49520266522433384276421811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66027022029911179035229081 49520266522433384276421811)
        ·
          refine ⟨74280399783650076414632717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49520266522433384276421811 74280399783650076414632717)
          ·
            refine ⟨27855149918868778655487269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74280399783650076414632717 27855149918868778655487269)
            ·
              refine ⟨5222840609787895997903863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27855149918868778655487269 5222840609787895997903863)
              ·
                refine ⟨7834260914681843996855795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222840609787895997903863 7834260914681843996855795)
                ·
                  refine ⟨11751391372022765995283693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834260914681843996855795 11751391372022765995283693)
                  ·
                    refine ⟨4406771764508537248231385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11751391372022765995283693 4406771764508537248231385)
                    ·
                      refine ⟨3305078823381402936173539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406771764508537248231385 3305078823381402936173539)
                      ·
                        rfl

theorem cell23_6436618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_6436618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436618 prefixEnd_6436618 := by exact prefixLift 6436618
  have htrace : WordTrace (prefixWord ++ tailWord_6436618) baseStart_6436618 baseEnd_6436618 := by
    simpa [prefixWord, tailWord_6436618, baseEnd_6436618] using wordTrace_append hprefix tailTrace_6436618
  have hstable : (prefixWord ++ tailWord_6436618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436618).length < 2 ^ (prefixWord ++ tailWord_6436618).sum := by decide
  have hdescent : baseEnd_6436618 < baseStart_6436618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436644 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6436644 : Nat := 118140960795 + 6436644 * 2 ^ 59
def prefixEnd_6436644 : Nat := 4983230072969 + 3 ^ 40 * 6436644 * 2
def baseEnd_6436644 : Nat := 3305092173878419834448419

theorem tailTrace_6436644 : CollatzResearch.WordTrace tailWord_6436644 prefixEnd_6436644 3305092173878419834448419 := by
  unfold tailWord_6436644
  simp only [CollatzResearch.WordTrace]
  refine ⟨117381846646572777060630493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156509128862097036080840657 117381846646572777060630493)
  ·
    refine ⟨44018192492464791397736435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117381846646572777060630493 44018192492464791397736435)
    ·
      refine ⟨66027288738697187096604653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44018192492464791397736435 66027288738697187096604653)
      ·
        refine ⟨24760233277011445161226745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66027288738697187096604653 24760233277011445161226745)
        ·
          refine ⟨18570174957758583870920059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24760233277011445161226745 18570174957758583870920059)
          ·
            refine ⟨27855262436637875806380089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18570174957758583870920059 27855262436637875806380089)
            ·
              refine ⟨20891446827478406854785067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27855262436637875806380089 20891446827478406854785067)
              ·
                refine ⟨31337170241217610282177601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20891446827478406854785067 31337170241217610282177601)
                ·
                  refine ⟨23502877680913207711633201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31337170241217610282177601 23502877680913207711633201)
                  ·
                    refine ⟨17627158260684905783724901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23502877680913207711633201 17627158260684905783724901)
                    ·
                      refine ⟨3305092173878419834448419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17627158260684905783724901 3305092173878419834448419)
                      ·
                        rfl

theorem cell23_6436644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6436644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436644 prefixEnd_6436644 := by exact prefixLift 6436644
  have htrace : WordTrace (prefixWord ++ tailWord_6436644) baseStart_6436644 baseEnd_6436644 := by
    simpa [prefixWord, tailWord_6436644, baseEnd_6436644] using wordTrace_append hprefix tailTrace_6436644
  have hstable : (prefixWord ++ tailWord_6436644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436644).length < 2 ^ (prefixWord ++ tailWord_6436644).sum := by decide
  have hdescent : baseEnd_6436644 < baseStart_6436644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436648 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6436648 : Nat := 118140960795 + 6436648 * 2 ^ 59
def prefixEnd_6436648 : Nat := 4983230072969 + 3 ^ 40 * 6436648 * 2
def baseEnd_6436648 : Nat := 3305094227801037818798401

theorem tailTrace_6436648 : CollatzResearch.WordTrace tailWord_6436648 prefixEnd_6436648 3305094227801037818798401 := by
  unfold tailWord_6436648
  simp only [CollatzResearch.WordTrace]
  refine ⟨117381919592565531402203299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156509226123420708536271065 117381919592565531402203299)
  ·
    refine ⟨176072879388848297103304949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117381919592565531402203299 176072879388848297103304949)
    ·
      refine ⟨16506832442704527853434839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176072879388848297103304949 16506832442704527853434839)
      ·
        refine ⟨24760248664056791780152259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16506832442704527853434839 24760248664056791780152259)
        ·
          refine ⟨37140372996085187670228389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24760248664056791780152259 37140372996085187670228389)
          ·
            refine ⟨6963819936765972688167823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37140372996085187670228389 6963819936765972688167823)
            ·
              refine ⟨10445729905148959032251735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963819936765972688167823 10445729905148959032251735)
              ·
                refine ⟨15668594857723438548377603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10445729905148959032251735 15668594857723438548377603)
                ·
                  refine ⟨23502892286585157822566405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15668594857723438548377603 23502892286585157822566405)
                  ·
                    refine ⟨4406792303734717091731201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23502892286585157822566405 4406792303734717091731201)
                    ·
                      refine ⟨3305094227801037818798401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406792303734717091731201 3305094227801037818798401)
                      ·
                        rfl

theorem cell23_6436648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6436648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436648 prefixEnd_6436648 := by exact prefixLift 6436648
  have htrace : WordTrace (prefixWord ++ tailWord_6436648) baseStart_6436648 baseEnd_6436648 := by
    simpa [prefixWord, tailWord_6436648, baseEnd_6436648] using wordTrace_append hprefix tailTrace_6436648
  have hstable : (prefixWord ++ tailWord_6436648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436648).length < 2 ^ (prefixWord ++ tailWord_6436648).sum := by decide
  have hdescent : baseEnd_6436648 < baseStart_6436648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436677 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_6436677 : Nat := 118140960795 + 6436677 * 2 ^ 59
def prefixEnd_6436677 : Nat := 4983230072969 + 3 ^ 40 * 6436677 * 2
def baseEnd_6436677 : Nat := 3305109118740018205335767

theorem tailTrace_6436677 : CollatzResearch.WordTrace tailWord_6436677 prefixEnd_6436677 3305109118740018205335767 := by
  unfold tailWord_6436677
  simp only [CollatzResearch.WordTrace]
  refine ⟨234764896902026000757212285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156509931268017333838141523 234764896902026000757212285)
  ·
    refine ⟨88036836338259750283954607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234764896902026000757212285 88036836338259750283954607)
    ·
      refine ⟨132055254507389625425931911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88036836338259750283954607 132055254507389625425931911)
      ·
        refine ⟨198082881761084438138897867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132055254507389625425931911 198082881761084438138897867)
        ·
          refine ⟨297124322641626657208346801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198082881761084438138897867 297124322641626657208346801)
          ·
            refine ⟨222843241981219992906260101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297124322641626657208346801 222843241981219992906260101)
            ·
              refine ⟨41783107871478748669923769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222843241981219992906260101 41783107871478748669923769)
              ·
                refine ⟨31337330903609061502442827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41783107871478748669923769 31337330903609061502442827)
                ·
                  refine ⟨47005996355413592253664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31337330903609061502442827 47005996355413592253664241)
                  ·
                    refine ⟨35254497266560194190248181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47005996355413592253664241 35254497266560194190248181)
                    ·
                      refine ⟨3305109118740018205335767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35254497266560194190248181 3305109118740018205335767)
                      ·
                        rfl

theorem cell23_6436677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_6436677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436677 prefixEnd_6436677 := by exact prefixLift 6436677
  have htrace : WordTrace (prefixWord ++ tailWord_6436677) baseStart_6436677 baseEnd_6436677 := by
    simpa [prefixWord, tailWord_6436677, baseEnd_6436677] using wordTrace_append hprefix tailTrace_6436677
  have hstable : (prefixWord ++ tailWord_6436677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436677).length < 2 ^ (prefixWord ++ tailWord_6436677).sum := by decide
  have hdescent : baseEnd_6436677 < baseStart_6436677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436731 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 1, 4]
def baseStart_6436731 : Nat := 118140960795 + 6436731 * 2 ^ 59
def prefixEnd_6436731 : Nat := 4983230072969 + 3 ^ 40 * 6436731 * 2
def baseEnd_6436731 : Nat := 1101712282231786998020173

theorem tailTrace_6436731 : CollatzResearch.WordTrace tailWord_6436731 prefixEnd_6436731 1101712282231786998020173 := by
  unfold tailWord_6436731
  simp only [CollatzResearch.WordTrace]
  refine ⟨234766866443830367979678047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156511244295886911986452031 234766866443830367979678047)
  ·
    refine ⟨352150299665745551969517071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234766866443830367979678047 352150299665745551969517071)
    ·
      refine ⟨528225449498618327954275607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352150299665745551969517071 528225449498618327954275607)
      ·
        refine ⟨792338174247927491931413411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528225449498618327954275607 792338174247927491931413411)
        ·
          refine ⟨1188507261371891237897120117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792338174247927491931413411 1188507261371891237897120117)
          ·
            refine ⟨111422555753614803552855011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1188507261371891237897120117 111422555753614803552855011)
            ·
              refine ⟨167133833630422205329282517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111422555753614803552855011 167133833630422205329282517)
              ·
                refine ⟨3917199225713020437405059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167133833630422205329282517 3917199225713020437405059)
                ·
                  refine ⟨5875798838569530656107589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917199225713020437405059 5875798838569530656107589)
                  ·
                    refine ⟨1101712282231786998020173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5875798838569530656107589 1101712282231786998020173)
                    ·
                      rfl

theorem cell23_6436731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 4].length) (baseStart_6436731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436731 prefixEnd_6436731 := by exact prefixLift 6436731
  have htrace : WordTrace (prefixWord ++ tailWord_6436731) baseStart_6436731 baseEnd_6436731 := by
    simpa [prefixWord, tailWord_6436731, baseEnd_6436731] using wordTrace_append hprefix tailTrace_6436731
  have hstable : (prefixWord ++ tailWord_6436731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436731).length < 2 ^ (prefixWord ++ tailWord_6436731).sum := by decide
  have hdescent : baseEnd_6436731 < baseStart_6436731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436747 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_6436747 : Nat := 118140960795 + 6436747 * 2 ^ 59
def prefixEnd_6436747 : Nat := 4983230072969 + 3 ^ 40 * 6436747 * 2
def baseEnd_6436747 : Nat := 3305145062385832931460445

theorem tailTrace_6436747 : CollatzResearch.WordTrace tailWord_6436747 prefixEnd_6436747 3305145062385832931460445 := by
  unfold tailWord_6436747
  simp only [CollatzResearch.WordTrace]
  refine ⟨234767450011772402712260495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156511633341181601808173663 234767450011772402712260495)
  ·
    refine ⟨352151175017658604068390743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234767450011772402712260495 352151175017658604068390743)
    ·
      refine ⟨528226762526487906102586115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352151175017658604068390743 528226762526487906102586115)
      ·
        refine ⟨792340143789731859153879173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528226762526487906102586115 792340143789731859153879173)
        ·
          refine ⟨148563776960574723591352345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 792340143789731859153879173 148563776960574723591352345)
          ·
            refine ⟨111422832720431042693514259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148563776960574723591352345 111422832720431042693514259)
            ·
              refine ⟨167134249080646564040271389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111422832720431042693514259 167134249080646564040271389)
              ·
                refine ⟨62675343405242461515101771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167134249080646564040271389 62675343405242461515101771)
                ·
                  refine ⟨94013015107863692272652657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62675343405242461515101771 94013015107863692272652657)
                  ·
                    refine ⟨70509761330897769204489493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94013015107863692272652657 70509761330897769204489493)
                    ·
                      refine ⟨3305145062385832931460445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70509761330897769204489493 3305145062385832931460445)
                      ·
                        rfl

theorem cell23_6436747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_6436747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436747 prefixEnd_6436747 := by exact prefixLift 6436747
  have htrace : WordTrace (prefixWord ++ tailWord_6436747) baseStart_6436747 baseEnd_6436747 := by
    simpa [prefixWord, tailWord_6436747, baseEnd_6436747] using wordTrace_append hprefix tailTrace_6436747
  have hstable : (prefixWord ++ tailWord_6436747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436747).length < 2 ^ (prefixWord ++ tailWord_6436747).sum := by decide
  have hdescent : baseEnd_6436747 < baseStart_6436747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436794 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_6436794 : Nat := 118140960795 + 6436794 * 2 ^ 59
def prefixEnd_6436794 : Nat := 4983230072969 + 3 ^ 40 * 6436794 * 2
def baseEnd_6436794 : Nat := 3305169195976594247572729

theorem tailTrace_6436794 : CollatzResearch.WordTrace tailWord_6436794 prefixEnd_6436794 3305169195976594247572729 := by
  unfold tailWord_6436794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58692291060650532434805359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156512776161734753159480957 58692291060650532434805359)
  ·
    refine ⟨88038436590975798652208039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58692291060650532434805359 88038436590975798652208039)
    ·
      refine ⟨132057654886463697978312059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88038436590975798652208039 132057654886463697978312059)
      ·
        refine ⟨198086482329695546967468089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132057654886463697978312059 198086482329695546967468089)
        ·
          refine ⟨148564861747271660225601067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198086482329695546967468089 148564861747271660225601067)
          ·
            refine ⟨222847292620907490338401601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148564861747271660225601067 222847292620907490338401601)
            ·
              refine ⟨167135469465680617753801201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222847292620907490338401601 167135469465680617753801201)
              ·
                refine ⟨125351602099260463315350901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167135469465680617753801201 125351602099260463315350901)
                ·
                  refine ⟨11751712696805668435814147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125351602099260463315350901 11751712696805668435814147)
                  ·
                    refine ⟨17627569045208502653721221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11751712696805668435814147 17627569045208502653721221)
                    ·
                      refine ⟨3305169195976594247572729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17627569045208502653721221 3305169195976594247572729)
                      ·
                        rfl

theorem cell23_6436794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_6436794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436794 prefixEnd_6436794 := by exact prefixLift 6436794
  have htrace : WordTrace (prefixWord ++ tailWord_6436794) baseStart_6436794 baseEnd_6436794 := by
    simpa [prefixWord, tailWord_6436794, baseEnd_6436794] using wordTrace_append hprefix tailTrace_6436794
  have hstable : (prefixWord ++ tailWord_6436794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436794).length < 2 ^ (prefixWord ++ tailWord_6436794).sum := by decide
  have hdescent : baseEnd_6436794 < baseStart_6436794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436821 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_6436821 : Nat := 118140960795 + 6436821 * 2 ^ 59
def prefixEnd_6436821 : Nat := 4983230072969 + 3 ^ 40 * 6436821 * 2
def baseEnd_6436821 : Nat := 1101727686651421880645035

theorem tailTrace_6436821 : CollatzResearch.WordTrace tailWord_6436821 prefixEnd_6436821 1101727686651421880645035 := by
  unfold tailWord_6436821
  simp only [CollatzResearch.WordTrace]
  refine ⟨234770149013504313350454317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156513432675669542233636211 234770149013504313350454317)
  ·
    refine ⟨88038805880064117506420369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234770149013504313350454317 88038805880064117506420369)
    ·
      refine ⟨66029104410048088129815277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88038805880064117506420369 66029104410048088129815277)
      ·
        refine ⟨24760914153768033048680729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66029104410048088129815277 24760914153768033048680729)
        ·
          refine ⟨18570685615326024786510547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24760914153768033048680729 18570685615326024786510547)
          ·
            refine ⟨27856028422989037179765821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18570685615326024786510547 27856028422989037179765821)
            ·
              refine ⟨10446010658620888942412183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27856028422989037179765821 10446010658620888942412183)
              ·
                refine ⟨15669015987931333413618275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10446010658620888942412183 15669015987931333413618275)
                ·
                  refine ⟨23503523981897000120427413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15669015987931333413618275 23503523981897000120427413)
                  ·
                    refine ⟨1101727686651421880645035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23503523981897000120427413 1101727686651421880645035)
                    ·
                      rfl

theorem cell23_6436821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_6436821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436821 prefixEnd_6436821 := by exact prefixLift 6436821
  have htrace : WordTrace (prefixWord ++ tailWord_6436821) baseStart_6436821 baseEnd_6436821 := by
    simpa [prefixWord, tailWord_6436821, baseEnd_6436821] using wordTrace_append hprefix tailTrace_6436821
  have hstable : (prefixWord ++ tailWord_6436821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436821).length < 2 ^ (prefixWord ++ tailWord_6436821).sum := by decide
  have hdescent : baseEnd_6436821 < baseStart_6436821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436824 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6436824 : Nat := 118140960795 + 6436824 * 2 ^ 59
def prefixEnd_6436824 : Nat := 4983230072969 + 3 ^ 40 * 6436824 * 2
def baseEnd_6436824 : Nat := 3305184600396229130197591

theorem tailTrace_6436824 : CollatzResearch.WordTrace tailWord_6436824 prefixEnd_6436824 3305184600396229130197591 := by
  unfold tailWord_6436824
  simp only [CollatzResearch.WordTrace]
  refine ⟨117385129216246722431406763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156513505621662296575209017 117385129216246722431406763)
  ·
    refine ⟨176077693824370083647110145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117385129216246722431406763 176077693824370083647110145)
    ·
      refine ⟨132058270368277562735332609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176077693824370083647110145 132058270368277562735332609)
      ·
        refine ⟨99043702776208172051499457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132058270368277562735332609 99043702776208172051499457)
        ·
          refine ⟨74282777082156129038624593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99043702776208172051499457 74282777082156129038624593)
          ·
            refine ⟨55712082811617096778968445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74282777082156129038624593 55712082811617096778968445)
            ·
              refine ⟨20892031054356411292113167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55712082811617096778968445 20892031054356411292113167)
              ·
                refine ⟨31338046581534616938169751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20892031054356411292113167 31338046581534616938169751)
                ·
                  refine ⟨47007069872301925407254627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31338046581534616938169751 47007069872301925407254627)
                  ·
                    refine ⟨70510604808452888110881941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47007069872301925407254627 70510604808452888110881941)
                    ·
                      refine ⟨3305184600396229130197591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70510604808452888110881941 3305184600396229130197591)
                      ·
                        rfl

theorem cell23_6436824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6436824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436824 prefixEnd_6436824 := by exact prefixLift 6436824
  have htrace : WordTrace (prefixWord ++ tailWord_6436824) baseStart_6436824 baseEnd_6436824 := by
    simpa [prefixWord, tailWord_6436824, baseEnd_6436824] using wordTrace_append hprefix tailTrace_6436824
  have hstable : (prefixWord ++ tailWord_6436824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436824).length < 2 ^ (prefixWord ++ tailWord_6436824).sum := by decide
  have hdescent : baseEnd_6436824 < baseStart_6436824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436839 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6436839 : Nat := 118140960795 + 6436839 * 2 ^ 59
def prefixEnd_6436839 : Nat := 4983230072969 + 3 ^ 40 * 6436839 * 2
def baseEnd_6436839 : Nat := 3305192302606046571510023

theorem tailTrace_6436839 : CollatzResearch.WordTrace tailWord_6436839 prefixEnd_6436839 3305192302606046571510023 := by
  unfold tailWord_6436839
  simp only [CollatzResearch.WordTrace]
  refine ⟨234770805527439102424609571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156513870351626068283073047 234770805527439102424609571)
  ·
    refine ⟨352156208291158653636914357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234770805527439102424609571 352156208291158653636914357)
    ·
      refine ⟨33014644527296123778460721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352156208291158653636914357 33014644527296123778460721)
      ·
        refine ⟨24760983395472092833845541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33014644527296123778460721 24760983395472092833845541)
        ·
          refine ⟨4642684386651017406346039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24760983395472092833845541 4642684386651017406346039)
          ·
            refine ⟨6964026579976526109519059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642684386651017406346039 6964026579976526109519059)
            ·
              refine ⟨10446039869964789164278589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964026579976526109519059 10446039869964789164278589)
              ·
                refine ⟨3917264951236795936604471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10446039869964789164278589 3917264951236795936604471)
                ·
                  refine ⟨5875897426855193904906707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917264951236795936604471 5875897426855193904906707)
                  ·
                    refine ⟨8813846140282790857360061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875897426855193904906707 8813846140282790857360061)
                    ·
                      refine ⟨3305192302606046571510023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8813846140282790857360061 3305192302606046571510023)
                      ·
                        rfl

theorem cell23_6436839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6436839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436839 prefixEnd_6436839 := by exact prefixLift 6436839
  have htrace : WordTrace (prefixWord ++ tailWord_6436839) baseStart_6436839 baseEnd_6436839 := by
    simpa [prefixWord, tailWord_6436839, baseEnd_6436839] using wordTrace_append hprefix tailTrace_6436839
  have hstable : (prefixWord ++ tailWord_6436839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436839).length < 2 ^ (prefixWord ++ tailWord_6436839).sum := by decide
  have hdescent : baseEnd_6436839 < baseStart_6436839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436862 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6436862 : Nat := 118140960795 + 6436862 * 2 ^ 59
def prefixEnd_6436862 : Nat := 4983230072969 + 3 ^ 40 * 6436862 * 2
def baseEnd_6436862 : Nat := 3305204112661099981522417

theorem tailTrace_6436862 : CollatzResearch.WordTrace tailWord_6436862 prefixEnd_6436862 3305204112661099981522417 := by
  unfold tailWord_6436862
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346455550794472169087105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156514429604237184901797893 29346455550794472169087105)
  ·
    refine ⟨22009841663095854126815329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29346455550794472169087105 22009841663095854126815329)
    ·
      refine ⟨16507381247321890595111497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22009841663095854126815329 16507381247321890595111497)
      ·
        refine ⟨12380535935491417946333623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16507381247321890595111497 12380535935491417946333623)
        ·
          refine ⟨18570803903237126919500435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12380535935491417946333623 18570803903237126919500435)
          ·
            refine ⟨27856205854855690379250653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18570803903237126919500435 27856205854855690379250653)
            ·
              refine ⟨10446077195570883892218995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27856205854855690379250653 10446077195570883892218995)
              ·
                refine ⟨15669115793356325838328493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10446077195570883892218995 15669115793356325838328493)
                ·
                  refine ⟨5875918422508622189373185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15669115793356325838328493 5875918422508622189373185)
                  ·
                    refine ⟨4406938816881466642029889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5875918422508622189373185 4406938816881466642029889)
                    ·
                      refine ⟨3305204112661099981522417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406938816881466642029889 3305204112661099981522417)
                      ·
                        rfl

theorem cell23_6436862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6436862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436862 prefixEnd_6436862 := by exact prefixLift 6436862
  have htrace : WordTrace (prefixWord ++ tailWord_6436862) baseStart_6436862 baseEnd_6436862 := by
    simpa [prefixWord, tailWord_6436862, baseEnd_6436862] using wordTrace_append hprefix tailTrace_6436862
  have hstable : (prefixWord ++ tailWord_6436862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436862).length < 2 ^ (prefixWord ++ tailWord_6436862).sum := by decide
  have hdescent : baseEnd_6436862 < baseStart_6436862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436868 : List Nat := [2, 3, 2, 4, 1, 1, 2, 8]
def baseStart_6436868 : Nat := 118140960795 + 6436868 * 2 ^ 59
def prefixEnd_6436868 : Nat := 4983230072969 + 3 ^ 40 * 6436868 * 2
def baseEnd_6436868 : Nat := 122415081242408405853607

theorem tailTrace_6436868 : CollatzResearch.WordTrace tailWord_6436868 prefixEnd_6436868 122415081242408405853607 := by
  unfold tailWord_6436868
  simp only [CollatzResearch.WordTrace]
  refine ⟨117385931622167020188707629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156514575496222693584943505 117385931622167020188707629)
  ·
    refine ⟨44019724358312632570765361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117385931622167020188707629 44019724358312632570765361)
    ·
      refine ⟨33014793268734474428074021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44019724358312632570765361 33014793268734474428074021)
      ·
        refine ⟨6190273737887713955263879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33014793268734474428074021 6190273737887713955263879)
        ·
          refine ⟨9285410606831570932895819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190273737887713955263879 9285410606831570932895819)
          ·
            refine ⟨13928115910247356399343729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285410606831570932895819 13928115910247356399343729)
            ·
              refine ⟨10446086932685517299507797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13928115910247356399343729 10446086932685517299507797)
              ·
                refine ⟨122415081242408405853607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10446086932685517299507797 122415081242408405853607)
                ·
                  rfl

theorem cell23_6436868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 8].length) (baseStart_6436868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436868 prefixEnd_6436868 := by exact prefixLift 6436868
  have htrace : WordTrace (prefixWord ++ tailWord_6436868) baseStart_6436868 baseEnd_6436868 := by
    simpa [prefixWord, tailWord_6436868, baseEnd_6436868] using wordTrace_append hprefix tailTrace_6436868
  have hstable : (prefixWord ++ tailWord_6436868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436868).length < 2 ^ (prefixWord ++ tailWord_6436868).sum := by decide
  have hdescent : baseEnd_6436868 < baseStart_6436868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436888 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6436888 : Nat := 118140960795 + 6436888 * 2 ^ 59
def prefixEnd_6436888 : Nat := 4983230072969 + 3 ^ 40 * 6436888 * 2
def baseEnd_6436888 : Nat := 3305217463158116879797297

theorem tailTrace_6436888 : CollatzResearch.WordTrace tailWord_6436888 prefixEnd_6436888 3305217463158116879797297 := by
  unfold tailWord_6436888
  simp only [CollatzResearch.WordTrace]
  refine ⟨117386296352130791896571659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156515061802841055862095545 117386296352130791896571659)
  ·
    refine ⟨176079444528196187844857489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117386296352130791896571659 176079444528196187844857489)
    ·
      refine ⟨132059583396147140883643117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176079444528196187844857489 132059583396147140883643117)
      ·
        refine ⟨49522343773555177831366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132059583396147140883643117 49522343773555177831366169)
        ·
          refine ⟨37141757830166383373524627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49522343773555177831366169 37141757830166383373524627)
          ·
            refine ⟨55712636745249575060286941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37141757830166383373524627 55712636745249575060286941)
            ·
              refine ⟨20892238779468590647607603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55712636745249575060286941 20892238779468590647607603)
              ·
                refine ⟨31338358169202885971411405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20892238779468590647607603 31338358169202885971411405)
                ·
                  refine ⟨11751884313451082239279277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31338358169202885971411405 11751884313451082239279277)
                  ·
                    refine ⟨4406956617544155839729729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11751884313451082239279277 4406956617544155839729729)
                    ·
                      refine ⟨3305217463158116879797297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406956617544155839729729 3305217463158116879797297)
                      ·
                        rfl

theorem cell23_6436888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6436888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436888 prefixEnd_6436888 := by exact prefixLift 6436888
  have htrace : WordTrace (prefixWord ++ tailWord_6436888) baseStart_6436888 baseEnd_6436888 := by
    simpa [prefixWord, tailWord_6436888, baseEnd_6436888] using wordTrace_append hprefix tailTrace_6436888
  have hstable : (prefixWord ++ tailWord_6436888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436888).length < 2 ^ (prefixWord ++ tailWord_6436888).sum := by decide
  have hdescent : baseEnd_6436888 < baseStart_6436888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6436935 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_6436935 : Nat := 118140960795 + 6436935 * 2 ^ 59
def prefixEnd_6436935 : Nat := 4983230072969 + 3 ^ 40 * 6436935 * 2
def baseEnd_6436935 : Nat := 3305241596748878195909581

theorem tailTrace_6436935 : CollatzResearch.WordTrace tailWord_6436935 prefixEnd_6436935 3305241596748878195909581 := by
  unfold tailWord_6436935
  simp only [CollatzResearch.WordTrace]
  refine ⟨234774306935091310820104259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156516204623394207213402839 234774306935091310820104259)
  ·
    refine ⟨352161460402636966230156389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234774306935091310820104259 352161460402636966230156389)
    ·
      refine ⟨66030273825494431168154323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352161460402636966230156389 66030273825494431168154323)
      ·
        refine ⟨99045410738241646752231485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66030273825494431168154323 99045410738241646752231485)
        ·
          refine ⟨37142029026840617532086807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99045410738241646752231485 37142029026840617532086807)
          ·
            refine ⟨55713043540260926298130211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37142029026840617532086807 55713043540260926298130211)
            ·
              refine ⟨83569565310391389447195317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55713043540260926298130211 83569565310391389447195317)
              ·
                refine ⟨7834646747849192760674561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83569565310391389447195317 7834646747849192760674561)
                ·
                  refine ⟨5875985060886894570505921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7834646747849192760674561 5875985060886894570505921)
                  ·
                    refine ⟨4406988795665170927879441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5875985060886894570505921 4406988795665170927879441)
                    ·
                      refine ⟨3305241596748878195909581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406988795665170927879441 3305241596748878195909581)
                      ·
                        rfl

theorem cell23_6436935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_6436935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6436935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6436935 prefixEnd_6436935 := by exact prefixLift 6436935
  have htrace : WordTrace (prefixWord ++ tailWord_6436935) baseStart_6436935 baseEnd_6436935 := by
    simpa [prefixWord, tailWord_6436935, baseEnd_6436935] using wordTrace_append hprefix tailTrace_6436935
  have hstable : (prefixWord ++ tailWord_6436935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6436935).length < 2 ^ (prefixWord ++ tailWord_6436935).sum := by decide
  have hdescent : baseEnd_6436935 < baseStart_6436935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6436935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437098 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6437098 : Nat := 118140960795 + 6437098 * 2 ^ 59
def prefixEnd_6437098 : Nat := 4983230072969 + 3 ^ 40 * 6437098 * 2
def baseEnd_6437098 : Nat := 3305325294095561058171331

theorem tailTrace_6437098 : CollatzResearch.WordTrace tailWord_6437098 prefixEnd_6437098 3305325294095561058171331 := by
  unfold tailWord_6437098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58695063008375197414571987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156520168022333859772191965 58695063008375197414571987)
  ·
    refine ⟨88042594512562796121857981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58695063008375197414571987 88042594512562796121857981)
    ·
      refine ⟨33015972942211048545696743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88042594512562796121857981 33015972942211048545696743)
      ·
        refine ⟨49523959413316572818545115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33015972942211048545696743 49523959413316572818545115)
        ·
          refine ⟨74285939119974859227817673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49523959413316572818545115 74285939119974859227817673)
          ·
            refine ⟨55714454339981144420863255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74285939119974859227817673 55714454339981144420863255)
            ·
              refine ⟨83571681509971716631294883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55714454339981144420863255 83571681509971716631294883)
              ·
                refine ⟨125357522264957574946942325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83571681509971716631294883 125357522264957574946942325)
                ·
                  refine ⟨11752267712339772651275843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125357522264957574946942325 11752267712339772651275843)
                  ·
                    refine ⟨17628401568509658976913765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11752267712339772651275843 17628401568509658976913765)
                    ·
                      refine ⟨3305325294095561058171331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17628401568509658976913765 3305325294095561058171331)
                      ·
                        rfl

theorem cell23_6437098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6437098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437098 prefixEnd_6437098 := by exact prefixLift 6437098
  have htrace : WordTrace (prefixWord ++ tailWord_6437098) baseStart_6437098 baseEnd_6437098 := by
    simpa [prefixWord, tailWord_6437098, baseEnd_6437098] using wordTrace_append hprefix tailTrace_6437098
  have hstable : (prefixWord ++ tailWord_6437098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437098).length < 2 ^ (prefixWord ++ tailWord_6437098).sum := by decide
  have hdescent : baseEnd_6437098 < baseStart_6437098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_6437161 : Nat := 118140960795 + 6437161 * 2 ^ 59
def prefixEnd_6437161 : Nat := 4983230072969 + 3 ^ 40 * 6437161 * 2
def baseEnd_6437161 : Nat := 3305357643376794311683541

theorem tailTrace_6437161 : CollatzResearch.WordTrace tailWord_6437161 prefixEnd_6437161 3305357643376794311683541 := by
  unfold tailWord_6437161
  simp only [CollatzResearch.WordTrace]
  refine ⟨234782549832272551417831337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156521699888181700945220891 234782549832272551417831337)
  ·
    refine ⟨176086912374204413563373503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234782549832272551417831337 176086912374204413563373503)
    ·
      refine ⟨264130368561306620345060255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176086912374204413563373503 264130368561306620345060255)
      ·
        refine ⟨396195552841959930517590383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264130368561306620345060255 396195552841959930517590383)
        ·
          refine ⟨594293329262939895776385575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396195552841959930517590383 594293329262939895776385575)
          ·
            refine ⟨891439993894409843664578363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594293329262939895776385575 891439993894409843664578363)
            ·
              refine ⟨1337159990841614765496867545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891439993894409843664578363 1337159990841614765496867545)
              ·
                refine ⟨1002869993131211074122650659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337159990841614765496867545 1002869993131211074122650659)
                ·
                  refine ⟨1504304989696816611183975989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002869993131211074122650659 1504304989696816611183975989)
                  ·
                    refine ⟨141028592784076557298497749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1504304989696816611183975989 141028592784076557298497749)
                    ·
                      refine ⟨3305357643376794311683541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141028592784076557298497749 3305357643376794311683541)
                      ·
                        rfl

theorem cell23_6437161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_6437161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437161 prefixEnd_6437161 := by exact prefixLift 6437161
  have htrace : WordTrace (prefixWord ++ tailWord_6437161) baseStart_6437161 baseEnd_6437161 := by
    simpa [prefixWord, tailWord_6437161, baseEnd_6437161] using wordTrace_append hprefix tailTrace_6437161
  have hstable : (prefixWord ++ tailWord_6437161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437161).length < 2 ^ (prefixWord ++ tailWord_6437161).sum := by decide
  have hdescent : baseEnd_6437161 < baseStart_6437161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437172 : List Nat := [2, 5, 1, 1, 1, 4, 2, 7]
def baseStart_6437172 : Nat := 118140960795 + 6437172 * 2 ^ 59
def prefixEnd_6437172 : Nat := 4983230072969 + 3 ^ 40 * 6437172 * 2
def baseEnd_6437172 : Nat := 122420862654221991431333

theorem tailTrace_6437172 : CollatzResearch.WordTrace tailWord_6437172 prefixEnd_6437172 122420862654221991431333 := by
  unfold tailWord_6437172
  simp only [CollatzResearch.WordTrace]
  refine ⟨117391475517616350148240885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156521967356821800197654513 117391475517616350148240885)
  ·
    refine ⟨11005450829776532826397583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117391475517616350148240885 11005450829776532826397583)
    ·
      refine ⟨16508176244664799239596375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005450829776532826397583 16508176244664799239596375)
      ·
        refine ⟨24762264366997198859394563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508176244664799239596375 24762264366997198859394563)
        ·
          refine ⟨37143396550495798289091845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762264366997198859394563 37143396550495798289091845)
          ·
            refine ⟨6964386853217962179204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37143396550495798289091845 6964386853217962179204721)
            ·
              refine ⟨5223290139913471634403541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964386853217962179204721 5223290139913471634403541)
              ·
                refine ⟨122420862654221991431333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5223290139913471634403541 122420862654221991431333)
                ·
                  rfl

theorem cell23_6437172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 7].length) (baseStart_6437172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437172 prefixEnd_6437172 := by exact prefixLift 6437172
  have htrace : WordTrace (prefixWord ++ tailWord_6437172) baseStart_6437172 baseEnd_6437172 := by
    simpa [prefixWord, tailWord_6437172, baseEnd_6437172] using wordTrace_append hprefix tailTrace_6437172
  have hstable : (prefixWord ++ tailWord_6437172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437172).length < 2 ^ (prefixWord ++ tailWord_6437172).sum := by decide
  have hdescent : baseEnd_6437172 < baseStart_6437172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437175 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_6437175 : Nat := 118140960795 + 6437175 * 2 ^ 59
def prefixEnd_6437175 : Nat := 4983230072969 + 3 ^ 40 * 6437175 * 2
def baseEnd_6437175 : Nat := 3305364832105957256908477

theorem tailTrace_6437175 : CollatzResearch.WordTrace tailWord_6437175 prefixEnd_6437175 3305364832105957256908477 := by
  unfold tailWord_6437175
  simp only [CollatzResearch.WordTrace]
  refine ⟨234783060454221831808840979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156522040302814554539227319 234783060454221831808840979)
  ·
    refine ⟨352174590681332747713261469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234783060454221831808840979 352174590681332747713261469)
    ·
      refine ⟨132065471505499780392473051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352174590681332747713261469 132065471505499780392473051)
      ·
        refine ⟨198098207258249670588709577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132065471505499780392473051 198098207258249670588709577)
        ·
          refine ⟨148573655443687252941532183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198098207258249670588709577 148573655443687252941532183)
          ·
            refine ⟨222860483165530879412298275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148573655443687252941532183 222860483165530879412298275)
            ·
              refine ⟨334290724748296319118447413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222860483165530879412298275 334290724748296319118447413)
              ·
                refine ⟨31339755445152779917354445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334290724748296319118447413 31339755445152779917354445)
                ·
                  refine ⟨11752408291932292469007917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31339755445152779917354445 11752408291932292469007917)
                  ·
                    refine ⟨4407153109474609675877969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11752408291932292469007917 4407153109474609675877969)
                    ·
                      refine ⟨3305364832105957256908477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407153109474609675877969 3305364832105957256908477)
                      ·
                        rfl

theorem cell23_6437175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_6437175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437175 prefixEnd_6437175 := by exact prefixLift 6437175
  have htrace : WordTrace (prefixWord ++ tailWord_6437175) baseStart_6437175 baseEnd_6437175 := by
    simpa [prefixWord, tailWord_6437175, baseEnd_6437175] using wordTrace_append hprefix tailTrace_6437175
  have hstable : (prefixWord ++ tailWord_6437175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437175).length < 2 ^ (prefixWord ++ tailWord_6437175).sum := by decide
  have hdescent : baseEnd_6437175 < baseStart_6437175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437178 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_6437178 : Nat := 118140960795 + 6437178 * 2 ^ 59
def prefixEnd_6437178 : Nat := 4983230072969 + 3 ^ 40 * 6437178 * 2
def baseEnd_6437178 : Nat := 3305366372547920745170963

theorem tailTrace_6437178 : CollatzResearch.WordTrace tailWord_6437178 prefixEnd_6437178 3305366372547920745170963 := by
  unfold tailWord_6437178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58695792468302740830300047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156522113248807308880800125 58695792468302740830300047)
  ·
    refine ⟨88043688702454111245450071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58695792468302740830300047 88043688702454111245450071)
    ·
      refine ⟨132065533053681166868175107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88043688702454111245450071 132065533053681166868175107)
      ·
        refine ⟨198098299580521750302262661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132065533053681166868175107 198098299580521750302262661)
        ·
          refine ⟨37143431171347828181674249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198098299580521750302262661 37143431171347828181674249)
          ·
            refine ⟨27857573378510871136255687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37143431171347828181674249 27857573378510871136255687)
            ·
              refine ⟨41786360067766306704383531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27857573378510871136255687 41786360067766306704383531)
              ·
                refine ⟨62679540101649460056575297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41786360067766306704383531 62679540101649460056575297)
                ·
                  refine ⟨47009655076237095042431473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62679540101649460056575297 47009655076237095042431473)
                  ·
                    refine ⟨35257241307177821281823605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47009655076237095042431473 35257241307177821281823605)
                    ·
                      refine ⟨3305366372547920745170963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35257241307177821281823605 3305366372547920745170963)
                      ·
                        rfl

theorem cell23_6437178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_6437178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437178 prefixEnd_6437178 := by exact prefixLift 6437178
  have htrace : WordTrace (prefixWord ++ tailWord_6437178) baseStart_6437178 baseEnd_6437178 := by
    simpa [prefixWord, tailWord_6437178, baseEnd_6437178] using wordTrace_append hprefix tailTrace_6437178
  have hstable : (prefixWord ++ tailWord_6437178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437178).length < 2 ^ (prefixWord ++ tailWord_6437178).sum := by decide
  have hdescent : baseEnd_6437178 < baseStart_6437178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437182 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_6437182 : Nat := 118140960795 + 6437182 * 2 ^ 59
def prefixEnd_6437182 : Nat := 4983230072969 + 3 ^ 40 * 6437182 * 2
def baseEnd_6437182 : Nat := 3305368426470538729520945

theorem tailTrace_6437182 : CollatzResearch.WordTrace tailWord_6437182 prefixEnd_6437182 3305368426470538729520945 := by
  unfold tailWord_6437182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29347914470649559000543225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156522210510130981336230533 29347914470649559000543225)
  ·
    refine ⟨22010935852987169250407419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29347914470649559000543225 22010935852987169250407419)
    ·
      refine ⟨33016403779480753875611129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22010935852987169250407419 33016403779480753875611129)
      ·
        refine ⟨24762302834610565406708347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33016403779480753875611129 24762302834610565406708347)
        ·
          refine ⟨37143454251915848110062521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762302834610565406708347 37143454251915848110062521)
          ·
            refine ⟨27857590688936886082546891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37143454251915848110062521 27857590688936886082546891)
            ·
              refine ⟨41786386033405329123820337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27857590688936886082546891 41786386033405329123820337)
              ·
                refine ⟨31339789525053996842865253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41786386033405329123820337 31339789525053996842865253)
                ·
                  refine ⟨5876210535947624408037235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31339789525053996842865253 5876210535947624408037235)
                  ·
                    refine ⟨8814315803921436612055853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876210535947624408037235 8814315803921436612055853)
                    ·
                      refine ⟨3305368426470538729520945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814315803921436612055853 3305368426470538729520945)
                      ·
                        rfl

theorem cell23_6437182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_6437182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437182 prefixEnd_6437182 := by exact prefixLift 6437182
  have htrace : WordTrace (prefixWord ++ tailWord_6437182) baseStart_6437182 baseEnd_6437182 := by
    simpa [prefixWord, tailWord_6437182, baseEnd_6437182] using wordTrace_append hprefix tailTrace_6437182
  have hstable : (prefixWord ++ tailWord_6437182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437182).length < 2 ^ (prefixWord ++ tailWord_6437182).sum := by decide
  have hdescent : baseEnd_6437182 < baseStart_6437182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437192 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_6437192 : Nat := 118140960795 + 6437192 * 2 ^ 59
def prefixEnd_6437192 : Nat := 4983230072969 + 3 ^ 40 * 6437192 * 2
def baseEnd_6437192 : Nat := 3305373561277083690395899

theorem tailTrace_6437192 : CollatzResearch.WordTrace tailWord_6437192 prefixEnd_6437192 3305373561277083690395899 := by
  unfold tailWord_6437192
  simp only [CollatzResearch.WordTrace]
  refine ⟨117391840247580121856104915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156522453663440162474806553 117391840247580121856104915)
  ·
    refine ⟨176087760371370182784157373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117391840247580121856104915 176087760371370182784157373)
    ·
      refine ⟨66032910139263818544059015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176087760371370182784157373 66032910139263818544059015)
      ·
        refine ⟨99049365208895727816088523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66032910139263818544059015 99049365208895727816088523)
        ·
          refine ⟨148574047813343591724132785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99049365208895727816088523 148574047813343591724132785)
          ·
            refine ⟨111430535860007693793099589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148574047813343591724132785 111430535860007693793099589)
            ·
              refine ⟨20893225473751442586206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111430535860007693793099589 20893225473751442586206173)
              ·
                refine ⟨7834959552656790969827315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20893225473751442586206173 7834959552656790969827315)
                ·
                  refine ⟨11752439328985186454740973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834959552656790969827315 11752439328985186454740973)
                  ·
                    refine ⟨4407164748369444920527865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11752439328985186454740973 4407164748369444920527865)
                    ·
                      refine ⟨3305373561277083690395899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407164748369444920527865 3305373561277083690395899)
                      ·
                        rfl

theorem cell23_6437192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_6437192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437192 prefixEnd_6437192 := by exact prefixLift 6437192
  have htrace : WordTrace (prefixWord ++ tailWord_6437192) baseStart_6437192 baseEnd_6437192 := by
    simpa [prefixWord, tailWord_6437192, baseEnd_6437192] using wordTrace_append hprefix tailTrace_6437192
  have hstable : (prefixWord ++ tailWord_6437192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437192).length < 2 ^ (prefixWord ++ tailWord_6437192).sum := by decide
  have hdescent : baseEnd_6437192 < baseStart_6437192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437198 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_6437198 : Nat := 118140960795 + 6437198 * 2 ^ 59
def prefixEnd_6437198 : Nat := 4983230072969 + 3 ^ 40 * 6437198 * 2
def baseEnd_6437198 : Nat := 1101792214053670222306957

theorem tailTrace_6437198 : CollatzResearch.WordTrace tailWord_6437198 prefixEnd_6437198 1101792214053670222306957 := by
  unfold tailWord_6437198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29347987416642313342116031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156522599555425671157952165 29347987416642313342116031)
  ·
    refine ⟨44021981124963470013174047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29347987416642313342116031 44021981124963470013174047)
    ·
      refine ⟨66032971687445205019761071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44021981124963470013174047 66032971687445205019761071)
      ·
        refine ⟨99049457531167807529641607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66032971687445205019761071 99049457531167807529641607)
        ·
          refine ⟨148574186296751711294462411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99049457531167807529641607 148574186296751711294462411)
          ·
            refine ⟨222861279445127566941693617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148574186296751711294462411 222861279445127566941693617)
            ·
              refine ⟨167145959583845675206270213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222861279445127566941693617 167145959583845675206270213)
              ·
                refine ⟨31339867421971064101175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167145959583845675206270213 31339867421971064101175665)
                ·
                  refine ⟨23504900566478298075881749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31339867421971064101175665 23504900566478298075881749)
                  ·
                    refine ⟨1101792214053670222306957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23504900566478298075881749 1101792214053670222306957)
                    ·
                      rfl

theorem cell23_6437198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_6437198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437198 prefixEnd_6437198 := by exact prefixLift 6437198
  have htrace : WordTrace (prefixWord ++ tailWord_6437198) baseStart_6437198 baseEnd_6437198 := by
    simpa [prefixWord, tailWord_6437198, baseEnd_6437198] using wordTrace_append hprefix tailTrace_6437198
  have hstable : (prefixWord ++ tailWord_6437198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437198).length < 2 ^ (prefixWord ++ tailWord_6437198).sum := by decide
  have hdescent : baseEnd_6437198 < baseStart_6437198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437216 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3]
def baseStart_6437216 : Nat := 118140960795 + 6437216 * 2 ^ 59
def prefixEnd_6437216 : Nat := 4983230072969 + 3 ^ 40 * 6437216 * 2
def baseEnd_6437216 : Nat := 3305385884812791596495789

theorem tailTrace_6437216 : CollatzResearch.WordTrace tailWord_6437216 prefixEnd_6437216 3305385884812791596495789 := by
  unfold tailWord_6437216
  simp only [CollatzResearch.WordTrace]
  refine ⟨117392277923536647905541751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156523037231382197207389001 117392277923536647905541751)
  ·
    refine ⟨176088416885304971858312627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117392277923536647905541751 176088416885304971858312627)
    ·
      refine ⟨264132625327957457787468941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176088416885304971858312627 264132625327957457787468941)
      ·
        refine ⟨99049734497984046670300853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264132625327957457787468941 99049734497984046670300853)
        ·
          refine ⟨9285912609186004375340705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99049734497984046670300853 9285912609186004375340705)
          ·
            refine ⟨6964434456889503281505529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9285912609186004375340705 6964434456889503281505529)
            ·
              refine ⟨5223325842667127461129147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964434456889503281505529 5223325842667127461129147)
              ·
                refine ⟨7834988764000691191693721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223325842667127461129147 7834988764000691191693721)
                ·
                  refine ⟨5876241573000518393770291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7834988764000691191693721 5876241573000518393770291)
                  ·
                    refine ⟨8814362359500777590655437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876241573000518393770291 8814362359500777590655437)
                    ·
                      refine ⟨3305385884812791596495789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814362359500777590655437 3305385884812791596495789)
                      ·
                        rfl

theorem cell23_6437216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_6437216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437216 prefixEnd_6437216 := by exact prefixLift 6437216
  have htrace : WordTrace (prefixWord ++ tailWord_6437216) baseStart_6437216 baseEnd_6437216 := by
    simpa [prefixWord, tailWord_6437216, baseEnd_6437216] using wordTrace_append hprefix tailTrace_6437216
  have hstable : (prefixWord ++ tailWord_6437216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437216).length < 2 ^ (prefixWord ++ tailWord_6437216).sum := by decide
  have hdescent : baseEnd_6437216 < baseStart_6437216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437226 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6437226 : Nat := 118140960795 + 6437226 * 2 ^ 59
def prefixEnd_6437226 : Nat := 4983230072969 + 3 ^ 40 * 6437226 * 2
def baseEnd_6437226 : Nat := 3305391019619336557370743

theorem tailTrace_6437226 : CollatzResearch.WordTrace tailWord_6437226 prefixEnd_6437226 3305391019619336557370743 := by
  unfold tailWord_6437226
  simp only [CollatzResearch.WordTrace]
  refine ⟨58696230144259266879736883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156523280384691378345965021 58696230144259266879736883)
  ·
    refine ⟨88044345216388900319605325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58696230144259266879736883 88044345216388900319605325)
    ·
      refine ⟨33016629456145837619851997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88044345216388900319605325 33016629456145837619851997)
      ·
        refine ⟨12381236046054689107444499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33016629456145837619851997 12381236046054689107444499)
        ·
          refine ⟨18571854069082033661166749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381236046054689107444499 18571854069082033661166749)
          ·
            refine ⟨6964445275905762622937531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18571854069082033661166749 6964445275905762622937531)
            ·
              refine ⟨10446667913858643934406297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964445275905762622937531 10446667913858643934406297)
              ·
                refine ⟨7835000935393982950804723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446667913858643934406297 7835000935393982950804723)
                ·
                  refine ⟨11752501403090974426207085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835000935393982950804723 11752501403090974426207085)
                  ·
                    refine ⟨4407188026159115409827657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11752501403090974426207085 4407188026159115409827657)
                    ·
                      refine ⟨3305391019619336557370743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407188026159115409827657 3305391019619336557370743)
                      ·
                        rfl

theorem cell23_6437226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6437226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437226 prefixEnd_6437226 := by exact prefixLift 6437226
  have htrace : WordTrace (prefixWord ++ tailWord_6437226) baseStart_6437226 baseEnd_6437226 := by
    simpa [prefixWord, tailWord_6437226, baseEnd_6437226] using wordTrace_append hprefix tailTrace_6437226
  have hstable : (prefixWord ++ tailWord_6437226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437226).length < 2 ^ (prefixWord ++ tailWord_6437226).sum := by decide
  have hdescent : baseEnd_6437226 < baseStart_6437226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437255 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_6437255 : Nat := 118140960795 + 6437255 * 2 ^ 59
def prefixEnd_6437255 : Nat := 4983230072969 + 3 ^ 40 * 6437255 * 2
def baseEnd_6437255 : Nat := 3305405910558316943908109

theorem tailTrace_6437255 : CollatzResearch.WordTrace tailWord_6437255 prefixEnd_6437255 3305405910558316943908109 := by
  unfold tailWord_6437255
  simp only [CollatzResearch.WordTrace]
  refine ⟨234785978293932005471753219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156523985529288003647835479 234785978293932005471753219)
  ·
    refine ⟨352178967440898008207629829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234785978293932005471753219 352178967440898008207629829)
    ·
      refine ⟨66033556395168376538930593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352178967440898008207629829 66033556395168376538930593)
      ·
        refine ⟨49525167296376282404197945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66033556395168376538930593 49525167296376282404197945)
        ·
          refine ⟨37143875472282211803148459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49525167296376282404197945 37143875472282211803148459)
          ·
            refine ⟨55715813208423317704722689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37143875472282211803148459 55715813208423317704722689)
            ·
              refine ⟨41786859906317488278542017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55715813208423317704722689 41786859906317488278542017)
              ·
                refine ⟨31340144929738116208906513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41786859906317488278542017 31340144929738116208906513)
                ·
                  refine ⟨23505108697303587156679885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31340144929738116208906513 23505108697303587156679885)
                  ·
                    refine ⟨8814415761488845183754957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23505108697303587156679885 8814415761488845183754957)
                    ·
                      refine ⟨3305405910558316943908109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814415761488845183754957 3305405910558316943908109)
                      ·
                        rfl

theorem cell23_6437255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_6437255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437255 prefixEnd_6437255 := by exact prefixLift 6437255
  have htrace : WordTrace (prefixWord ++ tailWord_6437255) baseStart_6437255 baseEnd_6437255 := by
    simpa [prefixWord, tailWord_6437255, baseEnd_6437255] using wordTrace_append hprefix tailTrace_6437255
  have hstable : (prefixWord ++ tailWord_6437255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437255).length < 2 ^ (prefixWord ++ tailWord_6437255).sum := by decide
  have hdescent : baseEnd_6437255 < baseStart_6437255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437272 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6437272 : Nat := 118140960795 + 6437272 * 2 ^ 59
def prefixEnd_6437272 : Nat := 4983230072969 + 3 ^ 40 * 6437272 * 2
def baseEnd_6437272 : Nat := 3305414639729443377395531

theorem tailTrace_6437272 : CollatzResearch.WordTrace tailWord_6437272 prefixEnd_6437272 3305414639729443377395531 := by
  unfold tailWord_6437272
  simp only [CollatzResearch.WordTrace]
  refine ⟨117393299167435208687561035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156524398889913611583414713 117393299167435208687561035)
  ·
    refine ⟨176089948751152813031341553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117393299167435208687561035 176089948751152813031341553)
    ·
      refine ⟨132067461563364609773506165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176089948751152813031341553 132067461563364609773506165)
      ·
        refine ⟨12381324521565432166266203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132067461563364609773506165 12381324521565432166266203)
        ·
          refine ⟨18571986782348148249399305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381324521565432166266203 18571986782348148249399305)
          ·
            refine ⟨13928990086761111187049479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18571986782348148249399305 13928990086761111187049479)
            ·
              refine ⟨20893485130141666780574219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13928990086761111187049479 20893485130141666780574219)
              ·
                refine ⟨31340227695212500170861329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20893485130141666780574219 31340227695212500170861329)
                ·
                  refine ⟨23505170771409375128145997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31340227695212500170861329 23505170771409375128145997)
                  ·
                    refine ⟨8814439039278515673054749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23505170771409375128145997 8814439039278515673054749)
                    ·
                      refine ⟨3305414639729443377395531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814439039278515673054749 3305414639729443377395531)
                      ·
                        rfl

theorem cell23_6437272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6437272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437272 prefixEnd_6437272 := by exact prefixLift 6437272
  have htrace : WordTrace (prefixWord ++ tailWord_6437272) baseStart_6437272 baseEnd_6437272 := by
    simpa [prefixWord, tailWord_6437272, baseEnd_6437272] using wordTrace_append hprefix tailTrace_6437272
  have hstable : (prefixWord ++ tailWord_6437272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437272).length < 2 ^ (prefixWord ++ tailWord_6437272).sum := by decide
  have hdescent : baseEnd_6437272 < baseStart_6437272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437282 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_6437282 : Nat := 118140960795 + 6437282 * 2 ^ 59
def prefixEnd_6437282 : Nat := 4983230072969 + 3 ^ 40 * 6437282 * 2
def baseEnd_6437282 : Nat := 3305419774535988338270485

theorem tailTrace_6437282 : CollatzResearch.WordTrace tailWord_6437282 prefixEnd_6437282 3305419774535988338270485 := by
  unfold tailWord_6437282
  simp only [CollatzResearch.WordTrace]
  refine ⟨58696740766208547270746525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156524642043222792721990733 58696740766208547270746525)
  ·
    refine ⟨22011277787328205226529947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58696740766208547270746525 22011277787328205226529947)
    ·
      refine ⟨33016916680992307839794921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22011277787328205226529947 33016916680992307839794921)
      ·
        refine ⟨24762687510744230879846191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33016916680992307839794921 24762687510744230879846191)
        ·
          refine ⟨37144031266116346319769287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762687510744230879846191 37144031266116346319769287)
          ·
            refine ⟨55716046899174519479653931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37144031266116346319769287 55716046899174519479653931)
            ·
              refine ⟨83574070348761779219480897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55716046899174519479653931 83574070348761779219480897)
              ·
                refine ⟨62680552761571334414610673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83574070348761779219480897 62680552761571334414610673)
                ·
                  refine ⟨47010414571178500810958005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62680552761571334414610673 47010414571178500810958005)
                  ·
                    refine ⟨4407226366047984451027313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47010414571178500810958005 4407226366047984451027313)
                    ·
                      refine ⟨3305419774535988338270485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407226366047984451027313 3305419774535988338270485)
                      ·
                        rfl

theorem cell23_6437282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_6437282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437282 prefixEnd_6437282 := by exact prefixLift 6437282
  have htrace : WordTrace (prefixWord ++ tailWord_6437282) baseStart_6437282 baseEnd_6437282 := by
    simpa [prefixWord, tailWord_6437282, baseEnd_6437282] using wordTrace_append hprefix tailTrace_6437282
  have hstable : (prefixWord ++ tailWord_6437282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437282).length < 2 ^ (prefixWord ++ tailWord_6437282).sum := by decide
  have hdescent : baseEnd_6437282 < baseStart_6437282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437315 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3]
def baseStart_6437315 : Nat := 118140960795 + 6437315 * 2 ^ 59
def prefixEnd_6437315 : Nat := 4983230072969 + 3 ^ 40 * 6437315 * 2
def baseEnd_6437315 : Nat := 3305436719397586709157833

theorem tailTrace_6437315 : CollatzResearch.WordTrace tailWord_6437315 prefixEnd_6437315 3305436719397586709157833 := by
  unfold tailWord_6437315
  simp only [CollatzResearch.WordTrace]
  refine ⟨234788166673714635718937399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156525444449143090479291599 234788166673714635718937399)
  ·
    refine ⟨352182250010571953578406099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234788166673714635718937399 352182250010571953578406099)
    ·
      refine ⟨528273375015857930367609149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352182250010571953578406099 528273375015857930367609149)
      ·
        refine ⟨198102515630946723887853431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 528273375015857930367609149 198102515630946723887853431)
        ·
          refine ⟨297153773446420085831780147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198102515630946723887853431 297153773446420085831780147)
          ·
            refine ⟨445730660169630128747670221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297153773446420085831780147 445730660169630128747670221)
            ·
              refine ⟨167148997563611298280376333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445730660169630128747670221 167148997563611298280376333)
              ·
                refine ⟨62680874086354236855141125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167148997563611298280376333 62680874086354236855141125)
                ·
                  refine ⟨11752663891191419410338961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62680874086354236855141125 11752663891191419410338961)
                  ·
                    refine ⟨8814497918393564557754221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11752663891191419410338961 8814497918393564557754221)
                    ·
                      refine ⟨3305436719397586709157833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814497918393564557754221 3305436719397586709157833)
                      ·
                        rfl

theorem cell23_6437315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_6437315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437315 prefixEnd_6437315 := by exact prefixLift 6437315
  have htrace : WordTrace (prefixWord ++ tailWord_6437315) baseStart_6437315 baseEnd_6437315 := by
    simpa [prefixWord, tailWord_6437315, baseEnd_6437315] using wordTrace_append hprefix tailTrace_6437315
  have hstable : (prefixWord ++ tailWord_6437315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437315).length < 2 ^ (prefixWord ++ tailWord_6437315).sum := by decide
  have hdescent : baseEnd_6437315 < baseStart_6437315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437322 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_6437322 : Nat := 118140960795 + 6437322 * 2 ^ 59
def prefixEnd_6437322 : Nat := 4983230072969 + 3 ^ 40 * 6437322 * 2
def baseEnd_6437322 : Nat := 1101813437920722727256767

theorem tailTrace_6437322 : CollatzResearch.WordTrace tailWord_6437322 prefixEnd_6437322 1101813437920722727256767 := by
  unfold tailWord_6437322
  simp only [CollatzResearch.WordTrace]
  refine ⟨58697105496172318978610555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156525614656459517276294813 58697105496172318978610555)
  ·
    refine ⟨88045658244258478467915833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58697105496172318978610555 88045658244258478467915833)
    ·
      refine ⟨66034243683193858850936875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88045658244258478467915833 66034243683193858850936875)
      ·
        refine ⟨99051365524790788276405313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66034243683193858850936875 99051365524790788276405313)
        ·
          refine ⟨74288524143593091207303985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99051365524790788276405313 74288524143593091207303985)
          ·
            refine ⟨55716393107694818405477989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74288524143593091207303985 55716393107694818405477989)
            ·
              refine ⟨10446823707692778451027123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55716393107694818405477989 10446823707692778451027123)
              ·
                refine ⟨15670235561539167676540685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10446823707692778451027123 15670235561539167676540685)
                ·
                  refine ⟨5876338335577187878702757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15670235561539167676540685 5876338335577187878702757)
                  ·
                    refine ⟨1101813437920722727256767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876338335577187878702757 1101813437920722727256767)
                    ·
                      rfl

theorem cell23_6437322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_6437322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437322 prefixEnd_6437322 := by exact prefixLift 6437322
  have htrace : WordTrace (prefixWord ++ tailWord_6437322) baseStart_6437322 baseEnd_6437322 := by
    simpa [prefixWord, tailWord_6437322, baseEnd_6437322] using wordTrace_append hprefix tailTrace_6437322
  have hstable : (prefixWord ++ tailWord_6437322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437322).length < 2 ^ (prefixWord ++ tailWord_6437322).sum := by decide
  have hdescent : baseEnd_6437322 < baseStart_6437322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437332 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6437332 : Nat := 118140960795 + 6437332 * 2 ^ 59
def prefixEnd_6437332 : Nat := 4983230072969 + 3 ^ 40 * 6437332 * 2
def baseEnd_6437332 : Nat := 3305445448568713142645255

theorem tailTrace_6437332 : CollatzResearch.WordTrace tailWord_6437332 prefixEnd_6437332 3305445448568713142645255 := by
  unfold tailWord_6437332
  simp only [CollatzResearch.WordTrace]
  refine ⟨117394393357326523811153125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156525857809768698414870833 117394393357326523811153125)
  ·
    refine ⟨22011448754498723214591211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117394393357326523811153125 22011448754498723214591211)
    ·
      refine ⟨33017173131748084821886817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22011448754498723214591211 33017173131748084821886817)
      ·
        refine ⟨24762879848811063616415113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33017173131748084821886817 24762879848811063616415113)
        ·
          refine ⟨18572159886608297712311335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24762879848811063616415113 18572159886608297712311335)
          ·
            refine ⟨27858239829912446568467003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572159886608297712311335 27858239829912446568467003)
            ·
              refine ⟨41787359744868669852700505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27858239829912446568467003 41787359744868669852700505)
              ·
                refine ⟨31340519808651502389525379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41787359744868669852700505 31340519808651502389525379)
                ·
                  refine ⟨47010779712977253584288069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31340519808651502389525379 47010779712977253584288069)
                  ·
                    refine ⟨8814521196183235047054013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47010779712977253584288069 8814521196183235047054013)
                    ·
                      refine ⟨3305445448568713142645255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814521196183235047054013 3305445448568713142645255)
                      ·
                        rfl

theorem cell23_6437332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6437332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437332 prefixEnd_6437332 := by exact prefixLift 6437332
  have htrace : WordTrace (prefixWord ++ tailWord_6437332) baseStart_6437332 baseEnd_6437332 := by
    simpa [prefixWord, tailWord_6437332, baseEnd_6437332] using wordTrace_append hprefix tailTrace_6437332
  have hstable : (prefixWord ++ tailWord_6437332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437332).length < 2 ^ (prefixWord ++ tailWord_6437332).sum := by decide
  have hdescent : baseEnd_6437332 < baseStart_6437332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437345 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_6437345 : Nat := 118140960795 + 6437345 * 2 ^ 59
def prefixEnd_6437345 : Nat := 4983230072969 + 3 ^ 40 * 6437345 * 2
def baseEnd_6437345 : Nat := 3305452123817221591782695

theorem tailTrace_6437345 : CollatzResearch.WordTrace tailWord_6437345 prefixEnd_6437345 3305452123817221591782695 := by
  unfold tailWord_6437345
  simp only [CollatzResearch.WordTrace]
  refine ⟨234789260863605950842529489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156526173909070633895019659 234789260863605950842529489)
  ·
    refine ⟨176091945647704463131897117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234789260863605950842529489 176091945647704463131897117)
    ·
      refine ⟨66034479617889173674461419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176091945647704463131897117 66034479617889173674461419)
      ·
        refine ⟨99051719426833760511692129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66034479617889173674461419 99051719426833760511692129)
        ·
          refine ⟨74288789570125320383769097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99051719426833760511692129 74288789570125320383769097)
          ·
            refine ⟨55716592177593990287826823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74288789570125320383769097 55716592177593990287826823)
            ·
              refine ⟨83574888266390985431740235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55716592177593990287826823 83574888266390985431740235)
              ·
                refine ⟨125362332399586478147610353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83574888266390985431740235 125362332399586478147610353)
                ·
                  refine ⟨94021749299689858610707765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125362332399586478147610353 94021749299689858610707765)
                  ·
                    refine ⟨8814538996845924244753853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94021749299689858610707765 8814538996845924244753853)
                    ·
                      refine ⟨3305452123817221591782695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814538996845924244753853 3305452123817221591782695)
                      ·
                        rfl

theorem cell23_6437345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_6437345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437345 prefixEnd_6437345 := by exact prefixLift 6437345
  have htrace : WordTrace (prefixWord ++ tailWord_6437345) baseStart_6437345 baseEnd_6437345 := by
    simpa [prefixWord, tailWord_6437345, baseEnd_6437345] using wordTrace_append hprefix tailTrace_6437345
  have hstable : (prefixWord ++ tailWord_6437345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437345).length < 2 ^ (prefixWord ++ tailWord_6437345).sum := by decide
  have hdescent : baseEnd_6437345 < baseStart_6437345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437395 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 6]
def baseStart_6437395 : Nat := 118140960795 + 6437395 * 2 ^ 59
def prefixEnd_6437395 : Nat := 4983230072969 + 3 ^ 40 * 6437395 * 2
def baseEnd_6437395 : Nat := 1101825932616648798719155

theorem tailTrace_6437395 : CollatzResearch.WordTrace tailWord_6437395 prefixEnd_6437395 1101825932616648798719155 := by
  unfold tailWord_6437395
  simp only [CollatzResearch.WordTrace]
  refine ⟨234791084513424809381849639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156527389675616539587899759 234791084513424809381849639)
  ·
    refine ⟨352186626770137214072774459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234791084513424809381849639 352186626770137214072774459)
    ·
      refine ⟨528279940155205821109161689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352186626770137214072774459 528279940155205821109161689)
      ·
        refine ⟨396209955116404365831871267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528279940155205821109161689 396209955116404365831871267)
        ·
          refine ⟨594314932674606548747806901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396209955116404365831871267 594314932674606548747806901)
          ·
            refine ⟨55717024938244363945106897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 594314932674606548747806901 55717024938244363945106897)
            ·
              refine ⟨41787768703683272958830173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55717024938244363945106897 41787768703683272958830173)
              ·
                refine ⟨15670413263881227359561315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41787768703683272958830173 15670413263881227359561315)
                ·
                  refine ⟨23505619895821841039341973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15670413263881227359561315 23505619895821841039341973)
                  ·
                    refine ⟨1101825932616648798719155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23505619895821841039341973 1101825932616648798719155)
                    ·
                      rfl

theorem cell23_6437395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_6437395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437395 prefixEnd_6437395 := by exact prefixLift 6437395
  have htrace : WordTrace (prefixWord ++ tailWord_6437395) baseStart_6437395 baseEnd_6437395 := by
    simpa [prefixWord, tailWord_6437395, baseEnd_6437395] using wordTrace_append hprefix tailTrace_6437395
  have hstable : (prefixWord ++ tailWord_6437395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437395).length < 2 ^ (prefixWord ++ tailWord_6437395).sum := by decide
  have hdescent : baseEnd_6437395 < baseStart_6437395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437399 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 3, 5]
def baseStart_6437399 : Nat := 118140960795 + 6437399 * 2 ^ 59
def prefixEnd_6437399 : Nat := 4983230072969 + 3 ^ 40 * 6437399 * 2
def baseEnd_6437399 : Nat := 1101826617257521460169149

theorem tailTrace_6437399 : CollatzResearch.WordTrace tailWord_6437399 prefixEnd_6437399 1101826617257521460169149 := by
  unfold tailWord_6437399
  simp only [CollatzResearch.WordTrace]
  refine ⟨234791230405410318064995251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156527486936940212043330167 234791230405410318064995251)
  ·
    refine ⟨352186845608115477097492877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234791230405410318064995251 352186845608115477097492877)
    ·
      refine ⟨132070067103043303911559829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352186845608115477097492877 132070067103043303911559829)
      ·
        refine ⟨6190784395455154870854367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132070067103043303911559829 6190784395455154870854367)
        ·
          refine ⟨9286176593182732306281551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190784395455154870854367 9286176593182732306281551)
          ·
            refine ⟨13929264889774098459422327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286176593182732306281551 13929264889774098459422327)
            ·
              refine ⟨20893897334661147689133491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929264889774098459422327 20893897334661147689133491)
              ·
                refine ⟨31340846001991721533700237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20893897334661147689133491 31340846001991721533700237)
                ·
                  refine ⟨11752817250746895575137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31340846001991721533700237 11752817250746895575137589)
                  ·
                    refine ⟨1101826617257521460169149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11752817250746895575137589 1101826617257521460169149)
                    ·
                      rfl

theorem cell23_6437399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_6437399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437399 prefixEnd_6437399 := by exact prefixLift 6437399
  have htrace : WordTrace (prefixWord ++ tailWord_6437399) baseStart_6437399 baseEnd_6437399 := by
    simpa [prefixWord, tailWord_6437399, baseEnd_6437399] using wordTrace_append hprefix tailTrace_6437399
  have hstable : (prefixWord ++ tailWord_6437399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437399).length < 2 ^ (prefixWord ++ tailWord_6437399).sum := by decide
  have hdescent : baseEnd_6437399 < baseStart_6437399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437402 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_6437402 : Nat := 118140960795 + 6437402 * 2 ^ 59
def prefixEnd_6437402 : Nat := 4983230072969 + 3 ^ 40 * 6437402 * 2
def baseEnd_6437402 : Nat := 3305481392214527868769933

theorem tailTrace_6437402 : CollatzResearch.WordTrace tailWord_6437402 prefixEnd_6437402 3305481392214527868769933 := by
  unfold tailWord_6437402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58697834956099862394338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156527559882932966384902973 58697834956099862394338615)
  ·
    refine ⟨88046752434149793591507923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58697834956099862394338615 88046752434149793591507923)
    ·
      refine ⟨132070128651224690387261885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88046752434149793591507923 132070128651224690387261885)
      ·
        refine ⟨49526298244209258895223207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132070128651224690387261885 49526298244209258895223207)
        ·
          refine ⟨74289447366313888342834811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49526298244209258895223207 74289447366313888342834811)
          ·
            refine ⟨111434171049470832514252217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74289447366313888342834811 111434171049470832514252217)
            ·
              refine ⟨83575628287103124385689163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111434171049470832514252217 83575628287103124385689163)
              ·
                refine ⟨125363442430654686578533745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83575628287103124385689163 125363442430654686578533745)
                ·
                  refine ⟨94022581822991014933900309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125363442430654686578533745 94022581822991014933900309)
                  ·
                    refine ⟨4407308522952703825026577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94022581822991014933900309 4407308522952703825026577)
                    ·
                      refine ⟨3305481392214527868769933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407308522952703825026577 3305481392214527868769933)
                      ·
                        rfl

theorem cell23_6437402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_6437402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437402 prefixEnd_6437402 := by exact prefixLift 6437402
  have htrace : WordTrace (prefixWord ++ tailWord_6437402) baseStart_6437402 baseEnd_6437402 := by
    simpa [prefixWord, tailWord_6437402, baseEnd_6437402] using wordTrace_append hprefix tailTrace_6437402
  have hstable : (prefixWord ++ tailWord_6437402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437402).length < 2 ^ (prefixWord ++ tailWord_6437402).sum := by decide
  have hdescent : baseEnd_6437402 < baseStart_6437402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437416 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6437416 : Nat := 118140960795 + 6437416 * 2 ^ 59
def prefixEnd_6437416 : Nat := 4983230072969 + 3 ^ 40 * 6437416 * 2
def baseEnd_6437416 : Nat := 1101829526981230271331623

theorem tailTrace_6437416 : CollatzResearch.WordTrace tailWord_6437416 prefixEnd_6437416 1101829526981230271331623 := by
  unfold tailWord_6437416
  simp only [CollatzResearch.WordTrace]
  refine ⟨117395925223174364984182051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156527900297565819978909401 117395925223174364984182051)
  ·
    refine ⟨176093887834761547476273077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117395925223174364984182051 176093887834761547476273077)
    ·
      refine ⟨16508801984508895075900601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176093887834761547476273077 16508801984508895075900601)
      ·
        refine ⟨12381601488381671306925451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16508801984508895075900601 12381601488381671306925451)
        ·
          refine ⟨18572402232572506960388177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381601488381671306925451 18572402232572506960388177)
          ·
            refine ⟨13929301674429380220291133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18572402232572506960388177 13929301674429380220291133)
            ·
              refine ⟨5223488127911017582609175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13929301674429380220291133 5223488127911017582609175)
              ·
                refine ⟨7835232191866526373913763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223488127911017582609175 7835232191866526373913763)
                ·
                  refine ⟨11752848287799789560870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835232191866526373913763 11752848287799789560870645)
                  ·
                    refine ⟨1101829526981230271331623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11752848287799789560870645 1101829526981230271331623)
                    ·
                      rfl

theorem cell23_6437416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6437416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437416 prefixEnd_6437416 := by exact prefixLift 6437416
  have htrace : WordTrace (prefixWord ++ tailWord_6437416) baseStart_6437416 baseEnd_6437416 := by
    simpa [prefixWord, tailWord_6437416, baseEnd_6437416] using wordTrace_append hprefix tailTrace_6437416
  have hstable : (prefixWord ++ tailWord_6437416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437416).length < 2 ^ (prefixWord ++ tailWord_6437416).sum := by decide
  have hdescent : baseEnd_6437416 < baseStart_6437416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437429 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_6437429 : Nat := 118140960795 + 6437429 * 2 ^ 59
def prefixEnd_6437429 : Nat := 4983230072969 + 3 ^ 40 * 6437429 * 2
def baseEnd_6437429 : Nat := 1101831752064066421044103

theorem tailTrace_6437429 : CollatzResearch.WordTrace tailWord_6437429 prefixEnd_6437429 1101831752064066421044103 := by
  unfold tailWord_6437429
  simp only [CollatzResearch.WordTrace]
  refine ⟨234792324595301633188587341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156528216396867755459058227 234792324595301633188587341)
  ·
    refine ⟨88047121723238112445720253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234792324595301633188587341 88047121723238112445720253)
    ·
      refine ⟨33017670646214292167145095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88047121723238112445720253 33017670646214292167145095)
      ·
        refine ⟨49526505969321438250717643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33017670646214292167145095 49526505969321438250717643)
        ·
          refine ⟨74289758953982157376076465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49526505969321438250717643 74289758953982157376076465)
          ·
            refine ⟨55717319215486618032057349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74289758953982157376076465 55717319215486618032057349)
            ·
              refine ⟨10446997352903740881010753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55717319215486618032057349 10446997352903740881010753)
              ·
                refine ⟨7835248014677805660758065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446997352903740881010753 7835248014677805660758065)
                ·
                  refine ⟨5876436011008354245568549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7835248014677805660758065 5876436011008354245568549)
                  ·
                    refine ⟨1101831752064066421044103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876436011008354245568549 1101831752064066421044103)
                    ·
                      rfl

theorem cell23_6437429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_6437429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437429 prefixEnd_6437429 := by exact prefixLift 6437429
  have htrace : WordTrace (prefixWord ++ tailWord_6437429) baseStart_6437429 baseEnd_6437429 := by
    simpa [prefixWord, tailWord_6437429, baseEnd_6437429] using wordTrace_append hprefix tailTrace_6437429
  have hstable : (prefixWord ++ tailWord_6437429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437429).length < 2 ^ (prefixWord ++ tailWord_6437429).sum := by decide
  have hdescent : baseEnd_6437429 < baseStart_6437429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437430 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6437430 : Nat := 118140960795 + 6437430 * 2 ^ 59
def prefixEnd_6437430 : Nat := 4983230072969 + 3 ^ 40 * 6437430 * 2
def baseEnd_6437430 : Nat := 3305495769672853759219805

theorem tailTrace_6437430 : CollatzResearch.WordTrace tailWord_6437430 prefixEnd_6437430 3305495769672853759219805 := by
  unfold tailWord_6437430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674522566768625647460859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156528240712198673572915829 14674522566768625647460859)
  ·
    refine ⟨22011783850152938471191289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14674522566768625647460859 22011783850152938471191289)
    ·
      refine ⟨16508837887614703853393467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22011783850152938471191289 16508837887614703853393467)
      ·
        refine ⟨24763256831422055780090201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508837887614703853393467 24763256831422055780090201)
        ·
          refine ⟨18572442623566541835067651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24763256831422055780090201 18572442623566541835067651)
          ·
            refine ⟨27858663935349812752601477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572442623566541835067651 27858663935349812752601477)
            ·
              refine ⟨5223499487878089891112777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27858663935349812752601477 5223499487878089891112777)
              ·
                refine ⟨3917624615908567418334583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5223499487878089891112777 3917624615908567418334583)
                ·
                  refine ⟨5876436923862851127501875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917624615908567418334583 5876436923862851127501875)
                  ·
                    refine ⟨8814655385794276691252813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876436923862851127501875 8814655385794276691252813)
                    ·
                      refine ⟨3305495769672853759219805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814655385794276691252813 3305495769672853759219805)
                      ·
                        rfl

theorem cell23_6437430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6437430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437430 prefixEnd_6437430 := by exact prefixLift 6437430
  have htrace : WordTrace (prefixWord ++ tailWord_6437430) baseStart_6437430 baseEnd_6437430 := by
    simpa [prefixWord, tailWord_6437430, baseEnd_6437430] using wordTrace_append hprefix tailTrace_6437430
  have hstable : (prefixWord ++ tailWord_6437430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437430).length < 2 ^ (prefixWord ++ tailWord_6437430).sum := by decide
  have hdescent : baseEnd_6437430 < baseStart_6437430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437446 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6437446 : Nat := 118140960795 + 6437446 * 2 ^ 59
def prefixEnd_6437446 : Nat := 4983230072969 + 3 ^ 40 * 6437446 * 2
def baseEnd_6437446 : Nat := 1101834661787775232206577

theorem tailTrace_6437446 : CollatzResearch.WordTrace tailWord_6437446 prefixEnd_6437446 1101834661787775232206577 := by
  unfold tailWord_6437446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337279519882501409123631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156528629757493363394637461 7337279519882501409123631)
  ·
    refine ⟨11005919279823752113685447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7337279519882501409123631 11005919279823752113685447)
    ·
      refine ⟨16508878919735628170528171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005919279823752113685447 16508878919735628170528171)
      ·
        refine ⟨24763318379603442255792257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508878919735628170528171 24763318379603442255792257)
        ·
          refine ⟨18572488784702581691844193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24763318379603442255792257 18572488784702581691844193)
          ·
            refine ⟨13929366588526936268883145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18572488784702581691844193 13929366588526936268883145)
            ·
              refine ⟨10447024941395202201662359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13929366588526936268883145 10447024941395202201662359)
              ·
                refine ⟨15670537412092803302493539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447024941395202201662359 15670537412092803302493539)
                ·
                  refine ⟨23505806118139204953740309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15670537412092803302493539 23505806118139204953740309)
                  ·
                    refine ⟨1101834661787775232206577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23505806118139204953740309 1101834661787775232206577)
                    ·
                      rfl

theorem cell23_6437446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6437446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437446 prefixEnd_6437446 := by exact prefixLift 6437446
  have htrace : WordTrace (prefixWord ++ tailWord_6437446) baseStart_6437446 baseEnd_6437446 := by
    simpa [prefixWord, tailWord_6437446, baseEnd_6437446] using wordTrace_append hprefix tailTrace_6437446
  have hstable : (prefixWord ++ tailWord_6437446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437446).length < 2 ^ (prefixWord ++ tailWord_6437446).sum := by decide
  have hdescent : baseEnd_6437446 < baseStart_6437446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437453 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6437453 : Nat := 118140960795 + 6437453 * 2 ^ 59
def prefixEnd_6437453 : Nat := 4983230072969 + 3 ^ 40 * 6437453 * 2
def baseEnd_6437453 : Nat := 3305507579727907169232199

theorem tailTrace_6437453 : CollatzResearch.WordTrace tailWord_6437453 prefixEnd_6437453 3305507579727907169232199 := by
  unfold tailWord_6437453
  simp only [CollatzResearch.WordTrace]
  refine ⟨234793199947214685287461013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156528799964809790191640675 234793199947214685287461013)
  ·
    refine ⟨11005931247525688372849735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234793199947214685287461013 11005931247525688372849735)
    ·
      refine ⟨16508896871288532559274603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005931247525688372849735 16508896871288532559274603)
      ·
        refine ⟨24763345306932798838911905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508896871288532559274603 24763345306932798838911905)
        ·
          refine ⟨18572508980199599129183929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24763345306932798838911905 18572508980199599129183929)
          ·
            refine ⟨13929381735149699346887947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18572508980199599129183929 13929381735149699346887947)
            ·
              refine ⟨20894072602724549020331921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929381735149699346887947 20894072602724549020331921)
              ·
                refine ⟨15670554452043411765248941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20894072602724549020331921 15670554452043411765248941)
                ·
                  refine ⟨5876457919516279411968353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15670554452043411765248941 5876457919516279411968353)
                  ·
                    refine ⟨4407343439637209558976265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5876457919516279411968353 4407343439637209558976265)
                    ·
                      refine ⟨3305507579727907169232199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407343439637209558976265 3305507579727907169232199)
                      ·
                        rfl

theorem cell23_6437453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6437453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437453 prefixEnd_6437453 := by exact prefixLift 6437453
  have htrace : WordTrace (prefixWord ++ tailWord_6437453) baseStart_6437453 baseEnd_6437453 := by
    simpa [prefixWord, tailWord_6437453, baseEnd_6437453] using wordTrace_append hprefix tailTrace_6437453
  have hstable : (prefixWord ++ tailWord_6437453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437453).length < 2 ^ (prefixWord ++ tailWord_6437453).sum := by decide
  have hdescent : baseEnd_6437453 < baseStart_6437453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437470 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6437470 : Nat := 118140960795 + 6437470 * 2 ^ 59
def prefixEnd_6437470 : Nat := 4983230072969 + 3 ^ 40 * 6437470 * 2
def baseEnd_6437470 : Nat := 3305516308899033602719621

theorem tailTrace_6437470 : CollatzResearch.WordTrace tailWord_6437470 prefixEnd_6437470 3305516308899033602719621 := by
  unfold tailWord_6437470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349227498519137148853733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156529213325435398127219909 29349227498519137148853733)
  ·
    refine ⟨5502980155972338215410075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29349227498519137148853733 5502980155972338215410075)
    ·
      refine ⟨8254470233958507323115113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502980155972338215410075 8254470233958507323115113)
      ·
        refine ⟨6190852675468880492336335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8254470233958507323115113 6190852675468880492336335)
        ·
          refine ⟨9286279013203320738504503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190852675468880492336335 9286279013203320738504503)
          ·
            refine ⟨13929418519804981107756755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286279013203320738504503 13929418519804981107756755)
            ·
              refine ⟨20894127779707471661635133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929418519804981107756755 20894127779707471661635133)
              ·
                refine ⟨7835297917390301873113175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20894127779707471661635133 7835297917390301873113175)
                ·
                  refine ⟨11752946876085452809669763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835297917390301873113175 11752946876085452809669763)
                  ·
                    refine ⟨17629420314128179214504645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11752946876085452809669763 17629420314128179214504645)
                    ·
                      refine ⟨3305516308899033602719621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17629420314128179214504645 3305516308899033602719621)
                      ·
                        rfl

theorem cell23_6437470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6437470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437470 prefixEnd_6437470 := by exact prefixLift 6437470
  have htrace : WordTrace (prefixWord ++ tailWord_6437470) baseStart_6437470 baseEnd_6437470 := by
    simpa [prefixWord, tailWord_6437470, baseEnd_6437470] using wordTrace_append hprefix tailTrace_6437470
  have hstable : (prefixWord ++ tailWord_6437470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437470).length < 2 ^ (prefixWord ++ tailWord_6437470).sum := by decide
  have hdescent : baseEnd_6437470 < baseStart_6437470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437486 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6437486 : Nat := 118140960795 + 6437486 * 2 ^ 59
def prefixEnd_6437486 : Nat := 4983230072969 + 3 ^ 40 * 6437486 * 2
def baseEnd_6437486 : Nat := 3305524524589505540119547

theorem tailTrace_6437486 : CollatzResearch.WordTrace tailWord_6437486 prefixEnd_6437486 3305524524589505540119547 := by
  unfold tailWord_6437486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349300444511891490426539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156529602370730087948941541 29349300444511891490426539)
  ·
    refine ⟨44023950666767837235639809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29349300444511891490426539 44023950666767837235639809)
    ·
      refine ⟨33017963000075877926729857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44023950666767837235639809 33017963000075877926729857)
      ·
        refine ⟨24763472250056908445047393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33017963000075877926729857 24763472250056908445047393)
        ·
          refine ⟨18572604187542681333785545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24763472250056908445047393 18572604187542681333785545)
          ·
            refine ⟨13929453140657011000339159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18572604187542681333785545 13929453140657011000339159)
            ·
              refine ⟨20894179710985516500508739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929453140657011000339159 20894179710985516500508739)
              ·
                refine ⟨31341269566478274750763109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20894179710985516500508739 31341269566478274750763109)
                ·
                  refine ⟨5876488043714676515768083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31341269566478274750763109 5876488043714676515768083)
                  ·
                    refine ⟨8814732065572014773652125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876488043714676515768083 8814732065572014773652125)
                    ·
                      refine ⟨3305524524589505540119547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8814732065572014773652125 3305524524589505540119547)
                      ·
                        rfl

theorem cell23_6437486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6437486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437486 prefixEnd_6437486 := by exact prefixLift 6437486
  have htrace : WordTrace (prefixWord ++ tailWord_6437486) baseStart_6437486 baseEnd_6437486 := by
    simpa [prefixWord, tailWord_6437486, baseEnd_6437486] using wordTrace_append hprefix tailTrace_6437486
  have hstable : (prefixWord ++ tailWord_6437486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437486).length < 2 ^ (prefixWord ++ tailWord_6437486).sum := by decide
  have hdescent : baseEnd_6437486 < baseStart_6437486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437515 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 9]
def baseStart_6437515 : Nat := 118140960795 + 6437515 * 2 ^ 59
def prefixEnd_6437515 : Nat := 4983230072969 + 3 ^ 40 * 6437515 * 2
def baseEnd_6437515 : Nat := 367282157280942880739657

theorem tailTrace_6437515 : CollatzResearch.WordTrace tailWord_6437515 prefixEnd_6437515 367282157280942880739657 := by
  unfold tailWord_6437515
  simp only [CollatzResearch.WordTrace]
  refine ⟨234795461272990069876217999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156530307515326713250811999 234795461272990069876217999)
  ·
    refine ⟨352193191909485104814326999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234795461272990069876217999 352193191909485104814326999)
    ·
      refine ⟨528289787864227657221490499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352193191909485104814326999 528289787864227657221490499)
      ·
        refine ⟨792434681796341485832235749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528289787864227657221490499 792434681796341485832235749)
        ·
          refine ⟨148581502836814028593544203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 792434681796341485832235749 148581502836814028593544203)
          ·
            refine ⟨222872254255221042890316305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148581502836814028593544203 222872254255221042890316305)
            ·
              refine ⟨167154190691415782167737229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222872254255221042890316305 167154190691415782167737229)
              ·
                refine ⟨62682821509280918312901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167154190691415782167737229 62682821509280918312901461)
                ·
                  refine ⟨367282157280942880739657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62682821509280918312901461 367282157280942880739657)
                  ·
                    rfl

theorem cell23_6437515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_6437515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437515 prefixEnd_6437515 := by exact prefixLift 6437515
  have htrace : WordTrace (prefixWord ++ tailWord_6437515) baseStart_6437515 baseEnd_6437515 := by
    simpa [prefixWord, tailWord_6437515, baseEnd_6437515] using wordTrace_append hprefix tailTrace_6437515
  have hstable : (prefixWord ++ tailWord_6437515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437515).length < 2 ^ (prefixWord ++ tailWord_6437515).sum := by decide
  have hdescent : baseEnd_6437515 < baseStart_6437515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437549 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 7]
def baseStart_6437549 : Nat := 118140960795 + 6437549 * 2 ^ 59
def prefixEnd_6437549 : Nat := 4983230072969 + 3 ^ 40 * 6437549 * 2
def baseEnd_6437549 : Nat := 367284097096748754847973

theorem tailTrace_6437549 : CollatzResearch.WordTrace tailWord_6437549 prefixEnd_6437549 367284097096748754847973 := by
  unfold tailWord_6437549
  simp only [CollatzResearch.WordTrace]
  refine ⟨234796701354866893682955701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156531134236577929121970467 234796701354866893682955701)
  ·
    refine ⟨22012190752018771282777097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234796701354866893682955701 22012190752018771282777097)
    ·
      refine ⟨16509143064014078462082823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22012190752018771282777097 16509143064014078462082823)
      ·
        refine ⟨24763714596021117693124235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16509143064014078462082823 24763714596021117693124235)
        ·
          refine ⟨37145571894031676539686353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24763714596021117693124235 37145571894031676539686353)
          ·
            refine ⟨27859178920523757404764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37145571894031676539686353 27859178920523757404764765)
            ·
              refine ⟨10447192095196409026786787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27859178920523757404764765 10447192095196409026786787)
              ·
                refine ⟨15670788142794613540180181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447192095196409026786787 15670788142794613540180181)
                ·
                  refine ⟨367284097096748754847973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15670788142794613540180181 367284097096748754847973)
                  ·
                    rfl

theorem cell23_6437549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_6437549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437549 prefixEnd_6437549 := by exact prefixLift 6437549
  have htrace : WordTrace (prefixWord ++ tailWord_6437549) baseStart_6437549 baseEnd_6437549 := by
    simpa [prefixWord, tailWord_6437549, baseEnd_6437549] using wordTrace_append hprefix tailTrace_6437549
  have hstable : (prefixWord ++ tailWord_6437549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437549).length < 2 ^ (prefixWord ++ tailWord_6437549).sum := by decide
  have hdescent : baseEnd_6437549 < baseStart_6437549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437562 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_6437562 : Nat := 118140960795 + 6437562 * 2 ^ 59
def prefixEnd_6437562 : Nat := 4983230072969 + 3 ^ 40 * 6437562 * 2
def baseEnd_6437562 : Nat := 1101854516373082414256399

theorem tailTrace_6437562 : CollatzResearch.WordTrace tailWord_6437562 prefixEnd_6437562 1101854516373082414256399 := by
  unfold tailWord_6437562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58699293875954949225794735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156531450335879864602119293 58699293875954949225794735)
  ·
    refine ⟨88048940813932423838692103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58699293875954949225794735 88048940813932423838692103)
    ·
      refine ⟨132073411220898635758038155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88048940813932423838692103 132073411220898635758038155)
      ·
        refine ⟨198110116831347953637057233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132073411220898635758038155 198110116831347953637057233)
        ·
          refine ⟨148582587623510965227792925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198110116831347953637057233 148582587623510965227792925)
          ·
            refine ⟨55718470358816611960422347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148582587623510965227792925 55718470358816611960422347)
            ·
              refine ⟨83577705538224917940633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55718470358816611960422347 83577705538224917940633521)
              ·
                refine ⟨62683279153668688455475141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83577705538224917940633521 62683279153668688455475141)
                ·
                  refine ⟨11753114841312879085401589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62683279153668688455475141 11753114841312879085401589)
                  ·
                    refine ⟨1101854516373082414256399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11753114841312879085401589 1101854516373082414256399)
                    ·
                      rfl

theorem cell23_6437562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_6437562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437562 prefixEnd_6437562 := by exact prefixLift 6437562
  have htrace : WordTrace (prefixWord ++ tailWord_6437562) baseStart_6437562 baseEnd_6437562 := by
    simpa [prefixWord, tailWord_6437562, baseEnd_6437562] using wordTrace_append hprefix tailTrace_6437562
  have hstable : (prefixWord ++ tailWord_6437562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437562).length < 2 ^ (prefixWord ++ tailWord_6437562).sum := by decide
  have hdescent : baseEnd_6437562 < baseStart_6437562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437596 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6437596 : Nat := 118140960795 + 6437596 * 2 ^ 59
def prefixEnd_6437596 : Nat := 4983230072969 + 3 ^ 40 * 6437596 * 2
def baseEnd_6437596 : Nat := 1101860335820500036581347

theorem tailTrace_6437596 : CollatzResearch.WordTrace tailWord_6437596 prefixEnd_6437596 1101860335820500036581347 := by
  unfold tailWord_6437596
  simp only [CollatzResearch.WordTrace]
  refine ⟨117399207792848310354958321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156532277057131080473277761 117399207792848310354958321)
  ·
    refine ⟨88049405844636232766218741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117399207792848310354958321 88049405844636232766218741)
    ·
      refine ⟨8254631797934646821833007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88049405844636232766218741 8254631797934646821833007)
      ·
        refine ⟨12381947696901970232749511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254631797934646821833007 12381947696901970232749511)
        ·
          refine ⟨18572921545352955349124267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381947696901970232749511 18572921545352955349124267)
          ·
            refine ⟨27859382318029433023686401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572921545352955349124267 27859382318029433023686401)
            ·
              refine ⟨20894536738522074767764801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27859382318029433023686401 20894536738522074767764801)
              ·
                refine ⟨15670902553891556075823601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20894536738522074767764801 15670902553891556075823601)
                ·
                  refine ⟨11753176915418667056867701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15670902553891556075823601 11753176915418667056867701)
                  ·
                    refine ⟨1101860335820500036581347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11753176915418667056867701 1101860335820500036581347)
                    ·
                      rfl

theorem cell23_6437596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6437596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437596 prefixEnd_6437596 := by exact prefixLift 6437596
  have htrace : WordTrace (prefixWord ++ tailWord_6437596) baseStart_6437596 baseEnd_6437596 := by
    simpa [prefixWord, tailWord_6437596, baseEnd_6437596] using wordTrace_append hprefix tailTrace_6437596
  have hstable : (prefixWord ++ tailWord_6437596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437596).length < 2 ^ (prefixWord ++ tailWord_6437596).sum := by decide
  have hdescent : baseEnd_6437596 < baseStart_6437596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437599 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_6437599 : Nat := 118140960795 + 6437599 * 2 ^ 59
def prefixEnd_6437599 : Nat := 4983230072969 + 3 ^ 40 * 6437599 * 2
def baseEnd_6437599 : Nat := 3305582547903463598006527

theorem tailTrace_6437599 : CollatzResearch.WordTrace tailWord_6437599 prefixEnd_6437599 3305582547903463598006527 := by
  unfold tailWord_6437599
  simp only [CollatzResearch.WordTrace]
  refine ⟨234798525004685752222275851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156532350003123834814850567 234798525004685752222275851)
  ·
    refine ⟨352197787507028628333413777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234798525004685752222275851 352197787507028628333413777)
    ·
      refine ⟨264148340630271471250060333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352197787507028628333413777 264148340630271471250060333)
      ·
        refine ⟨99055627736351801718772625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264148340630271471250060333 99055627736351801718772625)
        ·
          refine ⟨74291720802263851289079469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99055627736351801718772625 74291720802263851289079469)
          ·
            refine ⟨27859395300848944233404801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74291720802263851289079469 27859395300848944233404801)
            ·
              refine ⟨20894546475636708175053601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27859395300848944233404801 20894546475636708175053601)
              ·
                refine ⟨15670909856727531131290201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20894546475636708175053601 15670909856727531131290201)
                ·
                  refine ⟨11753182392545648348467651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15670909856727531131290201 11753182392545648348467651)
                  ·
                    refine ⟨17629773588818472522701477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11753182392545648348467651 17629773588818472522701477)
                    ·
                      refine ⟨3305582547903463598006527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17629773588818472522701477 3305582547903463598006527)
                      ·
                        rfl

theorem cell23_6437599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_6437599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437599 prefixEnd_6437599 := by exact prefixLift 6437599
  have htrace : WordTrace (prefixWord ++ tailWord_6437599) baseStart_6437599 baseEnd_6437599 := by
    simpa [prefixWord, tailWord_6437599, baseEnd_6437599] using wordTrace_append hprefix tailTrace_6437599
  have hstable : (prefixWord ++ tailWord_6437599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437599).length < 2 ^ (prefixWord ++ tailWord_6437599).sum := by decide
  have hdescent : baseEnd_6437599 < baseStart_6437599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437612 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_6437612 : Nat := 118140960795 + 6437612 * 2 ^ 59
def prefixEnd_6437612 : Nat := 4983230072969 + 3 ^ 40 * 6437612 * 2
def baseEnd_6437612 : Nat := 3305589223151972047143967

theorem tailTrace_6437612 : CollatzResearch.WordTrace tailWord_6437612 prefixEnd_6437612 3305589223151972047143967 := by
  unfold tailWord_6437612
  simp only [CollatzResearch.WordTrace]
  refine ⟨117399499576819327721249545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156532666102425770294999393 117399499576819327721249545)
  ·
    refine ⟨88049624682614495790937159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117399499576819327721249545 88049624682614495790937159)
    ·
      refine ⟨132074437023921743686405739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88049624682614495790937159 132074437023921743686405739)
      ·
        refine ⟨198111655535882615529608609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132074437023921743686405739 198111655535882615529608609)
        ·
          refine ⟨148583741651911961647206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198111655535882615529608609 148583741651911961647206457)
          ·
            refine ⟨111437806238933971235404843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148583741651911961647206457 111437806238933971235404843)
            ·
              refine ⟨167156709358400956853107265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111437806238933971235404843 167156709358400956853107265)
              ·
                refine ⟨125367532018800717639830449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167156709358400956853107265 125367532018800717639830449)
                ·
                  refine ⟨94025649014100538229872837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125367532018800717639830449 94025649014100538229872837)
                  ·
                    refine ⟨17629809190143850918101157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94025649014100538229872837 17629809190143850918101157)
                    ·
                      refine ⟨3305589223151972047143967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17629809190143850918101157 3305589223151972047143967)
                      ·
                        rfl

theorem cell23_6437612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_6437612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437612 prefixEnd_6437612 := by exact prefixLift 6437612
  have htrace : WordTrace (prefixWord ++ tailWord_6437612) baseStart_6437612 baseEnd_6437612 := by
    simpa [prefixWord, tailWord_6437612, baseEnd_6437612] using wordTrace_append hprefix tailTrace_6437612
  have hstable : (prefixWord ++ tailWord_6437612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437612).length < 2 ^ (prefixWord ++ tailWord_6437612).sum := by decide
  have hdescent : baseEnd_6437612 < baseStart_6437612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437659 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 5, 2]
def baseStart_6437659 : Nat := 118140960795 + 6437659 * 2 ^ 59
def prefixEnd_6437659 : Nat := 4983230072969 + 3 ^ 40 * 6437659 * 2
def baseEnd_6437659 : Nat := 3305613356742733363256251

theorem tailTrace_6437659 : CollatzResearch.WordTrace tailWord_6437659 prefixEnd_6437659 3305613356742733363256251 := by
  unfold tailWord_6437659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234800713384468382469460031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156533808922978921646306687 234800713384468382469460031)
  ·
    refine ⟨352201070076702573704190047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234800713384468382469460031 352201070076702573704190047)
    ·
      refine ⟨528301605115053860556285071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352201070076702573704190047 528301605115053860556285071)
      ·
        refine ⟨792452407672580790834427607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528301605115053860556285071 792452407672580790834427607)
        ·
          refine ⟨1188678611508871186251641411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792452407672580790834427607 1188678611508871186251641411)
          ·
            refine ⟨1783017917263306779377462117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188678611508871186251641411 1783017917263306779377462117)
            ·
              refine ⟨334315859486870021133274147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1783017917263306779377462117 334315859486870021133274147)
              ·
                refine ⟨501473789230305031699911221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334315859486870021133274147 501473789230305031699911221)
                ·
                  refine ⟨47013167740341096721866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501473789230305031699911221 47013167740341096721866677)
                  ·
                    refine ⟨4407484475656977817675001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47013167740341096721866677 4407484475656977817675001)
                    ·
                      refine ⟨3305613356742733363256251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407484475656977817675001 3305613356742733363256251)
                      ·
                        rfl

theorem cell23_6437659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5, 2].length) (baseStart_6437659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437659 prefixEnd_6437659 := by exact prefixLift 6437659
  have htrace : WordTrace (prefixWord ++ tailWord_6437659) baseStart_6437659 baseEnd_6437659 := by
    simpa [prefixWord, tailWord_6437659, baseEnd_6437659] using wordTrace_append hprefix tailTrace_6437659
  have hstable : (prefixWord ++ tailWord_6437659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437659).length < 2 ^ (prefixWord ++ tailWord_6437659).sum := by decide
  have hdescent : baseEnd_6437659 < baseStart_6437659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437699 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 6, 4]
def baseStart_6437699 : Nat := 118140960795 + 6437699 * 2 ^ 59
def prefixEnd_6437699 : Nat := 4983230072969 + 3 ^ 40 * 6437699 * 2
def baseEnd_6437699 : Nat := 1101877965322971068918689

theorem tailTrace_6437699 : CollatzResearch.WordTrace tailWord_6437699 prefixEnd_6437699 1101877965322971068918689 := by
  unfold tailWord_6437699
  simp only [CollatzResearch.WordTrace]
  refine ⟨234802172304323469300916151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156534781536215646200610767 234802172304323469300916151)
  ·
    refine ⟨352203258456485203951374227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234802172304323469300916151 352203258456485203951374227)
    ·
      refine ⟨528304887684727805927061341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352203258456485203951374227 528304887684727805927061341)
      ·
        refine ⟨198114332881772927222648003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 528304887684727805927061341 198114332881772927222648003)
        ·
          refine ⟨297171499322659390833972005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198114332881772927222648003 297171499322659390833972005)
          ·
            refine ⟨55719656122998635781369751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297171499322659390833972005 55719656122998635781369751)
            ·
              refine ⟨83579484184497953672054627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55719656122998635781369751 83579484184497953672054627)
              ·
                refine ⟨125369226276746930508081941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83579484184497953672054627 125369226276746930508081941)
                ·
                  refine ⟨5876682481722512367566341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125369226276746930508081941 5876682481722512367566341)
                  ·
                    refine ⟨1101877965322971068918689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876682481722512367566341 1101877965322971068918689)
                    ·
                      rfl

theorem cell23_6437699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 4].length) (baseStart_6437699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437699 prefixEnd_6437699 := by exact prefixLift 6437699
  have htrace : WordTrace (prefixWord ++ tailWord_6437699) baseStart_6437699 baseEnd_6437699 := by
    simpa [prefixWord, tailWord_6437699, baseEnd_6437699] using wordTrace_append hprefix tailTrace_6437699
  have hstable : (prefixWord ++ tailWord_6437699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437699).length < 2 ^ (prefixWord ++ tailWord_6437699).sum := by decide
  have hdescent : baseEnd_6437699 < baseStart_6437699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437712 : List Nat := [2, 1, 1, 1, 1, 4, 13]
def baseStart_6437712 : Nat := 118140960795 + 6437712 * 2 ^ 59
def prefixEnd_6437712 : Nat := 4983230072969 + 3 ^ 40 * 6437712 * 2
def baseEnd_6437712 : Nat := 40810377422437304393747

theorem tailTrace_6437712 : CollatzResearch.WordTrace tailWord_6437712 prefixEnd_6437712 40810377422437304393747 := by
  unfold tailWord_6437712
  simp only [CollatzResearch.WordTrace]
  refine ⟨117401323226638186260569695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156535097635517581680759593 117401323226638186260569695)
  ·
    refine ⟨176101984839957279390854543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117401323226638186260569695 176101984839957279390854543)
    ·
      refine ⟨264152977259935919086281815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176101984839957279390854543 264152977259935919086281815)
      ·
        refine ⟨396229465889903878629422723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264152977259935919086281815 396229465889903878629422723)
        ·
          refine ⟨594344198834855817944134085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396229465889903878629422723 594344198834855817944134085)
          ·
            refine ⟨111439537281535465864525141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 594344198834855817944134085 111439537281535465864525141)
            ·
              refine ⟨40810377422437304393747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 111439537281535465864525141 40810377422437304393747)
              ·
                rfl

theorem cell23_6437712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 13].length) (baseStart_6437712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437712 prefixEnd_6437712 := by exact prefixLift 6437712
  have htrace : WordTrace (prefixWord ++ tailWord_6437712) baseStart_6437712 baseEnd_6437712 := by
    simpa [prefixWord, tailWord_6437712, baseEnd_6437712] using wordTrace_append hprefix tailTrace_6437712
  have hstable : (prefixWord ++ tailWord_6437712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437712).length < 2 ^ (prefixWord ++ tailWord_6437712).sum := by decide
  have hdescent : baseEnd_6437712 < baseStart_6437712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437719 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_6437719 : Nat := 118140960795 + 6437719 * 2 ^ 59
def prefixEnd_6437719 : Nat := 4983230072969 + 3 ^ 40 * 6437719 * 2
def baseEnd_6437719 : Nat := 3305644165582003128505975

theorem tailTrace_6437719 : CollatzResearch.WordTrace tailWord_6437719 prefixEnd_6437719 3305644165582003128505975 := by
  unfold tailWord_6437719
  simp only [CollatzResearch.WordTrace]
  refine ⟨234802901764251012716644211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156535267842834008477762807 234802901764251012716644211)
  ·
    refine ⟨352204352646376519074966317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234802901764251012716644211 352204352646376519074966317)
    ·
      refine ⟨132076632242391194653112369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352204352646376519074966317 132076632242391194653112369)
      ·
        refine ⟨99057474181793395989834277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132076632242391194653112369 99057474181793395989834277)
        ·
          refine ⟨18573276409086261748093927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99057474181793395989834277 18573276409086261748093927)
          ·
            refine ⟨27859914613629392622140891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18573276409086261748093927 27859914613629392622140891)
            ·
              refine ⟨41789871920444088933211337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27859914613629392622140891 41789871920444088933211337)
              ·
                refine ⟨31342403940333066699908503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41789871920444088933211337 31342403940333066699908503)
                ·
                  refine ⟨47013605910499600049862755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31342403940333066699908503 47013605910499600049862755)
                  ·
                    refine ⟨70520408865749400074794133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47013605910499600049862755 70520408865749400074794133)
                    ·
                      refine ⟨3305644165582003128505975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70520408865749400074794133 3305644165582003128505975)
                      ·
                        rfl

theorem cell23_6437719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_6437719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437719 prefixEnd_6437719 := by exact prefixLift 6437719
  have htrace : WordTrace (prefixWord ++ tailWord_6437719) baseStart_6437719 baseEnd_6437719 := by
    simpa [prefixWord, tailWord_6437719, baseEnd_6437719] using wordTrace_append hprefix tailTrace_6437719
  have hstable : (prefixWord ++ tailWord_6437719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437719).length < 2 ^ (prefixWord ++ tailWord_6437719).sum := by decide
  have hdescent : baseEnd_6437719 < baseStart_6437719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437733 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_6437733 : Nat := 118140960795 + 6437733 * 2 ^ 59
def prefixEnd_6437733 : Nat := 4983230072969 + 3 ^ 40 * 6437733 * 2
def baseEnd_6437733 : Nat := 1101883784770388691243637

theorem tailTrace_6437733 : CollatzResearch.WordTrace tailWord_6437733 prefixEnd_6437733 1101883784770388691243637 := by
  unfold tailWord_6437733
  simp only [CollatzResearch.WordTrace]
  refine ⟨234803412386200293107653853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156535608257466862071769235 234803412386200293107653853)
  ·
    refine ⟨88051279644825109915370195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234803412386200293107653853 88051279644825109915370195)
    ·
      refine ⟨132076919467237664873055293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88051279644825109915370195 132076919467237664873055293)
      ·
        refine ⟨49528844800214124327395735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132076919467237664873055293 49528844800214124327395735)
        ·
          refine ⟨74293267200321186491093603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49528844800214124327395735 74293267200321186491093603)
          ·
            refine ⟨111439900800481779736640405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74293267200321186491093603 111439900800481779736640405)
            ·
              refine ⟨5223745350022583425155019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111439900800481779736640405 5223745350022583425155019)
              ·
                refine ⟨7835618025033875137732529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223745350022583425155019 7835618025033875137732529)
                ·
                  refine ⟨5876713518775406353299397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7835618025033875137732529 5876713518775406353299397)
                  ·
                    refine ⟨1101883784770388691243637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876713518775406353299397 1101883784770388691243637)
                    ·
                      rfl

theorem cell23_6437733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_6437733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437733 prefixEnd_6437733 := by exact prefixLift 6437733
  have htrace : WordTrace (prefixWord ++ tailWord_6437733) baseStart_6437733 baseEnd_6437733 := by
    simpa [prefixWord, tailWord_6437733, baseEnd_6437733] using wordTrace_append hprefix tailTrace_6437733
  have hstable : (prefixWord ++ tailWord_6437733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437733).length < 2 ^ (prefixWord ++ tailWord_6437733).sum := by decide
  have hdescent : baseEnd_6437733 < baseStart_6437733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437756 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_6437756 : Nat := 118140960795 + 6437756 * 2 ^ 59
def prefixEnd_6437756 : Nat := 4983230072969 + 3 ^ 40 * 6437756 * 2
def baseEnd_6437756 : Nat := 3305663164366219483743305

theorem tailTrace_6437756 : CollatzResearch.WordTrace tailWord_6437756 prefixEnd_6437756 3305663164366219483743305 := by
  unfold tailWord_6437756
  simp only [CollatzResearch.WordTrace]
  refine ⟨117402125632558484017870561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156536167510077978690494081 117402125632558484017870561)
  ·
    refine ⟨88051594224418863013402921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117402125632558484017870561 88051594224418863013402921)
    ·
      refine ⟨66038695668314147260052191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88051594224418863013402921 66038695668314147260052191)
      ·
        refine ⟨99058043502471220890078287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66038695668314147260052191 99058043502471220890078287)
        ·
          refine ⟨148587065253706831335117431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99058043502471220890078287 148587065253706831335117431)
          ·
            refine ⟨222880597880560247002676147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148587065253706831335117431 222880597880560247002676147)
            ·
              refine ⟨334320896820840370504014221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222880597880560247002676147 334320896820840370504014221)
              ·
                refine ⟨125370336307815138939005333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334320896820840370504014221 125370336307815138939005333)
                ·
                  refine ⟨5876734514428834637765875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125370336307815138939005333 5876734514428834637765875)
                  ·
                    refine ⟨8815101771643251956648813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876734514428834637765875 8815101771643251956648813)
                    ·
                      refine ⟨3305663164366219483743305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8815101771643251956648813 3305663164366219483743305)
                      ·
                        rfl

theorem cell23_6437756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_6437756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437756 prefixEnd_6437756 := by exact prefixLift 6437756
  have htrace : WordTrace (prefixWord ++ tailWord_6437756) baseStart_6437756 baseEnd_6437756 := by
    simpa [prefixWord, tailWord_6437756, baseEnd_6437756] using wordTrace_append hprefix tailTrace_6437756
  have hstable : (prefixWord ++ tailWord_6437756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437756).length < 2 ^ (prefixWord ++ tailWord_6437756).sum := by decide
  have hdescent : baseEnd_6437756 < baseStart_6437756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437813 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_6437813 : Nat := 118140960795 + 6437813 * 2 ^ 59
def prefixEnd_6437813 : Nat := 4983230072969 + 3 ^ 40 * 6437813 * 2
def baseEnd_6437813 : Nat := 3305692432763525760730543

theorem tailTrace_6437813 : CollatzResearch.WordTrace tailWord_6437813 prefixEnd_6437813 3305692432763525760730543 := by
  unfold tailWord_6437813
  simp only [CollatzResearch.WordTrace]
  refine ⟨234806330225910466770566093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156537553483940311180377395 234806330225910466770566093)
  ·
    refine ⟨88052373834716425038962285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234806330225910466770566093 88052373834716425038962285)
    ·
      refine ⟨33019640188018659389610857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88052373834716425038962285 33019640188018659389610857)
      ·
        refine ⟨24764730141013994542208143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33019640188018659389610857 24764730141013994542208143)
        ·
          refine ⟨37147095211520991813312215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24764730141013994542208143 37147095211520991813312215)
          ·
            refine ⟨55720642817281487719968323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37147095211520991813312215 55720642817281487719968323)
            ·
              refine ⟨83580964225922231579952485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55720642817281487719968323 83580964225922231579952485)
              ·
                refine ⟨15671430792360418421241091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83580964225922231579952485 15671430792360418421241091)
                ·
                  refine ⟨23507146188540627631861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15671430792360418421241091 23507146188540627631861637)
                  ·
                    refine ⟨4407589910351367680974057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23507146188540627631861637 4407589910351367680974057)
                    ·
                      refine ⟨3305692432763525760730543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407589910351367680974057 3305692432763525760730543)
                      ·
                        rfl

theorem cell23_6437813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_6437813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437813 prefixEnd_6437813 := by exact prefixLift 6437813
  have htrace : WordTrace (prefixWord ++ tailWord_6437813) baseStart_6437813 baseEnd_6437813 := by
    simpa [prefixWord, tailWord_6437813, baseEnd_6437813] using wordTrace_append hprefix tailTrace_6437813
  have hstable : (prefixWord ++ tailWord_6437813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437813).length < 2 ^ (prefixWord ++ tailWord_6437813).sum := by decide
  have hdescent : baseEnd_6437813 < baseStart_6437813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437817 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6437817 : Nat := 118140960795 + 6437817 * 2 ^ 59
def prefixEnd_6437817 : Nat := 4983230072969 + 3 ^ 40 * 6437817 * 2
def baseEnd_6437817 : Nat := 3305694486686143745080525

theorem tailTrace_6437817 : CollatzResearch.WordTrace tailWord_6437817 prefixEnd_6437817 3305694486686143745080525 := by
  unfold tailWord_6437817
  simp only [CollatzResearch.WordTrace]
  refine ⟨234806476117895975453711705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156537650745263983635807803 234806476117895975453711705)
  ·
    refine ⟨176104857088421981590283779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234806476117895975453711705 176104857088421981590283779)
    ·
      refine ⟨264157285632632972385425669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176104857088421981590283779 264157285632632972385425669)
      ·
        refine ⟨49529491056118682322267313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264157285632632972385425669 49529491056118682322267313)
        ·
          refine ⟨37147118292089011741700485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49529491056118682322267313 37147118292089011741700485)
          ·
            refine ⟨6965084679766689701568841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37147118292089011741700485 6965084679766689701568841)
            ·
              refine ⟨5223813509825017276176631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6965084679766689701568841 5223813509825017276176631)
              ·
                refine ⟨7835720264737525914264947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223813509825017276176631 7835720264737525914264947)
                ·
                  refine ⟨11753580397106288871397421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835720264737525914264947 11753580397106288871397421)
                  ·
                    refine ⟨4407592648914858326774033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11753580397106288871397421 4407592648914858326774033)
                    ·
                      refine ⟨3305694486686143745080525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407592648914858326774033 3305694486686143745080525)
                      ·
                        rfl

theorem cell23_6437817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6437817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437817 prefixEnd_6437817 := by exact prefixLift 6437817
  have htrace : WordTrace (prefixWord ++ tailWord_6437817) baseStart_6437817 baseEnd_6437817 := by
    simpa [prefixWord, tailWord_6437817, baseEnd_6437817] using wordTrace_append hprefix tailTrace_6437817
  have hstable : (prefixWord ++ tailWord_6437817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437817).length < 2 ^ (prefixWord ++ tailWord_6437817).sum := by decide
  have hdescent : baseEnd_6437817 < baseStart_6437817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437836 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 7]
def baseStart_6437836 : Nat := 118140960795 + 6437836 * 2 ^ 59
def prefixEnd_6437836 : Nat := 4983230072969 + 3 ^ 40 * 6437836 * 2
def baseEnd_6437836 : Nat := 367300471424286574526993

theorem tailTrace_6437836 : CollatzResearch.WordTrace tailWord_6437836 prefixEnd_6437836 367300471424286574526993 := by
  unfold tailWord_6437836
  simp only [CollatzResearch.WordTrace]
  refine ⟨117403584552413570849326681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156538112736551427799102241 117403584552413570849326681)
  ·
    refine ⟨88052688414310178136995011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117403584552413570849326681 88052688414310178136995011)
    ·
      refine ⟨132079032621465267205492517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88052688414310178136995011 132079032621465267205492517)
      ·
        refine ⟨24764818616524737601029847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132079032621465267205492517 24764818616524737601029847)
        ·
          refine ⟨37147227924787106401544771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24764818616524737601029847 37147227924787106401544771)
          ·
            refine ⟨55720841887180659602317157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37147227924787106401544771 55720841887180659602317157)
            ·
              refine ⟨10447657853846373675434467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55720841887180659602317157 10447657853846373675434467)
              ·
                refine ⟨15671486780769560513151701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447657853846373675434467 15671486780769560513151701)
                ·
                  refine ⟨367300471424286574526993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15671486780769560513151701 367300471424286574526993)
                  ·
                    rfl

theorem cell23_6437836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_6437836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437836 prefixEnd_6437836 := by exact prefixLift 6437836
  have htrace : WordTrace (prefixWord ++ tailWord_6437836) baseStart_6437836 baseEnd_6437836 := by
    simpa [prefixWord, tailWord_6437836, baseEnd_6437836] using wordTrace_append hprefix tailTrace_6437836
  have hstable : (prefixWord ++ tailWord_6437836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437836).length < 2 ^ (prefixWord ++ tailWord_6437836).sum := by decide
  have hdescent : baseEnd_6437836 < baseStart_6437836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437866 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_6437866 : Nat := 118140960795 + 6437866 * 2 ^ 59
def prefixEnd_6437866 : Nat := 4983230072969 + 3 ^ 40 * 6437866 * 2
def baseEnd_6437866 : Nat := 1101906549079404684455933

theorem tailTrace_6437866 : CollatzResearch.WordTrace tailWord_6437866 prefixEnd_6437866 1101906549079404684455933 := by
  unfold tailWord_6437866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58702065823679614205561363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156538842196478971214830301 58702065823679614205561363)
  ·
    refine ⟨88053098735519421308342045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58702065823679614205561363 88053098735519421308342045)
    ·
      refine ⟨33019912025819782990628267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88053098735519421308342045 33019912025819782990628267)
      ·
        refine ⟨49529868038729674485942401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33019912025819782990628267 49529868038729674485942401)
        ·
          refine ⟨37147401029047255864456801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49529868038729674485942401 37147401029047255864456801)
          ·
            refine ⟨27860550771785441898342601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37147401029047255864456801 27860550771785441898342601)
            ·
              refine ⟨20895413078839081423756951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27860550771785441898342601 20895413078839081423756951)
              ·
                refine ⟨31343119618258622135635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20895413078839081423756951 31343119618258622135635427)
                ·
                  refine ⟨47014679427387933203453141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31343119618258622135635427 47014679427387933203453141)
                  ·
                    refine ⟨1101906549079404684455933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47014679427387933203453141 1101906549079404684455933)
                    ·
                      rfl

theorem cell23_6437866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_6437866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437866 prefixEnd_6437866 := by exact prefixLift 6437866
  have htrace : WordTrace (prefixWord ++ tailWord_6437866) baseStart_6437866 baseEnd_6437866 := by
    simpa [prefixWord, tailWord_6437866, baseEnd_6437866] using wordTrace_append hprefix tailTrace_6437866
  have hstable : (prefixWord ++ tailWord_6437866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437866).length < 2 ^ (prefixWord ++ tailWord_6437866).sum := by decide
  have hdescent : baseEnd_6437866 < baseStart_6437866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437923 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3]
def baseStart_6437923 : Nat := 118140960795 + 6437923 * 2 ^ 59
def prefixEnd_6437923 : Nat := 4983230072969 + 3 ^ 40 * 6437923 * 2
def baseEnd_6437923 : Nat := 3305748915635520330355037

theorem tailTrace_6437923 : CollatzResearch.WordTrace tailWord_6437923 prefixEnd_6437923 3305748915635520330355037 := by
  unfold tailWord_6437923
  simp only [CollatzResearch.WordTrace]
  refine ⟨234810342255511955557070423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156540228170341303704713615 234810342255511955557070423)
  ·
    refine ⟨352215513383267933335605635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234810342255511955557070423 352215513383267933335605635)
    ·
      refine ⟨528323270074901900003408453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352215513383267933335605635 528323270074901900003408453)
      ·
        refine ⟨99060613139044106250639085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528323270074901900003408453 99060613139044106250639085)
        ·
          refine ⟨37147729927141539843989657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99060613139044106250639085 37147729927141539843989657)
          ·
            refine ⟨27860797445356154882992243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37147729927141539843989657 27860797445356154882992243)
            ·
              refine ⟨41791196168034232324488365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27860797445356154882992243 41791196168034232324488365)
              ·
                refine ⟨15671698563012837121683137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41791196168034232324488365 15671698563012837121683137)
                ·
                  refine ⟨11753773922259627841262353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15671698563012837121683137 11753773922259627841262353)
                  ·
                    refine ⟨8815330441694720880946765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11753773922259627841262353 8815330441694720880946765)
                    ·
                      refine ⟨3305748915635520330355037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8815330441694720880946765 3305748915635520330355037)
                      ·
                        rfl

theorem cell23_6437923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_6437923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437923 prefixEnd_6437923 := by exact prefixLift 6437923
  have htrace : WordTrace (prefixWord ++ tailWord_6437923) baseStart_6437923 baseEnd_6437923 := by
    simpa [prefixWord, tailWord_6437923, baseEnd_6437923] using wordTrace_append hprefix tailTrace_6437923
  have hstable : (prefixWord ++ tailWord_6437923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437923).length < 2 ^ (prefixWord ++ tailWord_6437923).sum := by decide
  have hdescent : baseEnd_6437923 < baseStart_6437923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437966 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6437966 : Nat := 118140960795 + 6437966 * 2 ^ 59
def prefixEnd_6437966 : Nat := 4983230072969 + 3 ^ 40 * 6437966 * 2
def baseEnd_6437966 : Nat := 3305770995303663662117339

theorem tailTrace_6437966 : CollatzResearch.WordTrace tailWord_6437966 prefixEnd_6437966 3305770995303663662117339 := by
  unfold tailWord_6437966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29351488824294521737610719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156541273729570782600590501 29351488824294521737610719)
  ·
    refine ⟨44027233236441782606416079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29351488824294521737610719 44027233236441782606416079)
    ·
      refine ⟨66040849854662673909624119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44027233236441782606416079 66040849854662673909624119)
      ·
        refine ⟨99061274781994010864436179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66040849854662673909624119 99061274781994010864436179)
        ·
          refine ⟨148591912172991016296654269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99061274781994010864436179 148591912172991016296654269)
          ·
            refine ⟨55721967064871631111245351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148591912172991016296654269 55721967064871631111245351)
            ·
              refine ⟨83582950597307446666868027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55721967064871631111245351 83582950597307446666868027)
              ·
                refine ⟨125374425895961170000302041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83582950597307446666868027 125374425895961170000302041)
                ·
                  refine ⟨94030819421970877500226531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125374425895961170000302041 94030819421970877500226531)
                  ·
                    refine ⟨141046229132956316250339797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94030819421970877500226531 141046229132956316250339797)
                    ·
                      refine ⟨3305770995303663662117339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141046229132956316250339797 3305770995303663662117339)
                      ·
                        rfl

theorem cell23_6437966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6437966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437966 prefixEnd_6437966 := by exact prefixLift 6437966
  have htrace : WordTrace (prefixWord ++ tailWord_6437966) baseStart_6437966 baseEnd_6437966 := by
    simpa [prefixWord, tailWord_6437966, baseEnd_6437966] using wordTrace_append hprefix tailTrace_6437966
  have hstable : (prefixWord ++ tailWord_6437966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437966).length < 2 ^ (prefixWord ++ tailWord_6437966).sum := by decide
  have hdescent : baseEnd_6437966 < baseStart_6437966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437970 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_6437970 : Nat := 118140960795 + 6437970 * 2 ^ 59
def prefixEnd_6437970 : Nat := 4983230072969 + 3 ^ 40 * 6437970 * 2
def baseEnd_6437970 : Nat := 3305773049226281646467321

theorem tailTrace_6437970 : CollatzResearch.WordTrace tailWord_6437970 prefixEnd_6437970 3305773049226281646467321 := by
  unfold tailWord_6437970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58703014121585420646007841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156541370990894455056020909 58703014121585420646007841)
  ·
    refine ⟨44027260591189065484505881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58703014121585420646007841 44027260591189065484505881)
    ·
      refine ⟨33020445443391799113379411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44027260591189065484505881 33020445443391799113379411)
      ·
        refine ⟨49530668165087698670069117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33020445443391799113379411 49530668165087698670069117)
        ·
          refine ⟨18574000561907887001275919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49530668165087698670069117 18574000561907887001275919)
          ·
            refine ⟨27861000842861830501913879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18574000561907887001275919 27861000842861830501913879)
            ·
              refine ⟨41791501264292745752870819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27861000842861830501913879 41791501264292745752870819)
              ·
                refine ⟨62687251896439118629306229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41791501264292745752870819 62687251896439118629306229)
                ·
                  refine ⟨5876929865291167371497459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62687251896439118629306229 5876929865291167371497459)
                  ·
                    refine ⟨8815394797936751057246189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5876929865291167371497459 8815394797936751057246189)
                    ·
                      refine ⟨3305773049226281646467321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8815394797936751057246189 3305773049226281646467321)
                      ·
                        rfl

theorem cell23_6437970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_6437970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437970 prefixEnd_6437970 := by exact prefixLift 6437970
  have htrace : WordTrace (prefixWord ++ tailWord_6437970) baseStart_6437970 baseEnd_6437970 := by
    simpa [prefixWord, tailWord_6437970, baseEnd_6437970] using wordTrace_append hprefix tailTrace_6437970
  have hstable : (prefixWord ++ tailWord_6437970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437970).length < 2 ^ (prefixWord ++ tailWord_6437970).sum := by decide
  have hdescent : baseEnd_6437970 < baseStart_6437970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437973 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_6437973 : Nat := 118140960795 + 6437973 * 2 ^ 59
def prefixEnd_6437973 : Nat := 4983230072969 + 3 ^ 40 * 6437973 * 2
def baseEnd_6437973 : Nat := 1101924863222748378243269

theorem tailTrace_6437973 : CollatzResearch.WordTrace tailWord_6437973 prefixEnd_6437973 1101924863222748378243269 := by
  unfold tailWord_6437973
  simp only [CollatzResearch.WordTrace]
  refine ⟨234812165905330814096390573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156541443936887209397593715 234812165905330814096390573)
  ·
    refine ⟨88054562214499055286146465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234812165905330814096390573 88054562214499055286146465)
    ·
      refine ⟨66040921660874291464609849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88054562214499055286146465 66040921660874291464609849)
      ·
        refine ⟨49530691245655718598457387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66040921660874291464609849 49530691245655718598457387)
        ·
          refine ⟨74296036868483577897686081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49530691245655718598457387 74296036868483577897686081)
          ·
            refine ⟨55722027651362683423264561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74296036868483577897686081 55722027651362683423264561)
            ·
              refine ⟨41791520738522012567448421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55722027651362683423264561 41791520738522012567448421)
              ·
                refine ⟨7835910138472877356396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41791520738522012567448421 7835910138472877356396579)
                ·
                  refine ⟨11753865207709316034594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7835910138472877356396579 11753865207709316034594869)
                  ·
                    refine ⟨1101924863222748378243269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11753865207709316034594869 1101924863222748378243269)
                    ·
                      rfl

theorem cell23_6437973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_6437973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437973 prefixEnd_6437973 := by exact prefixLift 6437973
  have htrace : WordTrace (prefixWord ++ tailWord_6437973) baseStart_6437973 baseEnd_6437973 := by
    simpa [prefixWord, tailWord_6437973, baseEnd_6437973] using wordTrace_append hprefix tailTrace_6437973
  have hstable : (prefixWord ++ tailWord_6437973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437973).length < 2 ^ (prefixWord ++ tailWord_6437973).sum := by decide
  have hdescent : baseEnd_6437973 < baseStart_6437973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6437980 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6437980 : Nat := 118140960795 + 6437980 * 2 ^ 59
def prefixEnd_6437980 : Nat := 4983230072969 + 3 ^ 40 * 6437980 * 2
def baseEnd_6437980 : Nat := 3305778184032826607342275

theorem tailTrace_6437980 : CollatzResearch.WordTrace tailWord_6437980 prefixEnd_6437980 3305778184032826607342275 := by
  unfold tailWord_6437980
  simp only [CollatzResearch.WordTrace]
  refine ⟨117406210608152727145947697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156541614144203636194596929 117406210608152727145947697)
  ·
    refine ⟨88054657956114545359460773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117406210608152727145947697 88054657956114545359460773)
    ·
      refine ⟨16510248366771477254898895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88054657956114545359460773 16510248366771477254898895)
      ·
        refine ⟨24765372550157215882348343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510248366771477254898895 24765372550157215882348343)
        ·
          refine ⟨37148058825235823823522515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24765372550157215882348343 37148058825235823823522515)
          ·
            refine ⟨55722088237853735735283773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37148058825235823823522515 55722088237853735735283773)
            ·
              refine ⟨20895783089195150900731415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55722088237853735735283773 20895783089195150900731415)
              ·
                refine ⟨31343674633792726351097123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20895783089195150900731415 31343674633792726351097123)
                ·
                  refine ⟨47015511950689089526645685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31343674633792726351097123 47015511950689089526645685)
                  ·
                    refine ⟨4407704245377102143123033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47015511950689089526645685 4407704245377102143123033)
                    ·
                      refine ⟨3305778184032826607342275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407704245377102143123033 3305778184032826607342275)
                      ·
                        rfl

theorem cell23_6437980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6437980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6437980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6437980 prefixEnd_6437980 := by exact prefixLift 6437980
  have htrace : WordTrace (prefixWord ++ tailWord_6437980) baseStart_6437980 baseEnd_6437980 := by
    simpa [prefixWord, tailWord_6437980, baseEnd_6437980] using wordTrace_append hprefix tailTrace_6437980
  have hstable : (prefixWord ++ tailWord_6437980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6437980).length < 2 ^ (prefixWord ++ tailWord_6437980).sum := by decide
  have hdescent : baseEnd_6437980 < baseStart_6437980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6437980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438013 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_6438013 : Nat := 118140960795 + 6438013 * 2 ^ 59
def prefixEnd_6438013 : Nat := 4983230072969 + 3 ^ 40 * 6438013 * 2
def baseEnd_6438013 : Nat := 3305795128894424978229623

theorem tailTrace_6438013 : CollatzResearch.WordTrace tailWord_6438013 prefixEnd_6438013 3305795128894424978229623 := by
  unfold tailWord_6438013
  simp only [CollatzResearch.WordTrace]
  refine ⟨234813624825185900927846693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156542416550123933951897795 234813624825185900927846693)
  ·
    refine ⟨44027554654722356423971255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234813624825185900927846693 44027554654722356423971255)
    ·
      refine ⟨66041331982083534635956883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44027554654722356423971255 66041331982083534635956883)
      ·
        refine ⟨99061997973125301953935325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66041331982083534635956883 99061997973125301953935325)
        ·
          refine ⟨37148249239921988232725747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99061997973125301953935325 37148249239921988232725747)
          ·
            refine ⟨55722373859882982349088621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37148249239921988232725747 55722373859882982349088621)
            ·
              refine ⟨20895890197456118380908233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55722373859882982349088621 20895890197456118380908233)
              ·
                refine ⟨15671917648092088785681175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20895890197456118380908233 15671917648092088785681175)
                ·
                  refine ⟨23507876472138133178521763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15671917648092088785681175 23507876472138133178521763)
                  ·
                    refine ⟨35261814708207199767782645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23507876472138133178521763 35261814708207199767782645)
                    ·
                      refine ⟨3305795128894424978229623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35261814708207199767782645 3305795128894424978229623)
                      ·
                        rfl

theorem cell23_6438013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_6438013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438013 prefixEnd_6438013 := by exact prefixLift 6438013
  have htrace : WordTrace (prefixWord ++ tailWord_6438013) baseStart_6438013 baseEnd_6438013 := by
    simpa [prefixWord, tailWord_6438013, baseEnd_6438013] using wordTrace_append hprefix tailTrace_6438013
  have hstable : (prefixWord ++ tailWord_6438013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438013).length < 2 ^ (prefixWord ++ tailWord_6438013).sum := by decide
  have hdescent : baseEnd_6438013 < baseStart_6438013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438020 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6438020 : Nat := 118140960795 + 6438020 * 2 ^ 59
def prefixEnd_6438020 : Nat := 4983230072969 + 3 ^ 40 * 6438020 * 2
def baseEnd_6438020 : Nat := 1101932907753002150280697

theorem tailTrace_6438020 : CollatzResearch.WordTrace tailWord_6438020 prefixEnd_6438020 1101932907753002150280697 := by
  unfold tailWord_6438020
  simp only [CollatzResearch.WordTrace]
  refine ⟨117406940068080270561675757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156542586757440360748901009 117406940068080270561675757)
  ·
    refine ⟨44027602525530101460628409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117406940068080270561675757 44027602525530101460628409)
    ·
      refine ⟨33020701894147576095471307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44027602525530101460628409 33020701894147576095471307)
      ·
        refine ⟨49531052841221364143206961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33020701894147576095471307 49531052841221364143206961)
        ·
          refine ⟨37148289630916023107405221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49531052841221364143206961 37148289630916023107405221)
          ·
            refine ⟨6965304305796754332638479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37148289630916023107405221 6965304305796754332638479)
            ·
              refine ⟨10447956458695131498957719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965304305796754332638479 10447956458695131498957719)
              ·
                refine ⟨15671934688042697248436579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447956458695131498957719 15671934688042697248436579)
                ·
                  refine ⟨23507902032064045872654869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15671934688042697248436579 23507902032064045872654869)
                  ·
                    refine ⟨1101932907753002150280697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23507902032064045872654869 1101932907753002150280697)
                    ·
                      rfl

theorem cell23_6438020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6438020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438020 prefixEnd_6438020 := by exact prefixLift 6438020
  have htrace : WordTrace (prefixWord ++ tailWord_6438020) baseStart_6438020 baseEnd_6438020 := by
    simpa [prefixWord, tailWord_6438020, baseEnd_6438020] using wordTrace_append hprefix tailTrace_6438020
  have hstable : (prefixWord ++ tailWord_6438020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438020).length < 2 ^ (prefixWord ++ tailWord_6438020).sum := by decide
  have hdescent : baseEnd_6438020 < baseStart_6438020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438050 : List Nat := [3, 3, 1, 3, 2, 2, 9]
def baseStart_6438050 : Nat := 118140960795 + 6438050 * 2 ^ 59
def prefixEnd_6438050 : Nat := 4983230072969 + 3 ^ 40 * 6438050 * 2
def baseEnd_6438050 : Nat := 40812520094798041153913

theorem tailTrace_6438050 : CollatzResearch.WordTrace tailWord_6438050 prefixEnd_6438050 40812520094798041153913 := by
  unfold tailWord_6438050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58703743581512964061735901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156543316217367904164629069 58703743581512964061735901)
  ·
    refine ⟨22013903843067361523150963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58703743581512964061735901 22013903843067361523150963)
    ·
      refine ⟨33020855764601042284726445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22013903843067361523150963 33020855764601042284726445)
      ·
        refine ⟨12382820911725390856772417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33020855764601042284726445 12382820911725390856772417)
        ·
          refine ⟨9287115683794043142579313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12382820911725390856772417 9287115683794043142579313)
          ·
            refine ⟨6965336762845532356934485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9287115683794043142579313 6965336762845532356934485)
            ·
              refine ⟨40812520094798041153913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6965336762845532356934485 40812520094798041153913)
              ·
                rfl

theorem cell23_6438050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 9].length) (baseStart_6438050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438050 prefixEnd_6438050 := by exact prefixLift 6438050
  have htrace : WordTrace (prefixWord ++ tailWord_6438050) baseStart_6438050 baseEnd_6438050 := by
    simpa [prefixWord, tailWord_6438050, baseEnd_6438050] using wordTrace_append hprefix tailTrace_6438050
  have hstable : (prefixWord ++ tailWord_6438050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438050).length < 2 ^ (prefixWord ++ tailWord_6438050).sum := by decide
  have hdescent : baseEnd_6438050 < baseStart_6438050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438061 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_6438061 : Nat := 118140960795 + 6438061 * 2 ^ 59
def prefixEnd_6438061 : Nat := 4983230072969 + 3 ^ 40 * 6438061 * 2
def baseEnd_6438061 : Nat := 3305819775965840790429403

theorem tailTrace_6438061 : CollatzResearch.WordTrace tailWord_6438061 prefixEnd_6438061 3305819775965840790429403 := by
  unfold tailWord_6438061
  simp only [CollatzResearch.WordTrace]
  refine ⟨234815375529012005125594037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156543583686008003417062691 234815375529012005125594037)
  ·
    refine ⟨22013941455844875480524441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234815375529012005125594037 22013941455844875480524441)
    ·
      refine ⟨16510456091883656610393331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22013941455844875480524441 16510456091883656610393331)
      ·
        refine ⟨24765684137825484915589997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510456091883656610393331 24765684137825484915589997)
        ·
          refine ⟨9287131551684556843346249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24765684137825484915589997 9287131551684556843346249)
          ·
            refine ⟨6965348663763417632509687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9287131551684556843346249 6965348663763417632509687)
            ·
              refine ⟨10448022995645126448764531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965348663763417632509687 10448022995645126448764531)
              ·
                refine ⟨15672034493467689673146797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448022995645126448764531 15672034493467689673146797)
                ·
                  refine ⟨5877012935050383627430049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15672034493467689673146797 5877012935050383627430049)
                  ·
                    refine ⟨4407759701287787720572537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877012935050383627430049 4407759701287787720572537)
                    ·
                      refine ⟨3305819775965840790429403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407759701287787720572537 3305819775965840790429403)
                      ·
                        rfl

theorem cell23_6438061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_6438061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438061 prefixEnd_6438061 := by exact prefixLift 6438061
  have htrace : WordTrace (prefixWord ++ tailWord_6438061) baseStart_6438061 baseEnd_6438061 := by
    simpa [prefixWord, tailWord_6438061, baseEnd_6438061] using wordTrace_append hprefix tailTrace_6438061
  have hstable : (prefixWord ++ tailWord_6438061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438061).length < 2 ^ (prefixWord ++ tailWord_6438061).sum := by decide
  have hdescent : baseEnd_6438061 < baseStart_6438061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438103 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_6438103 : Nat := 118140960795 + 6438103 * 2 ^ 59
def prefixEnd_6438103 : Nat := 4983230072969 + 3 ^ 40 * 6438103 * 2
def baseEnd_6438103 : Nat := 3305841342153329626104209

theorem tailTrace_6438103 : CollatzResearch.WordTrace tailWord_6438103 prefixEnd_6438103 3305841342153329626104209 := by
  unfold tailWord_6438103
  simp only [CollatzResearch.WordTrace]
  refine ⟨234816907394859846298622963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156544604929906564199081975 234816907394859846298622963)
  ·
    refine ⟨352225361092289769447934445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234816907394859846298622963 352225361092289769447934445)
    ·
      refine ⟨132084510409608663542975417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352225361092289769447934445 132084510409608663542975417)
      ·
        refine ⟨99063382807206497657231563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132084510409608663542975417 99063382807206497657231563)
        ·
          refine ⟨148595074210809746485847345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99063382807206497657231563 148595074210809746485847345)
          ·
            refine ⟨111446305658107309864385509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148595074210809746485847345 111446305658107309864385509)
            ·
              refine ⟨20896182310895120599572283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111446305658107309864385509 20896182310895120599572283)
              ·
                refine ⟨31344273466342680899358425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20896182310895120599572283 31344273466342680899358425)
                ·
                  refine ⟨23508205099757010674518819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31344273466342680899358425 23508205099757010674518819)
                  ·
                    refine ⟨35262307649635516011778229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23508205099757010674518819 35262307649635516011778229)
                    ·
                      refine ⟨3305841342153329626104209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35262307649635516011778229 3305841342153329626104209)
                      ·
                        rfl

theorem cell23_6438103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_6438103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438103 prefixEnd_6438103 := by exact prefixLift 6438103
  have htrace : WordTrace (prefixWord ++ tailWord_6438103) baseStart_6438103 baseEnd_6438103 := by
    simpa [prefixWord, tailWord_6438103, baseEnd_6438103] using wordTrace_append hprefix tailTrace_6438103
  have hstable : (prefixWord ++ tailWord_6438103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438103).length < 2 ^ (prefixWord ++ tailWord_6438103).sum := by decide
  have hdescent : baseEnd_6438103 < baseStart_6438103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438140 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 7]
def baseStart_6438140 : Nat := 118140960795 + 6438140 * 2 ^ 59
def prefixEnd_6438140 : Nat := 4983230072969 + 3 ^ 40 * 6438140 * 2
def baseEnd_6438140 : Nat := 367317815659727331260171

theorem tailTrace_6438140 : CollatzResearch.WordTrace tailWord_6438140 prefixEnd_6438140 367317815659727331260171 := by
  unfold tailWord_6438140
  simp only [CollatzResearch.WordTrace]
  refine ⟨117409128447862900808859937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156545504597150534411813249 117409128447862900808859937)
  ·
    refine ⟨88056846335897175606644953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117409128447862900808859937 88056846335897175606644953)
    ·
      refine ⟨66042634751922881704983715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88056846335897175606644953 66042634751922881704983715)
      ·
        refine ⟨99063952127884322557475573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66042634751922881704983715 99063952127884322557475573)
        ·
          refine ⟨9287245511989155239763335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99063952127884322557475573 9287245511989155239763335)
          ·
            refine ⟨13930868267983732859645003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287245511989155239763335 13930868267983732859645003)
            ·
              refine ⟨20896302401975599289467505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13930868267983732859645003 20896302401975599289467505)
              ·
                refine ⟨15672226801481699467100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20896302401975599289467505 15672226801481699467100629)
                ·
                  refine ⟨367317815659727331260171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15672226801481699467100629 367317815659727331260171)
                  ·
                    rfl

theorem cell23_6438140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_6438140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438140 prefixEnd_6438140 := by exact prefixLift 6438140
  have htrace : WordTrace (prefixWord ++ tailWord_6438140) baseStart_6438140 baseEnd_6438140 := by
    simpa [prefixWord, tailWord_6438140, baseEnd_6438140] using wordTrace_append hprefix tailTrace_6438140
  have hstable : (prefixWord ++ tailWord_6438140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438140).length < 2 ^ (prefixWord ++ tailWord_6438140).sum := by decide
  have hdescent : baseEnd_6438140 < baseStart_6438140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438153 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_6438153 : Nat := 118140960795 + 6438153 * 2 ^ 59
def prefixEnd_6438153 : Nat := 4983230072969 + 3 ^ 40 * 6438153 * 2
def baseEnd_6438153 : Nat := 1101955672062018143492993

theorem tailTrace_6438153 : CollatzResearch.WordTrace tailWord_6438153 prefixEnd_6438153 1101955672062018143492993 := by
  unfold tailWord_6438153
  simp only [CollatzResearch.WordTrace]
  refine ⟨234818731044678704837943113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156545820696452469891962075 234818731044678704837943113)
  ·
    refine ⟨176114048283509028628457335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234818731044678704837943113 176114048283509028628457335)
    ·
      refine ⟨264171072425263542942686003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176114048283509028628457335 264171072425263542942686003)
      ·
        refine ⟨396256608637895314414029005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264171072425263542942686003 396256608637895314414029005)
        ·
          refine ⟨148596228239210742905260877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396256608637895314414029005 148596228239210742905260877)
          ·
            refine ⟨55723585589704028589472829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148596228239210742905260877 55723585589704028589472829)
            ·
              refine ⟨20896344596139010721052311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55723585589704028589472829 20896344596139010721052311)
              ·
                refine ⟨31344516894208516081578467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20896344596139010721052311 31344516894208516081578467)
                ·
                  refine ⟨47016775341312774122367701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31344516894208516081578467 47016775341312774122367701)
                  ·
                    refine ⟨1101955672062018143492993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47016775341312774122367701 1101955672062018143492993)
                    ·
                      rfl

theorem cell23_6438153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_6438153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438153 prefixEnd_6438153 := by exact prefixLift 6438153
  have htrace : WordTrace (prefixWord ++ tailWord_6438153) baseStart_6438153 baseEnd_6438153 := by
    simpa [prefixWord, tailWord_6438153, baseEnd_6438153] using wordTrace_append hprefix tailTrace_6438153
  have hstable : (prefixWord ++ tailWord_6438153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438153).length < 2 ^ (prefixWord ++ tailWord_6438153).sum := by decide
  have hdescent : baseEnd_6438153 < baseStart_6438153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438174 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_6438174 : Nat := 118140960795 + 6438174 * 2 ^ 59
def prefixEnd_6438174 : Nat := 4983230072969 + 3 ^ 40 * 6438174 * 2
def baseEnd_6438174 : Nat := 367319755475533205368487

theorem tailTrace_6438174 : CollatzResearch.WordTrace tailWord_6438174 prefixEnd_6438174 367319755475533205368487 := by
  unfold tailWord_6438174
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352437122200328178057197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156546331318401750282971717 29352437122200328178057197)
  ·
    refine ⟨11007163920825123066771449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29352437122200328178057197 11007163920825123066771449)
    ·
      refine ⟨8255372940618842300078587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11007163920825123066771449 8255372940618842300078587)
      ·
        refine ⟨12383059410928263450117881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255372940618842300078587 12383059410928263450117881)
        ·
          refine ⟨9287294558196197587588411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12383059410928263450117881 9287294558196197587588411)
          ·
            refine ⟨13930941837294296381382617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287294558196197587588411 13930941837294296381382617)
            ·
              refine ⟨10448206377970722286036963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13930941837294296381382617 10448206377970722286036963)
              ·
                refine ⟨15672309566956083429055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448206377970722286036963 15672309566956083429055445)
                ·
                  refine ⟨367319755475533205368487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15672309566956083429055445 367319755475533205368487)
                  ·
                    rfl

theorem cell23_6438174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_6438174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438174 prefixEnd_6438174 := by exact prefixLift 6438174
  have htrace : WordTrace (prefixWord ++ tailWord_6438174) baseStart_6438174 baseEnd_6438174 := by
    simpa [prefixWord, tailWord_6438174, baseEnd_6438174] using wordTrace_append hprefix tailTrace_6438174
  have hstable : (prefixWord ++ tailWord_6438174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438174).length < 2 ^ (prefixWord ++ tailWord_6438174).sum := by decide
  have hdescent : baseEnd_6438174 < baseStart_6438174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438233 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_6438233 : Nat := 118140960795 + 6438233 * 2 ^ 59
def prefixEnd_6438233 : Nat := 4983230072969 + 3 ^ 40 * 6438233 * 2
def baseEnd_6438233 : Nat := 3305908094638414117478611

theorem tailTrace_6438233 : CollatzResearch.WordTrace tailWord_6438233 prefixEnd_6438233 3305908094638414117478611 := by
  unfold tailWord_6438233
  simp only [CollatzResearch.WordTrace]
  refine ⟨234821648884388878500855353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156547765922925919000570235 234821648884388878500855353)
  ·
    refine ⟨176116236663291658875641515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234821648884388878500855353 176116236663291658875641515)
    ·
      refine ⟨264174354994937488313462273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176116236663291658875641515 264174354994937488313462273)
      ·
        refine ⟨198130766246203116235096705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264174354994937488313462273 198130766246203116235096705)
        ·
          refine ⟨148598074684652337176322529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198130766246203116235096705 148598074684652337176322529)
          ·
            refine ⟨111448556013489252882241897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148598074684652337176322529 111448556013489252882241897)
            ·
              refine ⟨83586417010116939661681423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111448556013489252882241897 83586417010116939661681423)
              ·
                refine ⟨125379625515175409492522135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83586417010116939661681423 125379625515175409492522135)
                ·
                  refine ⟨188069438272763114238783203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125379625515175409492522135 188069438272763114238783203)
                  ·
                    refine ⟨282104157409144671358174805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188069438272763114238783203 282104157409144671358174805)
                    ·
                      refine ⟨3305908094638414117478611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 282104157409144671358174805 3305908094638414117478611)
                      ·
                        rfl

theorem cell23_6438233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_6438233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438233 prefixEnd_6438233 := by exact prefixLift 6438233
  have htrace : WordTrace (prefixWord ++ tailWord_6438233) baseStart_6438233 baseEnd_6438233 := by
    simpa [prefixWord, tailWord_6438233, baseEnd_6438233] using wordTrace_append hprefix tailTrace_6438233
  have hstable : (prefixWord ++ tailWord_6438233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438233).length < 2 ^ (prefixWord ++ tailWord_6438233).sum := by decide
  have hdescent : baseEnd_6438233 < baseStart_6438233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438247 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 6]
def baseStart_6438247 : Nat := 118140960795 + 6438247 * 2 ^ 59
def prefixEnd_6438247 : Nat := 4983230072969 + 3 ^ 40 * 6438247 * 2
def baseEnd_6438247 : Nat := 367323920374175229189283

theorem tailTrace_6438247 : CollatzResearch.WordTrace tailWord_6438247 prefixEnd_6438247 367323920374175229189283 := by
  unfold tailWord_6438247
  simp only [CollatzResearch.WordTrace]
  refine ⟨234822159506338158891864995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156548106337558772594576663 234822159506338158891864995)
  ·
    refine ⟨352233239259507238337797493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234822159506338158891864995 352233239259507238337797493)
    ·
      refine ⟨33021866180578803594168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352233239259507238337797493 33021866180578803594168515)
      ·
        refine ⟨49532799270868205391252773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33021866180578803594168515 49532799270868205391252773)
        ·
          refine ⟨9287399863287788510859895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49532799270868205391252773 9287399863287788510859895)
          ·
            refine ⟨13931099794931682766289843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287399863287788510859895 13931099794931682766289843)
            ·
              refine ⟨20896649692397524149434765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13931099794931682766289843 20896649692397524149434765)
              ·
                refine ⟨7836243634649071556038037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20896649692397524149434765 7836243634649071556038037)
                ·
                  refine ⟨367323920374175229189283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7836243634649071556038037 367323920374175229189283)
                  ·
                    rfl

theorem cell23_6438247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 6].length) (baseStart_6438247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438247 prefixEnd_6438247 := by exact prefixLift 6438247
  have htrace : WordTrace (prefixWord ++ tailWord_6438247) baseStart_6438247 baseEnd_6438247 := by
    simpa [prefixWord, tailWord_6438247, baseEnd_6438247] using wordTrace_append hprefix tailTrace_6438247
  have hstable : (prefixWord ++ tailWord_6438247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438247).length < 2 ^ (prefixWord ++ tailWord_6438247).sum := by decide
  have hdescent : baseEnd_6438247 < baseStart_6438247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438257 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_6438257 : Nat := 118140960795 + 6438257 * 2 ^ 59
def prefixEnd_6438257 : Nat := 4983230072969 + 3 ^ 40 * 6438257 * 2
def baseEnd_6438257 : Nat := 3305920418174122023578501

theorem tailTrace_6438257 : CollatzResearch.WordTrace tailWord_6438257 prefixEnd_6438257 3305920418174122023578501 := by
  unfold tailWord_6438257
  simp only [CollatzResearch.WordTrace]
  refine ⟨234822524236301930599729025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156548349490867953733152683 234822524236301930599729025)
  ·
    refine ⟨176116893177226447949796769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234822524236301930599729025 176116893177226447949796769)
    ·
      refine ⟨132087669882919835962347577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176116893177226447949796769 132087669882919835962347577)
      ·
        refine ⟨99065752412189876971760683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132087669882919835962347577 99065752412189876971760683)
        ·
          refine ⟨148598628618284815457641025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99065752412189876971760683 148598628618284815457641025)
          ·
            refine ⟨111448971463713611593230769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148598628618284815457641025 111448971463713611593230769)
            ·
              refine ⟨83586728597785208694923077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111448971463713611593230769 83586728597785208694923077)
              ·
                refine ⟨15672511612084726630298077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83586728597785208694923077 15672511612084726630298077)
                ·
                  refine ⟨5877191854531772486361779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15672511612084726630298077 5877191854531772486361779)
                  ·
                    refine ⟨8815787781797658729542669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877191854531772486361779 8815787781797658729542669)
                    ·
                      refine ⟨3305920418174122023578501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8815787781797658729542669 3305920418174122023578501)
                      ·
                        rfl

theorem cell23_6438257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_6438257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438257 prefixEnd_6438257 := by exact prefixLift 6438257
  have htrace : WordTrace (prefixWord ++ tailWord_6438257) baseStart_6438257 baseEnd_6438257 := by
    simpa [prefixWord, tailWord_6438257, baseEnd_6438257] using wordTrace_append hprefix tailTrace_6438257
  have hstable : (prefixWord ++ tailWord_6438257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438257).length < 2 ^ (prefixWord ++ tailWord_6438257).sum := by decide
  have hdescent : baseEnd_6438257 < baseStart_6438257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438307 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 2, 4]
def baseStart_6438307 : Nat := 118140960795 + 6438307 * 2 ^ 59
def prefixEnd_6438307 : Nat := 4983230072969 + 3 ^ 40 * 6438307 * 2
def baseEnd_6438307 : Nat := 1101982030735615609317757

theorem tailTrace_6438307 : CollatzResearch.WordTrace tailWord_6438307 prefixEnd_6438307 1101982030735615609317757 := by
  unfold tailWord_6438307
  simp only [CollatzResearch.WordTrace]
  refine ⟨234824347886120789139049175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156549565257413859426032783 234824347886120789139049175)
  ·
    refine ⟨352236521829181183708573763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234824347886120789139049175 352236521829181183708573763)
    ·
      refine ⟨528354782743771775562860645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352236521829181183708573763 528354782743771775562860645)
      ·
        refine ⟨99066521764457207918036371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528354782743771775562860645 99066521764457207918036371)
        ·
          refine ⟨148599782646685811877054557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99066521764457207918036371 148599782646685811877054557)
          ·
            refine ⟨55724918492507179453895459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148599782646685811877054557 55724918492507179453895459)
            ·
              refine ⟨83587377738760769180843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55724918492507179453895459 83587377738760769180843189)
              ·
                refine ⟨7836316663008822110704049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83587377738760769180843189 7836316663008822110704049)
                ·
                  refine ⟨5877237497256616583028037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836316663008822110704049 5877237497256616583028037)
                  ·
                    refine ⟨1101982030735615609317757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5877237497256616583028037 1101982030735615609317757)
                    ·
                      rfl

theorem cell23_6438307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 4].length) (baseStart_6438307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438307 prefixEnd_6438307 := by exact prefixLift 6438307
  have htrace : WordTrace (prefixWord ++ tailWord_6438307) baseStart_6438307 baseEnd_6438307 := by
    simpa [prefixWord, tailWord_6438307, baseEnd_6438307] using wordTrace_append hprefix tailTrace_6438307
  have hstable : (prefixWord ++ tailWord_6438307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438307).length < 2 ^ (prefixWord ++ tailWord_6438307).sum := by decide
  have hdescent : baseEnd_6438307 < baseStart_6438307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438348 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6438348 : Nat := 118140960795 + 6438348 * 2 ^ 59
def prefixEnd_6438348 : Nat := 4983230072969 + 3 ^ 40 * 6438348 * 2
def baseEnd_6438348 : Nat := 3305967144913681167540583

theorem tailTrace_6438348 : CollatzResearch.WordTrace tailWord_6438348 prefixEnd_6438348 3305967144913681167540583 := by
  unfold tailWord_6438348
  simp only [CollatzResearch.WordTrace]
  refine ⟨117412921639486126570645849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156550562185981502094194465 117412921639486126570645849)
  ·
    refine ⟨88059691229614594927984387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117412921639486126570645849 88059691229614594927984387)
    ·
      refine ⟨132089536844421892391976581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88059691229614594927984387 132089536844421892391976581)
      ·
        refine ⟨24766788158329104823495609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132089536844421892391976581 24766788158329104823495609)
        ·
          refine ⟨18575091118746828617621707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24766788158329104823495609 18575091118746828617621707)
          ·
            refine ⟨27862636678120242926432561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18575091118746828617621707 27862636678120242926432561)
            ·
              refine ⟨20896977508590182194824421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27862636678120242926432561 20896977508590182194824421)
              ·
                refine ⟨3918183282860659161529579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20896977508590182194824421 3918183282860659161529579)
                ·
                  refine ⟨5877274924290988742294369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918183282860659161529579 5877274924290988742294369)
                  ·
                    refine ⟨4407956193218241556720777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877274924290988742294369 4407956193218241556720777)
                    ·
                      refine ⟨3305967144913681167540583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4407956193218241556720777 3305967144913681167540583)
                      ·
                        rfl

theorem cell23_6438348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6438348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438348 prefixEnd_6438348 := by exact prefixLift 6438348
  have htrace : WordTrace (prefixWord ++ tailWord_6438348) baseStart_6438348 baseEnd_6438348 := by
    simpa [prefixWord, tailWord_6438348, baseEnd_6438348] using wordTrace_append hprefix tailTrace_6438348
  have hstable : (prefixWord ++ tailWord_6438348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438348).length < 2 ^ (prefixWord ++ tailWord_6438348).sum := by decide
  have hdescent : baseEnd_6438348 < baseStart_6438348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438350 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_6438350 : Nat := 118140960795 + 6438350 * 2 ^ 59
def prefixEnd_6438350 : Nat := 4983230072969 + 3 ^ 40 * 6438350 * 2
def baseEnd_6438350 : Nat := 1101989390624996719905191

theorem tailTrace_6438350 : CollatzResearch.WordTrace tailWord_6438350 prefixEnd_6438350 1101989390624996719905191 := by
  unfold tailWord_6438350
  simp only [CollatzResearch.WordTrace]
  refine ⟨29353239528120625935358063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156550610816643338321909669 29353239528120625935358063)
  ·
    refine ⟨44029859292180938903037095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29353239528120625935358063 44029859292180938903037095)
    ·
      refine ⟨66044788938271408354555643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44029859292180938903037095 66044788938271408354555643)
      ·
        refine ⟨99067183407407112531833465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66044788938271408354555643 99067183407407112531833465)
        ·
          refine ⟨74300387555555334398875099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99067183407407112531833465 74300387555555334398875099)
          ·
            refine ⟨111450581333333001598312649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74300387555555334398875099 111450581333333001598312649)
            ·
              refine ⟨83587935999999751198734487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111450581333333001598312649 83587935999999751198734487)
              ·
                refine ⟨125381903999999626798101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83587935999999751198734487 125381903999999626798101731)
                ·
                  refine ⟨188072855999999440197152597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125381903999999626798101731 188072855999999440197152597)
                  ·
                    refine ⟨1101989390624996719905191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188072855999999440197152597 1101989390624996719905191)
                    ·
                      rfl

theorem cell23_6438350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_6438350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438350 prefixEnd_6438350 := by exact prefixLift 6438350
  have htrace : WordTrace (prefixWord ++ tailWord_6438350) baseStart_6438350 baseEnd_6438350 := by
    simpa [prefixWord, tailWord_6438350, baseEnd_6438350] using wordTrace_append hprefix tailTrace_6438350
  have hstable : (prefixWord ++ tailWord_6438350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438350).length < 2 ^ (prefixWord ++ tailWord_6438350).sum := by decide
  have hdescent : baseEnd_6438350 < baseStart_6438350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438358 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6438358 : Nat := 118140960795 + 6438358 * 2 ^ 59
def prefixEnd_6438358 : Nat := 4983230072969 + 3 ^ 40 * 6438358 * 2
def baseEnd_6438358 : Nat := 1101990759906742042805179

theorem tailTrace_6438358 : CollatzResearch.WordTrace tailWord_6438358 prefixEnd_6438358 1101990759906742042805179 := by
  unfold tailWord_6438358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676638000558501553072233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156550805339290683232770485 14676638000558501553072233)
  ·
    refine ⟨11007478500418876164804175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14676638000558501553072233 11007478500418876164804175)
    ·
      refine ⟨16511217750628314247206263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007478500418876164804175 16511217750628314247206263)
      ·
        refine ⟨24766826625942471370809395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16511217750628314247206263 24766826625942471370809395)
        ·
          refine ⟨37150239938913707056214093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24766826625942471370809395 37150239938913707056214093)
          ·
            refine ⟨13931339977092640146080285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37150239938913707056214093 13931339977092640146080285)
            ·
              refine ⟨5224252491409740054780107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13931339977092640146080285 5224252491409740054780107)
              ·
                refine ⟨7836378737114610082170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224252491409740054780107 7836378737114610082170161)
                ·
                  refine ⟨5877284052835957561627621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836378737114610082170161 5877284052835957561627621)
                  ·
                    refine ⟨1101990759906742042805179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5877284052835957561627621 1101990759906742042805179)
                    ·
                      rfl

theorem cell23_6438358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6438358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438358 prefixEnd_6438358 := by exact prefixLift 6438358
  have htrace : WordTrace (prefixWord ++ tailWord_6438358) baseStart_6438358 baseEnd_6438358 := by
    simpa [prefixWord, tailWord_6438358, baseEnd_6438358] using wordTrace_append hprefix tailTrace_6438358
  have hstable : (prefixWord ++ tailWord_6438358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438358).length < 2 ^ (prefixWord ++ tailWord_6438358).sum := by decide
  have hdescent : baseEnd_6438358 < baseStart_6438358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438380 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_6438380 : Nat := 118140960795 + 6438380 * 2 ^ 59
def prefixEnd_6438380 : Nat := 4983230072969 + 3 ^ 40 * 6438380 * 2
def baseEnd_6438380 : Nat := 1101994525431541680780145

theorem tailTrace_6438380 : CollatzResearch.WordTrace tailWord_6438380 prefixEnd_6438380 1101994525431541680780145 := by
  unfold tailWord_6438380
  simp only [CollatzResearch.WordTrace]
  refine ⟨117413505207428161303228297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156551340276570881737637729 117413505207428161303228297)
  ·
    refine ⟨88060128905571120977421223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117413505207428161303228297 88060128905571120977421223)
    ·
      refine ⟨132090193358356681466131835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88060128905571120977421223 132090193358356681466131835)
      ·
        refine ⟨198135290037535022199197753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132090193358356681466131835 198135290037535022199197753)
        ·
          refine ⟨148601467528151266649398315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198135290037535022199197753 148601467528151266649398315)
          ·
            refine ⟨222902201292226899974097473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148601467528151266649398315 222902201292226899974097473)
            ·
              refine ⟨167176650969170174980573105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222902201292226899974097473 167176650969170174980573105)
              ·
                refine ⟨125382488226877631235429829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167176650969170174980573105 125382488226877631235429829)
                ·
                  refine ⟨23509216542539555856643093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125382488226877631235429829 23509216542539555856643093)
                  ·
                    refine ⟨1101994525431541680780145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23509216542539555856643093 1101994525431541680780145)
                    ·
                      rfl

theorem cell23_6438380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_6438380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438380 prefixEnd_6438380 := by exact prefixLift 6438380
  have htrace : WordTrace (prefixWord ++ tailWord_6438380) baseStart_6438380 baseEnd_6438380 := by
    simpa [prefixWord, tailWord_6438380, baseEnd_6438380] using wordTrace_append hprefix tailTrace_6438380
  have hstable : (prefixWord ++ tailWord_6438380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438380).length < 2 ^ (prefixWord ++ tailWord_6438380).sum := by decide
  have hdescent : baseEnd_6438380 < baseStart_6438380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438437 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_6438437 : Nat := 118140960795 + 6438437 * 2 ^ 59
def prefixEnd_6438437 : Nat := 4983230072969 + 3 ^ 40 * 6438437 * 2
def baseEnd_6438437 : Nat := 3306012844691931319327673

theorem tailTrace_6438437 : CollatzResearch.WordTrace tailWord_6438437 prefixEnd_6438437 3306012844691931319327673 := by
  unfold tailWord_6438437
  simp only [CollatzResearch.WordTrace]
  refine ⟨234829089375649821341281565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156552726250433214227521043 234829089375649821341281565)
  ·
    refine ⟨88060908515868683002980587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234829089375649821341281565 88060908515868683002980587)
    ·
      refine ⟨132091362773803024504470881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88060908515868683002980587 132091362773803024504470881)
      ·
        refine ⟨99068522080352268378353161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132091362773803024504470881 99068522080352268378353161)
        ·
          refine ⟨74301391560264201283764871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99068522080352268378353161 74301391560264201283764871)
          ·
            refine ⟨111452087340396301925647307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74301391560264201283764871 111452087340396301925647307)
            ·
              refine ⟨167178131010594452888470961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111452087340396301925647307 167178131010594452888470961)
              ·
                refine ⟨125383598257945839666353221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167178131010594452888470961 125383598257945839666353221)
                ·
                  refine ⟨23509424673364844937441229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125383598257945839666353221 23509424673364844937441229)
                  ·
                    refine ⟨8816034252511816851540461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23509424673364844937441229 8816034252511816851540461)
                    ·
                      refine ⟨3306012844691931319327673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816034252511816851540461 3306012844691931319327673)
                      ·
                        rfl

theorem cell23_6438437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_6438437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438437 prefixEnd_6438437 := by exact prefixLift 6438437
  have htrace : WordTrace (prefixWord ++ tailWord_6438437) baseStart_6438437 baseEnd_6438437 := by
    simpa [prefixWord, tailWord_6438437, baseEnd_6438437] using wordTrace_append hprefix tailTrace_6438437
  have hstable : (prefixWord ++ tailWord_6438437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438437).length < 2 ^ (prefixWord ++ tailWord_6438437).sum := by decide
  have hdescent : baseEnd_6438437 < baseStart_6438437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438461 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 5]
def baseStart_6438461 : Nat := 118140960795 + 6438461 * 2 ^ 59
def prefixEnd_6438461 : Nat := 4983230072969 + 3 ^ 40 * 6438461 * 2
def baseEnd_6438461 : Nat := 367336129803071025047507

theorem tailTrace_6438461 : CollatzResearch.WordTrace tailWord_6438461 prefixEnd_6438461 367336129803071025047507 := by
  unfold tailWord_6438461
  simp only [CollatzResearch.WordTrace]
  refine ⟨234829964727562873440155237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156553309818375248960103491 234829964727562873440155237)
  ·
    refine ⟨44030618386418038770029107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234829964727562873440155237 44030618386418038770029107)
    ·
      refine ⟨66045927579627058155043661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44030618386418038770029107 66045927579627058155043661)
      ·
        refine ⟨24767222842360146808141373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66045927579627058155043661 24767222842360146808141373)
        ·
          refine ⟨9287708565885055053053015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24767222842360146808141373 9287708565885055053053015)
          ·
            refine ⟨13931562848827582579579523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287708565885055053053015 13931562848827582579579523)
            ·
              refine ⟨20897344273241373869369285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13931562848827582579579523 20897344273241373869369285)
              ·
                refine ⟨3918252051232757600506741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20897344273241373869369285 3918252051232757600506741)
                ·
                  refine ⟨367336129803071025047507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3918252051232757600506741 367336129803071025047507)
                  ·
                    rfl

theorem cell23_6438461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_6438461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438461 prefixEnd_6438461 := by exact prefixLift 6438461
  have htrace : WordTrace (prefixWord ++ tailWord_6438461) baseStart_6438461 baseEnd_6438461 := by
    simpa [prefixWord, tailWord_6438461, baseEnd_6438461] using wordTrace_append hprefix tailTrace_6438461
  have hstable : (prefixWord ++ tailWord_6438461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438461).length < 2 ^ (prefixWord ++ tailWord_6438461).sum := by decide
  have hdescent : baseEnd_6438461 < baseStart_6438461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438521 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 1, 4]
def baseStart_6438521 : Nat := 118140960795 + 6438521 * 2 ^ 59
def prefixEnd_6438521 : Nat := 4983230072969 + 3 ^ 40 * 6438521 * 2
def baseEnd_6438521 : Nat := 1102018659022302996892429

theorem tailTrace_6438521 : CollatzResearch.WordTrace tailWord_6438521 prefixEnd_6438521 1102018659022302996892429 := by
  unfold tailWord_6438521
  simp only [CollatzResearch.WordTrace]
  refine ⟨234832153107345503687339417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156554768738230335791559611 234832153107345503687339417)
  ·
    refine ⟨176124114830509127765504563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234832153107345503687339417 176124114830509127765504563)
    ·
      refine ⟨264186172245763691648256845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176124114830509127765504563 264186172245763691648256845)
      ·
        refine ⟨99069814592161384368096317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264186172245763691648256845 99069814592161384368096317)
        ·
          refine ⟨37151180472060519138036119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99069814592161384368096317 37151180472060519138036119)
          ·
            refine ⟨55726770708090778707054179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37151180472060519138036119 55726770708090778707054179)
            ·
              refine ⟨83590156062136168060581269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55726770708090778707054179 83590156062136168060581269)
              ·
                refine ⟨3918288565412632877839747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83590156062136168060581269 3918288565412632877839747)
                ·
                  refine ⟨5877432848118949316759621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918288565412632877839747 5877432848118949316759621)
                  ·
                    refine ⟨1102018659022302996892429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5877432848118949316759621 1102018659022302996892429)
                    ·
                      rfl

theorem cell23_6438521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_6438521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438521 prefixEnd_6438521 := by exact prefixLift 6438521
  have htrace : WordTrace (prefixWord ++ tailWord_6438521) baseStart_6438521 baseEnd_6438521 := by
    simpa [prefixWord, tailWord_6438521, baseEnd_6438521] using wordTrace_append hprefix tailTrace_6438521
  have hstable : (prefixWord ++ tailWord_6438521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438521).length < 2 ^ (prefixWord ++ tailWord_6438521).sum := by decide
  have hdescent : baseEnd_6438521 < baseStart_6438521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438578 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_6438578 : Nat := 118140960795 + 6438578 * 2 ^ 59
def prefixEnd_6438578 : Nat := 4983230072969 + 3 ^ 40 * 6438578 * 2
def baseEnd_6438578 : Nat := 3306085245464215267664525

theorem tailTrace_6438578 : CollatzResearch.WordTrace tailWord_6438578 prefixEnd_6438578 3306085245464215267664525 := by
  unfold tailWord_6438578
  simp only [CollatzResearch.WordTrace]
  refine ⟨58708558017034750605541097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156556154712092668281442925 58708558017034750605541097)
  ·
    refine ⟨44031418512776062954155823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58708558017034750605541097 44031418512776062954155823)
    ·
      refine ⟨66047127769164094431233735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44031418512776062954155823 66047127769164094431233735)
      ·
        refine ⟨99070691653746141646850603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66047127769164094431233735 99070691653746141646850603)
        ·
          refine ⟨148606037480619212470275905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99070691653746141646850603 148606037480619212470275905)
          ·
            refine ⟨111454528110464409352706929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148606037480619212470275905 111454528110464409352706929)
            ·
              refine ⟨83590896082848307014530197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111454528110464409352706929 83590896082848307014530197)
              ·
                refine ⟨3918323253883514391306103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83590896082848307014530197 3918323253883514391306103)
                ·
                  refine ⟨5877484880825271586959155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918323253883514391306103 5877484880825271586959155)
                  ·
                    refine ⟨8816227321237907380438733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877484880825271586959155 8816227321237907380438733)
                    ·
                      refine ⟨3306085245464215267664525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816227321237907380438733 3306085245464215267664525)
                      ·
                        rfl

theorem cell23_6438578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_6438578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438578 prefixEnd_6438578 := by exact prefixLift 6438578
  have htrace : WordTrace (prefixWord ++ tailWord_6438578) baseStart_6438578 baseEnd_6438578 := by
    simpa [prefixWord, tailWord_6438578, baseEnd_6438578] using wordTrace_append hprefix tailTrace_6438578
  have hstable : (prefixWord ++ tailWord_6438578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438578).length < 2 ^ (prefixWord ++ tailWord_6438578).sum := by decide
  have hdescent : baseEnd_6438578 < baseStart_6438578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438605 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6438605 : Nat := 118140960795 + 6438605 * 2 ^ 59
def prefixEnd_6438605 : Nat := 4983230072969 + 3 ^ 40 * 6438605 * 2
def baseEnd_6438605 : Nat := 3306099109441886662026901

theorem tailTrace_6438605 : CollatzResearch.WordTrace tailWord_6438605 prefixEnd_6438605 3306099109441886662026901 := by
  unfold tailWord_6438605
  simp only [CollatzResearch.WordTrace]
  refine ⟨234835216839041186033397269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156556811226027457355598179 234835216839041186033397269)
  ·
    refine ⟨11007900789330055595315497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234835216839041186033397269 11007900789330055595315497)
    ·
      refine ⟨8255925591997541696486623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11007900789330055595315497 8255925591997541696486623)
      ·
        refine ⟨12383888387996312544729935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255925591997541696486623 12383888387996312544729935)
        ·
          refine ⟨18575832581994468817094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383888387996312544729935 18575832581994468817094903)
          ·
            refine ⟨27863748872991703225642355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18575832581994468817094903 27863748872991703225642355)
            ·
              refine ⟨41795623309487554838463533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27863748872991703225642355 41795623309487554838463533)
              ·
                refine ⟨15673358741057833064423825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41795623309487554838463533 15673358741057833064423825)
                ·
                  refine ⟨11755019055793374798317869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15673358741057833064423825 11755019055793374798317869)
                  ·
                    refine ⟨4408132145922515549369201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11755019055793374798317869 4408132145922515549369201)
                    ·
                      refine ⟨3306099109441886662026901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408132145922515549369201 3306099109441886662026901)
                      ·
                        rfl

theorem cell23_6438605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6438605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438605 prefixEnd_6438605 := by exact prefixLift 6438605
  have htrace : WordTrace (prefixWord ++ tailWord_6438605) baseStart_6438605 baseEnd_6438605 := by
    simpa [prefixWord, tailWord_6438605, baseEnd_6438605] using wordTrace_append hprefix tailTrace_6438605
  have hstable : (prefixWord ++ tailWord_6438605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438605).length < 2 ^ (prefixWord ++ tailWord_6438605).sum := by decide
  have hdescent : baseEnd_6438605 < baseStart_6438605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438618 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_6438618 : Nat := 118140960795 + 6438618 * 2 ^ 59
def prefixEnd_6438618 : Nat := 4983230072969 + 3 ^ 40 * 6438618 * 2
def baseEnd_6438618 : Nat := 3306105784690395111164341

theorem tailTrace_6438618 : CollatzResearch.WordTrace tailWord_6438618 prefixEnd_6438618 3306105784690395111164341 := by
  unfold tailWord_6438618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58708922746998522313405127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156557127325329392835747005 58708922746998522313405127)
  ·
    refine ⟨88063384120497783470107691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58708922746998522313405127 88063384120497783470107691)
    ·
      refine ⟨132095076180746675205161537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88063384120497783470107691 132095076180746675205161537)
      ·
        refine ⟨99071307135560006403871153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132095076180746675205161537 99071307135560006403871153)
        ·
          refine ⟨74303480351670004802903365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99071307135560006403871153 74303480351670004802903365)
          ·
            refine ⟨13931902565938125900544381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74303480351670004802903365 13931902565938125900544381)
            ·
              refine ⟨5224463462226797212704143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13931902565938125900544381 5224463462226797212704143)
              ·
                refine ⟨7836695193340195819056215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224463462226797212704143 7836695193340195819056215)
                ·
                  refine ⟨11755042790010293728584323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836695193340195819056215 11755042790010293728584323)
                  ·
                    refine ⟨17632564185015440592876485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11755042790010293728584323 17632564185015440592876485)
                    ·
                      refine ⟨3306105784690395111164341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17632564185015440592876485 3306105784690395111164341)
                      ·
                        rfl

theorem cell23_6438618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_6438618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438618 prefixEnd_6438618 := by exact prefixLift 6438618
  have htrace : WordTrace (prefixWord ++ tailWord_6438618) baseStart_6438618 baseEnd_6438618 := by
    simpa [prefixWord, tailWord_6438618, baseEnd_6438618] using wordTrace_append hprefix tailTrace_6438618
  have hstable : (prefixWord ++ tailWord_6438618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438618).length < 2 ^ (prefixWord ++ tailWord_6438618).sum := by decide
  have hdescent : baseEnd_6438618 < baseStart_6438618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438664 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6438664 : Nat := 118140960795 + 6438664 * 2 ^ 59
def prefixEnd_6438664 : Nat := 4983230072969 + 3 ^ 40 * 6438664 * 2
def baseEnd_6438664 : Nat := 3306129404800501931189129

theorem tailTrace_6438664 : CollatzResearch.WordTrace tailWord_6438664 prefixEnd_6438664 3306129404800501931189129 := by
  unfold tailWord_6438664
  simp only [CollatzResearch.WordTrace]
  refine ⟨117418684372913719554897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156558245830551626073196697 117418684372913719554897523)
  ·
    refine ⟨176128026559370579332346285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117418684372913719554897523 176128026559370579332346285)
    ·
      refine ⟨66048009959763967249629857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176128026559370579332346285 66048009959763967249629857)
      ·
        refine ⟨49536007469822975437222393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66048009959763967249629857 49536007469822975437222393)
        ·
          refine ⟨37152005602367231577916795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49536007469822975437222393 37152005602367231577916795)
          ·
            refine ⟨55728008403550847366875193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37152005602367231577916795 55728008403550847366875193)
            ·
              refine ⟨41796006302663135525156395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55728008403550847366875193 41796006302663135525156395)
              ·
                refine ⟨62694009453994703287734593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41796006302663135525156395 62694009453994703287734593)
                ·
                  refine ⟨47020507090496027465800945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62694009453994703287734593 47020507090496027465800945)
                  ·
                    refine ⟨35265380317872020599350709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47020507090496027465800945 35265380317872020599350709)
                    ·
                      refine ⟨3306129404800501931189129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35265380317872020599350709 3306129404800501931189129)
                      ·
                        rfl

theorem cell23_6438664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6438664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438664 prefixEnd_6438664 := by exact prefixLift 6438664
  have htrace : WordTrace (prefixWord ++ tailWord_6438664) baseStart_6438664 baseEnd_6438664 := by
    simpa [prefixWord, tailWord_6438664, baseEnd_6438664] using wordTrace_append hprefix tailTrace_6438664
  have hstable : (prefixWord ++ tailWord_6438664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438664).length < 2 ^ (prefixWord ++ tailWord_6438664).sum := by decide
  have hdescent : baseEnd_6438664 < baseStart_6438664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438669 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6438669 : Nat := 118140960795 + 6438669 * 2 ^ 59
def prefixEnd_6438669 : Nat := 4983230072969 + 3 ^ 40 * 6438669 * 2
def baseEnd_6438669 : Nat := 3306131972203774411626607

theorem tailTrace_6438669 : CollatzResearch.WordTrace tailWord_6438669 prefixEnd_6438669 3306131972203774411626607 := by
  unfold tailWord_6438669
  simp only [CollatzResearch.WordTrace]
  refine ⟨234837551110809324963727061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156558367407206216642484707 234837551110809324963727061)
  ·
    refine ⟨5504005104159593553837353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 234837551110809324963727061 5504005104159593553837353)
    ·
      refine ⟨4128003828119695165378015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5504005104159593553837353 4128003828119695165378015)
      ·
        refine ⟨6192005742179542748067023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128003828119695165378015 6192005742179542748067023)
        ·
          refine ⟨9288008613269314122100535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192005742179542748067023 9288008613269314122100535)
          ·
            refine ⟨13932012919903971183150803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288008613269314122100535 13932012919903971183150803)
            ·
              refine ⟨20898019379855956774726205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13932012919903971183150803 20898019379855956774726205)
              ·
                refine ⟨7836757267445983790522327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20898019379855956774726205 7836757267445983790522327)
                ·
                  refine ⟨11755135901168975685783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836757267445983790522327 11755135901168975685783491)
                  ·
                    refine ⟨17632703851753463528675237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11755135901168975685783491 17632703851753463528675237)
                    ·
                      refine ⟨3306131972203774411626607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17632703851753463528675237 3306131972203774411626607)
                      ·
                        rfl

theorem cell23_6438669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6438669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438669 prefixEnd_6438669 := by exact prefixLift 6438669
  have htrace : WordTrace (prefixWord ++ tailWord_6438669) baseStart_6438669 baseEnd_6438669 := by
    simpa [prefixWord, tailWord_6438669, baseEnd_6438669] using wordTrace_append hprefix tailTrace_6438669
  have hstable : (prefixWord ++ tailWord_6438669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438669).length < 2 ^ (prefixWord ++ tailWord_6438669).sum := by decide
  have hdescent : baseEnd_6438669 < baseStart_6438669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438684 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6438684 : Nat := 118140960795 + 6438684 * 2 ^ 59
def prefixEnd_6438684 : Nat := 4983230072969 + 3 ^ 40 * 6438684 * 2
def baseEnd_6438684 : Nat := 1102046558137863950979679

theorem tailTrace_6438684 : CollatzResearch.WordTrace tailWord_6438684 prefixEnd_6438684 1102046558137863950979679 := by
  unfold tailWord_6438684
  simp only [CollatzResearch.WordTrace]
  refine ⟨117419049102877491262761553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156558732137169988350348737 117419049102877491262761553)
  ·
    refine ⟨88064286827158118447071165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117419049102877491262761553 88064286827158118447071165)
    ·
      refine ⟨33024107560184294417651687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88064286827158118447071165 33024107560184294417651687)
      ·
        refine ⟨49536161340276441626477531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33024107560184294417651687 49536161340276441626477531)
        ·
          refine ⟨74304242010414662439716297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49536161340276441626477531 74304242010414662439716297)
          ·
            refine ⟨55728181507810996829787223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74304242010414662439716297 55728181507810996829787223)
            ·
              refine ⟨83592272261716495244680835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55728181507810996829787223 83592272261716495244680835)
              ·
                refine ⟨125388408392574742867021253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83592272261716495244680835 125388408392574742867021253)
                ·
                  refine ⟨23510326573607764287566485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125388408392574742867021253 23510326573607764287566485)
                  ·
                    refine ⟨1102046558137863950979679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23510326573607764287566485 1102046558137863950979679)
                    ·
                      rfl

theorem cell23_6438684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6438684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438684 prefixEnd_6438684 := by exact prefixLift 6438684
  have htrace : WordTrace (prefixWord ++ tailWord_6438684) baseStart_6438684 baseEnd_6438684 := by
    simpa [prefixWord, tailWord_6438684, baseEnd_6438684] using wordTrace_append hprefix tailTrace_6438684
  have hstable : (prefixWord ++ tailWord_6438684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438684).length < 2 ^ (prefixWord ++ tailWord_6438684).sum := by decide
  have hdescent : baseEnd_6438684 < baseStart_6438684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438691 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 4, 2]
def baseStart_6438691 : Nat := 118140960795 + 6438691 * 2 ^ 59
def prefixEnd_6438691 : Nat := 4983230072969 + 3 ^ 40 * 6438691 * 2
def baseEnd_6438691 : Nat := 3306143268778173325551505

theorem tailTrace_6438691 : CollatzResearch.WordTrace tailWord_6438691 prefixEnd_6438691 3306143268778173325551505 := by
  unfold tailWord_6438691
  simp only [CollatzResearch.WordTrace]
  refine ⟨234838353516729622721027927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156558902344486415147351951 234838353516729622721027927)
  ·
    refine ⟨352257530275094434081541891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234838353516729622721027927 352257530275094434081541891)
    ·
      refine ⟨528386295412641651122312837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352257530275094434081541891 528386295412641651122312837)
      ·
        refine ⟨99072430389870309585433657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528386295412641651122312837 99072430389870309585433657)
        ·
          refine ⟨74304322792402732189075243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99072430389870309585433657 74304322792402732189075243)
          ·
            refine ⟨111456484188604098283612865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74304322792402732189075243 111456484188604098283612865)
            ·
              refine ⟨83592363141453073712709649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111456484188604098283612865 83592363141453073712709649)
              ·
                refine ⟨62694272356089805284532237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83592363141453073712709649 62694272356089805284532237)
                ·
                  refine ⟨23510352133533676981699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62694272356089805284532237 23510352133533676981699589)
                  ·
                    refine ⟨4408191025037564434068673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23510352133533676981699589 4408191025037564434068673)
                    ·
                      refine ⟨3306143268778173325551505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408191025037564434068673 3306143268778173325551505)
                      ·
                        rfl

theorem cell23_6438691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_6438691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438691 prefixEnd_6438691 := by exact prefixLift 6438691
  have htrace : WordTrace (prefixWord ++ tailWord_6438691) baseStart_6438691 baseEnd_6438691 := by
    simpa [prefixWord, tailWord_6438691, baseEnd_6438691] using wordTrace_append hprefix tailTrace_6438691
  have hstable : (prefixWord ++ tailWord_6438691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438691).length < 2 ^ (prefixWord ++ tailWord_6438691).sum := by decide
  have hdescent : baseEnd_6438691 < baseStart_6438691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438702 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6438702 : Nat := 118140960795 + 6438702 * 2 ^ 59
def prefixEnd_6438702 : Nat := 4983230072969 + 3 ^ 40 * 6438702 * 2
def baseEnd_6438702 : Nat := 3306148917065372782513955

theorem tailTrace_6438702 : CollatzResearch.WordTrace tailWord_6438702 prefixEnd_6438702 3306148917065372782513955 := by
  unfold tailWord_6438702
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354844339961221449959795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156559169813126514399785573 29354844339961221449959795)
  ·
    refine ⟨44032266509941832174939693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29354844339961221449959795 44032266509941832174939693)
    ·
      refine ⟨16512099941228187065602385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44032266509941832174939693 16512099941228187065602385)
      ·
        refine ⟨12384074955921140299201789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16512099941228187065602385 12384074955921140299201789)
        ·
          refine ⟨4644028108470427612200671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12384074955921140299201789 4644028108470427612200671)
          ·
            refine ⟨6966042162705641418301007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644028108470427612200671 6966042162705641418301007)
            ·
              refine ⟨10449063244058462127451511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966042162705641418301007 10449063244058462127451511)
              ·
                refine ⟨15673594866087693191177267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449063244058462127451511 15673594866087693191177267)
                ·
                  refine ⟨23510392299131539786765901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15673594866087693191177267 23510392299131539786765901)
                  ·
                    refine ⟨8816397112174327420037213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23510392299131539786765901 8816397112174327420037213)
                    ·
                      refine ⟨3306148917065372782513955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816397112174327420037213 3306148917065372782513955)
                      ·
                        rfl

theorem cell23_6438702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6438702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438702 prefixEnd_6438702 := by exact prefixLift 6438702
  have htrace : WordTrace (prefixWord ++ tailWord_6438702) baseStart_6438702 baseEnd_6438702 := by
    simpa [prefixWord, tailWord_6438702, baseEnd_6438702] using wordTrace_append hprefix tailTrace_6438702
  have hstable : (prefixWord ++ tailWord_6438702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438702).length < 2 ^ (prefixWord ++ tailWord_6438702).sum := by decide
  have hdescent : baseEnd_6438702 < baseStart_6438702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438734 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6438734 : Nat := 118140960795 + 6438734 * 2 ^ 59
def prefixEnd_6438734 : Nat := 4983230072969 + 3 ^ 40 * 6438734 * 2
def baseEnd_6438734 : Nat := 3306165348446316657313807

theorem tailTrace_6438734 : CollatzResearch.WordTrace tailWord_6438734 prefixEnd_6438734 3306165348446316657313807 := by
  unfold tailWord_6438734
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354990231946730133105407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156559947903715894043228837 29354990231946730133105407)
  ·
    refine ⟨44032485347920095199658111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29354990231946730133105407 44032485347920095199658111)
    ·
      refine ⟨66048728021880142799487167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44032485347920095199658111 66048728021880142799487167)
      ·
        refine ⟨99073092032820214199230751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66048728021880142799487167 99073092032820214199230751)
        ·
          refine ⟨148609638049230321298846127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99073092032820214199230751 148609638049230321298846127)
          ·
            refine ⟨222914457073845481948269191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148609638049230321298846127 222914457073845481948269191)
            ·
              refine ⟨334371685610768222922403787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222914457073845481948269191 334371685610768222922403787)
              ·
                refine ⟨501557528416152334383605681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334371685610768222922403787 501557528416152334383605681)
                ·
                  refine ⟨376168146312114250787704261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501557528416152334383605681 376168146312114250787704261)
                  ·
                    refine ⟨70531527433521422022694549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376168146312114250787704261 70531527433521422022694549)
                    ·
                      refine ⟨3306165348446316657313807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70531527433521422022694549 3306165348446316657313807)
                      ·
                        rfl

theorem cell23_6438734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6438734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438734 prefixEnd_6438734 := by exact prefixLift 6438734
  have htrace : WordTrace (prefixWord ++ tailWord_6438734) baseStart_6438734 baseEnd_6438734 := by
    simpa [prefixWord, tailWord_6438734, baseEnd_6438734] using wordTrace_append hprefix tailTrace_6438734
  have hstable : (prefixWord ++ tailWord_6438734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438734).length < 2 ^ (prefixWord ++ tailWord_6438734).sum := by decide
  have hdescent : baseEnd_6438734 < baseStart_6438734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438815 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6438815 : Nat := 118140960795 + 6438815 * 2 ^ 59
def prefixEnd_6438815 : Nat := 4983230072969 + 3 ^ 40 * 6438815 * 2
def baseEnd_6438815 : Nat := 3306206940379330840400935

theorem tailTrace_6438815 : CollatzResearch.WordTrace tailWord_6438815 prefixEnd_6438815 3306206940379330840400935 := by
  unfold tailWord_6438815
  simp only [CollatzResearch.WordTrace]
  refine ⟨234842876168280391898541899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156561917445520261265694599 234842876168280391898541899)
  ·
    refine ⟨352264314252420587847812849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234842876168280391898541899 352264314252420587847812849)
    ·
      refine ⟨264198235689315440885859637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352264314252420587847812849 264198235689315440885859637)
      ·
        refine ⟨24768584595873322583049341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264198235689315440885859637 24768584595873322583049341)
        ·
          refine ⟨9288219223452495968643503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24768584595873322583049341 9288219223452495968643503)
          ·
            refine ⟨13932328835178743952965255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288219223452495968643503 13932328835178743952965255)
            ·
              refine ⟨20898493252768115929447883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13932328835178743952965255 20898493252768115929447883)
              ·
                refine ⟨31347739879152173894171825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20898493252768115929447883 31347739879152173894171825)
                ·
                  refine ⟨23510804909364130420628869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31347739879152173894171825 23510804909364130420628869)
                  ·
                    refine ⟨4408275920505774453867913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23510804909364130420628869 4408275920505774453867913)
                    ·
                      refine ⟨3306206940379330840400935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408275920505774453867913 3306206940379330840400935)
                      ·
                        rfl

theorem cell23_6438815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6438815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438815 prefixEnd_6438815 := by exact prefixLift 6438815
  have htrace : WordTrace (prefixWord ++ tailWord_6438815) baseStart_6438815 baseEnd_6438815 := by
    simpa [prefixWord, tailWord_6438815, baseEnd_6438815] using wordTrace_append hprefix tailTrace_6438815
  have hstable : (prefixWord ++ tailWord_6438815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438815).length < 2 ^ (prefixWord ++ tailWord_6438815).sum := by decide
  have hdescent : baseEnd_6438815 < baseStart_6438815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438848 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_6438848 : Nat := 118140960795 + 6438848 * 2 ^ 59
def prefixEnd_6438848 : Nat := 4983230072969 + 3 ^ 40 * 6438848 * 2
def baseEnd_6438848 : Nat := 3306223885240929211288283

theorem tailTrace_6438848 : CollatzResearch.WordTrace tailWord_6438848 prefixEnd_6438848 3306223885240929211288283 := by
  unfold tailWord_6438848
  simp only [CollatzResearch.WordTrace]
  refine ⟨117422039888580419267246599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156562719851440559022995465 117422039888580419267246599)
  ·
    refine ⟨176133059832870628900869899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117422039888580419267246599 176133059832870628900869899)
    ·
      refine ⟨264199589749305943351304849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176133059832870628900869899 264199589749305943351304849)
      ·
        refine ⟨198149692311979457513478637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264199589749305943351304849 198149692311979457513478637)
        ·
          refine ⟨74306134616992296567554489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198149692311979457513478637 74306134616992296567554489)
          ·
            refine ⟨55729600962744222425665867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74306134616992296567554489 55729600962744222425665867)
            ·
              refine ⟨83594401444116333638498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55729600962744222425665867 83594401444116333638498801)
              ·
                refine ⟨62695801083087250228874101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83594401444116333638498801 62695801083087250228874101)
                ·
                  refine ⟨5877731351539429708956947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62695801083087250228874101 5877731351539429708956947)
                  ·
                    refine ⟨8816597027309144563435421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877731351539429708956947 8816597027309144563435421)
                    ·
                      refine ⟨3306223885240929211288283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816597027309144563435421 3306223885240929211288283)
                      ·
                        rfl

theorem cell23_6438848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_6438848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438848 prefixEnd_6438848 := by exact prefixLift 6438848
  have htrace : WordTrace (prefixWord ++ tailWord_6438848) baseStart_6438848 baseEnd_6438848 := by
    simpa [prefixWord, tailWord_6438848, baseEnd_6438848] using wordTrace_append hprefix tailTrace_6438848
  have hstable : (prefixWord ++ tailWord_6438848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438848).length < 2 ^ (prefixWord ++ tailWord_6438848).sum := by decide
  have hdescent : baseEnd_6438848 < baseStart_6438848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438888 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6438888 : Nat := 118140960795 + 6438888 * 2 ^ 59
def prefixEnd_6438888 : Nat := 4983230072969 + 3 ^ 40 * 6438888 * 2
def baseEnd_6438888 : Nat := 3306244424467109054788099

theorem tailTrace_6438888 : CollatzResearch.WordTrace tailWord_6438888 prefixEnd_6438888 3306244424467109054788099 := by
  unfold tailWord_6438888
  simp only [CollatzResearch.WordTrace]
  refine ⟨117422769348507962682974659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156563692464677283577299545 117422769348507962682974659)
  ·
    refine ⟨176134154022761944024461989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117422769348507962682974659 176134154022761944024461989)
    ·
      refine ⟨33025153879267864504586623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176134154022761944024461989 33025153879267864504586623)
      ·
        refine ⟨49537730818901796756879935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33025153879267864504586623 49537730818901796756879935)
        ·
          refine ⟨74306596228352695135319903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49537730818901796756879935 74306596228352695135319903)
          ·
            refine ⟨111459894342529042702979855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74306596228352695135319903 111459894342529042702979855)
            ·
              refine ⟨167189841513793564054469783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111459894342529042702979855 167189841513793564054469783)
              ·
                refine ⟨250784762270690346081704675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167189841513793564054469783 250784762270690346081704675)
                ·
                  refine ⟨376177143406035519122557013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250784762270690346081704675 376177143406035519122557013)
                  ·
                    refine ⟨4408325899289478739717465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 376177143406035519122557013 4408325899289478739717465)
                    ·
                      refine ⟨3306244424467109054788099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408325899289478739717465 3306244424467109054788099)
                      ·
                        rfl

theorem cell23_6438888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6438888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438888 prefixEnd_6438888 := by exact prefixLift 6438888
  have htrace : WordTrace (prefixWord ++ tailWord_6438888) baseStart_6438888 baseEnd_6438888 := by
    simpa [prefixWord, tailWord_6438888, baseEnd_6438888] using wordTrace_append hprefix tailTrace_6438888
  have hstable : (prefixWord ++ tailWord_6438888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438888).length < 2 ^ (prefixWord ++ tailWord_6438888).sum := by decide
  have hdescent : baseEnd_6438888 < baseStart_6438888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438891 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3]
def baseStart_6438891 : Nat := 118140960795 + 6438891 * 2 ^ 59
def prefixEnd_6438891 : Nat := 4983230072969 + 3 ^ 40 * 6438891 * 2
def baseEnd_6438891 : Nat := 3306245964909072543050585

theorem tailTrace_6438891 : CollatzResearch.WordTrace tailWord_6438891 prefixEnd_6438891 3306245964909072543050585 := by
  unfold tailWord_6438891
  simp only [CollatzResearch.WordTrace]
  refine ⟨234845648116005056878308527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156563765410670037918872351 234845648116005056878308527)
  ·
    refine ⟨352268472174007585317462791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234845648116005056878308527 352268472174007585317462791)
    ·
      refine ⟨528402708261011377976194187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352268472174007585317462791 528402708261011377976194187)
      ·
        refine ⟨792604062391517066964291281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528402708261011377976194187 792604062391517066964291281)
        ·
          refine ⟨594453046793637800223218461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792604062391517066964291281 594453046793637800223218461)
          ·
            refine ⟨222919892547614175083706923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 594453046793637800223218461 222919892547614175083706923)
            ·
              refine ⟨334379838821421262625560385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222919892547614175083706923 334379838821421262625560385)
              ·
                refine ⟨250784879116065946969170289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334379838821421262625560385 250784879116065946969170289)
                ·
                  refine ⟨188088659337049460226877717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250784879116065946969170289 188088659337049460226877717)
                  ·
                    refine ⟨8816655906424193448134893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188088659337049460226877717 8816655906424193448134893)
                    ·
                      refine ⟨3306245964909072543050585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816655906424193448134893 3306245964909072543050585)
                      ·
                        rfl

theorem cell23_6438891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].length) (baseStart_6438891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438891 prefixEnd_6438891 := by exact prefixLift 6438891
  have htrace : WordTrace (prefixWord ++ tailWord_6438891) baseStart_6438891 baseEnd_6438891 := by
    simpa [prefixWord, tailWord_6438891, baseEnd_6438891] using wordTrace_append hprefix tailTrace_6438891
  have hstable : (prefixWord ++ tailWord_6438891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438891).length < 2 ^ (prefixWord ++ tailWord_6438891).sum := by decide
  have hdescent : baseEnd_6438891 < baseStart_6438891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438908 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_6438908 : Nat := 118140960795 + 6438908 * 2 ^ 59
def prefixEnd_6438908 : Nat := 4983230072969 + 3 ^ 40 * 6438908 * 2
def baseEnd_6438908 : Nat := 3306254694080198976538007

theorem tailTrace_6438908 : CollatzResearch.WordTrace tailWord_6438908 prefixEnd_6438908 3306254694080198976538007 := by
  unfold tailWord_6438908
  simp only [CollatzResearch.WordTrace]
  refine ⟨117423134078471734390838689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156564178771295645854451585 117423134078471734390838689)
  ·
    refine ⟨88067350558853800793129017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117423134078471734390838689 88067350558853800793129017)
    ·
      refine ⟨66050512919140350594846763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88067350558853800793129017 66050512919140350594846763)
      ·
        refine ⟨99075769378710525892270145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66050512919140350594846763 99075769378710525892270145)
        ·
          refine ⟨74306827034032894419202609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99075769378710525892270145 74306827034032894419202609)
          ·
            refine ⟨55730120275524670814401957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74306827034032894419202609 55730120275524670814401957)
            ·
              refine ⟨10449397551660875777700367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55730120275524670814401957 10449397551660875777700367)
              ·
                refine ⟨15674096327491313666550551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449397551660875777700367 15674096327491313666550551)
                ·
                  refine ⟨23511144491236970499825827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15674096327491313666550551 23511144491236970499825827)
                  ·
                    refine ⟨35266716736855455749738741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23511144491236970499825827 35266716736855455749738741)
                    ·
                      refine ⟨3306254694080198976538007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35266716736855455749738741 3306254694080198976538007)
                      ·
                        rfl

theorem cell23_6438908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_6438908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438908 prefixEnd_6438908 := by exact prefixLift 6438908
  have htrace : WordTrace (prefixWord ++ tailWord_6438908) baseStart_6438908 baseEnd_6438908 := by
    simpa [prefixWord, tailWord_6438908, baseEnd_6438908] using wordTrace_append hprefix tailTrace_6438908
  have hstable : (prefixWord ++ tailWord_6438908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438908).length < 2 ^ (prefixWord ++ tailWord_6438908).sum := by decide
  have hdescent : baseEnd_6438908 < baseStart_6438908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438916 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6438916 : Nat := 118140960795 + 6438916 * 2 ^ 59
def prefixEnd_6438916 : Nat := 4983230072969 + 3 ^ 40 * 6438916 * 2
def baseEnd_6438916 : Nat := 3306258801925434945237971

theorem tailTrace_6438916 : CollatzResearch.WordTrace tailWord_6438916 prefixEnd_6438916 3306258801925434945237971 := by
  unfold tailWord_6438916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117423279970457243073984301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156564373293942990765312401 117423279970457243073984301)
  ·
    refine ⟨44033729988921466152744113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117423279970457243073984301 44033729988921466152744113)
    ·
      refine ⟨33025297491691099614558085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44033729988921466152744113 33025297491691099614558085)
      ·
        refine ⟨6192243279692081177729641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33025297491691099614558085 6192243279692081177729641)
        ·
          refine ⟨4644182459769060883297231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6192243279692081177729641 4644182459769060883297231)
          ·
            refine ⟨6966273689653591324945847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644182459769060883297231 6966273689653591324945847)
            ·
              refine ⟨10449410534480386987418771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966273689653591324945847 10449410534480386987418771)
              ·
                refine ⟨15674115801720580481128157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449410534480386987418771 15674115801720580481128157)
                ·
                  refine ⟨5877793425645217680423059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15674115801720580481128157 5877793425645217680423059)
                  ·
                    refine ⟨8816690138467826520634589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877793425645217680423059 8816690138467826520634589)
                    ·
                      refine ⟨3306258801925434945237971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816690138467826520634589 3306258801925434945237971)
                      ·
                        rfl

theorem cell23_6438916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6438916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438916 prefixEnd_6438916 := by exact prefixLift 6438916
  have htrace : WordTrace (prefixWord ++ tailWord_6438916) baseStart_6438916 baseEnd_6438916 := by
    simpa [prefixWord, tailWord_6438916, baseEnd_6438916] using wordTrace_append hprefix tailTrace_6438916
  have hstable : (prefixWord ++ tailWord_6438916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438916).length < 2 ^ (prefixWord ++ tailWord_6438916).sum := by decide
  have hdescent : baseEnd_6438916 < baseStart_6438916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438952 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6438952 : Nat := 118140960795 + 6438952 * 2 ^ 59
def prefixEnd_6438952 : Nat := 4983230072969 + 3 ^ 40 * 6438952 * 2
def baseEnd_6438952 : Nat := 3306277287228996804387805

theorem tailTrace_6438952 : CollatzResearch.WordTrace tailWord_6438952 prefixEnd_6438952 3306277287228996804387805 := by
  unfold tailWord_6438952
  simp only [CollatzResearch.WordTrace]
  refine ⟨117423936484392032148139555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156565248645856042864186073 117423936484392032148139555)
  ·
    refine ⟨176135904726588048222209333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117423936484392032148139555 176135904726588048222209333)
    ·
      refine ⟨16512741068117629520832125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176135904726588048222209333 16512741068117629520832125)
      ·
        refine ⟨6192277900544111070312047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16512741068117629520832125 6192277900544111070312047)
        ·
          refine ⟨9288416850816166605468071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192277900544111070312047 9288416850816166605468071)
          ·
            refine ⟨13932625276224249908202107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288416850816166605468071 13932625276224249908202107)
            ·
              refine ⟨20898937914336374862303161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13932625276224249908202107 20898937914336374862303161)
              ·
                refine ⟨15674203435752281146727371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20898937914336374862303161 15674203435752281146727371)
                ·
                  refine ⟨23511305153628421720091057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15674203435752281146727371 23511305153628421720091057)
                  ·
                    refine ⟨17633478865221316290068293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23511305153628421720091057 17633478865221316290068293)
                    ·
                      refine ⟨3306277287228996804387805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17633478865221316290068293 3306277287228996804387805)
                      ·
                        rfl

theorem cell23_6438952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6438952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438952 prefixEnd_6438952 := by exact prefixLift 6438952
  have htrace : WordTrace (prefixWord ++ tailWord_6438952) baseStart_6438952 baseEnd_6438952 := by
    simpa [prefixWord, tailWord_6438952, baseEnd_6438952] using wordTrace_append hprefix tailTrace_6438952
  have hstable : (prefixWord ++ tailWord_6438952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438952).length < 2 ^ (prefixWord ++ tailWord_6438952).sum := by decide
  have hdescent : baseEnd_6438952 < baseStart_6438952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 6]
def baseStart_6438971 : Nat := 118140960795 + 6438971 * 2 ^ 59
def prefixEnd_6438971 : Nat := 4983230072969 + 3 ^ 40 * 6438971 * 2
def baseEnd_6438971 : Nat := 1102095681120477410016739

theorem tailTrace_6438971 : CollatzResearch.WordTrace tailWord_6438971 prefixEnd_6438971 1102095681120477410016739 := by
  unfold tailWord_6438971
  simp only [CollatzResearch.WordTrace]
  refine ⟨234848565955715230541220767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156565710637143487027480511 234848565955715230541220767)
  ·
    refine ⟨352272848933572845811831151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234848565955715230541220767 352272848933572845811831151)
    ·
      refine ⟨528409273400359268717746727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352272848933572845811831151 528409273400359268717746727)
      ·
        refine ⟨792613910100538903076620091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528409273400359268717746727 792613910100538903076620091)
        ·
          refine ⟨1188920865150808354614930137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792613910100538903076620091 1188920865150808354614930137)
          ·
            refine ⟨891690648863106265961197603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188920865150808354614930137 891690648863106265961197603)
            ·
              refine ⟨1337535973294659398941796405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891690648863106265961197603 1337535973294659398941796405)
              ·
                refine ⟨125393997496374318650793413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1337535973294659398941796405 125393997496374318650793413)
                ·
                  refine ⟨23511374530570184747023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125393997496374318650793413 23511374530570184747023765)
                  ·
                    refine ⟨1102095681120477410016739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23511374530570184747023765 1102095681120477410016739)
                    ·
                      rfl

theorem cell23_6438971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_6438971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438971 prefixEnd_6438971 := by exact prefixLift 6438971
  have htrace : WordTrace (prefixWord ++ tailWord_6438971) baseStart_6438971 baseEnd_6438971 := by
    simpa [prefixWord, tailWord_6438971, baseEnd_6438971] using wordTrace_append hprefix tailTrace_6438971
  have hstable : (prefixWord ++ tailWord_6438971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438971).length < 2 ^ (prefixWord ++ tailWord_6438971).sum := by decide
  have hdescent : baseEnd_6438971 < baseStart_6438971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438972 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_6438972 : Nat := 118140960795 + 6438972 * 2 ^ 59
def prefixEnd_6438972 : Nat := 4983230072969 + 3 ^ 40 * 6438972 * 2
def baseEnd_6438972 : Nat := 3306287556842086726137713

theorem tailTrace_6438972 : CollatzResearch.WordTrace tailWord_6438972 prefixEnd_6438972 3306287556842086726137713 := by
  unfold tailWord_6438972
  simp only [CollatzResearch.WordTrace]
  refine ⟨117424301214355803856003585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156565734952474405141338113 117424301214355803856003585)
  ·
    refine ⟨88068225910766852892002689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117424301214355803856003585 88068225910766852892002689)
    ·
      refine ⟨66051169433075139669002017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88068225910766852892002689 66051169433075139669002017)
      ·
        refine ⟨49538377074806354751751513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66051169433075139669002017 49538377074806354751751513)
        ·
          refine ⟨37153782806104766063813635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49538377074806354751751513 37153782806104766063813635)
          ·
            refine ⟨55730674209157149095720453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37153782806104766063813635 55730674209157149095720453)
            ·
              refine ⟨10449501414216965455447585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55730674209157149095720453 10449501414216965455447585)
              ·
                refine ⟨7837126060662724091585689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10449501414216965455447585 7837126060662724091585689)
                ·
                  refine ⟨5877844545497043068689267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837126060662724091585689 5877844545497043068689267)
                  ·
                    refine ⟨8816766818245564603033901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877844545497043068689267 8816766818245564603033901)
                    ·
                      refine ⟨3306287556842086726137713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816766818245564603033901 3306287556842086726137713)
                      ·
                        rfl

theorem cell23_6438972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_6438972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438972 prefixEnd_6438972 := by exact prefixLift 6438972
  have htrace : WordTrace (prefixWord ++ tailWord_6438972) baseStart_6438972 baseEnd_6438972 := by
    simpa [prefixWord, tailWord_6438972, baseEnd_6438972] using wordTrace_append hprefix tailTrace_6438972
  have hstable : (prefixWord ++ tailWord_6438972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438972).length < 2 ^ (prefixWord ++ tailWord_6438972).sum := by decide
  have hdescent : baseEnd_6438972 < baseStart_6438972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6438991 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_6438991 : Nat := 118140960795 + 6438991 * 2 ^ 59
def prefixEnd_6438991 : Nat := 4983230072969 + 3 ^ 40 * 6438991 * 2
def baseEnd_6438991 : Nat := 3306297312974522151800125

theorem tailTrace_6438991 : CollatzResearch.WordTrace tailWord_6438991 prefixEnd_6438991 3306297312974522151800125 := by
  unfold tailWord_6438991
  simp only [CollatzResearch.WordTrace]
  refine ⟨234849295415642773956948827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156566196943761849304632551 234849295415642773956948827)
  ·
    refine ⟨352273943123464160935423241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234849295415642773956948827 352273943123464160935423241)
    ·
      refine ⟨264205457342598120701567431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352273943123464160935423241 264205457342598120701567431)
      ·
        refine ⟨396308186013897181052351147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264205457342598120701567431 396308186013897181052351147)
        ·
          refine ⟨594462279020845771578526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396308186013897181052351147 594462279020845771578526721)
          ·
            refine ⟨445846709265634328683895041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594462279020845771578526721 445846709265634328683895041)
            ·
              refine ⟨334385031949225746512921281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445846709265634328683895041 334385031949225746512921281)
              ·
                refine ⟨250788773961919309884690961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334385031949225746512921281 250788773961919309884690961)
                ·
                  refine ⟨188091580471439482413518221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250788773961919309884690961 188091580471439482413518221)
                  ·
                    refine ⟨70534342676789805905069333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188091580471439482413518221 70534342676789805905069333)
                    ·
                      refine ⟨3306297312974522151800125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70534342676789805905069333 3306297312974522151800125)
                      ·
                        rfl

theorem cell23_6438991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_6438991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6438991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6438991 prefixEnd_6438991 := by exact prefixLift 6438991
  have htrace : WordTrace (prefixWord ++ tailWord_6438991) baseStart_6438991 baseEnd_6438991 := by
    simpa [prefixWord, tailWord_6438991, baseEnd_6438991] using wordTrace_append hprefix tailTrace_6438991
  have hstable : (prefixWord ++ tailWord_6438991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6438991).length < 2 ^ (prefixWord ++ tailWord_6438991).sum := by decide
  have hdescent : baseEnd_6438991 < baseStart_6438991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6438991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439045 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_6439045 : Nat := 118140960795 + 6439045 * 2 ^ 59
def prefixEnd_6439045 : Nat := 4983230072969 + 3 ^ 40 * 6439045 * 2
def baseEnd_6439045 : Nat := 3306325040929864940524877

theorem tailTrace_6439045 : CollatzResearch.WordTrace tailWord_6439045 prefixEnd_6439045 3306325040929864940524877 := by
  unfold tailWord_6439045
  simp only [CollatzResearch.WordTrace]
  refine ⟨234851264957447141179414589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156567509971631427452943059 234851264957447141179414589)
  ·
    refine ⟨88069224359042677942280471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234851264957447141179414589 88069224359042677942280471)
    ·
      refine ⟨132103836538564016913420707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88069224359042677942280471 132103836538564016913420707)
      ·
        refine ⟨198155754807846025370131061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132103836538564016913420707 198155754807846025370131061)
        ·
          refine ⟨18577102013235564878449787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198155754807846025370131061 18577102013235564878449787)
          ·
            refine ⟨27865653019853347317674681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18577102013235564878449787 27865653019853347317674681)
            ·
              refine ⟨20899239764890010488256011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27865653019853347317674681 20899239764890010488256011)
              ·
                refine ⟨31348859647335015732384017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20899239764890010488256011 31348859647335015732384017)
                ·
                  refine ⟨23511644735501261799288013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31348859647335015732384017 23511644735501261799288013)
                  ·
                    refine ⟨8816866775812973174733005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23511644735501261799288013 8816866775812973174733005)
                    ·
                      refine ⟨3306325040929864940524877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816866775812973174733005 3306325040929864940524877)
                      ·
                        rfl

theorem cell23_6439045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_6439045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439045 prefixEnd_6439045 := by exact prefixLift 6439045
  have htrace : WordTrace (prefixWord ++ tailWord_6439045) baseStart_6439045 baseEnd_6439045 := by
    simpa [prefixWord, tailWord_6439045, baseEnd_6439045] using wordTrace_append hprefix tailTrace_6439045
  have hstable : (prefixWord ++ tailWord_6439045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439045).length < 2 ^ (prefixWord ++ tailWord_6439045).sum := by decide
  have hdescent : baseEnd_6439045 < baseStart_6439045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439086 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_6439086 : Nat := 118140960795 + 6439086 * 2 ^ 59
def prefixEnd_6439086 : Nat := 4983230072969 + 3 ^ 40 * 6439086 * 2
def baseEnd_6439086 : Nat := 367371788181855475568021

theorem tailTrace_6439086 : CollatzResearch.WordTrace tailWord_6439086 prefixEnd_6439086 367371788181855475568021 := by
  unfold tailWord_6439086
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356595043787325647707139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156568506900199070121104741 29356595043787325647707139)
  ·
    refine ⟨44034892565680988471560709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29356595043787325647707139 44034892565680988471560709)
    ·
      refine ⟨8256542356065185338417633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44034892565680988471560709 8256542356065185338417633)
      ·
        refine ⟨6192406767048889003813225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8256542356065185338417633 6192406767048889003813225)
        ·
          refine ⟨4644305075286666752859919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6192406767048889003813225 4644305075286666752859919)
          ·
            refine ⟨6966457612930000129289879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644305075286666752859919 6966457612930000129289879)
            ·
              refine ⟨10449686419395000193934819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966457612930000129289879 10449686419395000193934819)
              ·
                refine ⟨15674529629092500290902229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449686419395000193934819 15674529629092500290902229)
                ·
                  refine ⟨367371788181855475568021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15674529629092500290902229 367371788181855475568021)
                  ·
                    rfl

theorem cell23_6439086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_6439086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439086 prefixEnd_6439086 := by exact prefixLift 6439086
  have htrace : WordTrace (prefixWord ++ tailWord_6439086) baseStart_6439086 baseEnd_6439086 := by
    simpa [prefixWord, tailWord_6439086, baseEnd_6439086] using wordTrace_append hprefix tailTrace_6439086
  have hstable : (prefixWord ++ tailWord_6439086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439086).length < 2 ^ (prefixWord ++ tailWord_6439086).sum := by decide
  have hdescent : baseEnd_6439086 < baseStart_6439086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439098 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_6439098 : Nat := 118140960795 + 6439098 * 2 ^ 59
def prefixEnd_6439098 : Nat := 4983230072969 + 3 ^ 40 * 6439098 * 2
def baseEnd_6439098 : Nat := 3306352255404553233162133

theorem tailTrace_6439098 : CollatzResearch.WordTrace tailWord_6439098 prefixEnd_6439098 3306352255404553233162133 := by
  unfold tailWord_6439098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58713299506563782807773487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156568798684170087487395965 58713299506563782807773487)
  ·
    refine ⟨88069949259845674211660231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58713299506563782807773487 88069949259845674211660231)
    ·
      refine ⟨132104923889768511317490347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88069949259845674211660231 132104923889768511317490347)
      ·
        refine ⟨198157385834652766976235521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132104923889768511317490347 198157385834652766976235521)
        ·
          refine ⟨148618039375989575232176641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198157385834652766976235521 148618039375989575232176641)
          ·
            refine ⟨111463529531992181424132481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148618039375989575232176641 111463529531992181424132481)
            ·
              refine ⟨83597647148994136068099361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111463529531992181424132481 83597647148994136068099361)
              ·
                refine ⟨62698235361745602051074521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83597647148994136068099361 62698235361745602051074521)
                ·
                  refine ⟨47023676521309201538305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62698235361745602051074521 47023676521309201538305891)
                  ·
                    refine ⟨70535514781963802307458837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47023676521309201538305891 70535514781963802307458837)
                    ·
                      refine ⟨3306352255404553233162133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70535514781963802307458837 3306352255404553233162133)
                      ·
                        rfl

theorem cell23_6439098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_6439098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439098 prefixEnd_6439098 := by exact prefixLift 6439098
  have htrace : WordTrace (prefixWord ++ tailWord_6439098) baseStart_6439098 baseEnd_6439098 := by
    simpa [prefixWord, tailWord_6439098, baseEnd_6439098] using wordTrace_append hprefix tailTrace_6439098
  have hstable : (prefixWord ++ tailWord_6439098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439098).length < 2 ^ (prefixWord ++ tailWord_6439098).sum := by decide
  have hdescent : baseEnd_6439098 < baseStart_6439098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439122 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6439122 : Nat := 118140960795 + 6439122 * 2 ^ 59
def prefixEnd_6439122 : Nat := 4983230072969 + 3 ^ 40 * 6439122 * 2
def baseEnd_6439122 : Nat := 3306364578940261139262023

theorem tailTrace_6439122 : CollatzResearch.WordTrace tailWord_6439122 prefixEnd_6439122 3306364578940261139262023 := by
  unfold tailWord_6439122
  simp only [CollatzResearch.WordTrace]
  refine ⟨58713518344542045832491905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156569382252112122219978413 58713518344542045832491905)
  ·
    refine ⟨44035138758406534374368929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58713518344542045832491905 44035138758406534374368929)
    ·
      refine ⟨33026354068804900780776697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44035138758406534374368929 33026354068804900780776697)
      ·
        refine ⟨24769765551603675585582523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33026354068804900780776697 24769765551603675585582523)
        ·
          refine ⟨37154648327405513378373785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24769765551603675585582523 37154648327405513378373785)
          ·
            refine ⟨27865986245554135033780339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37154648327405513378373785 27865986245554135033780339)
            ·
              refine ⟨41798979368331202550670509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27865986245554135033780339 41798979368331202550670509)
              ·
                refine ⟨15674617263124200956501441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41798979368331202550670509 15674617263124200956501441)
                ·
                  refine ⟨11755962947343150717376081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15674617263124200956501441 11755962947343150717376081)
                  ·
                    refine ⟨8816972210507363038032061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11755962947343150717376081 8816972210507363038032061)
                    ·
                      refine ⟨3306364578940261139262023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8816972210507363038032061 3306364578940261139262023)
                      ·
                        rfl

theorem cell23_6439122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6439122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439122 prefixEnd_6439122 := by exact prefixLift 6439122
  have htrace : WordTrace (prefixWord ++ tailWord_6439122) baseStart_6439122 baseEnd_6439122 := by
    simpa [prefixWord, tailWord_6439122, baseEnd_6439122] using wordTrace_append hprefix tailTrace_6439122
  have hstable : (prefixWord ++ tailWord_6439122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439122).length < 2 ^ (prefixWord ++ tailWord_6439122).sum := by decide
  have hdescent : baseEnd_6439122 < baseStart_6439122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439185 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_6439185 : Nat := 118140960795 + 6439185 * 2 ^ 59
def prefixEnd_6439185 : Nat := 4983230072969 + 3 ^ 40 * 6439185 * 2
def baseEnd_6439185 : Nat := 1102132309407164797591411

theorem tailTrace_6439185 : CollatzResearch.WordTrace tailWord_6439185 prefixEnd_6439185 1102132309407164797591411 := by
  unfold tailWord_6439185
  simp only [CollatzResearch.WordTrace]
  refine ⟨234856371176939945089511009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156570914117959963393007339 234856371176939945089511009)
  ·
    refine ⟨176142278382704958817133257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234856371176939945089511009 176142278382704958817133257)
    ·
      refine ⟨132106708787028719112849943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176142278382704958817133257 132106708787028719112849943)
      ·
        refine ⟨198160063180543078669274915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132106708787028719112849943 198160063180543078669274915)
        ·
          refine ⟨297240094770814618003912373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198160063180543078669274915 297240094770814618003912373)
          ·
            refine ⟨27866258884763870437866785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297240094770814618003912373 27866258884763870437866785)
            ·
              refine ⟨20899694163572902828400089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27866258884763870437866785 20899694163572902828400089)
              ·
                refine ⟨15674770622679677121300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20899694163572902828400089 15674770622679677121300067)
                ·
                  refine ⟨23512155934019515681950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15674770622679677121300067 23512155934019515681950101)
                  ·
                    refine ⟨1102132309407164797591411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23512155934019515681950101 1102132309407164797591411)
                    ·
                      rfl

theorem cell23_6439185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_6439185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439185 prefixEnd_6439185 := by exact prefixLift 6439185
  have htrace : WordTrace (prefixWord ++ tailWord_6439185) baseStart_6439185 baseEnd_6439185 := by
    simpa [prefixWord, tailWord_6439185, baseEnd_6439185] using wordTrace_append hprefix tailTrace_6439185
  have hstable : (prefixWord ++ tailWord_6439185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439185).length < 2 ^ (prefixWord ++ tailWord_6439185).sum := by decide
  have hdescent : baseEnd_6439185 < baseStart_6439185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439192 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6439192 : Nat := 118140960795 + 6439192 * 2 ^ 59
def prefixEnd_6439192 : Nat := 4983230072969 + 3 ^ 40 * 6439192 * 2
def baseEnd_6439192 : Nat := 3306400522586075865386701

theorem tailTrace_6439192 : CollatzResearch.WordTrace tailWord_6439192 prefixEnd_6439192 3306400522586075865386701 := by
  unfold tailWord_6439192
  simp only [CollatzResearch.WordTrace]
  refine ⟨117428313243957292642507915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156571084325276390190010553 117428313243957292642507915)
  ·
    refine ⟨176142469865935938963761873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117428313243957292642507915 176142469865935938963761873)
    ·
      refine ⟨132106852399451954222821405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176142469865935938963761873 132106852399451954222821405)
      ·
        refine ⟨49540069649794482833558027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132106852399451954222821405 49540069649794482833558027)
        ·
          refine ⟨74310104474691724250337041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49540069649794482833558027 74310104474691724250337041)
          ·
            refine ⟨55732578356018793187752781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74310104474691724250337041 55732578356018793187752781)
            ·
              refine ⟨20899716883507047445407293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55732578356018793187752781 20899716883507047445407293)
              ·
                refine ⟨7837393831315142792027735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20899716883507047445407293 7837393831315142792027735)
                ·
                  refine ⟨11756090746972714188041603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7837393831315142792027735 11756090746972714188041603)
                  ·
                    refine ⟨17634136120459071282062405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11756090746972714188041603 17634136120459071282062405)
                    ·
                      refine ⟨3306400522586075865386701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17634136120459071282062405 3306400522586075865386701)
                      ·
                        rfl

theorem cell23_6439192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6439192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439192 prefixEnd_6439192 := by exact prefixLift 6439192
  have htrace : WordTrace (prefixWord ++ tailWord_6439192) baseStart_6439192 baseEnd_6439192 := by
    simpa [prefixWord, tailWord_6439192, baseEnd_6439192] using wordTrace_append hprefix tailTrace_6439192
  have hstable : (prefixWord ++ tailWord_6439192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439192).length < 2 ^ (prefixWord ++ tailWord_6439192).sum := by decide
  have hdescent : baseEnd_6439192 < baseStart_6439192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439219 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 2, 4]
def baseStart_6439219 : Nat := 118140960795 + 6439219 * 2 ^ 59
def prefixEnd_6439219 : Nat := 4983230072969 + 3 ^ 40 * 6439219 * 2
def baseEnd_6439219 : Nat := 1102138128854582419916359

theorem tailTrace_6439219 : CollatzResearch.WordTrace tailWord_6439219 prefixEnd_6439219 1102138128854582419916359 := by
  unfold tailWord_6439219
  simp only [CollatzResearch.WordTrace]
  refine ⟨234857611258816768896248711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156571740839211179264165807 234857611258816768896248711)
  ·
    refine ⟨352286416888225153344373067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234857611258816768896248711 352286416888225153344373067)
    ·
      refine ⟨528429625332337730016559601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352286416888225153344373067 528429625332337730016559601)
      ·
        refine ⟨396322218999253297512419701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528429625332337730016559601 396322218999253297512419701)
        ·
          refine ⟨37155208031179996641789347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 396322218999253297512419701 37155208031179996641789347)
          ·
            refine ⟨55732812046769994962684021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37155208031179996641789347 55732812046769994962684021)
            ·
              refine ⟨5224951129384687027751627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55732812046769994962684021 5224951129384687027751627)
              ·
                refine ⟨7837426694077030541627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224951129384687027751627 7837426694077030541627441)
                ·
                  refine ⟨5878070020557772906220581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837426694077030541627441 5878070020557772906220581)
                  ·
                    refine ⟨1102138128854582419916359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5878070020557772906220581 1102138128854582419916359)
                    ·
                      rfl

theorem cell23_6439219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 4].length) (baseStart_6439219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439219 prefixEnd_6439219 := by exact prefixLift 6439219
  have htrace : WordTrace (prefixWord ++ tailWord_6439219) baseStart_6439219 baseEnd_6439219 := by
    simpa [prefixWord, tailWord_6439219, baseEnd_6439219] using wordTrace_append hprefix tailTrace_6439219
  have hstable : (prefixWord ++ tailWord_6439219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439219).length < 2 ^ (prefixWord ++ tailWord_6439219).sum := by decide
  have hdescent : baseEnd_6439219 < baseStart_6439219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439255 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_6439255 : Nat := 118140960795 + 6439255 * 2 ^ 59
def prefixEnd_6439255 : Nat := 4983230072969 + 3 ^ 40 * 6439255 * 2
def baseEnd_6439255 : Nat := 3306432871867309118898911

theorem tailTrace_6439255 : CollatzResearch.WordTrace tailWord_6439255 prefixEnd_6439255 3306432871867309118898911 := by
  unfold tailWord_6439255
  simp only [CollatzResearch.WordTrace]
  refine ⟨234858924286686347044559219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156572616191124231363039479 234858924286686347044559219)
  ·
    refine ⟨352288386430029520566838829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234858924286686347044559219 352288386430029520566838829)
    ·
      refine ⟨132108144911261070212564561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352288386430029520566838829 132108144911261070212564561)
      ·
        refine ⟨99081108683445802659423421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132108144911261070212564561 99081108683445802659423421)
        ·
          refine ⟨37155415756292175997283783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99081108683445802659423421 37155415756292175997283783)
          ·
            refine ⟨55733123634438263995925675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37155415756292175997283783 55733123634438263995925675)
            ·
              refine ⟨83599685451657395993888513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55733123634438263995925675 83599685451657395993888513)
              ·
                refine ⟨62699764088743046995416385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83599685451657395993888513 62699764088743046995416385)
                ·
                  refine ⟨47024823066557285246562289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62699764088743046995416385 47024823066557285246562289)
                  ·
                    refine ⟨35268617299917963934921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47024823066557285246562289 35268617299917963934921717)
                    ·
                      refine ⟨3306432871867309118898911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35268617299917963934921717 3306432871867309118898911)
                      ·
                        rfl

theorem cell23_6439255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_6439255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439255 prefixEnd_6439255 := by exact prefixLift 6439255
  have htrace : WordTrace (prefixWord ++ tailWord_6439255) baseStart_6439255 baseEnd_6439255 := by
    simpa [prefixWord, tailWord_6439255, baseEnd_6439255] using wordTrace_append hprefix tailTrace_6439255
  have hstable : (prefixWord ++ tailWord_6439255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439255).length < 2 ^ (prefixWord ++ tailWord_6439255).sum := by decide
  have hdescent : baseEnd_6439255 < baseStart_6439255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439260 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6439260 : Nat := 118140960795 + 6439260 * 2 ^ 59
def prefixEnd_6439260 : Nat := 4983230072969 + 3 ^ 40 * 6439260 * 2
def baseEnd_6439260 : Nat := 3306435439270581599336389

theorem tailTrace_6439260 : CollatzResearch.WordTrace tailWord_6439260 prefixEnd_6439260 3306435439270581599336389 := by
  unfold tailWord_6439260
  simp only [CollatzResearch.WordTrace]
  refine ⟨117429553325834116449245617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156572737767778821932327489 117429553325834116449245617)
  ·
    refine ⟨88072164994375587336934213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117429553325834116449245617 88072164994375587336934213)
    ·
      refine ⟨16513530936445422625675165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88072164994375587336934213 16513530936445422625675165)
      ·
        refine ⟨6192574101167033484628187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16513530936445422625675165 6192574101167033484628187)
        ·
          refine ⟨9288861151750550226942281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192574101167033484628187 9288861151750550226942281)
          ·
            refine ⟨6966645863812912670206711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9288861151750550226942281 6966645863812912670206711)
            ·
              refine ⟨10449968795719369005310067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966645863812912670206711 10449968795719369005310067)
              ·
                refine ⟨15674953193579053507965101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449968795719369005310067 15674953193579053507965101)
                ·
                  refine ⟨5878107447592145065486913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15674953193579053507965101 5878107447592145065486913)
                  ·
                    refine ⟨4408580585694108799115185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878107447592145065486913 4408580585694108799115185)
                    ·
                      refine ⟨3306435439270581599336389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408580585694108799115185 3306435439270581599336389)
                      ·
                        rfl

theorem cell23_6439260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6439260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439260 prefixEnd_6439260 := by exact prefixLift 6439260
  have htrace : WordTrace (prefixWord ++ tailWord_6439260) baseStart_6439260 baseEnd_6439260 := by
    simpa [prefixWord, tailWord_6439260, baseEnd_6439260] using wordTrace_append hprefix tailTrace_6439260
  have hstable : (prefixWord ++ tailWord_6439260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439260).length < 2 ^ (prefixWord ++ tailWord_6439260).sum := by decide
  have hdescent : baseEnd_6439260 < baseStart_6439260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439276 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_6439276 : Nat := 118140960795 + 6439276 * 2 ^ 59
def prefixEnd_6439276 : Nat := 4983230072969 + 3 ^ 40 * 6439276 * 2
def baseEnd_6439276 : Nat := 3306443654961053536736315

theorem tailTrace_6439276 : CollatzResearch.WordTrace tailWord_6439276 prefixEnd_6439276 3306443654961053536736315 := by
  unfold tailWord_6439276
  simp only [CollatzResearch.WordTrace]
  refine ⟨117429845109805133815536841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156573126813073511754049121 117429845109805133815536841)
  ·
    refine ⟨88072383832353850361652631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117429845109805133815536841 88072383832353850361652631)
    ·
      refine ⟨132108575748530775542478947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88072383832353850361652631 132108575748530775542478947)
      ·
        refine ⟨198162863622796163313718421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132108575748530775542478947 198162863622796163313718421)
        ·
          refine ⟨9288884232318570155330551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198162863622796163313718421 9288884232318570155330551)
          ·
            refine ⟨13933326348477855232995827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288884232318570155330551 13933326348477855232995827)
            ·
              refine ⟨20899989522716782849493741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933326348477855232995827 20899989522716782849493741)
              ·
                refine ⟨7837496071018793568560153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20899989522716782849493741 7837496071018793568560153)
                ·
                  refine ⟨5878122053264095176420115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837496071018793568560153 5878122053264095176420115)
                  ·
                    refine ⟨8817183079896142764630173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5878122053264095176420115 8817183079896142764630173)
                    ·
                      refine ⟨3306443654961053536736315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817183079896142764630173 3306443654961053536736315)
                      ·
                        rfl

theorem cell23_6439276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_6439276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439276 prefixEnd_6439276 := by exact prefixLift 6439276
  have htrace : WordTrace (prefixWord ++ tailWord_6439276) baseStart_6439276 baseEnd_6439276 := by
    simpa [prefixWord, tailWord_6439276, baseEnd_6439276] using wordTrace_append hprefix tailTrace_6439276
  have hstable : (prefixWord ++ tailWord_6439276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439276).length < 2 ^ (prefixWord ++ tailWord_6439276).sum := by decide
  have hdescent : baseEnd_6439276 < baseStart_6439276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439295 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_6439295 : Nat := 118140960795 + 6439295 * 2 ^ 59
def prefixEnd_6439295 : Nat := 4983230072969 + 3 ^ 40 * 6439295 * 2
def baseEnd_6439295 : Nat := 3306453411093488962398727

theorem tailTrace_6439295 : CollatzResearch.WordTrace tailWord_6439295 prefixEnd_6439295 3306453411093488962398727 := by
  unfold tailWord_6439295
  simp only [CollatzResearch.WordTrace]
  refine ⟨234860383206541433876015339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156573588804360955917343559 234860383206541433876015339)
  ·
    refine ⟨352290574809812150814023009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234860383206541433876015339 352290574809812150814023009)
    ·
      refine ⟨264217931107359113110517257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352290574809812150814023009 264217931107359113110517257)
      ·
        refine ⟨198163448330519334832887943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264217931107359113110517257 198163448330519334832887943)
        ·
          refine ⟨297245172495779002249331915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198163448330519334832887943 297245172495779002249331915)
          ·
            refine ⟨445867758743668503373997873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297245172495779002249331915 445867758743668503373997873)
            ·
              refine ⟨334400819057751377530498405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445867758743668503373997873 334400819057751377530498405)
              ·
                refine ⟨62700153573328383286968451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334400819057751377530498405 62700153573328383286968451)
                ·
                  refine ⟨94050230359992574930452677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62700153573328383286968451 94050230359992574930452677)
                  ·
                    refine ⟨17634418192498607799459877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94050230359992574930452677 17634418192498607799459877)
                    ·
                      refine ⟨3306453411093488962398727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17634418192498607799459877 3306453411093488962398727)
                      ·
                        rfl

theorem cell23_6439295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_6439295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439295 prefixEnd_6439295 := by exact prefixLift 6439295
  have htrace : WordTrace (prefixWord ++ tailWord_6439295) baseStart_6439295 baseEnd_6439295 := by
    simpa [prefixWord, tailWord_6439295, baseEnd_6439295] using wordTrace_append hprefix tailTrace_6439295
  have hstable : (prefixWord ++ tailWord_6439295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439295).length < 2 ^ (prefixWord ++ tailWord_6439295).sum := by decide
  have hdescent : baseEnd_6439295 < baseStart_6439295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439332 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_6439332 : Nat := 118140960795 + 6439332 * 2 ^ 59
def prefixEnd_6439332 : Nat := 4983230072969 + 3 ^ 40 * 6439332 * 2
def baseEnd_6439332 : Nat := 3306472409877705317636057

theorem tailTrace_6439332 : CollatzResearch.WordTrace tailWord_6439332 prefixEnd_6439332 3306472409877705317636057 := by
  unfold tailWord_6439332
  simp only [CollatzResearch.WordTrace]
  refine ⟨117430866353703694597556125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156574488471604926130074833 117430866353703694597556125)
  ·
    refine ⟨44036574882638885474083547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117430866353703694597556125 44036574882638885474083547)
    ·
      refine ⟨66054862323958328211125321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44036574882638885474083547 66054862323958328211125321)
      ·
        refine ⟨49541146742968746158343991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66054862323958328211125321 49541146742968746158343991)
        ·
          refine ⟨74311720114453119237515987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49541146742968746158343991 74311720114453119237515987)
          ·
            refine ⟨111467580171679678856273981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74311720114453119237515987 111467580171679678856273981)
            ·
              refine ⟨41800342564379879571102743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111467580171679678856273981 41800342564379879571102743)
              ·
                refine ⟨62700513846569819356654115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41800342564379879571102743 62700513846569819356654115)
                ·
                  refine ⟨94050770769854729034981173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62700513846569819356654115 94050770769854729034981173)
                  ·
                    refine ⟨8817259759673880847029485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94050770769854729034981173 8817259759673880847029485)
                    ·
                      refine ⟨3306472409877705317636057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817259759673880847029485 3306472409877705317636057)
                      ·
                        rfl

theorem cell23_6439332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_6439332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439332 prefixEnd_6439332 := by exact prefixLift 6439332
  have htrace : WordTrace (prefixWord ++ tailWord_6439332) baseStart_6439332 baseEnd_6439332 := by
    simpa [prefixWord, tailWord_6439332, baseEnd_6439332] using wordTrace_append hprefix tailTrace_6439332
  have hstable : (prefixWord ++ tailWord_6439332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439332).length < 2 ^ (prefixWord ++ tailWord_6439332).sum := by decide
  have hdescent : baseEnd_6439332 < baseStart_6439332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439356 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 5]
def baseStart_6439356 : Nat := 118140960795 + 6439356 * 2 ^ 59
def prefixEnd_6439356 : Nat := 4983230072969 + 3 ^ 40 * 6439356 * 2
def baseEnd_6439356 : Nat := 367387192601490358192883

theorem tailTrace_6439356 : CollatzResearch.WordTrace tailWord_6439356 prefixEnd_6439356 367387192601490358192883 := by
  unfold tailWord_6439356
  simp only [CollatzResearch.WordTrace]
  refine ⟨117431304029660220646992961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156575072039546960862657281 117431304029660220646992961)
  ·
    refine ⟨88073478022245165485244721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117431304029660220646992961 88073478022245165485244721)
    ·
      refine ⟨66055108516683874113933541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88073478022245165485244721 66055108516683874113933541)
      ·
        refine ⟨12385332846878226396362539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66055108516683874113933541 12385332846878226396362539)
        ·
          refine ⟨18577999270317339594543809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385332846878226396362539 18577999270317339594543809)
          ·
            refine ⟨13933499452738004695907857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18577999270317339594543809 13933499452738004695907857)
            ·
              refine ⟨10450124589553503521930893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13933499452738004695907857 10450124589553503521930893)
              ·
                refine ⟨3918796721082563820724085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10450124589553503521930893 3918796721082563820724085)
                ·
                  refine ⟨367387192601490358192883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3918796721082563820724085 367387192601490358192883)
                  ·
                    rfl

theorem cell23_6439356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_6439356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439356 prefixEnd_6439356 := by exact prefixLift 6439356
  have htrace : WordTrace (prefixWord ++ tailWord_6439356) baseStart_6439356 baseEnd_6439356 := by
    simpa [prefixWord, tailWord_6439356, baseEnd_6439356] using wordTrace_append hprefix tailTrace_6439356
  have hstable : (prefixWord ++ tailWord_6439356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439356).length < 2 ^ (prefixWord ++ tailWord_6439356).sum := by decide
  have hdescent : baseEnd_6439356 < baseStart_6439356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439365 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_6439365 : Nat := 118140960795 + 6439365 * 2 ^ 59
def prefixEnd_6439365 : Nat := 4983230072969 + 3 ^ 40 * 6439365 * 2
def baseEnd_6439365 : Nat := 1102163118246434562841135

theorem tailTrace_6439365 : CollatzResearch.WordTrace tailWord_6439365 prefixEnd_6439365 1102163118246434562841135 := by
  unfold tailWord_6439365
  simp only [CollatzResearch.WordTrace]
  refine ⟨234862936316287835831063549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156575290877525223887375699 234862936316287835831063549)
  ·
    refine ⟨88073601118607938436648831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234862936316287835831063549 88073601118607938436648831)
    ·
      refine ⟨132110401677911907654973247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88073601118607938436648831 132110401677911907654973247)
      ·
        refine ⟨198165602516867861482459871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132110401677911907654973247 198165602516867861482459871)
        ·
          refine ⟨297248403775301792223689807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198165602516867861482459871 297248403775301792223689807)
          ·
            refine ⟨445872605662952688335534711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297248403775301792223689807 445872605662952688335534711)
            ·
              refine ⟨668808908494429032503302067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445872605662952688335534711 668808908494429032503302067)
              ·
                refine ⟨1003213362741643548754953101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668808908494429032503302067 1003213362741643548754953101)
                ·
                  refine ⟨376205011028116330783107413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003213362741643548754953101 376205011028116330783107413)
                  ·
                    refine ⟨1102163118246434562841135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 376205011028116330783107413 1102163118246434562841135)
                    ·
                      rfl

theorem cell23_6439365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_6439365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439365 prefixEnd_6439365 := by exact prefixLift 6439365
  have htrace : WordTrace (prefixWord ++ tailWord_6439365) baseStart_6439365 baseEnd_6439365 := by
    simpa [prefixWord, tailWord_6439365, baseEnd_6439365] using wordTrace_append hprefix tailTrace_6439365
  have hstable : (prefixWord ++ tailWord_6439365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439365).length < 2 ^ (prefixWord ++ tailWord_6439365).sum := by decide
  have hdescent : baseEnd_6439365 < baseStart_6439365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439392 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_6439392 : Nat := 118140960795 + 6439392 * 2 ^ 59
def prefixEnd_6439392 : Nat := 4983230072969 + 3 ^ 40 * 6439392 * 2
def baseEnd_6439392 : Nat := 3306503218716975082885781

theorem tailTrace_6439392 : CollatzResearch.WordTrace tailWord_6439392 prefixEnd_6439392 3306503218716975082885781 := by
  unfold tailWord_6439392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117431960543595009721148215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156575947391460012961530953 117431960543595009721148215)
  ·
    refine ⟨176147940815392514581722323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117431960543595009721148215 176147940815392514581722323)
    ·
      refine ⟨264221911223088771872583485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176147940815392514581722323 264221911223088771872583485)
      ·
        refine ⟨99083216708658289452218807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264221911223088771872583485 99083216708658289452218807)
        ·
          refine ⟨148624825062987434178328211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99083216708658289452218807 148624825062987434178328211)
          ·
            refine ⟨222937237594481151267492317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148624825062987434178328211 222937237594481151267492317)
            ·
              refine ⟨83601464097930431725309619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222937237594481151267492317 83601464097930431725309619)
              ·
                refine ⟨125402196146895647587964429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83601464097930431725309619 125402196146895647587964429)
                ·
                  refine ⟨47025823555085867845486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125402196146895647587964429 47025823555085867845486661)
                  ·
                    refine ⟨8817341916578600221028749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47025823555085867845486661 8817341916578600221028749)
                    ·
                      refine ⟨3306503218716975082885781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817341916578600221028749 3306503218716975082885781)
                      ·
                        rfl

theorem cell23_6439392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_6439392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439392 prefixEnd_6439392 := by exact prefixLift 6439392
  have htrace : WordTrace (prefixWord ++ tailWord_6439392) baseStart_6439392 baseEnd_6439392 := by
    simpa [prefixWord, tailWord_6439392, baseEnd_6439392] using wordTrace_append hprefix tailTrace_6439392
  have hstable : (prefixWord ++ tailWord_6439392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439392).length < 2 ^ (prefixWord ++ tailWord_6439392).sum := by decide
  have hdescent : baseEnd_6439392 < baseStart_6439392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439399 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 3, 4]
def baseStart_6439399 : Nat := 118140960795 + 6439399 * 2 ^ 59
def prefixEnd_6439399 : Nat := 4983230072969 + 3 ^ 40 * 6439399 * 2
def baseEnd_6439399 : Nat := 1102168937693852185166083

theorem tailTrace_6439399 : CollatzResearch.WordTrace tailWord_6439399 prefixEnd_6439399 1102168937693852185166083 := by
  unfold tailWord_6439399
  simp only [CollatzResearch.WordTrace]
  refine ⟨234864176398164659637801251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156576117598776439758534167 234864176398164659637801251)
  ·
    refine ⟨352296264597246989456701877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234864176398164659637801251 352296264597246989456701877)
    ·
      refine ⟨33027774805991905261565801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352296264597246989456701877 33027774805991905261565801)
      ·
        refine ⟨24770831104493928946174351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33027774805991905261565801 24770831104493928946174351)
        ·
          refine ⟨37156246656740893419261527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24770831104493928946174351 37156246656740893419261527)
          ·
            refine ⟨55734369985111340128892291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37156246656740893419261527 55734369985111340128892291)
            ·
              refine ⟨83601554977667010193338437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55734369985111340128892291 83601554977667010193338437)
              ·
                refine ⟨15675291558312564411250957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83601554977667010193338437 15675291558312564411250957)
                ·
                  refine ⟨5878234334367211654219109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15675291558312564411250957 5878234334367211654219109)
                  ·
                    refine ⟨1102168937693852185166083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5878234334367211654219109 1102168937693852185166083)
                    ·
                      rfl

theorem cell23_6439399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_6439399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439399 prefixEnd_6439399 := by exact prefixLift 6439399
  have htrace : WordTrace (prefixWord ++ tailWord_6439399) baseStart_6439399 baseEnd_6439399 := by
    simpa [prefixWord, tailWord_6439399, baseEnd_6439399] using wordTrace_append hprefix tailTrace_6439399
  have hstable : (prefixWord ++ tailWord_6439399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439399).length < 2 ^ (prefixWord ++ tailWord_6439399).sum := by decide
  have hdescent : baseEnd_6439399 < baseStart_6439399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439409 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_6439409 : Nat := 118140960795 + 6439409 * 2 ^ 59
def prefixEnd_6439409 : Nat := 4983230072969 + 3 ^ 40 * 6439409 * 2
def baseEnd_6439409 : Nat := 3306511947888101516373203

theorem tailTrace_6439409 : CollatzResearch.WordTrace tailWord_6439409 prefixEnd_6439409 3306511947888101516373203 := by
  unfold tailWord_6439409
  simp only [CollatzResearch.WordTrace]
  refine ⟨234864541128128431345665281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156576360752085620897110187 234864541128128431345665281)
  ·
    refine ⟨176148405846096323509248961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234864541128128431345665281 176148405846096323509248961)
    ·
      refine ⟨132111304384572242631936721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176148405846096323509248961 132111304384572242631936721)
      ·
        refine ⟨99083478288429181973952541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132111304384572242631936721 99083478288429181973952541)
        ·
          refine ⟨37156304358160943240232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99083478288429181973952541 37156304358160943240232203)
          ·
            refine ⟨55734456537241414860348305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37156304358160943240232203 55734456537241414860348305)
            ·
              refine ⟨41800842402931061145261229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55734456537241414860348305 41800842402931061145261229)
              ·
                refine ⟨15675315901099147929472961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41800842402931061145261229 15675315901099147929472961)
                ·
                  refine ⟨11756486925824360947104721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15675315901099147929472961 11756486925824360947104721)
                  ·
                    refine ⟨8817365194368270710328541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11756486925824360947104721 8817365194368270710328541)
                    ·
                      refine ⟨3306511947888101516373203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817365194368270710328541 3306511947888101516373203)
                      ·
                        rfl

theorem cell23_6439409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_6439409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439409 prefixEnd_6439409 := by exact prefixLift 6439409
  have htrace : WordTrace (prefixWord ++ tailWord_6439409) baseStart_6439409 baseEnd_6439409 := by
    simpa [prefixWord, tailWord_6439409, baseEnd_6439409] using wordTrace_append hprefix tailTrace_6439409
  have hstable : (prefixWord ++ tailWord_6439409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439409).length < 2 ^ (prefixWord ++ tailWord_6439409).sum := by decide
  have hdescent : baseEnd_6439409 < baseStart_6439409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439459 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 3, 5]
def baseStart_6439459 : Nat := 118140960795 + 6439459 * 2 ^ 59
def prefixEnd_6439459 : Nat := 4983230072969 + 3 ^ 40 * 6439459 * 2
def baseEnd_6439459 : Nat := 1102179207306942106915991

theorem tailTrace_6439459 : CollatzResearch.WordTrace tailWord_6439459 prefixEnd_6439459 1102179207306942106915991 := by
  unfold tailWord_6439459
  simp only [CollatzResearch.WordTrace]
  refine ⟨234866364777947289884985431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156577576518631526589990287 234866364777947289884985431)
  ·
    refine ⟨352299547166920934827478147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234866364777947289884985431 352299547166920934827478147)
    ·
      refine ⟨528449320750381402241217221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352299547166920934827478147 528449320750381402241217221)
      ·
        refine ⟨99084247640696512920228229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528449320750381402241217221 99084247640696512920228229)
        ·
          refine ⟨18578296432630596172542793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99084247640696512920228229 18578296432630596172542793)
          ·
            refine ⟨13933722324472947129407095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18578296432630596172542793 13933722324472947129407095)
            ·
              refine ⟨20900583486709420694110643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933722324472947129407095 20900583486709420694110643)
              ·
                refine ⟨31350875230064131041165965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20900583486709420694110643 31350875230064131041165965)
                ·
                  refine ⟨11756578211274049140437237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31350875230064131041165965 11756578211274049140437237)
                  ·
                    refine ⟨1102179207306942106915991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11756578211274049140437237 1102179207306942106915991)
                    ·
                      rfl

theorem cell23_6439459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].length) (baseStart_6439459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439459 prefixEnd_6439459 := by exact prefixLift 6439459
  have htrace : WordTrace (prefixWord ++ tailWord_6439459) baseStart_6439459 baseEnd_6439459 := by
    simpa [prefixWord, tailWord_6439459, baseEnd_6439459] using wordTrace_append hprefix tailTrace_6439459
  have hstable : (prefixWord ++ tailWord_6439459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439459).length < 2 ^ (prefixWord ++ tailWord_6439459).sum := by decide
  have hdescent : baseEnd_6439459 < baseStart_6439459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439472 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_6439472 : Nat := 118140960795 + 6439472 * 2 ^ 59
def prefixEnd_6439472 : Nat := 4983230072969 + 3 ^ 40 * 6439472 * 2
def baseEnd_6439472 : Nat := 1102181432389778256628471

theorem tailTrace_6439472 : CollatzResearch.WordTrace tailWord_6439472 prefixEnd_6439472 1102181432389778256628471 := by
  unfold tailWord_6439472
  simp only [CollatzResearch.WordTrace]
  refine ⟨117433419463450096552604335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156577892617933462070139113 117433419463450096552604335)
  ·
    refine ⟨176150129195175144828906503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117433419463450096552604335 176150129195175144828906503)
    ·
      refine ⟨264225193792762717243359755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176150129195175144828906503 264225193792762717243359755)
      ·
        refine ⟨396337790689144075865039633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264225193792762717243359755 396337790689144075865039633)
        ·
          refine ⟨297253343016858056898779725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396337790689144075865039633 297253343016858056898779725)
          ·
            refine ⟨111470003631321771337042397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297253343016858056898779725 111470003631321771337042397)
            ·
              refine ⟨41801251361745664251390899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111470003631321771337042397 41801251361745664251390899)
              ·
                refine ⟨62701877042618496377086349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41801251361745664251390899 62701877042618496377086349)
                ·
                  refine ⟨23513203890981936141407381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62701877042618496377086349 23513203890981936141407381)
                  ·
                    refine ⟨1102181432389778256628471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23513203890981936141407381 1102181432389778256628471)
                    ·
                      rfl

theorem cell23_6439472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_6439472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439472 prefixEnd_6439472 := by exact prefixLift 6439472
  have htrace : WordTrace (prefixWord ++ tailWord_6439472) baseStart_6439472 baseEnd_6439472 := by
    simpa [prefixWord, tailWord_6439472, baseEnd_6439472] using wordTrace_append hprefix tailTrace_6439472
  have hstable : (prefixWord ++ tailWord_6439472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439472).length < 2 ^ (prefixWord ++ tailWord_6439472).sum := by decide
  have hdescent : baseEnd_6439472 < baseStart_6439472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_6439496 : Nat := 118140960795 + 6439496 * 2 ^ 59
def prefixEnd_6439496 : Nat := 4983230072969 + 3 ^ 40 * 6439496 * 2
def baseEnd_6439496 : Nat := 3306556620705042675985303

theorem tailTrace_6439496 : CollatzResearch.WordTrace tailWord_6439496 prefixEnd_6439496 3306556620705042675985303 := by
  unfold tailWord_6439496
  simp only [CollatzResearch.WordTrace]
  refine ⟨117433857139406622602041171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156578476185875496802721561 117433857139406622602041171)
  ·
    refine ⟨176150785709109933903061757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117433857139406622602041171 176150785709109933903061757)
    ·
      refine ⟨66056544640916225213648159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176150785709109933903061757 66056544640916225213648159)
      ·
        refine ⟨99084816961374337820472239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66056544640916225213648159 99084816961374337820472239)
        ·
          refine ⟨148627225442061506730708359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99084816961374337820472239 148627225442061506730708359)
          ·
            refine ⟨222940838163092260096062539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148627225442061506730708359 222940838163092260096062539)
            ·
              refine ⟨334411257244638390144093809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222940838163092260096062539 334411257244638390144093809)
              ·
                refine ⟨250808442933478792608070357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334411257244638390144093809 250808442933478792608070357)
                ·
                  refine ⟨5878322881253409201751649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250808442933478792608070357 5878322881253409201751649)
                  ·
                    refine ⟨4408742160940056901313737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878322881253409201751649 4408742160940056901313737)
                    ·
                      refine ⟨3306556620705042675985303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408742160940056901313737 3306556620705042675985303)
                      ·
                        rfl

theorem cell23_6439496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_6439496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439496 prefixEnd_6439496 := by exact prefixLift 6439496
  have htrace : WordTrace (prefixWord ++ tailWord_6439496) baseStart_6439496 baseEnd_6439496 := by
    simpa [prefixWord, tailWord_6439496, baseEnd_6439496] using wordTrace_append hprefix tailTrace_6439496
  have hstable : (prefixWord ++ tailWord_6439496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439496).length < 2 ^ (prefixWord ++ tailWord_6439496).sum := by decide
  have hdescent : baseEnd_6439496 < baseStart_6439496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439499 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3]
def baseStart_6439499 : Nat := 118140960795 + 6439499 * 2 ^ 59
def prefixEnd_6439499 : Nat := 4983230072969 + 3 ^ 40 * 6439499 * 2
def baseEnd_6439499 : Nat := 3306558161147006164247789

theorem tailTrace_6439499 : CollatzResearch.WordTrace tailWord_6439499 prefixEnd_6439499 3306558161147006164247789 := by
  unfold tailWord_6439499
  simp only [CollatzResearch.WordTrace]
  refine ⟨234867823697802376716441551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156578549131868251144294367 234867823697802376716441551)
  ·
    refine ⟨352301735546703565074662327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234867823697802376716441551 352301735546703565074662327)
    ·
      refine ⟨528452603320055347611993491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352301735546703565074662327 528452603320055347611993491)
      ·
        refine ⟨792678904980083021417990237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528452603320055347611993491 792678904980083021417990237)
        ·
          refine ⟨297254589367531133031746339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 792678904980083021417990237 297254589367531133031746339)
          ·
            refine ⟨445881884051296699547619509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297254589367531133031746339 445881884051296699547619509)
            ·
              refine ⟨41801426629809065582589329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 445881884051296699547619509 41801426629809065582589329)
              ·
                refine ⟨31351069972356799186941997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41801426629809065582589329 31351069972356799186941997)
                ·
                  refine ⟨11756651239633799695103249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31351069972356799186941997 11756651239633799695103249)
                  ·
                    refine ⟨8817488429725349771327437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11756651239633799695103249 8817488429725349771327437)
                    ·
                      refine ⟨3306558161147006164247789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817488429725349771327437 3306558161147006164247789)
                      ·
                        rfl

theorem cell23_6439499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].length) (baseStart_6439499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439499 prefixEnd_6439499 := by exact prefixLift 6439499
  have htrace : WordTrace (prefixWord ++ tailWord_6439499) baseStart_6439499 baseEnd_6439499 := by
    simpa [prefixWord, tailWord_6439499, baseEnd_6439499] using wordTrace_append hprefix tailTrace_6439499
  have hstable : (prefixWord ++ tailWord_6439499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439499).length < 2 ^ (prefixWord ++ tailWord_6439499).sum := by decide
  have hdescent : baseEnd_6439499 < baseStart_6439499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439506 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_6439506 : Nat := 118140960795 + 6439506 * 2 ^ 59
def prefixEnd_6439506 : Nat := 4983230072969 + 3 ^ 40 * 6439506 * 2
def baseEnd_6439506 : Nat := 1102187251837195878953419

theorem tailTrace_6439506 : CollatzResearch.WordTrace tailWord_6439506 prefixEnd_6439506 1102187251837195878953419 := by
  unfold tailWord_6439506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58717019752194254227986593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156578719339184677941297581 58717019752194254227986593)
  ·
    refine ⟨44037764814145690670989945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58717019752194254227986593 44037764814145690670989945)
    ·
      refine ⟨33028323610609268003242459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44037764814145690670989945 33028323610609268003242459)
      ·
        refine ⟨49542485415913902004863689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33028323610609268003242459 49542485415913902004863689)
        ·
          refine ⟨37156864061935426503647767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49542485415913902004863689 37156864061935426503647767)
          ·
            refine ⟨55735296092903139755471651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37156864061935426503647767 55735296092903139755471651)
            ·
              refine ⟨83602944139354709633207477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55735296092903139755471651 83602944139354709633207477)
              ·
                refine ⟨7837776013064504028113201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83602944139354709633207477 7837776013064504028113201)
                ·
                  refine ⟨5878332009798378021084901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7837776013064504028113201 5878332009798378021084901)
                  ·
                    refine ⟨1102187251837195878953419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5878332009798378021084901 1102187251837195878953419)
                    ·
                      rfl

theorem cell23_6439506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_6439506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439506 prefixEnd_6439506 := by exact prefixLift 6439506
  have htrace : WordTrace (prefixWord ++ tailWord_6439506) baseStart_6439506 baseEnd_6439506 := by
    simpa [prefixWord, tailWord_6439506, baseEnd_6439506] using wordTrace_append hprefix tailTrace_6439506
  have hstable : (prefixWord ++ tailWord_6439506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439506).length < 2 ^ (prefixWord ++ tailWord_6439506).sum := by decide
  have hdescent : baseEnd_6439506 < baseStart_6439506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439509 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6439509 : Nat := 118140960795 + 6439509 * 2 ^ 59
def prefixEnd_6439509 : Nat := 4983230072969 + 3 ^ 40 * 6439509 * 2
def baseEnd_6439509 : Nat := 3306563295953551125122743

theorem tailTrace_6439509 : CollatzResearch.WordTrace tailWord_6439509 prefixEnd_6439509 3306563295953551125122743 := by
  unfold tailWord_6439509
  simp only [CollatzResearch.WordTrace]
  refine ⟨234868188427766148424305581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156578792285177432282870387 234868188427766148424305581)
  ·
    refine ⟨88075570660412305659114593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234868188427766148424305581 88075570660412305659114593)
    ·
      refine ⟨66056677995309229244335945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88075570660412305659114593 66056677995309229244335945)
      ·
        refine ⟨49542508496481921933251959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66056677995309229244335945 49542508496481921933251959)
        ·
          refine ⟨74313762744722882899877939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49542508496481921933251959 74313762744722882899877939)
          ·
            refine ⟨111470644117084324349816909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74313762744722882899877939 111470644117084324349816909)
            ·
              refine ⟨41801491543906621631181341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111470644117084324349816909 41801491543906621631181341)
              ·
                refine ⟨15675559328964983111693003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41801491543906621631181341 15675559328964983111693003)
                ·
                  refine ⟨23513338993447474667539505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15675559328964983111693003 23513338993447474667539505)
                  ·
                    refine ⟨17635004245085606000654629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23513338993447474667539505 17635004245085606000654629)
                    ·
                      refine ⟨3306563295953551125122743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17635004245085606000654629 3306563295953551125122743)
                      ·
                        rfl

theorem cell23_6439509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6439509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439509 prefixEnd_6439509 := by exact prefixLift 6439509
  have htrace : WordTrace (prefixWord ++ tailWord_6439509) baseStart_6439509 baseEnd_6439509 := by
    simpa [prefixWord, tailWord_6439509, baseEnd_6439509] using wordTrace_append hprefix tailTrace_6439509
  have hstable : (prefixWord ++ tailWord_6439509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439509).length < 2 ^ (prefixWord ++ tailWord_6439509).sum := by decide
  have hdescent : baseEnd_6439509 < baseStart_6439509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439533 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6439533 : Nat := 118140960795 + 6439533 * 2 ^ 59
def prefixEnd_6439533 : Nat := 4983230072969 + 3 ^ 40 * 6439533 * 2
def baseEnd_6439533 : Nat := 3306575619489259031222633

theorem tailTrace_6439533 : CollatzResearch.WordTrace tailWord_6439533 prefixEnd_6439533 3306575619489259031222633 := by
  unfold tailWord_6439533
  simp only [CollatzResearch.WordTrace]
  refine ⟨234869063779679200523179253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156579375853119467015452835 234869063779679200523179253)
  ·
    refine ⟨22018974729344925049048055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234869063779679200523179253 22018974729344925049048055)
    ·
      refine ⟨33028462094017387573572083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22018974729344925049048055 33028462094017387573572083)
      ·
        refine ⟨49542693141026081360358125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33028462094017387573572083 49542693141026081360358125)
        ·
          refine ⟨18578509927884780510134297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49542693141026081360358125 18578509927884780510134297)
          ·
            refine ⟨13933882445913585382600723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18578509927884780510134297 13933882445913585382600723)
            ·
              refine ⟨20900823668870378073901085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933882445913585382600723 20900823668870378073901085)
              ·
                refine ⟨7837808875826391777712907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20900823668870378073901085 7837808875826391777712907)
                ·
                  refine ⟨11756713313739587666569361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7837808875826391777712907 11756713313739587666569361)
                  ·
                    refine ⟨8817534985304690749927021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11756713313739587666569361 8817534985304690749927021)
                    ·
                      refine ⟨3306575619489259031222633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817534985304690749927021 3306575619489259031222633)
                      ·
                        rfl

theorem cell23_6439533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6439533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439533 prefixEnd_6439533 := by exact prefixLift 6439533
  have htrace : WordTrace (prefixWord ++ tailWord_6439533) baseStart_6439533 baseEnd_6439533 := by
    simpa [prefixWord, tailWord_6439533, baseEnd_6439533] using wordTrace_append hprefix tailTrace_6439533
  have hstable : (prefixWord ++ tailWord_6439533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439533).length < 2 ^ (prefixWord ++ tailWord_6439533).sum := by decide
  have hdescent : baseEnd_6439533 < baseStart_6439533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439589 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_6439589 : Nat := 118140960795 + 6439589 * 2 ^ 59
def prefixEnd_6439589 : Nat := 4983230072969 + 3 ^ 40 * 6439589 * 2
def baseEnd_6439589 : Nat := 3306604374405910812122375

theorem tailTrace_6439589 : CollatzResearch.WordTrace tailWord_6439589 prefixEnd_6439589 3306604374405910812122375 := by
  unfold tailWord_6439589
  simp only [CollatzResearch.WordTrace]
  refine ⟨234871106267476322087217821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156580737511650881391478547 234871106267476322087217821)
  ·
    refine ⟨88076664850303620782706683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234871106267476322087217821 88076664850303620782706683)
    ·
      refine ⟨132114997275455431174060025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88076664850303620782706683 132114997275455431174060025)
      ·
        refine ⟨99086247956591573380545019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132114997275455431174060025 99086247956591573380545019)
        ·
          refine ⟨148629371934887360070817529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99086247956591573380545019 148629371934887360070817529)
          ·
            refine ⟨111472028951165520053113147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148629371934887360070817529 111472028951165520053113147)
            ·
              refine ⟨167208043426748280079669721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111472028951165520053113147 167208043426748280079669721)
              ·
                refine ⟨125406032570061210059752291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167208043426748280079669721 125406032570061210059752291)
                ·
                  refine ⟨188109048855091815089628437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125406032570061210059752291 188109048855091815089628437)
                  ·
                    refine ⟨8817611665082428832326333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188109048855091815089628437 8817611665082428832326333)
                    ·
                      refine ⟨3306604374405910812122375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8817611665082428832326333 3306604374405910812122375)
                      ·
                        rfl

theorem cell23_6439589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_6439589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439589 prefixEnd_6439589 := by exact prefixLift 6439589
  have htrace : WordTrace (prefixWord ++ tailWord_6439589) baseStart_6439589 baseEnd_6439589 := by
    simpa [prefixWord, tailWord_6439589, baseEnd_6439589] using wordTrace_append hprefix tailTrace_6439589
  have hstable : (prefixWord ++ tailWord_6439589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439589).length < 2 ^ (prefixWord ++ tailWord_6439589).sum := by decide
  have hdescent : baseEnd_6439589 < baseStart_6439589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439603 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 4, 2, 2]
def baseStart_6439603 : Nat := 118140960795 + 6439603 * 2 ^ 59
def prefixEnd_6439603 : Nat := 4983230072969 + 3 ^ 40 * 6439603 * 2
def baseEnd_6439603 : Nat := 3306611563135073757347311

theorem tailTrace_6439603 : CollatzResearch.WordTrace tailWord_6439603 prefixEnd_6439603 3306611563135073757347311 := by
  unfold tailWord_6439603
  simp only [CollatzResearch.WordTrace]
  refine ⟨234871616889425602478227463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156581077926283734985484975 234871616889425602478227463)
  ·
    refine ⟨352307425334138403717341195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234871616889425602478227463 352307425334138403717341195)
    ·
      refine ⟨528461138001207605576011793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352307425334138403717341195 528461138001207605576011793)
      ·
        refine ⟨396345853500905704182008845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528461138001207605576011793 396345853500905704182008845)
        ·
          refine ⟨148629695062839639068253317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396345853500905704182008845 148629695062839639068253317)
          ·
            refine ⟨27868067824282432325297497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148629695062839639068253317 27868067824282432325297497)
            ·
              refine ⟨20901050868211824243973123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27868067824282432325297497 20901050868211824243973123)
              ·
                refine ⟨31351576302317736365959685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20901050868211824243973123 31351576302317736365959685)
                ·
                  refine ⟨5878420556684575568617441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31351576302317736365959685 5878420556684575568617441)
                  ·
                    refine ⟨4408815417513431676463081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878420556684575568617441 4408815417513431676463081)
                    ·
                      refine ⟨3306611563135073757347311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408815417513431676463081 3306611563135073757347311)
                      ·
                        rfl

theorem cell23_6439603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2, 2].length) (baseStart_6439603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439603 prefixEnd_6439603 := by exact prefixLift 6439603
  have htrace : WordTrace (prefixWord ++ tailWord_6439603) baseStart_6439603 baseEnd_6439603 := by
    simpa [prefixWord, tailWord_6439603, baseEnd_6439603] using wordTrace_append hprefix tailTrace_6439603
  have hstable : (prefixWord ++ tailWord_6439603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439603).length < 2 ^ (prefixWord ++ tailWord_6439603).sum := by decide
  have hdescent : baseEnd_6439603 < baseStart_6439603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439659 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_6439659 : Nat := 118140960795 + 6439659 * 2 ^ 59
def prefixEnd_6439659 : Nat := 4983230072969 + 3 ^ 40 * 6439659 * 2
def baseEnd_6439659 : Nat := 3306640318051725538247053

theorem tailTrace_6439659 : CollatzResearch.WordTrace tailWord_6439659 prefixEnd_6439659 3306640318051725538247053 := by
  unfold tailWord_6439659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234873659377222724042266031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156582439584815149361510687 234873659377222724042266031)
  ·
    refine ⟨352310489065834086063399047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234873659377222724042266031 352310489065834086063399047)
    ·
      refine ⟨528465733598751129095098571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352310489065834086063399047 528465733598751129095098571)
      ·
        refine ⟨792698600398126693642647857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528465733598751129095098571 792698600398126693642647857)
        ·
          refine ⟨594523950298595020231985893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792698600398126693642647857 594523950298595020231985893)
          ·
            refine ⟨111473240680986566293497355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 594523950298595020231985893 111473240680986566293497355)
            ·
              refine ⟨167209861021479849440246033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111473240680986566293497355 167209861021479849440246033)
              ·
                refine ⟨125407395766109887080184525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167209861021479849440246033 125407395766109887080184525)
                ·
                  refine ⟨47027773412291207655069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125407395766109887080184525 47027773412291207655069197)
                  ·
                    refine ⟨17635415029609202870650949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47027773412291207655069197 17635415029609202870650949)
                    ·
                      refine ⟨3306640318051725538247053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17635415029609202870650949 3306640318051725538247053)
                      ·
                        rfl

theorem cell23_6439659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_6439659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439659 prefixEnd_6439659 := by exact prefixLift 6439659
  have htrace : WordTrace (prefixWord ++ tailWord_6439659) baseStart_6439659 baseEnd_6439659 := by
    simpa [prefixWord, tailWord_6439659, baseEnd_6439659] using wordTrace_append hprefix tailTrace_6439659
  have hstable : (prefixWord ++ tailWord_6439659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439659).length < 2 ^ (prefixWord ++ tailWord_6439659).sum := by decide
  have hdescent : baseEnd_6439659 < baseStart_6439659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439666 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6439666 : Nat := 118140960795 + 6439666 * 2 ^ 59
def prefixEnd_6439666 : Nat := 4983230072969 + 3 ^ 40 * 6439666 * 2
def baseEnd_6439666 : Nat := 3306643912416307010859521

theorem tailTrace_6439666 : CollatzResearch.WordTrace tailWord_6439666 prefixEnd_6439666 3306643912416307010859521 := by
  unfold tailWord_6439666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58718478672049341059442713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156582609792131576158513901 58718478672049341059442713)
  ·
    refine ⟨44038859004037005794582035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58718478672049341059442713 44038859004037005794582035)
    ·
      refine ⟨66058288506055508691873053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44038859004037005794582035 66058288506055508691873053)
      ·
        refine ⟨24771858189770815759452395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66058288506055508691873053 24771858189770815759452395)
        ·
          refine ⟨37157787284656223639178593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24771858189770815759452395 37157787284656223639178593)
          ·
            refine ⟨27868340463492167729383945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37157787284656223639178593 27868340463492167729383945)
            ·
              refine ⟨20901255347619125797037959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27868340463492167729383945 20901255347619125797037959)
              ·
                refine ⟨31351883021428688695556939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20901255347619125797037959 31351883021428688695556939)
                ·
                  refine ⟨47027824532143033043335409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31351883021428688695556939 47027824532143033043335409)
                  ·
                    refine ⟨35270868399107274782501557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47027824532143033043335409 35270868399107274782501557)
                    ·
                      refine ⟨3306643912416307010859521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35270868399107274782501557 3306643912416307010859521)
                      ·
                        rfl

theorem cell23_6439666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6439666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439666 prefixEnd_6439666 := by exact prefixLift 6439666
  have htrace : WordTrace (prefixWord ++ tailWord_6439666) baseStart_6439666 baseEnd_6439666 := by
    simpa [prefixWord, tailWord_6439666, baseEnd_6439666] using wordTrace_append hprefix tailTrace_6439666
  have hstable : (prefixWord ++ tailWord_6439666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439666).length < 2 ^ (prefixWord ++ tailWord_6439666).sum := by decide
  have hdescent : baseEnd_6439666 < baseStart_6439666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439699 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 8]
def baseStart_6439699 : Nat := 118140960795 + 6439699 * 2 ^ 59
def prefixEnd_6439699 : Nat := 4983230072969 + 3 ^ 40 * 6439699 * 2
def baseEnd_6439699 : Nat := 367406761919767264638541

theorem tailTrace_6439699 : CollatzResearch.WordTrace tailWord_6439699 prefixEnd_6439699 367406761919767264638541 := by
  unfold tailWord_6439699
  simp only [CollatzResearch.WordTrace]
  refine ⟨234875118297077810873722151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156583412198051873915814767 234875118297077810873722151)
  ·
    refine ⟨352312677445616716310583227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234875118297077810873722151 352312677445616716310583227)
    ·
      refine ⟨528469016168425074465874841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352312677445616716310583227 528469016168425074465874841)
      ·
        refine ⟨396351762126318805849406131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528469016168425074465874841 396351762126318805849406131)
        ·
          refine ⟨594527643189478208774109197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396351762126318805849406131 594527643189478208774109197)
          ·
            refine ⟨222947866196054328290290949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 594527643189478208774109197 222947866196054328290290949)
            ·
              refine ⟨41802724911760186554429553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222947866196054328290290949 41802724911760186554429553)
              ·
                refine ⟨31352043683820139915822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41802724911760186554429553 31352043683820139915822165)
                ·
                  refine ⟨367406761919767264638541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31352043683820139915822165 367406761919767264638541)
                  ·
                    rfl

theorem cell23_6439699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 8].length) (baseStart_6439699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439699 prefixEnd_6439699 := by exact prefixLift 6439699
  have htrace : WordTrace (prefixWord ++ tailWord_6439699) baseStart_6439699 baseEnd_6439699 := by
    simpa [prefixWord, tailWord_6439699, baseEnd_6439699] using wordTrace_append hprefix tailTrace_6439699
  have hstable : (prefixWord ++ tailWord_6439699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439699).length < 2 ^ (prefixWord ++ tailWord_6439699).sum := by decide
  have hdescent : baseEnd_6439699 < baseStart_6439699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439720 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6439720 : Nat := 118140960795 + 6439720 * 2 ^ 59
def prefixEnd_6439720 : Nat := 4983230072969 + 3 ^ 40 * 6439720 * 2
def baseEnd_6439720 : Nat := 1102223880123883266528091

theorem tailTrace_6439720 : CollatzResearch.WordTrace tailWord_6439720 prefixEnd_6439720 1102223880123883266528091 := by
  unfold tailWord_6439720
  simp only [CollatzResearch.WordTrace]
  refine ⟨117437942115000865730118307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156583922820001154306824409 117437942115000865730118307)
  ·
    refine ⟨176156913172501298595177461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117437942115000865730118307 176156913172501298595177461)
    ·
      refine ⟨16514710609921996743297887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176156913172501298595177461 16514710609921996743297887)
      ·
        refine ⟨24772065914882995114946831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16514710609921996743297887 24772065914882995114946831)
        ·
          refine ⟨37158098872324492672420247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24772065914882995114946831 37158098872324492672420247)
          ·
            refine ⟨55737148308486739008630371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37158098872324492672420247 55737148308486739008630371)
            ·
              refine ⟨83605722462730108512945557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55737148308486739008630371 83605722462730108512945557)
              ·
                refine ⟨3919018240440473836544323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83605722462730108512945557 3919018240440473836544323)
                ·
                  refine ⟨5878527360660710754816485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919018240440473836544323 5878527360660710754816485)
                  ·
                    refine ⟨1102223880123883266528091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5878527360660710754816485 1102223880123883266528091)
                    ·
                      rfl

theorem cell23_6439720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6439720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439720 prefixEnd_6439720 := by exact prefixLift 6439720
  have htrace : WordTrace (prefixWord ++ tailWord_6439720) baseStart_6439720 baseEnd_6439720 := by
    simpa [prefixWord, tailWord_6439720, baseEnd_6439720] using wordTrace_append hprefix tailTrace_6439720
  have hstable : (prefixWord ++ tailWord_6439720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439720).length < 2 ^ (prefixWord ++ tailWord_6439720).sum := by decide
  have hdescent : baseEnd_6439720 < baseStart_6439720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439753 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 5, 2]
def baseStart_6439753 : Nat := 118140960795 + 6439753 * 2 ^ 59
def prefixEnd_6439753 : Nat := 4983230072969 + 3 ^ 40 * 6439753 * 2
def baseEnd_6439753 : Nat := 3306688585233248170471621

theorem tailTrace_6439753 : CollatzResearch.WordTrace tailWord_6439753 prefixEnd_6439753 3306688585233248170471621 := by
  unfold tailWord_6439753
  simp only [CollatzResearch.WordTrace]
  refine ⟨234877087838882178096187913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156584725225921452064125275 234877087838882178096187913)
  ·
    refine ⟨176157815879161633572140935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234877087838882178096187913 176157815879161633572140935)
    ·
      refine ⟨264236723818742450358211403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176157815879161633572140935 264236723818742450358211403)
      ·
        refine ⟨396355085728113675537317105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264236723818742450358211403 396355085728113675537317105)
        ·
          refine ⟨297266314296085256652987829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396355085728113675537317105 297266314296085256652987829)
          ·
            refine ⟨27868716965257992811217609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297266314296085256652987829 27868716965257992811217609)
            ·
              refine ⟨20901537723943494608413207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27868716965257992811217609 20901537723943494608413207)
              ·
                refine ⟨31352306585915241912619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20901537723943494608413207 31352306585915241912619811)
                ·
                  refine ⟨47028459878872862868929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31352306585915241912619811 47028459878872862868929717)
                  ·
                    refine ⟨4408918113644330893962161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47028459878872862868929717 4408918113644330893962161)
                    ·
                      refine ⟨3306688585233248170471621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408918113644330893962161 3306688585233248170471621)
                      ·
                        rfl

theorem cell23_6439753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5, 2].length) (baseStart_6439753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439753 prefixEnd_6439753 := by exact prefixLift 6439753
  have htrace : WordTrace (prefixWord ++ tailWord_6439753) baseStart_6439753 baseEnd_6439753 := by
    simpa [prefixWord, tailWord_6439753, baseEnd_6439753] using wordTrace_append hprefix tailTrace_6439753
  have hstable : (prefixWord ++ tailWord_6439753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439753).length < 2 ^ (prefixWord ++ tailWord_6439753).sum := by decide
  have hdescent : baseEnd_6439753 < baseStart_6439753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439770 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_6439770 : Nat := 118140960795 + 6439770 * 2 ^ 59
def prefixEnd_6439770 : Nat := 4983230072969 + 3 ^ 40 * 6439770 * 2
def baseEnd_6439770 : Nat := 3306697314404374603959043

theorem tailTrace_6439770 : CollatzResearch.WordTrace tailWord_6439770 prefixEnd_6439770 3306697314404374603959043 := by
  unfold tailWord_6439770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58719426969955147499889191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156585138586547059999704509 58719426969955147499889191)
  ·
    refine ⟨88079140454932721249833787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58719426969955147499889191 88079140454932721249833787)
    ·
      refine ⟨132118710682399081874750681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88079140454932721249833787 132118710682399081874750681)
      ·
        refine ⟨99089033011799311406063011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132118710682399081874750681 99089033011799311406063011)
        ·
          refine ⟨148633549517698967109094517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99089033011799311406063011 148633549517698967109094517)
          ·
            refine ⟨13934395267284278166477611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148633549517698967109094517 13934395267284278166477611)
            ·
              refine ⟨20901592900926417249716417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13934395267284278166477611 20901592900926417249716417)
              ·
                refine ⟨15676194675694812937287313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20901592900926417249716417 15676194675694812937287313)
                ·
                  refine ⟨11757146006771109702965485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676194675694812937287313 11757146006771109702965485)
                  ·
                    refine ⟨4408929752539166138612057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11757146006771109702965485 4408929752539166138612057)
                    ·
                      refine ⟨3306697314404374603959043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4408929752539166138612057 3306697314404374603959043)
                      ·
                        rfl

theorem cell23_6439770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_6439770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439770 prefixEnd_6439770 := by exact prefixLift 6439770
  have htrace : WordTrace (prefixWord ++ tailWord_6439770) baseStart_6439770 baseEnd_6439770 := by
    simpa [prefixWord, tailWord_6439770, baseEnd_6439770] using wordTrace_append hprefix tailTrace_6439770
  have hstable : (prefixWord ++ tailWord_6439770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439770).length < 2 ^ (prefixWord ++ tailWord_6439770).sum := by decide
  have hdescent : baseEnd_6439770 < baseStart_6439770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439813 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_6439813 : Nat := 118140960795 + 6439813 * 2 ^ 59
def prefixEnd_6439813 : Nat := 4983230072969 + 3 ^ 40 * 6439813 * 2
def baseEnd_6439813 : Nat := 3306719394072517935721345

theorem tailTrace_6439813 : CollatzResearch.WordTrace tailWord_6439813 prefixEnd_6439813 3306719394072517935721345 := by
  unfold tailWord_6439813
  simp only [CollatzResearch.WordTrace]
  refine ⟨234879276218664808343372093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156586184145776538895581395 234879276218664808343372093)
  ·
    refine ⟨88079728581999303128764535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234879276218664808343372093 88079728581999303128764535)
    ·
      refine ⟨132119592872998954693146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88079728581999303128764535 132119592872998954693146803)
      ·
        refine ⟨198179389309498432039720205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132119592872998954693146803 198179389309498432039720205)
        ·
          refine ⟨74317270991061912014895077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198179389309498432039720205 74317270991061912014895077)
          ·
            refine ⟨13934488310824108502792827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74317270991061912014895077 13934488310824108502792827)
            ·
              refine ⟨20901732466236162754189241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13934488310824108502792827 20901732466236162754189241)
              ·
                refine ⟨15676299349677122065641931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20901732466236162754189241 15676299349677122065641931)
                ·
                  refine ⟨23514449024515683098462897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15676299349677122065641931 23514449024515683098462897)
                  ·
                    refine ⟨17635836768386762323847173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23514449024515683098462897 17635836768386762323847173)
                    ·
                      refine ⟨3306719394072517935721345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17635836768386762323847173 3306719394072517935721345)
                      ·
                        rfl

theorem cell23_6439813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_6439813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439813 prefixEnd_6439813 := by exact prefixLift 6439813
  have htrace : WordTrace (prefixWord ++ tailWord_6439813) baseStart_6439813 baseEnd_6439813 := by
    simpa [prefixWord, tailWord_6439813, baseEnd_6439813] using wordTrace_append hprefix tailTrace_6439813
  have hstable : (prefixWord ++ tailWord_6439813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439813).length < 2 ^ (prefixWord ++ tailWord_6439813).sum := by decide
  have hdescent : baseEnd_6439813 < baseStart_6439813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439866 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_6439866 : Nat := 118140960795 + 6439866 * 2 ^ 59
def prefixEnd_6439866 : Nat := 4983230072969 + 3 ^ 40 * 6439866 * 2
def baseEnd_6439866 : Nat := 1102248869515735409452867

theorem tailTrace_6439866 : CollatzResearch.WordTrace tailWord_6439866 prefixEnd_6439866 1102248869515735409452867 := by
  unfold tailWord_6439866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58720302321868199598762863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156587472858315198930034301 58720302321868199598762863)
  ·
    refine ⟨88080453482802299398144295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58720302321868199598762863 88080453482802299398144295)
    ·
      refine ⟨132120680224203449097216443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88080453482802299398144295 132120680224203449097216443)
      ·
        refine ⟨198181020336305173645824665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132120680224203449097216443 198181020336305173645824665)
        ·
          refine ⟨148635765252228880234368499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198181020336305173645824665 148635765252228880234368499)
          ·
            refine ⟨222953647878343320351552749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148635765252228880234368499 222953647878343320351552749)
            ·
              refine ⟨83607617954378745131832281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222953647878343320351552749 83607617954378745131832281)
              ·
                refine ⟨62705713465784058848874211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83607617954378745131832281 62705713465784058848874211)
                ·
                  refine ⟨94058570198676088273311317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62705713465784058848874211 94058570198676088273311317)
                  ·
                    refine ⟨1102248869515735409452867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94058570198676088273311317 1102248869515735409452867)
                    ·
                      rfl

theorem cell23_6439866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_6439866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439866 prefixEnd_6439866 := by exact prefixLift 6439866
  have htrace : WordTrace (prefixWord ++ tailWord_6439866) baseStart_6439866 baseEnd_6439866 := by
    simpa [prefixWord, tailWord_6439866, baseEnd_6439866] using wordTrace_append hprefix tailTrace_6439866
  have hstable : (prefixWord ++ tailWord_6439866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439866).length < 2 ^ (prefixWord ++ tailWord_6439866).sum := by decide
  have hdescent : baseEnd_6439866 < baseStart_6439866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439947 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 5]
def baseStart_6439947 : Nat := 118140960795 + 6439947 * 2 ^ 59
def prefixEnd_6439947 : Nat := 4983230072969 + 3 ^ 40 * 6439947 * 2
def baseEnd_6439947 : Nat := 367420911164468934605081

theorem tailTrace_6439947 : CollatzResearch.WordTrace tailWord_6439947 prefixEnd_6439947 367420911164468934605081 := by
  unfold tailWord_6439947
  simp only [CollatzResearch.WordTrace]
  refine ⟨234884163600179349228750095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156589442400119566152500063 234884163600179349228750095)
  ·
    refine ⟨352326245400269023843125143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234884163600179349228750095 352326245400269023843125143)
    ·
      refine ⟨528489368100403535764687715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352326245400269023843125143 528489368100403535764687715)
      ·
        refine ⟨792734052150605303647031573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528489368100403535764687715 792734052150605303647031573)
        ·
          refine ⟨37159408694559623608454605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 792734052150605303647031573 37159408694559623608454605)
          ·
            refine ⟨13934778260459858853170477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37159408694559623608454605 13934778260459858853170477)
            ·
              refine ⟨5225541847672447069938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13934778260459858853170477 5225541847672447069938929)
              ·
                refine ⟨3919156385754335302454197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225541847672447069938929 3919156385754335302454197)
                ·
                  refine ⟨367420911164468934605081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3919156385754335302454197 367420911164468934605081)
                  ·
                    rfl

theorem cell23_6439947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 5].length) (baseStart_6439947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439947 prefixEnd_6439947 := by exact prefixLift 6439947
  have htrace : WordTrace (prefixWord ++ tailWord_6439947) baseStart_6439947 baseEnd_6439947 := by
    simpa [prefixWord, tailWord_6439947, baseEnd_6439947] using wordTrace_append hprefix tailTrace_6439947
  have hstable : (prefixWord ++ tailWord_6439947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439947).length < 2 ^ (prefixWord ++ tailWord_6439947).sum := by decide
  have hdescent : baseEnd_6439947 < baseStart_6439947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439980 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_6439980 : Nat := 118140960795 + 6439980 * 2 ^ 59
def prefixEnd_6439980 : Nat := 4983230072969 + 3 ^ 40 * 6439980 * 2
def baseEnd_6439980 : Nat := 3306805145341818782333077

theorem tailTrace_6439980 : CollatzResearch.WordTrace tailWord_6439980 prefixEnd_6439980 3306805145341818782333077 := by
  unfold tailWord_6439980
  simp only [CollatzResearch.WordTrace]
  refine ⟨117442683604529897932350697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156590244806039863909800929 117442683604529897932350697)
  ·
    refine ⟨88082012703397423449263023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117442683604529897932350697 88082012703397423449263023)
    ·
      refine ⟨132123019055096135173894535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88082012703397423449263023 132123019055096135173894535)
      ·
        refine ⟨198184528582644202760841803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132123019055096135173894535 198184528582644202760841803)
        ·
          refine ⟨297276792873966304141262705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198184528582644202760841803 297276792873966304141262705)
          ·
            refine ⟨222957594655474728105947029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297276792873966304141262705 222957594655474728105947029)
            ·
              refine ⟨10451137249475377879966267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222957594655474728105947029 10451137249475377879966267)
              ·
                refine ⟨15676705874213066819949401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451137249475377879966267 15676705874213066819949401)
                ·
                  refine ⟨11757529405659800114962051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676705874213066819949401 11757529405659800114962051)
                  ·
                    refine ⟨17636294108489700172443077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11757529405659800114962051 17636294108489700172443077)
                    ·
                      refine ⟨3306805145341818782333077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17636294108489700172443077 3306805145341818782333077)
                      ·
                        rfl

theorem cell23_6439980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_6439980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439980 prefixEnd_6439980 := by exact prefixLift 6439980
  have htrace : WordTrace (prefixWord ++ tailWord_6439980) baseStart_6439980 baseEnd_6439980 := by
    simpa [prefixWord, tailWord_6439980, baseEnd_6439980] using wordTrace_append hprefix tailTrace_6439980
  have hstable : (prefixWord ++ tailWord_6439980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439980).length < 2 ^ (prefixWord ++ tailWord_6439980).sum := by decide
  have hdescent : baseEnd_6439980 < baseStart_6439980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6439983 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_6439983 : Nat := 118140960795 + 6439983 * 2 ^ 59
def prefixEnd_6439983 : Nat := 4983230072969 + 3 ^ 40 * 6439983 * 2
def baseEnd_6439983 : Nat := 3306806685783782270595563

theorem tailTrace_6439983 : CollatzResearch.WordTrace tailWord_6439983 prefixEnd_6439983 3306806685783782270595563 := by
  unfold tailWord_6439983
  simp only [CollatzResearch.WordTrace]
  refine ⟨234885476628048927377060603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156590317752032618251373735 234885476628048927377060603)
  ·
    refine ⟨352328214942073391065590905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234885476628048927377060603 352328214942073391065590905)
    ·
      refine ⟨264246161206555043299193179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352328214942073391065590905 264246161206555043299193179)
      ·
        refine ⟨396369241809832564948789769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264246161206555043299193179 396369241809832564948789769)
        ·
          refine ⟨297276931357374423711592327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396369241809832564948789769 297276931357374423711592327)
          ·
            refine ⟨445915397036061635567388491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297276931357374423711592327 445915397036061635567388491)
            ·
              refine ⟨668873095554092453351082737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445915397036061635567388491 668873095554092453351082737)
              ·
                refine ⟨501654821665569340013312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668873095554092453351082737 501654821665569340013312053)
                ·
                  refine ⟨47030139531147125626248005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501654821665569340013312053 47030139531147125626248005)
                  ·
                    refine ⟨8818151162090086054921501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47030139531147125626248005 8818151162090086054921501)
                    ·
                      refine ⟨3306806685783782270595563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818151162090086054921501 3306806685783782270595563)
                      ·
                        rfl

theorem cell23_6439983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_6439983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6439983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6439983 prefixEnd_6439983 := by exact prefixLift 6439983
  have htrace : WordTrace (prefixWord ++ tailWord_6439983) baseStart_6439983 baseEnd_6439983 := by
    simpa [prefixWord, tailWord_6439983, baseEnd_6439983] using wordTrace_append hprefix tailTrace_6439983
  have hstable : (prefixWord ++ tailWord_6439983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6439983).length < 2 ^ (prefixWord ++ tailWord_6439983).sum := by decide
  have hdescent : baseEnd_6439983 < baseStart_6439983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6439983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440000 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_6440000 : Nat := 118140960795 + 6440000 * 2 ^ 59
def prefixEnd_6440000 : Nat := 4983230072969 + 3 ^ 40 * 6440000 * 2
def baseEnd_6440000 : Nat := 3306815414954908704082985

theorem tailTrace_6440000 : CollatzResearch.WordTrace tailWord_6440000 prefixEnd_6440000 3306815414954908704082985 := by
  unfold tailWord_6440000
  simp only [CollatzResearch.WordTrace]
  refine ⟨117443048334493669640214727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156590731112658226186952969 117443048334493669640214727)
  ·
    refine ⟨176164572501740504460322091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117443048334493669640214727 176164572501740504460322091)
    ·
      refine ⟨264246858752610756690483137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176164572501740504460322091 264246858752610756690483137)
      ·
        refine ⟨198185144064458067517862353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264246858752610756690483137 198185144064458067517862353)
        ·
          refine ⟨148638858048343550638396765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198185144064458067517862353 148638858048343550638396765)
          ·
            refine ⟨55739571768128831489398787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148638858048343550638396765 55739571768128831489398787)
            ·
              refine ⟨83609357652193247234098181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55739571768128831489398787 83609357652193247234098181)
              ·
                refine ⟨15676754559786233856393409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83609357652193247234098181 15676754559786233856393409)
                ·
                  refine ⟨11757565919839675392295057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676754559786233856393409 11757565919839675392295057)
                  ·
                    refine ⟨8818174439879756544221293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11757565919839675392295057 8818174439879756544221293)
                    ·
                      refine ⟨3306815414954908704082985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818174439879756544221293 3306815414954908704082985)
                      ·
                        rfl

theorem cell23_6440000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_6440000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440000 prefixEnd_6440000 := by exact prefixLift 6440000
  have htrace : WordTrace (prefixWord ++ tailWord_6440000) baseStart_6440000 baseEnd_6440000 := by
    simpa [prefixWord, tailWord_6440000, baseEnd_6440000] using wordTrace_append hprefix tailTrace_6440000
  have hstable : (prefixWord ++ tailWord_6440000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440000).length < 2 ^ (prefixWord ++ tailWord_6440000).sum := by decide
  have hdescent : baseEnd_6440000 < baseStart_6440000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440020 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 6]
def baseStart_6440020 : Nat := 118140960795 + 6440020 * 2 ^ 59
def prefixEnd_6440020 : Nat := 4983230072969 + 3 ^ 40 * 6440020 * 2
def baseEnd_6440020 : Nat := 367425076063110958425877

theorem tailTrace_6440020 : CollatzResearch.WordTrace tailWord_6440020 prefixEnd_6440020 367425076063110958425877 := by
  unfold tailWord_6440020
  simp only [CollatzResearch.WordTrace]
  refine ⟨117443413064457441348078757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156591217419276588464105009 117443413064457441348078757)
  ·
    refine ⟨22020639949585770252764767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117443413064457441348078757 22020639949585770252764767)
    ·
      refine ⟨33030959924378655379147151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22020639949585770252764767 33030959924378655379147151)
      ·
        refine ⟨49546439886567983068720727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33030959924378655379147151 49546439886567983068720727)
        ·
          refine ⟨74319659829851974603081091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49546439886567983068720727 74319659829851974603081091)
          ·
            refine ⟨111479489744777961904621637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74319659829851974603081091 111479489744777961904621637)
            ·
              refine ⟨20902404327145867857116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111479489744777961904621637 20902404327145867857116557)
              ·
                refine ⟨7838401622679700446418709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20902404327145867857116557 7838401622679700446418709)
                ·
                  refine ⟨367425076063110958425877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7838401622679700446418709 367425076063110958425877)
                  ·
                    rfl

theorem cell23_6440020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_6440020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440020 prefixEnd_6440020 := by exact prefixLift 6440020
  have htrace : WordTrace (prefixWord ++ tailWord_6440020) baseStart_6440020 baseEnd_6440020 := by
    simpa [prefixWord, tailWord_6440020, baseEnd_6440020] using wordTrace_append hprefix tailTrace_6440020
  have hstable : (prefixWord ++ tailWord_6440020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440020).length < 2 ^ (prefixWord ++ tailWord_6440020).sum := by decide
  have hdescent : baseEnd_6440020 < baseStart_6440020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440034 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6440034 : Nat := 118140960795 + 6440034 * 2 ^ 59
def prefixEnd_6440034 : Nat := 4983230072969 + 3 ^ 40 * 6440034 * 2
def baseEnd_6440034 : Nat := 3306832873297161571057829

theorem tailTrace_6440034 : CollatzResearch.WordTrace tailWord_6440034 prefixEnd_6440034 3306832873297161571057829 := by
  unfold tailWord_6440034
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721834187716040771791789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156591557833909442058111437 58721834187716040771791789)
  ·
    refine ⟨22020687820393515289421921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58721834187716040771791789 22020687820393515289421921)
    ·
      refine ⟨16515515865295136467066441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22020687820393515289421921 16515515865295136467066441)
      ·
        refine ⟨12386636898971352350299831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16515515865295136467066441 12386636898971352350299831)
        ·
          refine ⟨18579955348457028525449747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12386636898971352350299831 18579955348457028525449747)
          ·
            refine ⟨27869933022685542788174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18579955348457028525449747 27869933022685542788174621)
            ·
              refine ⟨10451224883507078545565483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27869933022685542788174621 10451224883507078545565483)
              ·
                refine ⟨15676837325260617818348225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451224883507078545565483 15676837325260617818348225)
                ·
                  refine ⟨11757627993945463363761169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676837325260617818348225 11757627993945463363761169)
                  ·
                    refine ⟨8818220995459097522820877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11757627993945463363761169 8818220995459097522820877)
                    ·
                      refine ⟨3306832873297161571057829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818220995459097522820877 3306832873297161571057829)
                      ·
                        rfl

theorem cell23_6440034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6440034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440034 prefixEnd_6440034 := by exact prefixLift 6440034
  have htrace : WordTrace (prefixWord ++ tailWord_6440034) baseStart_6440034 baseEnd_6440034 := by
    simpa [prefixWord, tailWord_6440034, baseEnd_6440034] using wordTrace_append hprefix tailTrace_6440034
  have hstable : (prefixWord ++ tailWord_6440034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440034).length < 2 ^ (prefixWord ++ tailWord_6440034).sum := by decide
  have hdescent : baseEnd_6440034 < baseStart_6440034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440064 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 1, 1, 3]
def baseStart_6440064 : Nat := 118140960795 + 6440064 * 2 ^ 59
def prefixEnd_6440064 : Nat := 4983230072969 + 3 ^ 40 * 6440064 * 2
def baseEnd_6440064 : Nat := 3306848277716796453682691

theorem tailTrace_6440064 : CollatzResearch.WordTrace tailWord_6440064 prefixEnd_6440064 3306848277716796453682691 := by
  unfold tailWord_6440064
  simp only [CollatzResearch.WordTrace]
  refine ⟨117444215470377739105379623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156592287293836985473839497 117444215470377739105379623)
  ·
    refine ⟨176166323205566608658069435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117444215470377739105379623 176166323205566608658069435)
    ·
      refine ⟨264249484808349912987104153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176166323205566608658069435 264249484808349912987104153)
      ·
        refine ⟨198187113606262434740328115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264249484808349912987104153 198187113606262434740328115)
        ·
          refine ⟨297280670409393652110492173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198187113606262434740328115 297280670409393652110492173)
          ·
            refine ⟨111480251403522619541434565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297280670409393652110492173 111480251403522619541434565)
            ·
              refine ⟨20902547138160491164018981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111480251403522619541434565 20902547138160491164018981)
              ·
                refine ⟨3919227588405092093253559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20902547138160491164018981 3919227588405092093253559)
                ·
                  refine ⟨5878841382607638139880339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919227588405092093253559 5878841382607638139880339)
                  ·
                    refine ⟨8818262073911457209820509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5878841382607638139880339 8818262073911457209820509)
                    ·
                      refine ⟨3306848277716796453682691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818262073911457209820509 3306848277716796453682691)
                      ·
                        rfl

theorem cell23_6440064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_6440064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440064 prefixEnd_6440064 := by exact prefixLift 6440064
  have htrace : WordTrace (prefixWord ++ tailWord_6440064) baseStart_6440064 baseEnd_6440064 := by
    simpa [prefixWord, tailWord_6440064, baseEnd_6440064] using wordTrace_append hprefix tailTrace_6440064
  have hstable : (prefixWord ++ tailWord_6440064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440064).length < 2 ^ (prefixWord ++ tailWord_6440064).sum := by decide
  have hdescent : baseEnd_6440064 < baseStart_6440064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440087 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_6440087 : Nat := 118140960795 + 6440087 * 2 ^ 59
def prefixEnd_6440087 : Nat := 4983230072969 + 3 ^ 40 * 6440087 * 2
def baseEnd_6440087 : Nat := 3306860087771849863695085

theorem tailTrace_6440087 : CollatzResearch.WordTrace tailWord_6440087 prefixEnd_6440087 3306860087771849863695085 := by
  unfold tailWord_6440087
  simp only [CollatzResearch.WordTrace]
  refine ⟨234889269819672153138846515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156592846546448102092564343 234889269819672153138846515)
  ·
    refine ⟨352333904729508229708269773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234889269819672153138846515 352333904729508229708269773)
    ·
      refine ⟨132125214273565586140601165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352333904729508229708269773 132125214273565586140601165)
      ·
        refine ⟨49546955352587094802725437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132125214273565586140601165 49546955352587094802725437)
        ·
          refine ⟨18580108257220160551022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49546955352587094802725437 18580108257220160551022039)
          ·
            refine ⟨27870162385830240826533059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18580108257220160551022039 27870162385830240826533059)
            ·
              refine ⟨41805243578745361239799589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27870162385830240826533059 41805243578745361239799589)
              ·
                refine ⟨7838483171014755232462423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41805243578745361239799589 7838483171014755232462423)
                ·
                  refine ⟨11757724756522132848693635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838483171014755232462423 11757724756522132848693635)
                  ·
                    refine ⟨17636587134783199273040453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11757724756522132848693635 17636587134783199273040453)
                    ·
                      refine ⟨3306860087771849863695085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17636587134783199273040453 3306860087771849863695085)
                      ·
                        rfl

theorem cell23_6440087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_6440087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440087 prefixEnd_6440087 := by exact prefixLift 6440087
  have htrace : WordTrace (prefixWord ++ tailWord_6440087) baseStart_6440087 baseEnd_6440087 := by
    simpa [prefixWord, tailWord_6440087, baseEnd_6440087] using wordTrace_append hprefix tailTrace_6440087
  have hstable : (prefixWord ++ tailWord_6440087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440087).length < 2 ^ (prefixWord ++ tailWord_6440087).sum := by decide
  have hdescent : baseEnd_6440087 < baseStart_6440087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440120 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_6440120 : Nat := 118140960795 + 6440120 * 2 ^ 59
def prefixEnd_6440120 : Nat := 4983230072969 + 3 ^ 40 * 6440120 * 2
def baseEnd_6440120 : Nat := 3306877032633448234582433

theorem tailTrace_6440120 : CollatzResearch.WordTrace tailWord_6440120 prefixEnd_6440120 3306877032633448234582433 := by
  unfold tailWord_6440120
  simp only [CollatzResearch.WordTrace]
  refine ⟨117445236714276299887398907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156593648952368399849865209 117445236714276299887398907)
  ·
    refine ⟨176167855071414449831098361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117445236714276299887398907 176167855071414449831098361)
    ·
      refine ⟨132125891303560837373323771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176167855071414449831098361 132125891303560837373323771)
      ·
        refine ⟨198188836955341256059985657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132125891303560837373323771 198188836955341256059985657)
        ·
          refine ⟨148641627716505942044989243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198188836955341256059985657 148641627716505942044989243)
          ·
            refine ⟨222962441574758913067483865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148641627716505942044989243 222962441574758913067483865)
            ·
              refine ⟨167221831181069184800612899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222962441574758913067483865 167221831181069184800612899)
              ·
                refine ⟨250832746771603777200919349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167221831181069184800612899 250832746771603777200919349)
                ·
                  refine ⟨23515570009837854112586189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250832746771603777200919349 23515570009837854112586189)
                  ·
                    refine ⟨8818338753689195292219821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23515570009837854112586189 8818338753689195292219821)
                    ·
                      refine ⟨3306877032633448234582433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818338753689195292219821 3306877032633448234582433)
                      ·
                        rfl

theorem cell23_6440120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_6440120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440120 prefixEnd_6440120 := by exact prefixLift 6440120
  have htrace : WordTrace (prefixWord ++ tailWord_6440120) baseStart_6440120 baseEnd_6440120 := by
    simpa [prefixWord, tailWord_6440120, baseEnd_6440120] using wordTrace_append hprefix tailTrace_6440120
  have hstable : (prefixWord ++ tailWord_6440120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440120).length < 2 ^ (prefixWord ++ tailWord_6440120).sum := by decide
  have hdescent : baseEnd_6440120 < baseStart_6440120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440121 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6440121 : Nat := 118140960795 + 6440121 * 2 ^ 59
def prefixEnd_6440121 : Nat := 4983230072969 + 3 ^ 40 * 6440121 * 2
def baseEnd_6440121 : Nat := 3306877546114102730669929

theorem tailTrace_6440121 : CollatzResearch.WordTrace tailWord_6440121 prefixEnd_6440121 3306877546114102730669929 := by
  unfold tailWord_6440121
  simp only [CollatzResearch.WordTrace]
  refine ⟨234890509901548976945584217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156593673267699317963722811 234890509901548976945584217)
  ·
    refine ⟨176167882426161732709188163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234890509901548976945584217 176167882426161732709188163)
    ·
      refine ⟨264251823639242599063782245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176167882426161732709188163 264251823639242599063782245)
      ·
        refine ⟨49547216932357987324459171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264251823639242599063782245 49547216932357987324459171)
        ·
          refine ⟨74320825398536980986688757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49547216932357987324459171 74320825398536980986688757)
          ·
            refine ⟨6967577381112841967502071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74320825398536980986688757 6967577381112841967502071)
            ·
              refine ⟨10451366071669262951253107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967577381112841967502071 10451366071669262951253107)
              ·
                refine ⟨15677049107503894426879661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451366071669262951253107 15677049107503894426879661)
                ·
                  refine ⟨5878893415313960410079873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15677049107503894426879661 5878893415313960410079873)
                  ·
                    refine ⟨4409170061485470307559905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878893415313960410079873 4409170061485470307559905)
                    ·
                      refine ⟨3306877546114102730669929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409170061485470307559905 3306877546114102730669929)
                      ·
                        rfl

theorem cell23_6440121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6440121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440121 prefixEnd_6440121 := by exact prefixLift 6440121
  have htrace : WordTrace (prefixWord ++ tailWord_6440121) baseStart_6440121 baseEnd_6440121 := by
    simpa [prefixWord, tailWord_6440121, baseEnd_6440121] using wordTrace_append hprefix tailTrace_6440121
  have hstable : (prefixWord ++ tailWord_6440121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440121).length < 2 ^ (prefixWord ++ tailWord_6440121).sum := by decide
  have hdescent : baseEnd_6440121 < baseStart_6440121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440147 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 3, 3, 2]
def baseStart_6440147 : Nat := 118140960795 + 6440147 * 2 ^ 59
def prefixEnd_6440147 : Nat := 4983230072969 + 3 ^ 40 * 6440147 * 2
def baseEnd_6440147 : Nat := 3306890896611119628944809

theorem tailTrace_6440147 : CollatzResearch.WordTrace tailWord_6440147 prefixEnd_6440147 3306890896611119628944809 := by
  unfold tailWord_6440147
  simp only [CollatzResearch.WordTrace]
  refine ⟨234891458199454783386030695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156594305466303188924020463 234891458199454783386030695)
  ·
    refine ⟨352337187299182175079046043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234891458199454783386030695 352337187299182175079046043)
    ·
      refine ⟨528505780948773262618569065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352337187299182175079046043 528505780948773262618569065)
      ·
        refine ⟨396379335711579946963926799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528505780948773262618569065 396379335711579946963926799)
        ·
          refine ⟨594569003567369920445890199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396379335711579946963926799 594569003567369920445890199)
          ·
            refine ⟨891853505351054880668835299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594569003567369920445890199 891853505351054880668835299)
            ·
              refine ⟨1337780258026582321003252949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891853505351054880668835299 1337780258026582321003252949)
              ·
                refine ⟨31354224797498023148513741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1337780258026582321003252949 31354224797498023148513741)
                ·
                  refine ⟨11757834299061758680692653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31354224797498023148513741 11757834299061758680692653)
                  ·
                    refine ⟨4409187862148159505259745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11757834299061758680692653 4409187862148159505259745)
                    ·
                      refine ⟨3306890896611119628944809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409187862148159505259745 3306890896611119628944809)
                      ·
                        rfl

theorem cell23_6440147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3, 2].length) (baseStart_6440147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440147 prefixEnd_6440147 := by exact prefixLift 6440147
  have htrace : WordTrace (prefixWord ++ tailWord_6440147) baseStart_6440147 baseEnd_6440147 := by
    simpa [prefixWord, tailWord_6440147, baseEnd_6440147] using wordTrace_append hprefix tailTrace_6440147
  have hstable : (prefixWord ++ tailWord_6440147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440147).length < 2 ^ (prefixWord ++ tailWord_6440147).sum := by decide
  have hdescent : baseEnd_6440147 < baseStart_6440147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440164 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_6440164 : Nat := 118140960795 + 6440164 * 2 ^ 59
def prefixEnd_6440164 : Nat := 4983230072969 + 3 ^ 40 * 6440164 * 2
def baseEnd_6440164 : Nat := 3306899625782246062432231

theorem tailTrace_6440164 : CollatzResearch.WordTrace tailWord_6440164 prefixEnd_6440164 3306899625782246062432231 := by
  unfold tailWord_6440164
  simp only [CollatzResearch.WordTrace]
  refine ⟨117446039120196597644699773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156594718826928796859599697 117446039120196597644699773)
  ·
    refine ⟨44042264670073724116762415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117446039120196597644699773 44042264670073724116762415)
    ·
      refine ⟨66063397005110586175143623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44042264670073724116762415 66063397005110586175143623)
      ·
        refine ⟨99095095507665879262715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66063397005110586175143623 99095095507665879262715435)
        ·
          refine ⟨148642643261498818894073153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99095095507665879262715435 148642643261498818894073153)
          ·
            refine ⟨111481982446124114170554865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148642643261498818894073153 111481982446124114170554865)
            ·
              refine ⟨83611486834593085627916149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111481982446124114170554865 83611486834593085627916149)
              ·
                refine ⟨7838576890743101777617139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83611486834593085627916149 7838576890743101777617139)
                ·
                  refine ⟨11757865336114652666425709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838576890743101777617139 11757865336114652666425709)
                  ·
                    refine ⟨4409199501042994749909641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11757865336114652666425709 4409199501042994749909641)
                    ·
                      refine ⟨3306899625782246062432231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409199501042994749909641 3306899625782246062432231)
                      ·
                        rfl

theorem cell23_6440164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_6440164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440164 prefixEnd_6440164 := by exact prefixLift 6440164
  have htrace : WordTrace (prefixWord ++ tailWord_6440164) baseStart_6440164 baseEnd_6440164 := by
    simpa [prefixWord, tailWord_6440164, baseEnd_6440164] using wordTrace_append hprefix tailTrace_6440164
  have hstable : (prefixWord ++ tailWord_6440164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440164).length < 2 ^ (prefixWord ++ tailWord_6440164).sum := by decide
  have hdescent : baseEnd_6440164 < baseStart_6440164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_6440177 : Nat := 118140960795 + 6440177 * 2 ^ 59
def prefixEnd_6440177 : Nat := 4983230072969 + 3 ^ 40 * 6440177 * 2
def baseEnd_6440177 : Nat := 3306906301030754511569671

theorem tailTrace_6440177 : CollatzResearch.WordTrace tailWord_6440177 prefixEnd_6440177 3306906301030754511569671 := by
  unfold tailWord_6440177
  simp only [CollatzResearch.WordTrace]
  refine ⟨234892552389346098509622785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156595034926230732339748523 234892552389346098509622785)
  ·
    refine ⟨176169414292009573882217089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234892552389346098509622785 176169414292009573882217089)
    ·
      refine ⟨132127060719007180411662817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176169414292009573882217089 132127060719007180411662817)
      ·
        refine ⟨99095295539255385308747113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132127060719007180411662817 99095295539255385308747113)
        ·
          refine ⟨74321471654441538981560335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99095295539255385308747113 74321471654441538981560335)
          ·
            refine ⟨111482207481662308472340503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74321471654441538981560335 111482207481662308472340503)
            ·
              refine ⟨167223311222493462708510755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111482207481662308472340503 167223311222493462708510755)
              ·
                refine ⟨250834966833740194062766133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167223311222493462708510755 250834966833740194062766133)
                ·
                  refine ⟨23515778140663143193384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250834966833740194062766133 23515778140663143193384325)
                  ·
                    refine ⟨4409208401374339348759561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23515778140663143193384325 4409208401374339348759561)
                    ·
                      refine ⟨3306906301030754511569671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409208401374339348759561 3306906301030754511569671)
                      ·
                        rfl

theorem cell23_6440177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_6440177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440177 prefixEnd_6440177 := by exact prefixLift 6440177
  have htrace : WordTrace (prefixWord ++ tailWord_6440177) baseStart_6440177 baseEnd_6440177 := by
    simpa [prefixWord, tailWord_6440177, baseEnd_6440177] using wordTrace_append hprefix tailTrace_6440177
  have hstable : (prefixWord ++ tailWord_6440177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440177).length < 2 ^ (prefixWord ++ tailWord_6440177).sum := by decide
  have hdescent : baseEnd_6440177 < baseStart_6440177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440222 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6440222 : Nat := 118140960795 + 6440222 * 2 ^ 59
def prefixEnd_6440222 : Nat := 4983230072969 + 3 ^ 40 * 6440222 * 2
def baseEnd_6440222 : Nat := 3306929407660206835506965

theorem tailTrace_6440222 : CollatzResearch.WordTrace tailWord_6440222 prefixEnd_6440222 3306929407660206835506965 := by
  unfold tailWord_6440222
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361774209272883899376365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156596129116122047463340613 29361774209272883899376365)
  ·
    refine ⟨11010665328477331462266137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29361774209272883899376365 11010665328477331462266137)
    ·
      refine ⟨8257998996357998596699603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11010665328477331462266137 8257998996357998596699603)
      ·
        refine ⟨12386998494536997895049405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257998996357998596699603 12386998494536997895049405)
        ·
          refine ⟨4645124435451374210643527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12386998494536997895049405 4645124435451374210643527)
          ·
            refine ⟨6967686653177061315965291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645124435451374210643527 6967686653177061315965291)
            ·
              refine ⟨10451529979765591973947937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967686653177061315965291 10451529979765591973947937)
              ·
                refine ⟨7838647484824193980460953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10451529979765591973947937 7838647484824193980460953)
                ·
                  refine ⟨5878985613618145485345715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7838647484824193980460953 5878985613618145485345715)
                  ·
                    refine ⟨8818478420427218228018573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5878985613618145485345715 8818478420427218228018573)
                    ·
                      refine ⟨3306929407660206835506965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818478420427218228018573 3306929407660206835506965)
                      ·
                        rfl

theorem cell23_6440222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6440222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440222 prefixEnd_6440222 := by exact prefixLift 6440222
  have htrace : WordTrace (prefixWord ++ tailWord_6440222) baseStart_6440222 baseEnd_6440222 := by
    simpa [prefixWord, tailWord_6440222, baseEnd_6440222] using wordTrace_append hprefix tailTrace_6440222
  have hstable : (prefixWord ++ tailWord_6440222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440222).length < 2 ^ (prefixWord ++ tailWord_6440222).sum := by decide
  have hdescent : baseEnd_6440222 < baseStart_6440222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440227 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3]
def baseStart_6440227 : Nat := 118140960795 + 6440227 * 2 ^ 59
def prefixEnd_6440227 : Nat := 4983230072969 + 3 ^ 40 * 6440227 * 2
def baseEnd_6440227 : Nat := 3306931975063479315944441

theorem tailTrace_6440227 : CollatzResearch.WordTrace tailWord_6440227 prefixEnd_6440227 3306931975063479315944441 := by
  unfold tailWord_6440227
  simp only [CollatzResearch.WordTrace]
  refine ⟨234894376039164957048942935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156596250692776638032628623 234894376039164957048942935)
  ·
    refine ⟨352341564058747435573414403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234894376039164957048942935 352341564058747435573414403)
    ·
      refine ⟨528512346088121153360121605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352341564058747435573414403 528512346088121153360121605)
      ·
        refine ⟨99096064891522716255022801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528512346088121153360121605 99096064891522716255022801)
        ·
          refine ⟨74322048668642037191267101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99096064891522716255022801 74322048668642037191267101)
          ·
            refine ⟨27870768250740763946725163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74322048668642037191267101 27870768250740763946725163)
            ·
              refine ⟨41806152376111145920087745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27870768250740763946725163 41806152376111145920087745)
              ·
                refine ⟨31354614282083359440065809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41806152376111145920087745 31354614282083359440065809)
                ·
                  refine ⟨23515960711562519580049357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31354614282083359440065809 23515960711562519580049357)
                  ·
                    refine ⟨8818485266835944842518509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23515960711562519580049357 8818485266835944842518509)
                    ·
                      refine ⟨3306931975063479315944441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818485266835944842518509 3306931975063479315944441)
                      ·
                        rfl

theorem cell23_6440227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_6440227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440227 prefixEnd_6440227 := by exact prefixLift 6440227
  have htrace : WordTrace (prefixWord ++ tailWord_6440227) baseStart_6440227 baseEnd_6440227 := by
    simpa [prefixWord, tailWord_6440227, baseEnd_6440227] using wordTrace_append hprefix tailTrace_6440227
  have hstable : (prefixWord ++ tailWord_6440227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440227).length < 2 ^ (prefixWord ++ tailWord_6440227).sum := by decide
  have hdescent : baseEnd_6440227 < baseStart_6440227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440234 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_6440234 : Nat := 118140960795 + 6440234 * 2 ^ 59
def prefixEnd_6440234 : Nat := 4983230072969 + 3 ^ 40 * 6440234 * 2
def baseEnd_6440234 : Nat := 367437285492006754284101

theorem tailTrace_6440234 : CollatzResearch.WordTrace tailWord_6440234 prefixEnd_6440234 367437285492006754284101 := by
  unfold tailWord_6440234
  simp only [CollatzResearch.WordTrace]
  refine ⟨58723657837534899311111939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156596420900093064829631837 58723657837534899311111939)
  ·
    refine ⟨88085486756302348966667909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58723657837534899311111939 88085486756302348966667909)
    ·
      refine ⟨16516028766806690431250233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88085486756302348966667909 16516028766806690431250233)
      ·
        refine ⟨12387021575105017823437675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16516028766806690431250233 12387021575105017823437675)
        ·
          refine ⟨18580532362657526735156513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387021575105017823437675 18580532362657526735156513)
          ·
            refine ⟨13935399271993145051367385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18580532362657526735156513 13935399271993145051367385)
            ·
              refine ⟨10451549453994858788525539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13935399271993145051367385 10451549453994858788525539)
              ·
                refine ⟨15677324180992288182788309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451549453994858788525539 15677324180992288182788309)
                ·
                  refine ⟨367437285492006754284101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15677324180992288182788309 367437285492006754284101)
                  ·
                    rfl

theorem cell23_6440234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_6440234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440234 prefixEnd_6440234 := by exact prefixLift 6440234
  have htrace : WordTrace (prefixWord ++ tailWord_6440234) baseStart_6440234 baseEnd_6440234 := by
    simpa [prefixWord, tailWord_6440234, baseEnd_6440234] using wordTrace_append hprefix tailTrace_6440234
  have hstable : (prefixWord ++ tailWord_6440234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440234).length < 2 ^ (prefixWord ++ tailWord_6440234).sum := by decide
  have hdescent : baseEnd_6440234 < baseStart_6440234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440240 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_6440240 : Nat := 118140960795 + 6440240 * 2 ^ 59
def prefixEnd_6440240 : Nat := 4983230072969 + 3 ^ 40 * 6440240 * 2
def baseEnd_6440240 : Nat := 3306938650311987765081881

theorem tailTrace_6440240 : CollatzResearch.WordTrace tailWord_6440240 prefixEnd_6440240 3306938650311987765081881 := by
  unfold tailWord_6440240
  simp only [CollatzResearch.WordTrace]
  refine ⟨117447425094058930134583087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156596566792078573512777449 117447425094058930134583087)
  ·
    refine ⟨176171137641088395201874631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117447425094058930134583087 176171137641088395201874631)
    ·
      refine ⟨264256706461632592802811947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176171137641088395201874631 264256706461632592802811947)
      ·
        refine ⟨396385059692448889204217921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264256706461632592802811947 396385059692448889204217921)
        ·
          refine ⟨297288794769336666903163441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396385059692448889204217921 297288794769336666903163441)
          ·
            refine ⟨222966596077002500177372581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297288794769336666903163441 222966596077002500177372581)
            ·
              refine ⟨41806236764437968783257359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222966596077002500177372581 41806236764437968783257359)
              ·
                refine ⟨62709355146656953174886039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41806236764437968783257359 62709355146656953174886039)
                ·
                  refine ⟨94064032719985429762329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62709355146656953174886039 94064032719985429762329059)
                  ·
                    refine ⟨141096049079978144643493589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94064032719985429762329059 141096049079978144643493589)
                    ·
                      refine ⟨3306938650311987765081881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141096049079978144643493589 3306938650311987765081881)
                      ·
                        rfl

theorem cell23_6440240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_6440240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440240 prefixEnd_6440240 := by exact prefixLift 6440240
  have htrace : WordTrace (prefixWord ++ tailWord_6440240) baseStart_6440240 baseEnd_6440240 := by
    simpa [prefixWord, tailWord_6440240, baseEnd_6440240] using wordTrace_append hprefix tailTrace_6440240
  have hstable : (prefixWord ++ tailWord_6440240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440240).length < 2 ^ (prefixWord ++ tailWord_6440240).sum := by decide
  have hdescent : baseEnd_6440240 < baseStart_6440240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440244 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6440244 : Nat := 118140960795 + 6440244 * 2 ^ 59
def prefixEnd_6440244 : Nat := 4983230072969 + 3 ^ 40 * 6440244 * 2
def baseEnd_6440244 : Nat := 3306940704234605749431863

theorem tailTrace_6440244 : CollatzResearch.WordTrace tailWord_6440244 prefixEnd_6440244 3306940704234605749431863 := by
  unfold tailWord_6440244
  simp only [CollatzResearch.WordTrace]
  refine ⟨117447498040051684476155893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156596664053402245968207857 117447498040051684476155893)
  ·
    refine ⟨11010702941254845419639615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117447498040051684476155893 11010702941254845419639615)
    ·
      refine ⟨16516054411882268129459423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11010702941254845419639615 16516054411882268129459423)
      ·
        refine ⟨24774081617823402194189135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16516054411882268129459423 24774081617823402194189135)
        ·
          refine ⟨37161122426735103291283703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24774081617823402194189135 37161122426735103291283703)
          ·
            refine ⟨55741683640102654936925555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37161122426735103291283703 55741683640102654936925555)
            ·
              refine ⟨83612525460153982405388333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55741683640102654936925555 83612525460153982405388333)
              ·
                refine ⟨31354697047557743402020625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83612525460153982405388333 31354697047557743402020625)
                ·
                  refine ⟨23516022785668307551515469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31354697047557743402020625 23516022785668307551515469)
                  ·
                    refine ⟨8818508544625615331818301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23516022785668307551515469 8818508544625615331818301)
                    ·
                      refine ⟨3306940704234605749431863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8818508544625615331818301 3306940704234605749431863)
                      ·
                        rfl

theorem cell23_6440244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6440244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440244 prefixEnd_6440244 := by exact prefixLift 6440244
  have htrace : WordTrace (prefixWord ++ tailWord_6440244) baseStart_6440244 baseEnd_6440244 := by
    simpa [prefixWord, tailWord_6440244, baseEnd_6440244] using wordTrace_append hprefix tailTrace_6440244
  have hstable : (prefixWord ++ tailWord_6440244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440244).length < 2 ^ (prefixWord ++ tailWord_6440244).sum := by decide
  have hdescent : baseEnd_6440244 < baseStart_6440244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440285 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 7]
def baseStart_6440285 : Nat := 118140960795 + 6440285 * 2 ^ 59
def prefixEnd_6440285 : Nat := 4983230072969 + 3 ^ 40 * 6440285 * 2
def baseEnd_6440285 : Nat := 367440195215715565446575

theorem tailTrace_6440285 : CollatzResearch.WordTrace tailWord_6440285 prefixEnd_6440285 367440195215715565446575 := by
  unfold tailWord_6440285
  simp only [CollatzResearch.WordTrace]
  refine ⟨234896491472954832954554309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156597660981969888636369539 234896491472954832954554309)
  ·
    refine ⟨44043092151179031178978933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234896491472954832954554309 44043092151179031178978933)
    ·
      refine ⟨4129039889173034173029275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44043092151179031178978933 4129039889173034173029275)
      ·
        refine ⟨6193559833759551259543913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129039889173034173029275 6193559833759551259543913)
        ·
          refine ⟨4645169875319663444657935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193559833759551259543913 4645169875319663444657935)
          ·
            refine ⟨6967754812979495166986903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645169875319663444657935 6967754812979495166986903)
            ·
              refine ⟨10451632219469242750480355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967754812979495166986903 10451632219469242750480355)
              ·
                refine ⟨15677448329203864125720533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451632219469242750480355 15677448329203864125720533)
                ·
                  refine ⟨367440195215715565446575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15677448329203864125720533 367440195215715565446575)
                  ·
                    rfl

theorem cell23_6440285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_6440285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440285 prefixEnd_6440285 := by exact prefixLift 6440285
  have htrace : WordTrace (prefixWord ++ tailWord_6440285) baseStart_6440285 baseEnd_6440285 := by
    simpa [prefixWord, tailWord_6440285, baseEnd_6440285] using wordTrace_append hprefix tailTrace_6440285
  have hstable : (prefixWord ++ tailWord_6440285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440285).length < 2 ^ (prefixWord ++ tailWord_6440285).sum := by decide
  have hdescent : baseEnd_6440285 < baseStart_6440285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440354 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6440354 : Nat := 118140960795 + 6440354 * 2 ^ 59
def prefixEnd_6440354 : Nat := 4983230072969 + 3 ^ 40 * 6440354 * 2
def baseEnd_6440354 : Nat := 1102332395702200106352119

theorem tailTrace_6440354 : CollatzResearch.WordTrace tailWord_6440354 prefixEnd_6440354 1102332395702200106352119 := by
  unfold tailWord_6440354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58724752027426214434704029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156599338739803238492544077 58724752027426214434704029)
  ·
    refine ⟨22021782010284830413014011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58724752027426214434704029 22021782010284830413014011)
    ·
      refine ⟨33032673015427245619521017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22021782010284830413014011 33032673015427245619521017)
      ·
        refine ⟨24774504761570434214640763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33032673015427245619521017 24774504761570434214640763)
        ·
          refine ⟨37161757142355651321961145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24774504761570434214640763 37161757142355651321961145)
          ·
            refine ⟨27871317856766738491470859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37161757142355651321961145 27871317856766738491470859)
            ·
              refine ⟨41806976785150107737206289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27871317856766738491470859 41806976785150107737206289)
              ·
                refine ⟨31355232588862580802904717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41806976785150107737206289 31355232588862580802904717)
                ·
                  refine ⟨11758212220823467801089269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31355232588862580802904717 11758212220823467801089269)
                  ·
                    refine ⟨1102332395702200106352119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11758212220823467801089269 1102332395702200106352119)
                    ·
                      rfl

theorem cell23_6440354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6440354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440354 prefixEnd_6440354 := by exact prefixLift 6440354
  have htrace : WordTrace (prefixWord ++ tailWord_6440354) baseStart_6440354 baseEnd_6440354 := by
    simpa [prefixWord, tailWord_6440354, baseEnd_6440354] using wordTrace_append hprefix tailTrace_6440354
  have hstable : (prefixWord ++ tailWord_6440354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440354).length < 2 ^ (prefixWord ++ tailWord_6440354).sum := by decide
  have hdescent : baseEnd_6440354 < baseStart_6440354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440388 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6440388 : Nat := 118140960795 + 6440388 * 2 ^ 59
def prefixEnd_6440388 : Nat := 4983230072969 + 3 ^ 40 * 6440388 * 2
def baseEnd_6440388 : Nat := 1102338215149617728677067

theorem tailTrace_6440388 : CollatzResearch.WordTrace tailWord_6440388 prefixEnd_6440388 1102338215149617728677067 := by
  unfold tailWord_6440388
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450124095790840772776909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156600165461054454363702545 117450124095790840772776909)
  ·
    refine ⟨44043796535921565289791341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117450124095790840772776909 44043796535921565289791341)
    ·
      refine ⟨16516423700970586983671753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44043796535921565289791341 16516423700970586983671753)
      ·
        refine ⟨12387317775727940237753815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16516423700970586983671753 12387317775727940237753815)
        ·
          refine ⟨18580976663591910356630723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387317775727940237753815 18580976663591910356630723)
          ·
            refine ⟨27871464995387865534946085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18580976663591910356630723 27871464995387865534946085)
            ·
              refine ⟨5225899686635224787802391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27871464995387865534946085 5225899686635224787802391)
              ·
                refine ⟨7838849529952837181703587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225899686635224787802391 7838849529952837181703587)
                ·
                  refine ⟨11758274294929255772555381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7838849529952837181703587 11758274294929255772555381)
                  ·
                    refine ⟨1102338215149617728677067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11758274294929255772555381 1102338215149617728677067)
                    ·
                      rfl

theorem cell23_6440388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6440388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440388 prefixEnd_6440388 := by exact prefixLift 6440388
  have htrace : WordTrace (prefixWord ++ tailWord_6440388) baseStart_6440388 baseEnd_6440388 := by
    simpa [prefixWord, tailWord_6440388, baseEnd_6440388] using wordTrace_append hprefix tailTrace_6440388
  have hstable : (prefixWord ++ tailWord_6440388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440388).length < 2 ^ (prefixWord ++ tailWord_6440388).sum := by decide
  have hdescent : baseEnd_6440388 < baseStart_6440388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440391 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_6440391 : Nat := 118140960795 + 6440391 * 2 ^ 59
def prefixEnd_6440391 : Nat := 4983230072969 + 3 ^ 40 * 6440391 * 2
def baseEnd_6440391 : Nat := 3307016185890816674293687

theorem tailTrace_6440391 : CollatzResearch.WordTrace tailWord_6440391 prefixEnd_6440391 3307016185890816674293687 := by
  unfold tailWord_6440391
  simp only [CollatzResearch.WordTrace]
  refine ⟨234900357610570813057913027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156600238407047208705275351 234900357610570813057913027)
  ·
    refine ⟨352350536415856219586869541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234900357610570813057913027 352350536415856219586869541)
    ·
      refine ⟨66065725577973041172538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352350536415856219586869541 66065725577973041172538039)
      ·
        refine ⟨99098588366959561758807059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66065725577973041172538039 99098588366959561758807059)
        ·
          refine ⟨148647882550439342638210589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99098588366959561758807059 148647882550439342638210589)
          ·
            refine ⟨55742955956414753489328971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148647882550439342638210589 55742955956414753489328971)
            ·
              refine ⟨83614433934622130233993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55742955956414753489328971 83614433934622130233993457)
              ·
                refine ⟨62710825450966597675495093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83614433934622130233993457 62710825450966597675495093)
                ·
                  refine ⟨5879139886028118532077665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62710825450966597675495093 5879139886028118532077665)
                  ·
                    refine ⟨4409354914521088899058249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879139886028118532077665 4409354914521088899058249)
                    ·
                      refine ⟨3307016185890816674293687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409354914521088899058249 3307016185890816674293687)
                      ·
                        rfl

theorem cell23_6440391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_6440391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440391 prefixEnd_6440391 := by exact prefixLift 6440391
  have htrace : WordTrace (prefixWord ++ tailWord_6440391) baseStart_6440391 baseEnd_6440391 := by
    simpa [prefixWord, tailWord_6440391, baseEnd_6440391] using wordTrace_append hprefix tailTrace_6440391
  have hstable : (prefixWord ++ tailWord_6440391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440391).length < 2 ^ (prefixWord ++ tailWord_6440391).sum := by decide
  have hdescent : baseEnd_6440391 < baseStart_6440391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440421 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6440421 : Nat := 118140960795 + 6440421 * 2 ^ 59
def prefixEnd_6440421 : Nat := 4983230072969 + 3 ^ 40 * 6440421 * 2
def baseEnd_6440421 : Nat := 3307031590310451556918549

theorem tailTrace_6440421 : CollatzResearch.WordTrace tailWord_6440421 prefixEnd_6440421 3307031590310451556918549 := by
  unfold tailWord_6440421
  simp only [CollatzResearch.WordTrace]
  refine ⟨234901451800462128181505117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156600967866974752121003411 234901451800462128181505117)
  ·
    refine ⟨88088044425173298068064419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234901451800462128181505117 88088044425173298068064419)
    ·
      refine ⟨132132066637759947102096629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88088044425173298068064419 132132066637759947102096629)
      ·
        refine ⟨12387381247289995040821559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132132066637759947102096629 12387381247289995040821559)
        ·
          refine ⟨18581071870934992561232339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387381247289995040821559 18581071870934992561232339)
          ·
            refine ⟨27871607806402488841848509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18581071870934992561232339 27871607806402488841848509)
            ·
              refine ⟨10451852927400933315693191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27871607806402488841848509 10451852927400933315693191)
              ·
                refine ⟨15677779391101399973539787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451852927400933315693191 15677779391101399973539787)
                ·
                  refine ⟨23516669086652099960309681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15677779391101399973539787 23516669086652099960309681)
                  ·
                    refine ⟨17637501814989074970232261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23516669086652099960309681 17637501814989074970232261)
                    ·
                      refine ⟨3307031590310451556918549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17637501814989074970232261 3307031590310451556918549)
                      ·
                        rfl

theorem cell23_6440421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6440421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440421 prefixEnd_6440421 := by exact prefixLift 6440421
  have htrace : WordTrace (prefixWord ++ tailWord_6440421) baseStart_6440421 baseEnd_6440421 := by
    simpa [prefixWord, tailWord_6440421, baseEnd_6440421] using wordTrace_append hprefix tailTrace_6440421
  have hstable : (prefixWord ++ tailWord_6440421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440421).length < 2 ^ (prefixWord ++ tailWord_6440421).sum := by decide
  have hdescent : baseEnd_6440421 < baseStart_6440421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440551 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 2, 5]
def baseStart_6440551 : Nat := 118140960795 + 6440551 * 2 ^ 59
def prefixEnd_6440551 : Nat := 4983230072969 + 3 ^ 40 * 6440551 * 2
def baseEnd_6440551 : Nat := 1102366114265178682764317

theorem tailTrace_6440551 : CollatzResearch.WordTrace tailWord_6440551 prefixEnd_6440551 1102366114265178682764317 := by
  unfold tailWord_6440551
  simp only [CollatzResearch.WordTrace]
  refine ⟨234906193289991160383737507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156604128859994106922491671 234906193289991160383737507)
  ·
    refine ⟨352359289934986740575606261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234906193289991160383737507 352359289934986740575606261)
    ·
      refine ⟨33033683431405006928963087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 352359289934986740575606261 33033683431405006928963087)
      ·
        refine ⟨49550525147107510393444631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33033683431405006928963087 49550525147107510393444631)
        ·
          refine ⟨74325787720661265590166947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49550525147107510393444631 74325787720661265590166947)
          ·
            refine ⟨111488681580991898385250421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74325787720661265590166947 111488681580991898385250421)
            ·
              refine ⟨10452063898217990473617227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111488681580991898385250421 10452063898217990473617227)
              ·
                refine ⟨15678095847326985710425841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452063898217990473617227 15678095847326985710425841)
                ·
                  refine ⟨11758571885495239282819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15678095847326985710425841 11758571885495239282819381)
                  ·
                    refine ⟨1102366114265178682764317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11758571885495239282819381 1102366114265178682764317)
                    ·
                      rfl

theorem cell23_6440551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_6440551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440551 prefixEnd_6440551 := by exact prefixLift 6440551
  have htrace : WordTrace (prefixWord ++ tailWord_6440551) baseStart_6440551 baseEnd_6440551 := by
    simpa [prefixWord, tailWord_6440551, baseEnd_6440551] using wordTrace_append hprefix tailTrace_6440551
  have hstable : (prefixWord ++ tailWord_6440551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440551).length < 2 ^ (prefixWord ++ tailWord_6440551).sum := by decide
  have hdescent : baseEnd_6440551 < baseStart_6440551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440571 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 4, 2]
def baseStart_6440571 : Nat := 118140960795 + 6440571 * 2 ^ 59
def prefixEnd_6440571 : Nat := 4983230072969 + 3 ^ 40 * 6440571 * 2
def baseEnd_6440571 : Nat := 3307108612408625970042859

theorem tailTrace_6440571 : CollatzResearch.WordTrace tailWord_6440571 prefixEnd_6440571 3307108612408625970042859 := by
  unfold tailWord_6440571
  simp only [CollatzResearch.WordTrace]
  refine ⟨234906922749918703799465567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156604615166612469199643711 234906922749918703799465567)
  ·
    refine ⟨352360384124878055699198351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234906922749918703799465567 352360384124878055699198351)
    ·
      refine ⟨528540576187317083548797527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352360384124878055699198351 528540576187317083548797527)
      ·
        refine ⟨792810864280975625323196291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528540576187317083548797527 792810864280975625323196291)
        ·
          refine ⟨1189216296421463437984794437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792810864280975625323196291 1189216296421463437984794437)
          ·
            refine ⟨222978055579024394622148957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1189216296421463437984794437 222978055579024394622148957)
            ·
              refine ⟨83616770842134147983305859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222978055579024394622148957 83616770842134147983305859)
              ·
                refine ⟨125425156263201221974958789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83616770842134147983305859 125425156263201221974958789)
                ·
                  refine ⟨23517216799350229120304773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125425156263201221974958789 23517216799350229120304773)
                  ·
                    refine ⟨4409478149878167960057145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23517216799350229120304773 4409478149878167960057145)
                    ·
                      refine ⟨3307108612408625970042859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409478149878167960057145 3307108612408625970042859)
                      ·
                        rfl

theorem cell23_6440571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4, 2].length) (baseStart_6440571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440571 prefixEnd_6440571 := by exact prefixLift 6440571
  have htrace : WordTrace (prefixWord ++ tailWord_6440571) baseStart_6440571 baseEnd_6440571 := by
    simpa [prefixWord, tailWord_6440571, baseEnd_6440571] using wordTrace_append hprefix tailTrace_6440571
  have hstable : (prefixWord ++ tailWord_6440571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440571).length < 2 ^ (prefixWord ++ tailWord_6440571).sum := by decide
  have hdescent : baseEnd_6440571 < baseStart_6440571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440648 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_6440648 : Nat := 118140960795 + 6440648 * 2 ^ 59
def prefixEnd_6440648 : Nat := 4983230072969 + 3 ^ 40 * 6440648 * 2
def baseEnd_6440648 : Nat := 3307148150419022168780005

theorem tailTrace_6440648 : CollatzResearch.WordTrace tailWord_6440648 prefixEnd_6440648 3307148150419022168780005 := by
  unfold tailWord_6440648
  simp only [CollatzResearch.WordTrace]
  refine ⟨117454865585319872975009299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156606487447093163966679065 117454865585319872975009299)
  ·
    refine ⟨176182298377979809462513949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117454865585319872975009299 176182298377979809462513949)
    ·
      refine ⟨66068361891742428548442731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176182298377979809462513949 66068361891742428548442731)
      ·
        refine ⟨99102542837613642822664097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66068361891742428548442731 99102542837613642822664097)
        ·
          refine ⟨74326907128210232116998073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99102542837613642822664097 74326907128210232116998073)
          ·
            refine ⟨55745180346157674087748555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74326907128210232116998073 55745180346157674087748555)
            ·
              refine ⟨83617770519236511131622833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55745180346157674087748555 83617770519236511131622833)
              ·
                refine ⟨62713327889427383348717125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83617770519236511131622833 62713327889427383348717125)
                ·
                  refine ⟨11758748979267634377884461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62713327889427383348717125 11758748979267634377884461)
                  ·
                    refine ⟨4409530867225362891706673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11758748979267634377884461 4409530867225362891706673)
                    ·
                      refine ⟨3307148150419022168780005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409530867225362891706673 3307148150419022168780005)
                      ·
                        rfl

theorem cell23_6440648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_6440648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440648 prefixEnd_6440648 := by exact prefixLift 6440648
  have htrace : WordTrace (prefixWord ++ tailWord_6440648) baseStart_6440648 baseEnd_6440648 := by
    simpa [prefixWord, tailWord_6440648, baseEnd_6440648] using wordTrace_append hprefix tailTrace_6440648
  have hstable : (prefixWord ++ tailWord_6440648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440648).length < 2 ^ (prefixWord ++ tailWord_6440648).sum := by decide
  have hdescent : baseEnd_6440648 < baseStart_6440648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440658 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_6440658 : Nat := 118140960795 + 6440658 * 2 ^ 59
def prefixEnd_6440658 : Nat := 4983230072969 + 3 ^ 40 * 6440658 * 2
def baseEnd_6440658 : Nat := 1102384428408522376551653

theorem tailTrace_6440658 : CollatzResearch.WordTrace tailWord_6440658 prefixEnd_6440658 1102384428408522376551653 := by
  unfold tailWord_6440658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58727523975150879414470657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156606730600402345105255085 58727523975150879414470657)
  ·
    refine ⟨44045642981363159560852993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58727523975150879414470657 44045642981363159560852993)
    ·
      refine ⟨33034232236022369670639745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44045642981363159560852993 33034232236022369670639745)
      ·
        refine ⟨24775674177016777252979809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33034232236022369670639745 24775674177016777252979809)
        ·
          refine ⟨18581755632762582939734857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24775674177016777252979809 18581755632762582939734857)
          ·
            refine ⟨13936316724571937204801143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18581755632762582939734857 13936316724571937204801143)
            ·
              refine ⟨20904475086857905807201715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936316724571937204801143 20904475086857905807201715)
              ·
                refine ⟨31356712630286858710802573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20904475086857905807201715 31356712630286858710802573)
                ·
                  refine ⟨11758767236357572016550965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31356712630286858710802573 11758767236357572016550965)
                  ·
                    refine ⟨1102384428408522376551653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11758767236357572016550965 1102384428408522376551653)
                    ·
                      rfl

theorem cell23_6440658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_6440658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440658 prefixEnd_6440658 := by exact prefixLift 6440658
  have htrace : WordTrace (prefixWord ++ tailWord_6440658) baseStart_6440658 baseEnd_6440658 := by
    simpa [prefixWord, tailWord_6440658, baseEnd_6440658] using wordTrace_append hprefix tailTrace_6440658
  have hstable : (prefixWord ++ tailWord_6440658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440658).length < 2 ^ (prefixWord ++ tailWord_6440658).sum := by decide
  have hdescent : baseEnd_6440658 < baseStart_6440658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440665 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 2, 3, 2]
def baseStart_6440665 : Nat := 118140960795 + 6440665 * 2 ^ 59
def prefixEnd_6440665 : Nat := 4983230072969 + 3 ^ 40 * 6440665 * 2
def baseEnd_6440665 : Nat := 3307156879590148602267427

theorem tailTrace_6440665 : CollatzResearch.WordTrace tailWord_6440665 prefixEnd_6440665 3307156879590148602267427 := by
  unfold tailWord_6440665
  simp only [CollatzResearch.WordTrace]
  refine ⟨234910351211578157853387449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156606900807718771902258299 234910351211578157853387449)
  ·
    refine ⟨176182763408683618390040587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234910351211578157853387449 176182763408683618390040587)
    ·
      refine ⟨264274145113025427585060881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176182763408683618390040587 264274145113025427585060881)
      ·
        refine ⟨198205608834769070688795661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264274145113025427585060881 198205608834769070688795661)
        ·
          refine ⟨74327103313038401508298373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198205608834769070688795661 74327103313038401508298373)
          ·
            refine ⟨13936331871194700282805945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74327103313038401508298373 13936331871194700282805945)
            ·
              refine ⟨10452248903396025212104459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13936331871194700282805945 10452248903396025212104459)
              ·
                refine ⟨15678373355094037818156689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452248903396025212104459 15678373355094037818156689)
                ·
                  refine ⟨11758780016320528363617517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15678373355094037818156689 11758780016320528363617517)
                  ·
                    refine ⟨4409542506120198136356569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11758780016320528363617517 4409542506120198136356569)
                    ·
                      refine ⟨3307156879590148602267427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409542506120198136356569 3307156879590148602267427)
                      ·
                        rfl

theorem cell23_6440665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_6440665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440665 prefixEnd_6440665 := by exact prefixLift 6440665
  have htrace : WordTrace (prefixWord ++ tailWord_6440665) baseStart_6440665 baseEnd_6440665 := by
    simpa [prefixWord, tailWord_6440665, baseEnd_6440665] using wordTrace_append hprefix tailTrace_6440665
  have hstable : (prefixWord ++ tailWord_6440665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440665).length < 2 ^ (prefixWord ++ tailWord_6440665).sum := by decide
  have hdescent : baseEnd_6440665 < baseStart_6440665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440671 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 6]
def baseStart_6440671 : Nat := 118140960795 + 6440671 * 2 ^ 59
def prefixEnd_6440671 : Nat := 4983230072969 + 3 ^ 40 * 6440671 * 2
def baseEnd_6440671 : Nat := 1102386653491358526264133

theorem tailTrace_6440671 : CollatzResearch.WordTrace tailWord_6440671 prefixEnd_6440671 1102386653491358526264133 := by
  unfold tailWord_6440671
  simp only [CollatzResearch.WordTrace]
  refine ⟨234910570049556420878105867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156607046699704280585403911 234910570049556420878105867)
  ·
    refine ⟨352365855074334631317158801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234910570049556420878105867 352365855074334631317158801)
    ·
      refine ⟨264274391305750973487869101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352365855074334631317158801 264274391305750973487869101)
      ·
        refine ⟨99102896739656615057950913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264274391305750973487869101 99102896739656615057950913)
        ·
          refine ⟨74327172554742461293463185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99102896739656615057950913 74327172554742461293463185)
          ·
            refine ⟨55745379416056845970097389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74327172554742461293463185 55745379416056845970097389)
            ·
              refine ⟨20904517281021317238786521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55745379416056845970097389 20904517281021317238786521)
              ·
                refine ⟨15678387960765987929089891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20904517281021317238786521 15678387960765987929089891)
                ·
                  refine ⟨23517581941148981893634837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15678387960765987929089891 23517581941148981893634837)
                  ·
                    refine ⟨1102386653491358526264133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23517581941148981893634837 1102386653491358526264133)
                    ·
                      rfl

theorem cell23_6440671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_6440671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440671 prefixEnd_6440671 := by exact prefixLift 6440671
  have htrace : WordTrace (prefixWord ++ tailWord_6440671) baseStart_6440671 baseEnd_6440671 := by
    simpa [prefixWord, tailWord_6440671, baseEnd_6440671] using wordTrace_append hprefix tailTrace_6440671
  have hstable : (prefixWord ++ tailWord_6440671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440671).length < 2 ^ (prefixWord ++ tailWord_6440671).sum := by decide
  have hdescent : baseEnd_6440671 < baseStart_6440671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440689 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_6440689 : Nat := 118140960795 + 6440689 * 2 ^ 59
def prefixEnd_6440689 : Nat := 4983230072969 + 3 ^ 40 * 6440689 * 2
def baseEnd_6440689 : Nat := 3307169203125856508367317

theorem tailTrace_6440689 : CollatzResearch.WordTrace tailWord_6440689 prefixEnd_6440689 3307169203125856508367317 := by
  unfold tailWord_6440689
  simp only [CollatzResearch.WordTrace]
  refine ⟨234911226563491209952261121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156607484375660806634840747 234911226563491209952261121)
  ·
    refine ⟨176183419922618407464195841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234911226563491209952261121 176183419922618407464195841)
    ·
      refine ⟨132137564941963805598146881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176183419922618407464195841 132137564941963805598146881)
      ·
        refine ⟨99103173706472854198610161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132137564941963805598146881 99103173706472854198610161)
        ·
          refine ⟨74327380279854640648957621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99103173706472854198610161 74327380279854640648957621)
          ·
            refine ⟨6968191901236372560839777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74327380279854640648957621 6968191901236372560839777)
            ·
              refine ⟨5226143925927279420629833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6968191901236372560839777 5226143925927279420629833)
              ·
                refine ⟨3919607944445459565472375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5226143925927279420629833 3919607944445459565472375)
                ·
                  refine ⟨5879411916668189348208563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919607944445459565472375 5879411916668189348208563)
                  ·
                    refine ⟨8819117875002284022312845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5879411916668189348208563 8819117875002284022312845)
                    ·
                      refine ⟨3307169203125856508367317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819117875002284022312845 3307169203125856508367317)
                      ·
                        rfl

theorem cell23_6440689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_6440689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440689 prefixEnd_6440689 := by exact prefixLift 6440689
  have htrace : WordTrace (prefixWord ++ tailWord_6440689) baseStart_6440689 baseEnd_6440689 := by
    simpa [prefixWord, tailWord_6440689, baseEnd_6440689] using wordTrace_append hprefix tailTrace_6440689
  have hstable : (prefixWord ++ tailWord_6440689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440689).length < 2 ^ (prefixWord ++ tailWord_6440689).sum := by decide
  have hdescent : baseEnd_6440689 < baseStart_6440689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440708 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6440708 : Nat := 118140960795 + 6440708 * 2 ^ 59
def prefixEnd_6440708 : Nat := 4983230072969 + 3 ^ 40 * 6440708 * 2
def baseEnd_6440708 : Nat := 3307178959258291934029729

theorem tailTrace_6440708 : CollatzResearch.WordTrace tailWord_6440708 prefixEnd_6440708 3307178959258291934029729 := by
  unfold tailWord_6440708
  simp only [CollatzResearch.WordTrace]
  refine ⟨117455959775211188098601389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156607946366948250798135185 117455959775211188098601389)
  ·
    refine ⟨44045984915704195536975521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117455959775211188098601389 44045984915704195536975521)
    ·
      refine ⟨33034488686778146652731641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44045984915704195536975521 33034488686778146652731641)
      ·
        refine ⟨24775866515083609989548731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33034488686778146652731641 24775866515083609989548731)
        ·
          refine ⟨37163799772625414984323097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24775866515083609989548731 37163799772625414984323097)
          ·
            refine ⟨27872849829469061238242323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37163799772625414984323097 27872849829469061238242323)
            ·
              refine ⟨41809274744203591857363485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27872849829469061238242323 41809274744203591857363485)
              ·
                refine ⟨15678478029076346946511307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41809274744203591857363485 15678478029076346946511307)
                ·
                  refine ⟨23517717043614520419766961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15678478029076346946511307 23517717043614520419766961)
                  ·
                    refine ⟨17638287782710890314825221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23517717043614520419766961 17638287782710890314825221)
                    ·
                      refine ⟨3307178959258291934029729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17638287782710890314825221 3307178959258291934029729)
                      ·
                        rfl

theorem cell23_6440708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6440708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440708 prefixEnd_6440708 := by exact prefixLift 6440708
  have htrace : WordTrace (prefixWord ++ tailWord_6440708) baseStart_6440708 baseEnd_6440708 := by
    simpa [prefixWord, tailWord_6440708, baseEnd_6440708] using wordTrace_append hprefix tailTrace_6440708
  have hstable : (prefixWord ++ tailWord_6440708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440708).length < 2 ^ (prefixWord ++ tailWord_6440708).sum := by decide
  have hdescent : baseEnd_6440708 < baseStart_6440708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440710 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6440710 : Nat := 118140960795 + 6440710 * 2 ^ 59
def prefixEnd_6440710 : Nat := 4983230072969 + 3 ^ 40 * 6440710 * 2
def baseEnd_6440710 : Nat := 3307179986219600926204721

theorem tailTrace_6440710 : CollatzResearch.WordTrace tailWord_6440710 prefixEnd_6440710 3307179986219600926204721 := by
  unfold tailWord_6440710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340999765512972829336737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156607994997610087025850389 7340999765512972829336737)
  ·
    refine ⟨5505749824134729622002553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7340999765512972829336737 5505749824134729622002553)
    ·
      refine ⟨4129312368101047216501915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505749824134729622002553 4129312368101047216501915)
      ·
        refine ⟨6193968552151570824752873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129312368101047216501915 6193968552151570824752873)
        ·
          refine ⟨4645476414113678118564655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193968552151570824752873 4645476414113678118564655)
          ·
            refine ⟨6968214621170517177846983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645476414113678118564655 6968214621170517177846983)
            ·
              refine ⟨10452321931755775766770475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968214621170517177846983 10452321931755775766770475)
              ·
                refine ⟨15678482897633663650155713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452321931755775766770475 15678482897633663650155713)
                ·
                  refine ⟨11758862173225247737616785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15678482897633663650155713 11758862173225247737616785)
                  ·
                    refine ⟨8819146629918935803212589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11758862173225247737616785 8819146629918935803212589)
                    ·
                      refine ⟨3307179986219600926204721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819146629918935803212589 3307179986219600926204721)
                      ·
                        rfl

theorem cell23_6440710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6440710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440710 prefixEnd_6440710 := by exact prefixLift 6440710
  have htrace : WordTrace (prefixWord ++ tailWord_6440710) baseStart_6440710 baseEnd_6440710 := by
    simpa [prefixWord, tailWord_6440710, baseEnd_6440710] using wordTrace_append hprefix tailTrace_6440710
  have hstable : (prefixWord ++ tailWord_6440710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440710).length < 2 ^ (prefixWord ++ tailWord_6440710).sum := by decide
  have hdescent : baseEnd_6440710 < baseStart_6440710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440728 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6440728 : Nat := 118140960795 + 6440728 * 2 ^ 59
def prefixEnd_6440728 : Nat := 4983230072969 + 3 ^ 40 * 6440728 * 2
def baseEnd_6440728 : Nat := 3307189228871381855779637

theorem tailTrace_6440728 : CollatzResearch.WordTrace tailWord_6440728 prefixEnd_6440728 3307189228871381855779637 := by
  unfold tailWord_6440728
  simp only [CollatzResearch.WordTrace]
  refine ⟨117456324505174959806465419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156608432673566613075287225 117456324505174959806465419)
  ·
    refine ⟨176184486757762439709698129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117456324505174959806465419 176184486757762439709698129)
    ·
      refine ⟨132138365068321829782273597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176184486757762439709698129 132138365068321829782273597)
      ·
        refine ⟨49551886900620686168352599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132138365068321829782273597 49551886900620686168352599)
        ·
          refine ⟨74327830350931029252528899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49551886900620686168352599 74327830350931029252528899)
          ·
            refine ⟨111491745526396543878793349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74327830350931029252528899 111491745526396543878793349)
            ·
              refine ⟨20904702286199351977273753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111491745526396543878793349 20904702286199351977273753)
              ·
                refine ⟨15678526714649513982955315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20904702286199351977273753 15678526714649513982955315)
                ·
                  refine ⟨23517790071974270974432973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15678526714649513982955315 23517790071974270974432973)
                  ·
                    refine ⟨8819171276990351615412365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23517790071974270974432973 8819171276990351615412365)
                    ·
                      refine ⟨3307189228871381855779637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819171276990351615412365 3307189228871381855779637)
                      ·
                        rfl

theorem cell23_6440728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6440728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440728 prefixEnd_6440728 := by exact prefixLift 6440728
  have htrace : WordTrace (prefixWord ++ tailWord_6440728) baseStart_6440728 baseEnd_6440728 := by
    simpa [prefixWord, tailWord_6440728, baseEnd_6440728] using wordTrace_append hprefix tailTrace_6440728
  have hstable : (prefixWord ++ tailWord_6440728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440728).length < 2 ^ (prefixWord ++ tailWord_6440728).sum := by decide
  have hdescent : baseEnd_6440728 < baseStart_6440728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440788 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_6440788 : Nat := 118140960795 + 6440788 * 2 ^ 59
def prefixEnd_6440788 : Nat := 4983230072969 + 3 ^ 40 * 6440788 * 2
def baseEnd_6440788 : Nat := 3307220037710651621029361

theorem tailTrace_6440788 : CollatzResearch.WordTrace tailWord_6440788 prefixEnd_6440788 3307220037710651621029361 := by
  unfold tailWord_6440788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117457418695066274930057509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156609891593421699906743345 117457418695066274930057509)
  ·
    refine ⟨22023266005324926549385783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117457418695066274930057509 22023266005324926549385783)
    ·
      refine ⟨33034899007987389824078675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023266005324926549385783 33034899007987389824078675)
      ·
        refine ⟨49552348511981084736118013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33034899007987389824078675 49552348511981084736118013)
        ·
          refine ⟨18582130691992906776044255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49552348511981084736118013 18582130691992906776044255)
          ·
            refine ⟨27873196037989360164066383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18582130691992906776044255 27873196037989360164066383)
            ·
              refine ⟨41809794056984040246099575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27873196037989360164066383 41809794056984040246099575)
              ·
                refine ⟨62714691085476060369149363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41809794056984040246099575 62714691085476060369149363)
                ·
                  refine ⟨94072036628214090553724045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62714691085476060369149363 94072036628214090553724045)
                  ·
                    refine ⟨35277013735580283957646517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94072036628214090553724045 35277013735580283957646517)
                    ·
                      refine ⟨3307220037710651621029361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35277013735580283957646517 3307220037710651621029361)
                      ·
                        rfl

theorem cell23_6440788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_6440788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440788 prefixEnd_6440788 := by exact prefixLift 6440788
  have htrace : WordTrace (prefixWord ++ tailWord_6440788) baseStart_6440788 baseEnd_6440788 := by
    simpa [prefixWord, tailWord_6440788, baseEnd_6440788] using wordTrace_append hprefix tailTrace_6440788
  have hstable : (prefixWord ++ tailWord_6440788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440788).length < 2 ^ (prefixWord ++ tailWord_6440788).sum := by decide
  have hdescent : baseEnd_6440788 < baseStart_6440788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440801 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6440801 : Nat := 118140960795 + 6440801 * 2 ^ 59
def prefixEnd_6440801 : Nat := 4983230072969 + 3 ^ 40 * 6440801 * 2
def baseEnd_6440801 : Nat := 3307226712959160070166801

theorem tailTrace_6440801 : CollatzResearch.WordTrace tailWord_6440801 prefixEnd_6440801 3307226712959160070166801 := by
  unfold tailWord_6440801
  simp only [CollatzResearch.WordTrace]
  refine ⟨234915311539085453080338257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156610207692723635386892171 234915311539085453080338257)
  ·
    refine ⟨176186483654314089810253693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234915311539085453080338257 176186483654314089810253693)
    ·
      refine ⟨66069931370367783678845135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176186483654314089810253693 66069931370367783678845135)
      ·
        refine ⟨99104897055551675518267703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66069931370367783678845135 99104897055551675518267703)
        ·
          refine ⟨148657345583327513277401555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99104897055551675518267703 148657345583327513277401555)
          ·
            refine ⟨222986018374991269916102333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148657345583327513277401555 222986018374991269916102333)
            ·
              refine ⟨83619756890621726218538375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222986018374991269916102333 83619756890621726218538375)
              ·
                refine ⟨125429635335932589327807563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83619756890621726218538375 125429635335932589327807563)
                ·
                  refine ⟨188144453003898883991711345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125429635335932589327807563 188144453003898883991711345)
                  ·
                    refine ⟨141108339752924162993783509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188144453003898883991711345 141108339752924162993783509)
                    ·
                      refine ⟨3307226712959160070166801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141108339752924162993783509 3307226712959160070166801)
                      ·
                        rfl

theorem cell23_6440801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6440801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440801 prefixEnd_6440801 := by exact prefixLift 6440801
  have htrace : WordTrace (prefixWord ++ tailWord_6440801) baseStart_6440801 baseEnd_6440801 := by
    simpa [prefixWord, tailWord_6440801, baseEnd_6440801] using wordTrace_append hprefix tailTrace_6440801
  have hstable : (prefixWord ++ tailWord_6440801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440801).length < 2 ^ (prefixWord ++ tailWord_6440801).sum := by decide
  have hdescent : baseEnd_6440801 < baseStart_6440801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440818 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6440818 : Nat := 118140960795 + 6440818 * 2 ^ 59
def prefixEnd_6440818 : Nat := 4983230072969 + 3 ^ 40 * 6440818 * 2
def baseEnd_6440818 : Nat := 3307235442130286503654223

theorem tailTrace_6440818 : CollatzResearch.WordTrace tailWord_6440818 prefixEnd_6440818 3307235442130286503654223 := by
  unfold tailWord_6440818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58728982895005966245926777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156610621053349243322471405 58728982895005966245926777)
  ·
    refine ⟨44046737171254474684445083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58728982895005966245926777 44046737171254474684445083)
    ·
      refine ⟨66070105756881712026667625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44046737171254474684445083 66070105756881712026667625)
      ·
        refine ⟨49552579317661284020000719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66070105756881712026667625 49552579317661284020000719)
        ·
          refine ⟨74328868976491926030001079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49552579317661284020000719 74328868976491926030001079)
          ·
            refine ⟨111493303464737889045001619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74328868976491926030001079 111493303464737889045001619)
            ·
              refine ⟨167239955197106833567502429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111493303464737889045001619 167239955197106833567502429)
              ·
                refine ⟨62714983198915062587813411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167239955197106833567502429 62714983198915062587813411)
                ·
                  refine ⟨94072474798372593881720117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62714983198915062587813411 94072474798372593881720117)
                  ·
                    refine ⟨8819294512347430676411261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94072474798372593881720117 8819294512347430676411261)
                    ·
                      refine ⟨3307235442130286503654223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819294512347430676411261 3307235442130286503654223)
                      ·
                        rfl

theorem cell23_6440818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6440818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440818 prefixEnd_6440818 := by exact prefixLift 6440818
  have htrace : WordTrace (prefixWord ++ tailWord_6440818) baseStart_6440818 baseEnd_6440818 := by
    simpa [prefixWord, tailWord_6440818, baseEnd_6440818] using wordTrace_append hprefix tailTrace_6440818
  have hstable : (prefixWord ++ tailWord_6440818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440818).length < 2 ^ (prefixWord ++ tailWord_6440818).sum := by decide
  have hdescent : baseEnd_6440818 < baseStart_6440818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440831 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_6440831 : Nat := 118140960795 + 6440831 * 2 ^ 59
def prefixEnd_6440831 : Nat := 4983230072969 + 3 ^ 40 * 6440831 * 2
def baseEnd_6440831 : Nat := 3307242117378794952791663

theorem tailTrace_6440831 : CollatzResearch.WordTrace tailWord_6440831 prefixEnd_6440831 3307242117378794952791663 := by
  unfold tailWord_6440831
  simp only [CollatzResearch.WordTrace]
  refine ⟨234916405728976768203930347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156610937152651178802620231 234916405728976768203930347)
  ·
    refine ⟨352374608593465152305895521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234916405728976768203930347 352374608593465152305895521)
    ·
      refine ⟨264280956445098864229421641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352374608593465152305895521 264280956445098864229421641)
      ·
        refine ⟨198210717333824148172066231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264280956445098864229421641 198210717333824148172066231)
        ·
          refine ⟨297316076000736222258099347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198210717333824148172066231 297316076000736222258099347)
          ·
            refine ⟨445974114001104333387149021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297316076000736222258099347 445974114001104333387149021)
            ·
              refine ⟨167240292750414125020180883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445974114001104333387149021 167240292750414125020180883)
              ·
                refine ⟨250860439125621187530271325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167240292750414125020180883 250860439125621187530271325)
                ·
                  refine ⟨94072664672107945323851747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250860439125621187530271325 94072664672107945323851747)
                  ·
                    refine ⟨141108997008161917985777621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94072664672107945323851747 141108997008161917985777621)
                    ·
                      refine ⟨3307242117378794952791663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141108997008161917985777621 3307242117378794952791663)
                      ·
                        rfl

theorem cell23_6440831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_6440831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440831 prefixEnd_6440831 := by exact prefixLift 6440831
  have htrace : WordTrace (prefixWord ++ tailWord_6440831) baseStart_6440831 baseEnd_6440831 := by
    simpa [prefixWord, tailWord_6440831, baseEnd_6440831] using wordTrace_append hprefix tailTrace_6440831
  have hstable : (prefixWord ++ tailWord_6440831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440831).length < 2 ^ (prefixWord ++ tailWord_6440831).sum := by decide
  have hdescent : baseEnd_6440831 < baseStart_6440831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440851 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 8]
def baseStart_6440851 : Nat := 118140960795 + 6440851 * 2 ^ 59
def prefixEnd_6440851 : Nat := 4983230072969 + 3 ^ 40 * 6440851 * 2
def baseEnd_6440851 : Nat := 1102417462330628291513857

theorem tailTrace_6440851 : CollatzResearch.WordTrace tailWord_6440851 prefixEnd_6440851 1102417462330628291513857 := by
  unfold tailWord_6440851
  simp only [CollatzResearch.WordTrace]
  refine ⟨234917135188904311619658407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156611423459269541079772271 234917135188904311619658407)
  ·
    refine ⟨352375702783356467429487611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234917135188904311619658407 352375702783356467429487611)
    ·
      refine ⟨528563554175034701144231417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352375702783356467429487611 528563554175034701144231417)
      ·
        refine ⟨396422665631276025858173563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528563554175034701144231417 396422665631276025858173563)
        ·
          refine ⟨594633998446914038787260345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396422665631276025858173563 594633998446914038787260345)
          ·
            refine ⟨445975498835185529090445259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594633998446914038787260345 445975498835185529090445259)
            ·
              refine ⟨668963248252778293635667889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445975498835185529090445259 668963248252778293635667889)
              ·
                refine ⟨501722436189583720226750917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668963248252778293635667889 501722436189583720226750917)
                ·
                  refine ⟨94072956785546947542515797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501722436189583720226750917 94072956785546947542515797)
                  ·
                    refine ⟨1102417462330628291513857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94072956785546947542515797 1102417462330628291513857)
                    ·
                      rfl

theorem cell23_6440851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_6440851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440851 prefixEnd_6440851 := by exact prefixLift 6440851
  have htrace : WordTrace (prefixWord ++ tailWord_6440851) baseStart_6440851 baseEnd_6440851 := by
    simpa [prefixWord, tailWord_6440851, baseEnd_6440851] using wordTrace_append hprefix tailTrace_6440851
  have hstable : (prefixWord ++ tailWord_6440851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440851).length < 2 ^ (prefixWord ++ tailWord_6440851).sum := by decide
  have hdescent : baseEnd_6440851 < baseStart_6440851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440885 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_6440885 : Nat := 118140960795 + 6440885 * 2 ^ 59
def prefixEnd_6440885 : Nat := 4983230072969 + 3 ^ 40 * 6440885 * 2
def baseEnd_6440885 : Nat := 1102423281778045913838805

theorem tailTrace_6440885 : CollatzResearch.WordTrace tailWord_6440885 prefixEnd_6440885 1102423281778045913838805 := by
  unfold tailWord_6440885
  simp only [CollatzResearch.WordTrace]
  refine ⟨234918375270781135426396109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156612250180520756950930739 234918375270781135426396109)
  ·
    refine ⟨88094390726542925784898541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234918375270781135426396109 88094390726542925784898541)
    ·
      refine ⟨33035396522453597169336953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88094390726542925784898541 33035396522453597169336953)
      ·
        refine ⟨24776547391840197877002715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33035396522453597169336953 24776547391840197877002715)
        ·
          refine ⟨37164821087760296815504073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24776547391840197877002715 37164821087760296815504073)
          ·
            refine ⟨27873615815820222611628055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37164821087760296815504073 27873615815820222611628055)
            ·
              refine ⟨41810423723730333917442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27873615815820222611628055 41810423723730333917442083)
              ·
                refine ⟨62715635585595500876163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41810423723730333917442083 62715635585595500876163125)
                ·
                  refine ⟨5879590836149578207140293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62715635585595500876163125 5879590836149578207140293)
                  ·
                    refine ⟨1102423281778045913838805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5879590836149578207140293 1102423281778045913838805)
                    ·
                      rfl

theorem cell23_6440885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_6440885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440885 prefixEnd_6440885 := by exact prefixLift 6440885
  have htrace : WordTrace (prefixWord ++ tailWord_6440885) baseStart_6440885 baseEnd_6440885 := by
    simpa [prefixWord, tailWord_6440885, baseEnd_6440885] using wordTrace_append hprefix tailTrace_6440885
  have hstable : (prefixWord ++ tailWord_6440885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440885).length < 2 ^ (prefixWord ++ tailWord_6440885).sum := by decide
  have hdescent : baseEnd_6440885 < baseStart_6440885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440892 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6440892 : Nat := 118140960795 + 6440892 * 2 ^ 59
def prefixEnd_6440892 : Nat := 4983230072969 + 3 ^ 40 * 6440892 * 2
def baseEnd_6440892 : Nat := 3307273439698719214128883

theorem tailTrace_6440892 : CollatzResearch.WordTrace tailWord_6440892 prefixEnd_6440892 3307273439698719214128883 := by
  unfold tailWord_6440892
  simp only [CollatzResearch.WordTrace]
  refine ⟨117459315290877887810950465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156612420387837183747933953 117459315290877887810950465)
  ·
    refine ⟨88094486468158415858212849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117459315290877887810950465 88094486468158415858212849)
    ·
      refine ⟨66070864851118811893659637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88094486468158415858212849 66070864851118811893659637)
      ·
        refine ⟨6194143579792388615030591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66070864851118811893659637 6194143579792388615030591)
        ·
          refine ⟨9291215369688582922545887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194143579792388615030591 9291215369688582922545887)
          ·
            refine ⟨13936823054532874383818831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291215369688582922545887 13936823054532874383818831)
            ·
              refine ⟨20905234581799311575728247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936823054532874383818831 20905234581799311575728247)
              ·
                refine ⟨31357851872698967363592371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20905234581799311575728247 31357851872698967363592371)
                ·
                  refine ⟨47036777809048451045388557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31357851872698967363592371 47036777809048451045388557)
                  ·
                    refine ⟨17638791678393169142020709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47036777809048451045388557 17638791678393169142020709)
                    ·
                      refine ⟨3307273439698719214128883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17638791678393169142020709 3307273439698719214128883)
                      ·
                        rfl

theorem cell23_6440892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6440892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440892 prefixEnd_6440892 := by exact prefixLift 6440892
  have htrace : WordTrace (prefixWord ++ tailWord_6440892) baseStart_6440892 baseEnd_6440892 := by
    simpa [prefixWord, tailWord_6440892, baseEnd_6440892] using wordTrace_append hprefix tailTrace_6440892
  have hstable : (prefixWord ++ tailWord_6440892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440892).length < 2 ^ (prefixWord ++ tailWord_6440892).sum := by decide
  have hdescent : baseEnd_6440892 < baseStart_6440892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440928 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_6440928 : Nat := 118140960795 + 6440928 * 2 ^ 59
def prefixEnd_6440928 : Nat := 4983230072969 + 3 ^ 40 * 6440928 * 2
def baseEnd_6440928 : Nat := 1102430641667427024426239

theorem tailTrace_6440928 : CollatzResearch.WordTrace tailWord_6440928 prefixEnd_6440928 1102430641667427024426239 := by
  unfold tailWord_6440928
  simp only [CollatzResearch.WordTrace]
  refine ⟨117459971804812676885105719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156613295739750235846807625 117459971804812676885105719)
  ·
    refine ⟨176189957707219015327658579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117459971804812676885105719 176189957707219015327658579)
    ·
      refine ⟨264284936560828522991487869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176189957707219015327658579 264284936560828522991487869)
      ·
        refine ⟨99106851210310696121807951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264284936560828522991487869 99106851210310696121807951)
        ·
          refine ⟨148660276815466044182711927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99106851210310696121807951 148660276815466044182711927)
          ·
            refine ⟨222990415223199066274067891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148660276815466044182711927 222990415223199066274067891)
            ·
              refine ⟨334485622834798599411101837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222990415223199066274067891 334485622834798599411101837)
              ·
                refine ⟨125432108563049474779163189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334485622834798599411101837 125432108563049474779163189)
                ·
                  refine ⟨11759260177785888260546549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125432108563049474779163189 11759260177785888260546549)
                  ·
                    refine ⟨1102430641667427024426239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11759260177785888260546549 1102430641667427024426239)
                    ·
                      rfl

theorem cell23_6440928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_6440928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440928 prefixEnd_6440928 := by exact prefixLift 6440928
  have htrace : WordTrace (prefixWord ++ tailWord_6440928) baseStart_6440928 baseEnd_6440928 := by
    simpa [prefixWord, tailWord_6440928, baseEnd_6440928] using wordTrace_append hprefix tailTrace_6440928
  have hstable : (prefixWord ++ tailWord_6440928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440928).length < 2 ^ (prefixWord ++ tailWord_6440928).sum := by decide
  have hdescent : baseEnd_6440928 < baseStart_6440928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440985 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_6440985 : Nat := 118140960795 + 6440985 * 2 ^ 59
def prefixEnd_6440985 : Nat := 4983230072969 + 3 ^ 40 * 6440985 * 2
def baseEnd_6440985 : Nat := 3307321193399587350265955

theorem tailTrace_6440985 : CollatzResearch.WordTrace tailWord_6440985 prefixEnd_6440985 3307321193399587350265955 := by
  unfold tailWord_6440985
  simp only [CollatzResearch.WordTrace]
  refine ⟨234922022570418852505036409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156614681713612568336690939 234922022570418852505036409)
  ·
    refine ⟨176191516927814139378777307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234922022570418852505036409 176191516927814139378777307)
    ·
      refine ⟨264287275391721209068165961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176191516927814139378777307 264287275391721209068165961)
      ·
        refine ⟨198215456543790906801124471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264287275391721209068165961 198215456543790906801124471)
        ·
          refine ⟨297323184815686360201686707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198215456543790906801124471 297323184815686360201686707)
          ·
            refine ⟨445984777223529540302530061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297323184815686360201686707 445984777223529540302530061)
            ·
              refine ⟨167244291458823577613448773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445984777223529540302530061 167244291458823577613448773)
              ·
                refine ⟨31358304648529420802521645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167244291458823577613448773 31358304648529420802521645)
                ·
                  refine ⟨11759364243198532800945617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31358304648529420802521645 11759364243198532800945617)
                  ·
                    refine ⟨8819523182398899600709213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759364243198532800945617 8819523182398899600709213)
                    ·
                      refine ⟨3307321193399587350265955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819523182398899600709213 3307321193399587350265955)
                      ·
                        rfl

theorem cell23_6440985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_6440985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440985 prefixEnd_6440985 := by exact prefixLift 6440985
  have htrace : WordTrace (prefixWord ++ tailWord_6440985) baseStart_6440985 baseEnd_6440985 := by
    simpa [prefixWord, tailWord_6440985, baseEnd_6440985] using wordTrace_append hprefix tailTrace_6440985
  have hstable : (prefixWord ++ tailWord_6440985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440985).length < 2 ^ (prefixWord ++ tailWord_6440985).sum := by decide
  have hdescent : baseEnd_6440985 < baseStart_6440985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440995 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_6440995 : Nat := 118140960795 + 6440995 * 2 ^ 59
def prefixEnd_6440995 : Nat := 4983230072969 + 3 ^ 40 * 6440995 * 2
def baseEnd_6440995 : Nat := 3307326328206132311140909

theorem tailTrace_6440995 : CollatzResearch.WordTrace tailWord_6440995 prefixEnd_6440995 3307326328206132311140909 := by
  unfold tailWord_6440995
  simp only [CollatzResearch.WordTrace]
  refine ⟨234922387300382624212900439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156614924866921749475266959 234922387300382624212900439)
  ·
    refine ⟨352383580950573936319350659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234922387300382624212900439 352383580950573936319350659)
    ·
      refine ⟨528575371425860904479025989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352383580950573936319350659 528575371425860904479025989)
      ·
        refine ⟨99107882142348919589817373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528575371425860904479025989 99107882142348919589817373)
        ·
          refine ⟨37165455803380844846181515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99107882142348919589817373 37165455803380844846181515)
          ·
            refine ⟨55748183705071267269272273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37165455803380844846181515 55748183705071267269272273)
            ·
              refine ⟨41811137778803450451954205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55748183705071267269272273 41811137778803450451954205)
              ·
                refine ⟨15679176667051293919482827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41811137778803450451954205 15679176667051293919482827)
                ·
                  refine ⟨23518765000576940879224241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15679176667051293919482827 23518765000576940879224241)
                  ·
                    refine ⟨17639073750432705659418181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23518765000576940879224241 17639073750432705659418181)
                    ·
                      refine ⟨3307326328206132311140909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17639073750432705659418181 3307326328206132311140909)
                      ·
                        rfl

theorem cell23_6440995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_6440995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440995 prefixEnd_6440995 := by exact prefixLift 6440995
  have htrace : WordTrace (prefixWord ++ tailWord_6440995) baseStart_6440995 baseEnd_6440995 := by
    simpa [prefixWord, tailWord_6440995, baseEnd_6440995] using wordTrace_append hprefix tailTrace_6440995
  have hstable : (prefixWord ++ tailWord_6440995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440995).length < 2 ^ (prefixWord ++ tailWord_6440995).sum := by decide
  have hdescent : baseEnd_6440995 < baseStart_6440995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440996 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_6440996 : Nat := 118140960795 + 6440996 * 2 ^ 59
def prefixEnd_6440996 : Nat := 4983230072969 + 3 ^ 40 * 6440996 * 2
def baseEnd_6440996 : Nat := 1102442280562262269076135

theorem tailTrace_6440996 : CollatzResearch.WordTrace tailWord_6440996 prefixEnd_6440996 1102442280562262269076135 := by
  unfold tailWord_6440996
  simp only [CollatzResearch.WordTrace]
  refine ⟨117461211886689500691843421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156614949182252667589124561 117461211886689500691843421)
  ·
    refine ⟨44047954457508562759441283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117461211886689500691843421 44047954457508562759441283)
    ·
      refine ⟨66071931686262844139161925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44047954457508562759441283 66071931686262844139161925)
      ·
        refine ⟨12388487191174283276092861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66071931686262844139161925 12388487191174283276092861)
        ·
          refine ⟨4645682696690356228534823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12388487191174283276092861 4645682696690356228534823)
          ·
            refine ⟨6968524045035534342802235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645682696690356228534823 6968524045035534342802235)
            ·
              refine ⟨10452786067553301514203353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968524045035534342802235 10452786067553301514203353)
              ·
                refine ⟨7839589550664976135652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10452786067553301514203353 7839589550664976135652515)
                ·
                  refine ⟨11759384325997464203478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839589550664976135652515 11759384325997464203478773)
                  ·
                    refine ⟨1102442280562262269076135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11759384325997464203478773 1102442280562262269076135)
                    ·
                      rfl

theorem cell23_6440996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_6440996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440996 prefixEnd_6440996 := by exact prefixLift 6440996
  have htrace : WordTrace (prefixWord ++ tailWord_6440996) baseStart_6440996 baseEnd_6440996 := by
    simpa [prefixWord, tailWord_6440996, baseEnd_6440996] using wordTrace_append hprefix tailTrace_6440996
  have hstable : (prefixWord ++ tailWord_6440996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440996).length < 2 ^ (prefixWord ++ tailWord_6440996).sum := by decide
  have hdescent : baseEnd_6440996 < baseStart_6440996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6440999 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6440999 : Nat := 118140960795 + 6440999 * 2 ^ 59
def prefixEnd_6440999 : Nat := 4983230072969 + 3 ^ 40 * 6440999 * 2
def baseEnd_6440999 : Nat := 3307328382128750295490891

theorem tailTrace_6440999 : CollatzResearch.WordTrace tailWord_6440999 prefixEnd_6440999 3307328382128750295490891 := by
  unfold tailWord_6440999
  simp only [CollatzResearch.WordTrace]
  refine ⟨234922533192368132896046051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156615022128245421930697367 234922533192368132896046051)
  ·
    refine ⟨352383799788552199344069077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234922533192368132896046051 352383799788552199344069077)
    ·
      refine ⟨8258995307544192172126619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 352383799788552199344069077 8258995307544192172126619)
      ·
        refine ⟨12388492961316288258189929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258995307544192172126619 12388492961316288258189929)
        ·
          refine ⟨9291369720987216193642447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12388492961316288258189929 9291369720987216193642447)
          ·
            refine ⟨13937054581480824290463671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291369720987216193642447 13937054581480824290463671)
            ·
              refine ⟨20905581872221236435695507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13937054581480824290463671 20905581872221236435695507)
              ·
                refine ⟨31358372808331854653543261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20905581872221236435695507 31358372808331854653543261)
                ·
                  refine ⟨11759389803124445495078723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31358372808331854653543261 11759389803124445495078723)
                  ·
                    refine ⟨17639084704686668242618085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11759389803124445495078723 17639084704686668242618085)
                    ·
                      refine ⟨3307328382128750295490891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17639084704686668242618085 3307328382128750295490891)
                      ·
                        rfl

theorem cell23_6440999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6440999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6440999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6440999 prefixEnd_6440999 := by exact prefixLift 6440999
  have htrace : WordTrace (prefixWord ++ tailWord_6440999) baseStart_6440999 baseEnd_6440999 := by
    simpa [prefixWord, tailWord_6440999, baseEnd_6440999] using wordTrace_append hprefix tailTrace_6440999
  have hstable : (prefixWord ++ tailWord_6440999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6440999).length < 2 ^ (prefixWord ++ tailWord_6440999).sum := by decide
  have hdescent : baseEnd_6440999 < baseStart_6440999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6440999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441015 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_6441015 : Nat := 118140960795 + 6441015 * 2 ^ 59
def prefixEnd_6441015 : Nat := 4983230072969 + 3 ^ 40 * 6441015 * 2
def baseEnd_6441015 : Nat := 3307336597819222232890817

theorem tailTrace_6441015 : CollatzResearch.WordTrace tailWord_6441015 prefixEnd_6441015 3307336597819222232890817 := by
  unfold tailWord_6441015
  simp only [CollatzResearch.WordTrace]
  refine ⟨234923116760310167628628499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156615411173540111752418999 234923116760310167628628499)
  ·
    refine ⟨352384675140465251442942749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234923116760310167628628499 352384675140465251442942749)
    ·
      refine ⟨132144253177674469291103531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352384675140465251442942749 132144253177674469291103531)
      ·
        refine ⟨198216379766511703936655297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132144253177674469291103531 198216379766511703936655297)
        ·
          refine ⟨148662284824883777952491473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198216379766511703936655297 148662284824883777952491473)
          ·
            refine ⟨111496713618662833464368605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148662284824883777952491473 111496713618662833464368605)
            ·
              refine ⟨41811267606998562549138227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111496713618662833464368605 41811267606998562549138227)
              ·
                refine ⟨62716901410497843823707341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41811267606998562549138227 62716901410497843823707341)
                ·
                  refine ⟨23518838028936691433890253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62716901410497843823707341 23518838028936691433890253)
                  ·
                    refine ⟨8819564260851259287708845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23518838028936691433890253 8819564260851259287708845)
                    ·
                      refine ⟨3307336597819222232890817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819564260851259287708845 3307336597819222232890817)
                      ·
                        rfl

theorem cell23_6441015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_6441015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441015 prefixEnd_6441015 := by exact prefixLift 6441015
  have htrace : WordTrace (prefixWord ++ tailWord_6441015) baseStart_6441015 baseEnd_6441015 := by
    simpa [prefixWord, tailWord_6441015, baseEnd_6441015] using wordTrace_append hprefix tailTrace_6441015
  have hstable : (prefixWord ++ tailWord_6441015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441015).length < 2 ^ (prefixWord ++ tailWord_6441015).sum := by decide
  have hdescent : baseEnd_6441015 < baseStart_6441015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441022 : List Nat := [4, 2, 1, 3, 3, 10]
def baseStart_6441022 : Nat := 118140960795 + 6441022 * 2 ^ 59
def prefixEnd_6441022 : Nat := 4983230072969 + 3 ^ 40 * 6441022 * 2
def baseEnd_6441022 : Nat := 13610453465776969981495

theorem tailTrace_6441022 : CollatzResearch.WordTrace tailWord_6441022 prefixEnd_6441022 13610453465776969981495 := by
  unfold tailWord_6441022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29365421508910600978016665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156615581380856538549422213 29365421508910600978016665)
  ·
    refine ⟨22024066131682950733512499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29365421508910600978016665 22024066131682950733512499)
    ·
      refine ⟨33036099197524426100268749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024066131682950733512499 33036099197524426100268749)
      ·
        refine ⟨12388537199071659787600781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33036099197524426100268749 12388537199071659787600781)
        ·
          refine ⟨4645701449651872420350293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12388537199071659787600781 4645701449651872420350293)
          ·
            refine ⟨13610453465776969981495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4645701449651872420350293 13610453465776969981495)
            ·
              rfl

theorem cell23_6441022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 10].length) (baseStart_6441022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441022 prefixEnd_6441022 := by exact prefixLift 6441022
  have htrace : WordTrace (prefixWord ++ tailWord_6441022) baseStart_6441022 baseEnd_6441022 := by
    simpa [prefixWord, tailWord_6441022, baseEnd_6441022] using wordTrace_append hprefix tailTrace_6441022
  have hstable : (prefixWord ++ tailWord_6441022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441022).length < 2 ^ (prefixWord ++ tailWord_6441022).sum := by decide
  have hdescent : baseEnd_6441022 < baseStart_6441022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441046 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6441046 : Nat := 118140960795 + 6441046 * 2 ^ 59
def prefixEnd_6441046 : Nat := 4983230072969 + 3 ^ 40 * 6441046 * 2
def baseEnd_6441046 : Nat := 3307352515719511611603175

theorem tailTrace_6441046 : CollatzResearch.WordTrace tailWord_6441046 prefixEnd_6441046 3307352515719511611603175 := by
  unfold tailWord_6441046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682765463949866245187937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156616164948798573282004661 14682765463949866245187937)
  ·
    refine ⟨11012074097962399683890953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14682765463949866245187937 11012074097962399683890953)
    ·
      refine ⟨8259055573471799762918215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11012074097962399683890953 8259055573471799762918215)
      ·
        refine ⟨12388583360207699644377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8259055573471799762918215 12388583360207699644377323)
        ·
          refine ⟨18582875040311549466565985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388583360207699644377323 18582875040311549466565985)
          ·
            refine ⟨13937156280233662099924489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18582875040311549466565985 13937156280233662099924489)
            ·
              refine ⟨10452867210175246574943367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937156280233662099924489 10452867210175246574943367)
              ·
                refine ⟨15679300815262869862415051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452867210175246574943367 15679300815262869862415051)
                ·
                  refine ⟨23518951222894304793622577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15679300815262869862415051 23518951222894304793622577)
                  ·
                    refine ⟨17639213417170728595216933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23518951222894304793622577 17639213417170728595216933)
                    ·
                      refine ⟨3307352515719511611603175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17639213417170728595216933 3307352515719511611603175)
                      ·
                        rfl

theorem cell23_6441046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6441046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441046 prefixEnd_6441046 := by exact prefixLift 6441046
  have htrace : WordTrace (prefixWord ++ tailWord_6441046) baseStart_6441046 baseEnd_6441046 := by
    simpa [prefixWord, tailWord_6441046, baseEnd_6441046] using wordTrace_append hprefix tailTrace_6441046
  have hstable : (prefixWord ++ tailWord_6441046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441046).length < 2 ^ (prefixWord ++ tailWord_6441046).sum := by decide
  have hdescent : baseEnd_6441046 < baseStart_6441046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441095 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 7]
def baseStart_6441095 : Nat := 118140960795 + 6441095 * 2 ^ 59
def prefixEnd_6441095 : Nat := 4983230072969 + 3 ^ 40 * 6441095 * 2
def baseEnd_6441095 : Nat := 367486408474620213321161

theorem tailTrace_6441095 : CollatzResearch.WordTrace tailWord_6441095 prefixEnd_6441095 367486408474620213321161 := by
  unfold tailWord_6441095
  simp only [CollatzResearch.WordTrace]
  refine ⟨234926034600020341291540739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156617356400013560861027159 234926034600020341291540739)
  ·
    refine ⟨352389051900030511937311109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234926034600020341291540739 352389051900030511937311109)
    ·
      refine ⟨66072947231255720988245833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352389051900030511937311109 66072947231255720988245833)
      ·
        refine ⟨49554710423441790741184375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66072947231255720988245833 49554710423441790741184375)
        ·
          refine ⟨74332065635162686111776563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49554710423441790741184375 74332065635162686111776563)
          ·
            refine ⟨111498098452744029167664845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74332065635162686111776563 111498098452744029167664845)
            ·
              refine ⟨41811786919779010937874317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111498098452744029167664845 41811786919779010937874317)
              ·
                refine ⟨15679420094917129101702869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41811786919779010937874317 15679420094917129101702869)
                ·
                  refine ⟨367486408474620213321161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15679420094917129101702869 367486408474620213321161)
                  ·
                    rfl

theorem cell23_6441095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 7].length) (baseStart_6441095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441095 prefixEnd_6441095 := by exact prefixLift 6441095
  have htrace : WordTrace (prefixWord ++ tailWord_6441095) baseStart_6441095 baseEnd_6441095 := by
    simpa [prefixWord, tailWord_6441095, baseEnd_6441095] using wordTrace_append hprefix tailTrace_6441095
  have hstable : (prefixWord ++ tailWord_6441095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441095).length < 2 ^ (prefixWord ++ tailWord_6441095).sum := by decide
  have hdescent : baseEnd_6441095 < baseStart_6441095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441125 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_6441125 : Nat := 118140960795 + 6441125 * 2 ^ 59
def prefixEnd_6441125 : Nat := 4983230072969 + 3 ^ 40 * 6441125 * 2
def baseEnd_6441125 : Nat := 1102464360230405600838437

theorem tailTrace_6441125 : CollatzResearch.WordTrace tailWord_6441125 prefixEnd_6441125 1102464360230405600838437 := by
  unfold tailWord_6441125
  simp only [CollatzResearch.WordTrace]
  refine ⟨234927128789911656415132829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156618085859941104276755219 234927128789911656415132829)
  ·
    refine ⟨88097673296216871155674811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234927128789911656415132829 88097673296216871155674811)
    ·
      refine ⟨132146509944325306733512217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88097673296216871155674811 132146509944325306733512217)
      ·
        refine ⟨99109882458243980050134163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132146509944325306733512217 99109882458243980050134163)
        ·
          refine ⟨148664823687365970075201245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99109882458243980050134163 148664823687365970075201245)
          ·
            refine ⟨55749308882762238778200467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148664823687365970075201245 55749308882762238778200467)
            ·
              refine ⟨83623963324143358167300701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55749308882762238778200467 83623963324143358167300701)
              ·
                refine ⟨31358986246553759312737763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83623963324143358167300701 31358986246553759312737763)
                ·
                  refine ⟨47038479369830638969106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31358986246553759312737763 47038479369830638969106645)
                  ·
                    refine ⟨1102464360230405600838437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47038479369830638969106645 1102464360230405600838437)
                    ·
                      rfl

theorem cell23_6441125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_6441125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441125 prefixEnd_6441125 := by exact prefixLift 6441125
  have htrace : WordTrace (prefixWord ++ tailWord_6441125) baseStart_6441125 baseEnd_6441125 := by
    simpa [prefixWord, tailWord_6441125, baseEnd_6441125] using wordTrace_append hprefix tailTrace_6441125
  have hstable : (prefixWord ++ tailWord_6441125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441125).length < 2 ^ (prefixWord ++ tailWord_6441125).sum := by decide
  have hdescent : baseEnd_6441125 < baseStart_6441125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441135 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_6441135 : Nat := 118140960795 + 6441135 * 2 ^ 59
def prefixEnd_6441135 : Nat := 4983230072969 + 3 ^ 40 * 6441135 * 2
def baseEnd_6441135 : Nat := 3307398215497761763390265

theorem tailTrace_6441135 : CollatzResearch.WordTrace tailWord_6441135 prefixEnd_6441135 3307398215497761763390265 := by
  unfold tailWord_6441135
  simp only [CollatzResearch.WordTrace]
  refine ⟨234927493519875428122996859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156618329013250285415331239 234927493519875428122996859)
  ·
    refine ⟨352391240279813142184495289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234927493519875428122996859 352391240279813142184495289)
    ·
      refine ⟨264293430209859856638371467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352391240279813142184495289 264293430209859856638371467)
      ·
        refine ⟨396440145314789784957557201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264293430209859856638371467 396440145314789784957557201)
        ·
          refine ⟨297330108986092338718167901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396440145314789784957557201 297330108986092338718167901)
          ·
            refine ⟨111498790869784627019312963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297330108986092338718167901 111498790869784627019312963)
            ·
              refine ⟨167248186304676940528969445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111498790869784627019312963 167248186304676940528969445)
              ·
                refine ⟨31359034932126926349181771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167248186304676940528969445 31359034932126926349181771)
                ·
                  refine ⟨47038552398190389523772657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31359034932126926349181771 47038552398190389523772657)
                  ·
                    refine ⟨35278914298642792142829493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47038552398190389523772657 35278914298642792142829493)
                    ·
                      refine ⟨3307398215497761763390265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35278914298642792142829493 3307398215497761763390265)
                      ·
                        rfl

theorem cell23_6441135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_6441135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441135 prefixEnd_6441135 := by exact prefixLift 6441135
  have htrace : WordTrace (prefixWord ++ tailWord_6441135) baseStart_6441135 baseEnd_6441135 := by
    simpa [prefixWord, tailWord_6441135, baseEnd_6441135] using wordTrace_append hprefix tailTrace_6441135
  have hstable : (prefixWord ++ tailWord_6441135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441135).length < 2 ^ (prefixWord ++ tailWord_6441135).sum := by decide
  have hdescent : baseEnd_6441135 < baseStart_6441135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441152 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_6441152 : Nat := 118140960795 + 6441152 * 2 ^ 59
def prefixEnd_6441152 : Nat := 4983230072969 + 3 ^ 40 * 6441152 * 2
def baseEnd_6441152 : Nat := 3307406944668888196877687

theorem tailTrace_6441152 : CollatzResearch.WordTrace tailWord_6441152 prefixEnd_6441152 3307406944668888196877687 := by
  unfold tailWord_6441152
  simp only [CollatzResearch.WordTrace]
  refine ⟨117464056780406920013182855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156618742373875893350910473 117464056780406920013182855)
  ·
    refine ⟨176196085170610380019774283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117464056780406920013182855 176196085170610380019774283)
    ·
      refine ⟨264294127755915570029661425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176196085170610380019774283 264294127755915570029661425)
      ·
        refine ⟨198220595816936677522246069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264294127755915570029661425 198220595816936677522246069)
        ·
          refine ⟨18583180857837813517710569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198220595816936677522246069 18583180857837813517710569)
          ·
            refine ⟨13937385643378360138282927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18583180857837813517710569 13937385643378360138282927)
            ·
              refine ⟨20906078465067540207424391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13937385643378360138282927 20906078465067540207424391)
              ·
                refine ⟨31359117697601310311136587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20906078465067540207424391 31359117697601310311136587)
                ·
                  refine ⟨47038676546401965466704881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31359117697601310311136587 47038676546401965466704881)
                  ·
                    refine ⟨35279007409801474100028661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47038676546401965466704881 35279007409801474100028661)
                    ·
                      refine ⟨3307406944668888196877687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35279007409801474100028661 3307406944668888196877687)
                      ·
                        rfl

theorem cell23_6441152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_6441152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441152 prefixEnd_6441152 := by exact prefixLift 6441152
  have htrace : WordTrace (prefixWord ++ tailWord_6441152) baseStart_6441152 baseEnd_6441152 := by
    simpa [prefixWord, tailWord_6441152, baseEnd_6441152] using wordTrace_append hprefix tailTrace_6441152
  have hstable : (prefixWord ++ tailWord_6441152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441152).length < 2 ^ (prefixWord ++ tailWord_6441152).sum := by decide
  have hdescent : baseEnd_6441152 < baseStart_6441152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441162 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_6441162 : Nat := 118140960795 + 6441162 * 2 ^ 59
def prefixEnd_6441162 : Nat := 4983230072969 + 3 ^ 40 * 6441162 * 2
def baseEnd_6441162 : Nat := 3307412079475433157752641

theorem tailTrace_6441162 : CollatzResearch.WordTrace tailWord_6441162 prefixEnd_6441162 3307412079475433157752641 := by
  unfold tailWord_6441162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58732119572694402933557435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156618985527185074489486493 58732119572694402933557435)
  ·
    refine ⟨88098179359041604400336153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58732119572694402933557435 88098179359041604400336153)
    ·
      refine ⟨66073634519281203300252115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88098179359041604400336153 66073634519281203300252115)
      ·
        refine ⟨99110451778921804950378173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66073634519281203300252115 99110451778921804950378173)
        ·
          refine ⟨37166419417095676856391815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99110451778921804950378173 37166419417095676856391815)
          ·
            refine ⟨55749629125643515284587723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37166419417095676856391815 55749629125643515284587723)
            ·
              refine ⟨83624443688465272926881585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55749629125643515284587723 83624443688465272926881585)
              ·
                refine ⟨62718332766348954695161189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83624443688465272926881585 62718332766348954695161189)
                ·
                  refine ⟨11759687393690429005342723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62718332766348954695161189 11759687393690429005342723)
                  ·
                    refine ⟨17639531090535643508014085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11759687393690429005342723 17639531090535643508014085)
                    ·
                      refine ⟨3307412079475433157752641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17639531090535643508014085 3307412079475433157752641)
                      ·
                        rfl

theorem cell23_6441162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_6441162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441162 prefixEnd_6441162 := by exact prefixLift 6441162
  have htrace : WordTrace (prefixWord ++ tailWord_6441162) baseStart_6441162 baseEnd_6441162 := by
    simpa [prefixWord, tailWord_6441162, baseEnd_6441162] using wordTrace_append hprefix tailTrace_6441162
  have hstable : (prefixWord ++ tailWord_6441162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441162).length < 2 ^ (prefixWord ++ tailWord_6441162).sum := by decide
  have hdescent : baseEnd_6441162 < baseStart_6441162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441175 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_6441175 : Nat := 118140960795 + 6441175 * 2 ^ 59
def prefixEnd_6441175 : Nat := 4983230072969 + 3 ^ 40 * 6441175 * 2
def baseEnd_6441175 : Nat := 3307418754723941606890081

theorem tailTrace_6441175 : CollatzResearch.WordTrace tailWord_6441175 prefixEnd_6441175 3307418754723941606890081 := by
  unfold tailWord_6441175
  simp only [CollatzResearch.WordTrace]
  refine ⟨234928952439730514954452979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156619301626487009969635319 234928952439730514954452979)
  ·
    refine ⟨352393428659595772431679469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234928952439730514954452979 352393428659595772431679469)
    ·
      refine ⟨132147535747348414661879801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352393428659595772431679469 132147535747348414661879801)
      ·
        refine ⟨99110651810511310996409851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132147535747348414661879801 99110651810511310996409851)
        ·
          refine ⟨148665977715766966494614777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99110651810511310996409851 148665977715766966494614777)
          ·
            refine ⟨111499483286825224870961083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148665977715766966494614777 111499483286825224870961083)
            ·
              refine ⟨167249224930237837306441625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111499483286825224870961083 167249224930237837306441625)
              ·
                refine ⟨125436918697678377979831219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167249224930237837306441625 125436918697678377979831219)
                ·
                  refine ⟨188155378046517566969746829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125436918697678377979831219 188155378046517566969746829)
                  ·
                    refine ⟨70558266767444087613655061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188155378046517566969746829 70558266767444087613655061)
                    ·
                      refine ⟨3307418754723941606890081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70558266767444087613655061 3307418754723941606890081)
                      ·
                        rfl

theorem cell23_6441175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_6441175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441175 prefixEnd_6441175 := by exact prefixLift 6441175
  have htrace : WordTrace (prefixWord ++ tailWord_6441175) baseStart_6441175 baseEnd_6441175 := by
    simpa [prefixWord, tailWord_6441175, baseEnd_6441175] using wordTrace_append hprefix tailTrace_6441175
  have hstable : (prefixWord ++ tailWord_6441175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441175).length < 2 ^ (prefixWord ++ tailWord_6441175).sum := by decide
  have hdescent : baseEnd_6441175 < baseStart_6441175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441199 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_6441199 : Nat := 118140960795 + 6441199 * 2 ^ 59
def prefixEnd_6441199 : Nat := 4983230072969 + 3 ^ 40 * 6441199 * 2
def baseEnd_6441199 : Nat := 3307431078259649512989971

theorem tailTrace_6441199 : CollatzResearch.WordTrace tailWord_6441199 prefixEnd_6441199 3307431078259649512989971 := by
  unfold tailWord_6441199
  simp only [CollatzResearch.WordTrace]
  refine ⟨234929827791643567053326651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156619885194429044702217767 234929827791643567053326651)
  ·
    refine ⟨352394741687465350579989977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234929827791643567053326651 352394741687465350579989977)
    ·
      refine ⟨264296056265599012934992483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352394741687465350579989977 264296056265599012934992483)
      ·
        refine ⟨396444084398398519402488725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264296056265599012934992483 396444084398398519402488725)
        ·
          refine ⟨18583316456174930596991659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 396444084398398519402488725 18583316456174930596991659)
          ·
            refine ⟨27874974684262395895487489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18583316456174930596991659 27874974684262395895487489)
            ·
              refine ⟨20906231013196796921615617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27874974684262395895487489 20906231013196796921615617)
              ·
                refine ⟨15679673259897597691211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20906231013196796921615617 15679673259897597691211713)
                ·
                  refine ⟨11759754944923198268408785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15679673259897597691211713 11759754944923198268408785)
                  ·
                    refine ⟨8819816208692398701306589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11759754944923198268408785 8819816208692398701306589)
                    ·
                      refine ⟨3307431078259649512989971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8819816208692398701306589 3307431078259649512989971)
                      ·
                        rfl

theorem cell23_6441199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_6441199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441199 prefixEnd_6441199 := by exact prefixLift 6441199
  have htrace : WordTrace (prefixWord ++ tailWord_6441199) baseStart_6441199 baseEnd_6441199 := by
    simpa [prefixWord, tailWord_6441199, baseEnd_6441199] using wordTrace_append hprefix tailTrace_6441199
  have hstable : (prefixWord ++ tailWord_6441199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441199).length < 2 ^ (prefixWord ++ tailWord_6441199).sum := by decide
  have hdescent : baseEnd_6441199 < baseStart_6441199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441272 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_6441272 : Nat := 118140960795 + 6441272 * 2 ^ 59
def prefixEnd_6441272 : Nat := 4983230072969 + 3 ^ 40 * 6441272 * 2
def baseEnd_6441272 : Nat := 3307468562347427727377135

theorem tailTrace_6441272 : CollatzResearch.WordTrace tailWord_6441272 prefixEnd_6441272 3307468562347427727377135 := by
  unfold tailWord_6441272
  simp only [CollatzResearch.WordTrace]
  refine ⟨117466245160189550260367035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156621660213586067013822713 117466245160189550260367035)
  ·
    refine ⟨176199367740284325390550553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117466245160189550260367035 176199367740284325390550553)
    ·
      refine ⟨132149525805213244042912915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176199367740284325390550553 132149525805213244042912915)
      ·
        refine ⟨198224288707819866064369373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132149525805213244042912915 198224288707819866064369373)
        ·
          refine ⟨74334108265432449774138515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198224288707819866064369373 74334108265432449774138515)
          ·
            refine ⟨111501162398148674661207773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74334108265432449774138515 111501162398148674661207773)
            ·
              refine ⟨41812935899305752997952915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111501162398148674661207773 41812935899305752997952915)
              ·
                refine ⟨62719403848958629496929373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41812935899305752997952915 62719403848958629496929373)
                ·
                  refine ⟨23519776443359486061348515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62719403848958629496929373 23519776443359486061348515)
                  ·
                    refine ⟨35279664665039229092022773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23519776443359486061348515 35279664665039229092022773)
                    ·
                      refine ⟨3307468562347427727377135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35279664665039229092022773 3307468562347427727377135)
                      ·
                        rfl

theorem cell23_6441272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_6441272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441272 prefixEnd_6441272 := by exact prefixLift 6441272
  have htrace : WordTrace (prefixWord ++ tailWord_6441272) baseStart_6441272 baseEnd_6441272 := by
    simpa [prefixWord, tailWord_6441272, baseEnd_6441272] using wordTrace_append hprefix tailTrace_6441272
  have hstable : (prefixWord ++ tailWord_6441272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441272).length < 2 ^ (prefixWord ++ tailWord_6441272).sum := by decide
  have hdescent : baseEnd_6441272 < baseStart_6441272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441292 : List Nat := [2, 2, 1, 3, 2, 1, 3, 9]
def baseStart_6441292 : Nat := 118140960795 + 6441292 * 2 ^ 59
def prefixEnd_6441292 : Nat := 4983230072969 + 3 ^ 40 * 6441292 * 2
def baseEnd_6441292 : Nat := 122499215998537690708409

theorem tailTrace_6441292 : CollatzResearch.WordTrace tailWord_6441292 prefixEnd_6441292 122499215998537690708409 := by
  unfold tailWord_6441292
  simp only [CollatzResearch.WordTrace]
  refine ⟨117466609890153321968231065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156622146520204429290974753 117466609890153321968231065)
  ·
    refine ⟨88099957417614991476173299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117466609890153321968231065 88099957417614991476173299)
    ·
      refine ⟨132149936126422487214259949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88099957417614991476173299 132149936126422487214259949)
      ·
        refine ⟨49556226047408432705347481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132149936126422487214259949 49556226047408432705347481)
        ·
          refine ⟨37167169535556324529010611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49556226047408432705347481 37167169535556324529010611)
          ·
            refine ⟨55750754303334486793515917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37167169535556324529010611 55750754303334486793515917)
            ·
              refine ⟨20906532863750432547568469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55750754303334486793515917 20906532863750432547568469)
              ·
                refine ⟨122499215998537690708409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20906532863750432547568469 122499215998537690708409)
                ·
                  rfl

theorem cell23_6441292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 9].length) (baseStart_6441292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441292 prefixEnd_6441292 := by exact prefixLift 6441292
  have htrace : WordTrace (prefixWord ++ tailWord_6441292) baseStart_6441292 baseEnd_6441292 := by
    simpa [prefixWord, tailWord_6441292, baseEnd_6441292] using wordTrace_append hprefix tailTrace_6441292
  have hstable : (prefixWord ++ tailWord_6441292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441292).length < 2 ^ (prefixWord ++ tailWord_6441292).sum := by decide
  have hdescent : baseEnd_6441292 < baseStart_6441292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441320 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6441320 : Nat := 118140960795 + 6441320 * 2 ^ 59
def prefixEnd_6441320 : Nat := 4983230072969 + 3 ^ 40 * 6441320 * 2
def baseEnd_6441320 : Nat := 3307493209418843539576915

theorem tailTrace_6441320 : CollatzResearch.WordTrace tailWord_6441320 prefixEnd_6441320 3307493209418843539576915 := by
  unfold tailWord_6441320
  simp only [CollatzResearch.WordTrace]
  refine ⟨117467120512102602359240707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156622827349470136478987609 117467120512102602359240707)
  ·
    refine ⟨176200680768153903538861061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117467120512102602359240707 176200680768153903538861061)
    ·
      refine ⟨33037627644028856913536449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176200680768153903538861061 33037627644028856913536449)
      ·
        refine ⟨24778220733021642685152337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33037627644028856913536449 24778220733021642685152337)
        ·
          refine ⟨18583665549766232013864253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24778220733021642685152337 18583665549766232013864253)
          ·
            refine ⟨6968874581162337005199095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18583665549766232013864253 6968874581162337005199095)
            ·
              refine ⟨10453311871743505507798643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968874581162337005199095 10453311871743505507798643)
              ·
                refine ⟨15679967807615258261697965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453311871743505507798643 15679967807615258261697965)
                ·
                  refine ⟨5879987927855721848136737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15679967807615258261697965 5879987927855721848136737)
                  ·
                    refine ⟨4409990945891791386102553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879987927855721848136737 4409990945891791386102553)
                    ·
                      refine ⟨3307493209418843539576915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409990945891791386102553 3307493209418843539576915)
                      ·
                        rfl

theorem cell23_6441320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6441320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441320 prefixEnd_6441320 := by exact prefixLift 6441320
  have htrace : WordTrace (prefixWord ++ tailWord_6441320) baseStart_6441320 baseEnd_6441320 := by
    simpa [prefixWord, tailWord_6441320, baseEnd_6441320] using wordTrace_append hprefix tailTrace_6441320
  have hstable : (prefixWord ++ tailWord_6441320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441320).length < 2 ^ (prefixWord ++ tailWord_6441320).sum := by decide
  have hdescent : baseEnd_6441320 < baseStart_6441320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441329 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_6441329 : Nat := 118140960795 + 6441329 * 2 ^ 59
def prefixEnd_6441329 : Nat := 4983230072969 + 3 ^ 40 * 6441329 * 2
def baseEnd_6441329 : Nat := 3307497830744734004364373

theorem tailTrace_6441329 : CollatzResearch.WordTrace tailWord_6441329 prefixEnd_6441329 3307497830744734004364373 := by
  unfold tailWord_6441329
  simp only [CollatzResearch.WordTrace]
  refine ⟨234934569281172599255559041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156623046187448399503706027 234934569281172599255559041)
  ·
    refine ⟨176200926960879449441669281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234934569281172599255559041 176200926960879449441669281)
    ·
      refine ⟨132150695220659587081251961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176200926960879449441669281 132150695220659587081251961)
      ·
        refine ⟨99113021415494690310938971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132150695220659587081251961 99113021415494690310938971)
        ·
          refine ⟨148669532123242035466408457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99113021415494690310938971 148669532123242035466408457)
          ·
            refine ⟨111502149092431526599806343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148669532123242035466408457 111502149092431526599806343)
            ·
              refine ⟨167253223638647289899709515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111502149092431526599806343 167253223638647289899709515)
              ·
                refine ⟨250879835457970934849564273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167253223638647289899709515 250879835457970934849564273)
                ·
                  refine ⟨188159876593478201137173205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250879835457970934849564273 188159876593478201137173205)
                  ·
                    refine ⟨4409997107659645339152497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188159876593478201137173205 4409997107659645339152497)
                    ·
                      refine ⟨3307497830744734004364373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4409997107659645339152497 3307497830744734004364373)
                      ·
                        rfl

theorem cell23_6441329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_6441329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441329 prefixEnd_6441329 := by exact prefixLift 6441329
  have htrace : WordTrace (prefixWord ++ tailWord_6441329) baseStart_6441329 baseEnd_6441329 := by
    simpa [prefixWord, tailWord_6441329, baseEnd_6441329] using wordTrace_append hprefix tailTrace_6441329
  have hstable : (prefixWord ++ tailWord_6441329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441329).length < 2 ^ (prefixWord ++ tailWord_6441329).sum := by decide
  have hdescent : baseEnd_6441329 < baseStart_6441329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441379 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3]
def baseStart_6441379 : Nat := 118140960795 + 6441379 * 2 ^ 59
def prefixEnd_6441379 : Nat := 4983230072969 + 3 ^ 40 * 6441379 * 2
def baseEnd_6441379 : Nat := 3307523504777458808739143

theorem tailTrace_6441379 : CollatzResearch.WordTrace tailWord_6441379 prefixEnd_6441379 3307523504777458808739143 := by
  unfold tailWord_6441379
  simp only [CollatzResearch.WordTrace]
  refine ⟨234936392930991457794879191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156624261953994305196586127 234936392930991457794879191)
  ·
    refine ⟨352404589396487186692318787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234936392930991457794879191 352404589396487186692318787)
    ·
      refine ⟨528606884094730780038478181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352404589396487186692318787 528606884094730780038478181)
      ·
        refine ⟨99113790767762021257214659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528606884094730780038478181 99113790767762021257214659)
        ·
          refine ⟨148670686151643031885821989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99113790767762021257214659 148670686151643031885821989)
          ·
            refine ⟨27875753653433068478591623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148670686151643031885821989 27875753653433068478591623)
            ·
              refine ⟨41813630480149602717887435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27875753653433068478591623 41813630480149602717887435)
              ·
                refine ⟨62720445720224404076831153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41813630480149602717887435 62720445720224404076831153)
                ·
                  refine ⟨47040334290168303057623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62720445720224404076831153 47040334290168303057623365)
                  ·
                    refine ⟨8820062679406556823304381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47040334290168303057623365 8820062679406556823304381)
                    ·
                      refine ⟨3307523504777458808739143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8820062679406556823304381 3307523504777458808739143)
                      ·
                        rfl

theorem cell23_6441379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_6441379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441379 prefixEnd_6441379 := by exact prefixLift 6441379
  have htrace : WordTrace (prefixWord ++ tailWord_6441379) baseStart_6441379 baseEnd_6441379 := by
    simpa [prefixWord, tailWord_6441379, baseEnd_6441379] using wordTrace_append hprefix tailTrace_6441379
  have hstable : (prefixWord ++ tailWord_6441379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441379).length < 2 ^ (prefixWord ++ tailWord_6441379).sum := by decide
  have hdescent : baseEnd_6441379 < baseStart_6441379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441392 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_6441392 : Nat := 118140960795 + 6441392 * 2 ^ 59
def prefixEnd_6441392 : Nat := 4983230072969 + 3 ^ 40 * 6441392 * 2
def baseEnd_6441392 : Nat := 3307530180025967257876583

theorem tailTrace_6441392 : CollatzResearch.WordTrace tailWord_6441392 prefixEnd_6441392 3307530180025967257876583 := by
  unfold tailWord_6441392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117468433539972180507551215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156624578053296240676734953 117468433539972180507551215)
  ·
    refine ⟨176202650309958270761326823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117468433539972180507551215 176202650309958270761326823)
    ·
      refine ⟨264303975464937406141990235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176202650309958270761326823 264303975464937406141990235)
      ·
        refine ⟨396455963197406109212985353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264303975464937406141990235 396455963197406109212985353)
        ·
          refine ⟨297341972398054581909739015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396455963197406109212985353 297341972398054581909739015)
          ·
            refine ⟨446012958597081872864608523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297341972398054581909739015 446012958597081872864608523)
            ·
              refine ⟨669019437895622809296912785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446012958597081872864608523 669019437895622809296912785)
              ·
                refine ⟨501764578421717106972684589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669019437895622809296912785 501764578421717106972684589)
                ·
                  refine ⟨188161716908143915114756721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501764578421717106972684589 188161716908143915114756721)
                  ·
                    refine ⟨141121287681107936336067541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188161716908143915114756721 141121287681107936336067541)
                    ·
                      refine ⟨3307530180025967257876583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141121287681107936336067541 3307530180025967257876583)
                      ·
                        rfl

theorem cell23_6441392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_6441392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441392 prefixEnd_6441392 := by exact prefixLift 6441392
  have htrace : WordTrace (prefixWord ++ tailWord_6441392) baseStart_6441392 baseEnd_6441392 := by
    simpa [prefixWord, tailWord_6441392, baseEnd_6441392] using wordTrace_append hprefix tailTrace_6441392
  have hstable : (prefixWord ++ tailWord_6441392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441392).length < 2 ^ (prefixWord ++ tailWord_6441392).sum := by decide
  have hdescent : baseEnd_6441392 < baseStart_6441392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441393 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6441393 : Nat := 118140960795 + 6441393 * 2 ^ 59
def prefixEnd_6441393 : Nat := 4983230072969 + 3 ^ 40 * 6441393 * 2
def baseEnd_6441393 : Nat := 3307530693506621753964079

theorem tailTrace_6441393 : CollatzResearch.WordTrace tailWord_6441393 prefixEnd_6441393 3307530693506621753964079 := by
  unfold tailWord_6441393
  simp only [CollatzResearch.WordTrace]
  refine ⟨234936903552940738185888833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156624602368627158790592555 234936903552940738185888833)
  ·
    refine ⟨176202677664705553639416625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234936903552940738185888833 176202677664705553639416625)
    ·
      refine ⟨132152008248529165229562469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176202677664705553639416625 132152008248529165229562469)
      ·
        refine ⟨24778501546599218480542963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132152008248529165229562469 24778501546599218480542963)
        ·
          refine ⟨37167752319898827720814445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24778501546599218480542963 37167752319898827720814445)
          ·
            refine ⟨13937907119962060395305417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37167752319898827720814445 13937907119962060395305417)
            ·
              refine ⟨10453430339971545296479063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937907119962060395305417 10453430339971545296479063)
              ·
                refine ⟨15680145509957317944718595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453430339971545296479063 15680145509957317944718595)
                ·
                  refine ⟨23520218264935976917077893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15680145509957317944718595 23520218264935976917077893)
                  ·
                    refine ⟨4410040924675495671952105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23520218264935976917077893 4410040924675495671952105)
                    ·
                      refine ⟨3307530693506621753964079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410040924675495671952105 3307530693506621753964079)
                      ·
                        rfl

theorem cell23_6441393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6441393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441393 prefixEnd_6441393 := by exact prefixLift 6441393
  have htrace : WordTrace (prefixWord ++ tailWord_6441393) baseStart_6441393 baseEnd_6441393 := by
    simpa [prefixWord, tailWord_6441393, baseEnd_6441393] using wordTrace_append hprefix tailTrace_6441393
  have hstable : (prefixWord ++ tailWord_6441393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441393).length < 2 ^ (prefixWord ++ tailWord_6441393).sum := by decide
  have hdescent : baseEnd_6441393 < baseStart_6441393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441399 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 7]
def baseStart_6441399 : Nat := 118140960795 + 6441399 * 2 ^ 59
def prefixEnd_6441399 : Nat := 4983230072969 + 3 ^ 40 * 6441399 * 2
def baseEnd_6441399 : Nat := 367503752710060970054339

theorem tailTrace_6441399 : CollatzResearch.WordTrace tailWord_6441399 prefixEnd_6441399 367503752710060970054339 := by
  unfold tailWord_6441399
  simp only [CollatzResearch.WordTrace]
  refine ⟨234937122390919001210607251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156624748260612667473738167 234937122390919001210607251)
  ·
    refine ⟨352405683586378501815910877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234937122390919001210607251 352405683586378501815910877)
    ·
      refine ⟨132152131344891938180966579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352405683586378501815910877 132152131344891938180966579)
      ·
        refine ⟨198228197017337907271449869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132152131344891938180966579 198228197017337907271449869)
        ·
          refine ⟨74335573881501715226793701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198228197017337907271449869 74335573881501715226793701)
          ·
            refine ⟨13937920102781571605023819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74335573881501715226793701 13937920102781571605023819)
            ·
              refine ⟨20906880154172357407535729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13937920102781571605023819 20906880154172357407535729)
              ·
                refine ⟨15680160115629268055651797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20906880154172357407535729 15680160115629268055651797)
                ·
                  refine ⟨367503752710060970054339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15680160115629268055651797 367503752710060970054339)
                  ·
                    rfl

theorem cell23_6441399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 7].length) (baseStart_6441399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441399 prefixEnd_6441399 := by exact prefixLift 6441399
  have htrace : WordTrace (prefixWord ++ tailWord_6441399) baseStart_6441399 baseEnd_6441399 := by
    simpa [prefixWord, tailWord_6441399, baseEnd_6441399] using wordTrace_append hprefix tailTrace_6441399
  have hstable : (prefixWord ++ tailWord_6441399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441399).length < 2 ^ (prefixWord ++ tailWord_6441399).sum := by decide
  have hdescent : baseEnd_6441399 < baseStart_6441399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441416 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 5]
def baseStart_6441416 : Nat := 118140960795 + 6441416 * 2 ^ 59
def prefixEnd_6441416 : Nat := 4983230072969 + 3 ^ 40 * 6441416 * 2
def baseEnd_6441416 : Nat := 367504722617963907108497

theorem tailTrace_6441416 : CollatzResearch.WordTrace tailWord_6441416 prefixEnd_6441416 367504722617963907108497 := by
  unfold tailWord_6441416
  simp only [CollatzResearch.WordTrace]
  refine ⟨117468871215928706556988051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156625161621238275409317401 117468871215928706556988051)
  ·
    refine ⟨176203306823893059835482077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117468871215928706556988051 176203306823893059835482077)
    ·
      refine ⟨66076240058959897438305779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176203306823893059835482077 66076240058959897438305779)
      ·
        refine ⟨99114360088439846157458669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66076240058959897438305779 99114360088439846157458669)
        ·
          refine ⟨37167885033164942309047001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99114360088439846157458669 37167885033164942309047001)
          ·
            refine ⟨27875913774873706731785251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37167885033164942309047001 27875913774873706731785251)
            ·
              refine ⟨41813870662310560097677877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27875913774873706731785251 41813870662310560097677877)
              ·
                refine ⟨3920050374591615009157301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41813870662310560097677877 3920050374591615009157301)
                ·
                  refine ⟨367504722617963907108497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3920050374591615009157301 367504722617963907108497)
                  ·
                    rfl

theorem cell23_6441416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 5].length) (baseStart_6441416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441416 prefixEnd_6441416 := by exact prefixLift 6441416
  have htrace : WordTrace (prefixWord ++ tailWord_6441416) baseStart_6441416 baseEnd_6441416 := by
    simpa [prefixWord, tailWord_6441416, baseEnd_6441416] using wordTrace_append hprefix tailTrace_6441416
  have hstable : (prefixWord ++ tailWord_6441416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441416).length < 2 ^ (prefixWord ++ tailWord_6441416).sum := by decide
  have hdescent : baseEnd_6441416 < baseStart_6441416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_6441449 : Nat := 118140960795 + 6441449 * 2 ^ 59
def prefixEnd_6441449 : Nat := 4983230072969 + 3 ^ 40 * 6441449 * 2
def baseEnd_6441449 : Nat := 3307559448423273534863821

theorem tailTrace_6441449 : CollatzResearch.WordTrace tailWord_6441449 prefixEnd_6441449 3307559448423273534863821 := by
  unfold tailWord_6441449
  simp only [CollatzResearch.WordTrace]
  refine ⟨234938946040737859749927401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156625964027158573166618267 234938946040737859749927401)
  ·
    refine ⟨176204209530553394812445551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234938946040737859749927401 176204209530553394812445551)
    ·
      refine ⟨264306314295830092218668327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176204209530553394812445551 264306314295830092218668327)
      ·
        refine ⟨396459471443745138328002491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264306314295830092218668327 396459471443745138328002491)
        ·
          refine ⟨594689207165617707492003737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396459471443745138328002491 594689207165617707492003737)
          ·
            refine ⟨446016905374213280619002803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594689207165617707492003737 446016905374213280619002803)
            ·
              refine ⟨669025358061319920928504205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446016905374213280619002803 669025358061319920928504205)
              ·
                refine ⟨250884509272994970348189077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669025358061319920928504205 250884509272994970348189077)
                ·
                  refine ⟨11760211372171639235071363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250884509272994970348189077 11760211372171639235071363)
                  ·
                    refine ⟨17640317058257458852607045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11760211372171639235071363 17640317058257458852607045)
                    ·
                      refine ⟨3307559448423273534863821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17640317058257458852607045 3307559448423273534863821)
                      ·
                        rfl

theorem cell23_6441449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_6441449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441449 prefixEnd_6441449 := by exact prefixLift 6441449
  have htrace : WordTrace (prefixWord ++ tailWord_6441449) baseStart_6441449 baseEnd_6441449 := by
    simpa [prefixWord, tailWord_6441449, baseEnd_6441449] using wordTrace_append hprefix tailTrace_6441449
  have hstable : (prefixWord ++ tailWord_6441449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441449).length < 2 ^ (prefixWord ++ tailWord_6441449).sum := by decide
  have hdescent : baseEnd_6441449 < baseStart_6441449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_6441466 : Nat := 118140960795 + 6441466 * 2 ^ 59
def prefixEnd_6441466 : Nat := 4983230072969 + 3 ^ 40 * 6441466 * 2
def baseEnd_6441466 : Nat := 3307568177594399968351243

theorem tailTrace_6441466 : CollatzResearch.WordTrace tailWord_6441466 prefixEnd_6441466 3307568177594399968351243 := by
  unfold tailWord_6441466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58734891520419067913324063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156626377387784181102197501 58734891520419067913324063)
  ·
    refine ⟨88102337280628601869986095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58734891520419067913324063 88102337280628601869986095)
    ·
      refine ⟨132153505920942902804979143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88102337280628601869986095 132153505920942902804979143)
      ·
        refine ⟨198230258881414354207468715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132153505920942902804979143 198230258881414354207468715)
        ·
          refine ⟨297345388322121531311203073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198230258881414354207468715 297345388322121531311203073)
          ·
            refine ⟨223009041241591148483402305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297345388322121531311203073 223009041241591148483402305)
            ·
              refine ⟨167256780931193361362551729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223009041241591148483402305 167256780931193361362551729)
              ·
                refine ⟨125442585698395021021913797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167256780931193361362551729 125442585698395021021913797)
                ·
                  refine ⟨23520484818449066441608837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125442585698395021021913797 23520484818449066441608837)
                  ·
                    refine ⟨4410090903459199957801657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23520484818449066441608837 4410090903459199957801657)
                    ·
                      refine ⟨3307568177594399968351243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410090903459199957801657 3307568177594399968351243)
                      ·
                        rfl

theorem cell23_6441466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_6441466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441466 prefixEnd_6441466 := by exact prefixLift 6441466
  have htrace : WordTrace (prefixWord ++ tailWord_6441466) baseStart_6441466 baseEnd_6441466 := by
    simpa [prefixWord, tailWord_6441466, baseEnd_6441466] using wordTrace_append hprefix tailTrace_6441466
  have hstable : (prefixWord ++ tailWord_6441466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441466).length < 2 ^ (prefixWord ++ tailWord_6441466).sum := by decide
  have hdescent : baseEnd_6441466 < baseStart_6441466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441509 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_6441509 : Nat := 118140960795 + 6441509 * 2 ^ 59
def prefixEnd_6441509 : Nat := 4983230072969 + 3 ^ 40 * 6441509 * 2
def baseEnd_6441509 : Nat := 3307590257262543300113545

theorem tailTrace_6441509 : CollatzResearch.WordTrace tailWord_6441509 prefixEnd_6441509 3307590257262543300113545 := by
  unfold tailWord_6441509
  simp only [CollatzResearch.WordTrace]
  refine ⟨234941134420520489997111581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156627422947013659998074387 234941134420520489997111581)
  ·
    refine ⟨88102925407695183748916843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234941134420520489997111581 88102925407695183748916843)
    ·
      refine ⟨132154388111542775623375265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88102925407695183748916843 132154388111542775623375265)
      ·
        refine ⟨99115791083657081717531449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132154388111542775623375265 99115791083657081717531449)
        ·
          refine ⟨74336843312742811288148587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99115791083657081717531449 74336843312742811288148587)
          ·
            refine ⟨111505264969114216932222881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74336843312742811288148587 111505264969114216932222881)
            ·
              refine ⟨83628948726835662699167161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111505264969114216932222881 83628948726835662699167161)
              ·
                refine ⟨62721711545126747024375371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83628948726835662699167161 62721711545126747024375371)
                ·
                  refine ⟨94082567317690120536563057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62721711545126747024375371 94082567317690120536563057)
                  ·
                    refine ⟨70561925488267590402422293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94082567317690120536563057 70561925488267590402422293)
                    ·
                      refine ⟨3307590257262543300113545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70561925488267590402422293 3307590257262543300113545)
                      ·
                        rfl

theorem cell23_6441509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_6441509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441509 prefixEnd_6441509 := by exact prefixLift 6441509
  have htrace : WordTrace (prefixWord ++ tailWord_6441509) baseStart_6441509 baseEnd_6441509 := by
    simpa [prefixWord, tailWord_6441509, baseEnd_6441509] using wordTrace_append hprefix tailTrace_6441509
  have hstable : (prefixWord ++ tailWord_6441509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441509).length < 2 ^ (prefixWord ++ tailWord_6441509).sum := by decide
  have hdescent : baseEnd_6441509 < baseStart_6441509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441536 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_6441536 : Nat := 118140960795 + 6441536 * 2 ^ 59
def prefixEnd_6441536 : Nat := 4983230072969 + 3 ^ 40 * 6441536 * 2
def baseEnd_6441536 : Nat := 1102534707080071564825307

theorem tailTrace_6441536 : CollatzResearch.WordTrace tailWord_6441536 prefixEnd_6441536 1102534707080071564825307 := by
  unfold tailWord_6441536
  simp only [CollatzResearch.WordTrace]
  refine ⟨117471059595711336804172231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156628079460948449072229641 117471059595711336804172231)
  ·
    refine ⟨176206589393567005206258347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117471059595711336804172231 176206589393567005206258347)
    ·
      refine ⟨264309884090350507809387521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176206589393567005206258347 264309884090350507809387521)
      ·
        refine ⟨198232413067762880857040641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264309884090350507809387521 198232413067762880857040641)
        ·
          refine ⟨148674309800822160642780481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198232413067762880857040641 148674309800822160642780481)
          ·
            refine ⟨111505732350616620482085361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148674309800822160642780481 111505732350616620482085361)
            ·
              refine ⟨83629299262962465361564021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111505732350616620482085361 83629299262962465361564021)
              ·
                refine ⟨7840246805902731127646627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83629299262962465361564021 7840246805902731127646627)
                ·
                  refine ⟨11760370208854096691469941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7840246805902731127646627 11760370208854096691469941)
                  ·
                    refine ⟨1102534707080071564825307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11760370208854096691469941 1102534707080071564825307)
                    ·
                      rfl

theorem cell23_6441536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_6441536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441536 prefixEnd_6441536 := by exact prefixLift 6441536
  have htrace : WordTrace (prefixWord ++ tailWord_6441536) baseStart_6441536 baseEnd_6441536 := by
    simpa [prefixWord, tailWord_6441536, baseEnd_6441536] using wordTrace_append hprefix tailTrace_6441536
  have hstable : (prefixWord ++ tailWord_6441536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441536).length < 2 ^ (prefixWord ++ tailWord_6441536).sum := by decide
  have hdescent : baseEnd_6441536 < baseStart_6441536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441600 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_6441600 : Nat := 118140960795 + 6441600 * 2 ^ 59
def prefixEnd_6441600 : Nat := 4983230072969 + 3 ^ 40 * 6441600 * 2
def baseEnd_6441600 : Nat := 1102545661334034148025209

theorem tailTrace_6441600 : CollatzResearch.WordTrace tailWord_6441600 prefixEnd_6441600 1102545661334034148025209 := by
  unfold tailWord_6441600
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472226731595406269337127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156629635642127208359116169 117472226731595406269337127)
  ·
    refine ⟨176208340097393109404005691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117472226731595406269337127 176208340097393109404005691)
    ·
      refine ⟨264312510146089664106008537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176208340097393109404005691 264312510146089664106008537)
      ·
        refine ⟨198234382609567248079506403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264312510146089664106008537 198234382609567248079506403)
        ·
          refine ⟨297351573914350872119259605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198234382609567248079506403 297351573914350872119259605)
          ·
            refine ⟨6969177513617598565295147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 297351573914350872119259605 6969177513617598565295147)
            ·
              refine ⟨10453766270426397847942721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969177513617598565295147 10453766270426397847942721)
              ·
                refine ⟨7840324702819798385957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10453766270426397847942721 7840324702819798385957041)
                ·
                  refine ⟨5880243527114848789467781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840324702819798385957041 5880243527114848789467781)
                  ·
                    refine ⟨1102545661334034148025209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880243527114848789467781 1102545661334034148025209)
                    ·
                      rfl

theorem cell23_6441600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_6441600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441600 prefixEnd_6441600 := by exact prefixLift 6441600
  have htrace : WordTrace (prefixWord ++ tailWord_6441600) baseStart_6441600 baseEnd_6441600 := by
    simpa [prefixWord, tailWord_6441600, baseEnd_6441600] using wordTrace_append hprefix tailTrace_6441600
  have hstable : (prefixWord ++ tailWord_6441600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441600).length < 2 ^ (prefixWord ++ tailWord_6441600).sum := by decide
  have hdescent : baseEnd_6441600 < baseStart_6441600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441607 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_6441607 : Nat := 118140960795 + 6441607 * 2 ^ 59
def prefixEnd_6441607 : Nat := 4983230072969 + 3 ^ 40 * 6441607 * 2
def baseEnd_6441607 : Nat := 3307640578366683916688095

theorem tailTrace_6441607 : CollatzResearch.WordTrace tailWord_6441607 prefixEnd_6441607 3307640578366683916688095 := by
  unfold tailWord_6441607
  simp only [CollatzResearch.WordTrace]
  refine ⟨234944708774165452734179075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156629805849443635156119383 234944708774165452734179075)
  ·
    refine ⟨352417063161248179101268613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234944708774165452734179075 352417063161248179101268613)
    ·
      refine ⟨66078199342734033581487865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 352417063161248179101268613 66078199342734033581487865)
      ·
        refine ⟨49558649507050525186115899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66078199342734033581487865 49558649507050525186115899)
        ·
          refine ⟨74337974260575787779173849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49558649507050525186115899 74337974260575787779173849)
          ·
            refine ⟨55753480695431840834380387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74337974260575787779173849 55753480695431840834380387)
            ·
              refine ⟨83630221043147761251570581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55753480695431840834380387 83630221043147761251570581)
              ·
                refine ⟨3920166611397551308667371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83630221043147761251570581 3920166611397551308667371)
                ·
                  refine ⟨5880249917096326963001057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920166611397551308667371 5880249917096326963001057)
                  ·
                    refine ⟨4410187437822245222250793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880249917096326963001057 4410187437822245222250793)
                    ·
                      refine ⟨3307640578366683916688095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410187437822245222250793 3307640578366683916688095)
                      ·
                        rfl

theorem cell23_6441607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_6441607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441607 prefixEnd_6441607 := by exact prefixLift 6441607
  have htrace : WordTrace (prefixWord ++ tailWord_6441607) baseStart_6441607 baseEnd_6441607 := by
    simpa [prefixWord, tailWord_6441607, baseEnd_6441607] using wordTrace_append hprefix tailTrace_6441607
  have hstable : (prefixWord ++ tailWord_6441607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441607).length < 2 ^ (prefixWord ++ tailWord_6441607).sum := by decide
  have hdescent : baseEnd_6441607 < baseStart_6441607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441620 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6441620 : Nat := 118140960795 + 6441620 * 2 ^ 59
def prefixEnd_6441620 : Nat := 4983230072969 + 3 ^ 40 * 6441620 * 2
def baseEnd_6441620 : Nat := 3307647253615192365825535

theorem tailTrace_6441620 : CollatzResearch.WordTrace tailWord_6441620 prefixEnd_6441620 3307647253615192365825535 := by
  unfold tailWord_6441620
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472591461559177977201157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156630121948745570636268209 117472591461559177977201157)
  ·
    refine ⟨22026110899042345870725217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117472591461559177977201157 22026110899042345870725217)
    ·
      refine ⟨16519583174281759403043913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22026110899042345870725217 16519583174281759403043913)
      ·
        refine ⟨12389687380711319552282935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16519583174281759403043913 12389687380711319552282935)
        ·
          refine ⟨18584531071066979328424403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12389687380711319552282935 18584531071066979328424403)
          ·
            refine ⟨27876796606600468992636605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18584531071066979328424403 27876796606600468992636605)
            ·
              refine ⟨10453798727475175872238727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27876796606600468992636605 10453798727475175872238727)
              ·
                refine ⟨15680698091212763808358091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453798727475175872238727 15680698091212763808358091)
                ·
                  refine ⟨23521047136819145712537137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15680698091212763808358091 23521047136819145712537137)
                  ·
                    refine ⟨17640785352614359284402853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23521047136819145712537137 17640785352614359284402853)
                    ·
                      refine ⟨3307647253615192365825535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17640785352614359284402853 3307647253615192365825535)
                      ·
                        rfl

theorem cell23_6441620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6441620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441620 prefixEnd_6441620 := by exact prefixLift 6441620
  have htrace : WordTrace (prefixWord ++ tailWord_6441620) baseStart_6441620 baseEnd_6441620 := by
    simpa [prefixWord, tailWord_6441620, baseEnd_6441620] using wordTrace_append hprefix tailTrace_6441620
  have hstable : (prefixWord ++ tailWord_6441620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441620).length < 2 ^ (prefixWord ++ tailWord_6441620).sum := by decide
  have hdescent : baseEnd_6441620 < baseStart_6441620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441636 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6441636 : Nat := 118140960795 + 6441636 * 2 ^ 59
def prefixEnd_6441636 : Nat := 4983230072969 + 3 ^ 40 * 6441636 * 2
def baseEnd_6441636 : Nat := 3307655469305664303225461

theorem tailTrace_6441636 : CollatzResearch.WordTrace tailWord_6441636 prefixEnd_6441636 3307655469305664303225461 := by
  unfold tailWord_6441636
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472883245530195343492381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156630510994040260457989841 117472883245530195343492381)
  ·
    refine ⟨44052331217073823253809643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117472883245530195343492381 44052331217073823253809643)
    ·
      refine ⟨66078496825610734880714465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44052331217073823253809643 66078496825610734880714465)
      ·
        refine ⟨49558872619208051160535849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66078496825610734880714465 49558872619208051160535849)
        ·
          refine ⟨37169154464406038370401887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49558872619208051160535849 37169154464406038370401887)
          ·
            refine ⟨55753731696609057555602831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37169154464406038370401887 55753731696609057555602831)
            ·
              refine ⟨83630597544913586333404247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55753731696609057555602831 83630597544913586333404247)
              ·
                refine ⟨125445896317370379500106371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83630597544913586333404247 125445896317370379500106371)
                ·
                  refine ⟨188168844476055569250159557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125445896317370379500106371 188168844476055569250159557)
                  ·
                    refine ⟨35281658339260419234404917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188168844476055569250159557 35281658339260419234404917)
                    ·
                      refine ⟨3307655469305664303225461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35281658339260419234404917 3307655469305664303225461)
                      ·
                        rfl

theorem cell23_6441636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6441636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441636 prefixEnd_6441636 := by exact prefixLift 6441636
  have htrace : WordTrace (prefixWord ++ tailWord_6441636) baseStart_6441636 baseEnd_6441636 := by
    simpa [prefixWord, tailWord_6441636, baseEnd_6441636] using wordTrace_append hprefix tailTrace_6441636
  have hstable : (prefixWord ++ tailWord_6441636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441636).length < 2 ^ (prefixWord ++ tailWord_6441636).sum := by decide
  have hdescent : baseEnd_6441636 < baseStart_6441636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441674 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_6441674 : Nat := 118140960795 + 6441674 * 2 ^ 59
def prefixEnd_6441674 : Nat := 4983230072969 + 3 ^ 40 * 6441674 * 2
def baseEnd_6441674 : Nat := 3307674981570535154550287

theorem tailTrace_6441674 : CollatzResearch.WordTrace tailWord_6441674 prefixEnd_6441674 3307674981570535154550287 := by
  unfold tailWord_6441674
  simp only [CollatzResearch.WordTrace]
  refine ⟨58736788116230680794217019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156631434976615148784578717 58736788116230680794217019)
  ·
    refine ⟨88105182174346021191325529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58736788116230680794217019 88105182174346021191325529)
    ·
      refine ⟨66078886630759515893494147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88105182174346021191325529 66078886630759515893494147)
      ·
        refine ⟨99118329946139273840241221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66078886630759515893494147 99118329946139273840241221)
        ·
          refine ⟨18584686864901113845045229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99118329946139273840241221 18584686864901113845045229)
          ·
            refine ⟨6969257574337917691891961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18584686864901113845045229 6969257574337917691891961)
            ·
              refine ⟨5226943180753438268918971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969257574337917691891961 5226943180753438268918971)
              ·
                refine ⟨7840414771130157403378457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226943180753438268918971 7840414771130157403378457)
                ·
                  refine ⟨5880311078347618052533843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840414771130157403378457 5880311078347618052533843)
                  ·
                    refine ⟨8820466617521427078800765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5880311078347618052533843 8820466617521427078800765)
                    ·
                      refine ⟨3307674981570535154550287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8820466617521427078800765 3307674981570535154550287)
                      ·
                        rfl

theorem cell23_6441674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_6441674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441674 prefixEnd_6441674 := by exact prefixLift 6441674
  have htrace : WordTrace (prefixWord ++ tailWord_6441674) baseStart_6441674 baseEnd_6441674 := by
    simpa [prefixWord, tailWord_6441674, baseEnd_6441674] using wordTrace_append hprefix tailTrace_6441674
  have hstable : (prefixWord ++ tailWord_6441674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441674).length < 2 ^ (prefixWord ++ tailWord_6441674).sum := by decide
  have hdescent : baseEnd_6441674 < baseStart_6441674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441713 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_6441713 : Nat := 118140960795 + 6441713 * 2 ^ 59
def prefixEnd_6441713 : Nat := 4983230072969 + 3 ^ 40 * 6441713 * 2
def baseEnd_6441713 : Nat := 3307695007316060501962607

theorem tailTrace_6441713 : CollatzResearch.WordTrace tailWord_6441713 prefixEnd_6441713 3307695007316060501962607 := by
  unfold tailWord_6441713
  simp only [CollatzResearch.WordTrace]
  refine ⟨234948574911781432837537793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156632383274520955225025195 234948574911781432837537793)
  ·
    refine ⟨176211431183836074628153345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234948574911781432837537793 176211431183836074628153345)
    ·
      refine ⟨132158573387877055971115009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176211431183836074628153345 132158573387877055971115009)
      ·
        refine ⟨99118930040907791978336257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132158573387877055971115009 99118930040907791978336257)
        ·
          refine ⟨74339197530680843983752193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99118930040907791978336257 74339197530680843983752193)
          ·
            refine ⟨55754398148010632987814145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74339197530680843983752193 55754398148010632987814145)
            ·
              refine ⟨41815798611007974740860609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55754398148010632987814145 41815798611007974740860609)
              ·
                refine ⟨31361848958255981055645457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41815798611007974740860609 31361848958255981055645457)
                ·
                  refine ⟨23521386718691985791734093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31361848958255981055645457 23521386718691985791734093)
                  ·
                    refine ⟨8820520019509494671900285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23521386718691985791734093 8820520019509494671900285)
                    ·
                      refine ⟨3307695007316060501962607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8820520019509494671900285 3307695007316060501962607)
                      ·
                        rfl

theorem cell23_6441713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_6441713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441713 prefixEnd_6441713 := by exact prefixLift 6441713
  have htrace : WordTrace (prefixWord ++ tailWord_6441713) baseStart_6441713 baseEnd_6441713 := by
    simpa [prefixWord, tailWord_6441713, baseEnd_6441713] using wordTrace_append hprefix tailTrace_6441713
  have hstable : (prefixWord ++ tailWord_6441713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441713).length < 2 ^ (prefixWord ++ tailWord_6441713).sum := by decide
  have hdescent : baseEnd_6441713 < baseStart_6441713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441714 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6441714 : Nat := 118140960795 + 6441714 * 2 ^ 59
def prefixEnd_6441714 : Nat := 4983230072969 + 3 ^ 40 * 6441714 * 2
def baseEnd_6441714 : Nat := 3307695520796714998050103

theorem tailTrace_6441714 : CollatzResearch.WordTrace tailWord_6441714 prefixEnd_6441714 3307695520796714998050103 := by
  unfold tailWord_6441714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58737152846194452502081049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156632407589851873338882797 58737152846194452502081049)
  ·
    refine ⟨44052864634645839376560787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58737152846194452502081049 44052864634645839376560787)
    ·
      refine ⟨66079296951968759064841181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44052864634645839376560787 66079296951968759064841181)
      ·
        refine ⟨24779736356988284649315443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66079296951968759064841181 24779736356988284649315443)
        ·
          refine ⟨37169604535482426973973165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24779736356988284649315443 37169604535482426973973165)
          ·
            refine ⟨13938601700805910115239937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37169604535482426973973165 13938601700805910115239937)
            ·
              refine ⟨10453951275604432586429953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13938601700805910115239937 10453951275604432586429953)
              ·
                refine ⟨7840463456703324439822465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10453951275604432586429953 7840463456703324439822465)
                ·
                  refine ⟨5880347592527493329866849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840463456703324439822465 5880347592527493329866849)
                  ·
                    refine ⟨4410260694395619997400137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880347592527493329866849 4410260694395619997400137)
                    ·
                      refine ⟨3307695520796714998050103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410260694395619997400137 3307695520796714998050103)
                      ·
                        rfl

theorem cell23_6441714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6441714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441714 prefixEnd_6441714 := by exact prefixLift 6441714
  have htrace : WordTrace (prefixWord ++ tailWord_6441714) baseStart_6441714 baseEnd_6441714 := by
    simpa [prefixWord, tailWord_6441714, baseEnd_6441714] using wordTrace_append hprefix tailTrace_6441714
  have hstable : (prefixWord ++ tailWord_6441714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441714).length < 2 ^ (prefixWord ++ tailWord_6441714).sum := by decide
  have hdescent : baseEnd_6441714 < baseStart_6441714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441730 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_6441730 : Nat := 118140960795 + 6441730 * 2 ^ 59
def prefixEnd_6441730 : Nat := 4983230072969 + 3 ^ 40 * 6441730 * 2
def baseEnd_6441730 : Nat := 3307703736487186935450029

theorem tailTrace_6441730 : CollatzResearch.WordTrace tailWord_6441730 prefixEnd_6441730 3307703736487186935450029 := by
  unfold tailWord_6441730
  simp only [CollatzResearch.WordTrace]
  refine ⟨58737298738179961185226661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156632796635146563160604429 58737298738179961185226661)
  ·
    refine ⟨11013243513408742722229999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58737298738179961185226661 11013243513408742722229999)
    ·
      refine ⟨16519865270113114083344999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11013243513408742722229999 16519865270113114083344999)
      ·
        refine ⟨24779797905169671125017499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16519865270113114083344999 24779797905169671125017499)
        ·
          refine ⟨37169696857754506687526249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24779797905169671125017499 37169696857754506687526249)
          ·
            refine ⟨27877272643315880015644687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37169696857754506687526249 27877272643315880015644687)
            ·
              refine ⟨41815908964973820023467031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27877272643315880015644687 41815908964973820023467031)
              ·
                refine ⟨62723863447460730035200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41815908964973820023467031 62723863447460730035200547)
                ·
                  refine ⟨94085795171191095052800821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62723863447460730035200547 94085795171191095052800821)
                  ·
                    refine ⟨8820543297299165161200077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94085795171191095052800821 8820543297299165161200077)
                    ·
                      refine ⟨3307703736487186935450029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8820543297299165161200077 3307703736487186935450029)
                      ·
                        rfl

theorem cell23_6441730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_6441730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441730 prefixEnd_6441730 := by exact prefixLift 6441730
  have htrace : WordTrace (prefixWord ++ tailWord_6441730) baseStart_6441730 baseEnd_6441730 := by
    simpa [prefixWord, tailWord_6441730, baseEnd_6441730] using wordTrace_append hprefix tailTrace_6441730
  have hstable : (prefixWord ++ tailWord_6441730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441730).length < 2 ^ (prefixWord ++ tailWord_6441730).sum := by decide
  have hdescent : baseEnd_6441730 < baseStart_6441730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441753 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_6441753 : Nat := 118140960795 + 6441753 * 2 ^ 59
def prefixEnd_6441753 : Nat := 4983230072969 + 3 ^ 40 * 6441753 * 2
def baseEnd_6441753 : Nat := 3307715546542240345462423

theorem tailTrace_6441753 : CollatzResearch.WordTrace tailWord_6441753 prefixEnd_6441753 3307715546542240345462423 := by
  unfold tailWord_6441753
  simp only [CollatzResearch.WordTrace]
  refine ⟨234950033831636519668993913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156633355887757679779329275 234950033831636519668993913)
  ·
    refine ⟨176212525373727389751745435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234950033831636519668993913 176212525373727389751745435)
    ·
      refine ⟨264318788060591084627618153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176212525373727389751745435 264318788060591084627618153)
      ·
        refine ⟨198239091045443313470713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264318788060591084627618153 198239091045443313470713615)
        ·
          refine ⟨297358636568164970206070423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198239091045443313470713615 297358636568164970206070423)
          ·
            refine ⟨446037954852247455309105635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297358636568164970206070423 446037954852247455309105635)
            ·
              refine ⟨669056932278371182963658453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446037954852247455309105635 669056932278371182963658453)
              ·
                refine ⟨15681021850274324600710745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 669056932278371182963658453 15681021850274324600710745)
                ·
                  refine ⟨11760766387705743450533059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15681021850274324600710745 11760766387705743450533059)
                  ·
                    refine ⟨17641149581558615175799589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11760766387705743450533059 17641149581558615175799589)
                    ·
                      refine ⟨3307715546542240345462423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17641149581558615175799589 3307715546542240345462423)
                      ·
                        rfl

theorem cell23_6441753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_6441753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441753 prefixEnd_6441753 := by exact prefixLift 6441753
  have htrace : WordTrace (prefixWord ++ tailWord_6441753) baseStart_6441753 baseEnd_6441753 := by
    simpa [prefixWord, tailWord_6441753, baseEnd_6441753] using wordTrace_append hprefix tailTrace_6441753
  have hstable : (prefixWord ++ tailWord_6441753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441753).length < 2 ^ (prefixWord ++ tailWord_6441753).sum := by decide
  have hdescent : baseEnd_6441753 < baseStart_6441753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441763 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 7, 4]
def baseStart_6441763 : Nat := 118140960795 + 6441763 * 2 ^ 59
def prefixEnd_6441763 : Nat := 4983230072969 + 3 ^ 40 * 6441763 * 2
def baseEnd_6441763 : Nat := 1102573560449595102112459

theorem tailTrace_6441763 : CollatzResearch.WordTrace tailWord_6441763 prefixEnd_6441763 1102573560449595102112459 := by
  unfold tailWord_6441763
  simp only [CollatzResearch.WordTrace]
  refine ⟨234950398561600291376857943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156633599041066860917905295 234950398561600291376857943)
  ·
    refine ⟨352425597842400437065286915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234950398561600291376857943 352425597842400437065286915)
    ·
      refine ⟨528638396763600655597930373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352425597842400437065286915 528638396763600655597930373)
      ·
        refine ⟨99119699393175122924611945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528638396763600655597930373 99119699393175122924611945)
        ·
          refine ⟨74339774544881342193458959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99119699393175122924611945 74339774544881342193458959)
          ·
            refine ⟨111509661817322013290188439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74339774544881342193458959 111509661817322013290188439)
            ·
              refine ⟨167264492725983019935282659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111509661817322013290188439 167264492725983019935282659)
              ·
                refine ⟨250896739088974529902923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167264492725983019935282659 250896739088974529902923989)
                ·
                  refine ⟨5880392322397840544599781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250896739088974529902923989 5880392322397840544599781)
                  ·
                    refine ⟨1102573560449595102112459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880392322397840544599781 1102573560449595102112459)
                    ·
                      rfl

theorem cell23_6441763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 4].length) (baseStart_6441763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441763 prefixEnd_6441763 := by exact prefixLift 6441763
  have htrace : WordTrace (prefixWord ++ tailWord_6441763) baseStart_6441763 baseEnd_6441763 := by
    simpa [prefixWord, tailWord_6441763, baseEnd_6441763] using wordTrace_append hprefix tailTrace_6441763
  have hstable : (prefixWord ++ tailWord_6441763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441763).length < 2 ^ (prefixWord ++ tailWord_6441763).sum := by decide
  have hdescent : baseEnd_6441763 < baseStart_6441763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441864 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6441864 : Nat := 118140960795 + 6441864 * 2 ^ 59
def prefixEnd_6441864 : Nat := 4983230072969 + 3 ^ 40 * 6441864 * 2
def baseEnd_6441864 : Nat := 3307772542894889411174413

theorem tailTrace_6441864 : CollatzResearch.WordTrace tailWord_6441864 prefixEnd_6441864 3307772542894889411174413 := by
  unfold tailWord_6441864
  simp only [CollatzResearch.WordTrace]
  refine ⟨117477041167117192813142323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156636054889489590417523097 117477041167117192813142323)
  ·
    refine ⟨176215561750675789219713485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117477041167117192813142323 176215561750675789219713485)
    ·
      refine ⟨66080835656503420957392557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176215561750675789219713485 66080835656503420957392557)
      ·
        refine ⟨24780313371188782859022209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66080835656503420957392557 24780313371188782859022209)
        ·
          refine ⟨18585235028391587144266657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24780313371188782859022209 18585235028391587144266657)
          ·
            refine ⟨13938926271293690358199993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18585235028391587144266657 13938926271293690358199993)
            ·
              refine ⟨10454194703470267768649995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13938926271293690358199993 10454194703470267768649995)
              ·
                refine ⟨15681292055205401652974993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10454194703470267768649995 15681292055205401652974993)
                ·
                  refine ⟨11760969041404051239731245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15681292055205401652974993 11760969041404051239731245)
                  ·
                    refine ⟨4410363390526519214899217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11760969041404051239731245 4410363390526519214899217)
                    ·
                      refine ⟨3307772542894889411174413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410363390526519214899217 3307772542894889411174413)
                      ·
                        rfl

theorem cell23_6441864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6441864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441864 prefixEnd_6441864 := by exact prefixLift 6441864
  have htrace : WordTrace (prefixWord ++ tailWord_6441864) baseStart_6441864 baseEnd_6441864 := by
    simpa [prefixWord, tailWord_6441864, baseEnd_6441864] using wordTrace_append hprefix tailTrace_6441864
  have hstable : (prefixWord ++ tailWord_6441864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441864).length < 2 ^ (prefixWord ++ tailWord_6441864).sum := by decide
  have hdescent : baseEnd_6441864 < baseStart_6441864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441887 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 2, 4]
def baseStart_6441887 : Nat := 118140960795 + 6441887 * 2 ^ 59
def prefixEnd_6441887 : Nat := 4983230072969 + 3 ^ 40 * 6441887 * 2
def baseEnd_6441887 : Nat := 1102594784316647607062269

theorem tailTrace_6441887 : CollatzResearch.WordTrace tailWord_6441887 prefixEnd_6441887 1102594784316647607062269 := by
  unfold tailWord_6441887
  simp only [CollatzResearch.WordTrace]
  refine ⟨234954921213151060554371915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156636614142100707036247943 234954921213151060554371915)
  ·
    refine ⟨352432381819726590831557873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234954921213151060554371915 352432381819726590831557873)
    ·
      refine ⟨264324286364794943123668405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352432381819726590831557873 264324286364794943123668405)
      ·
        refine ⟨24780401846699525917843913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264324286364794943123668405 24780401846699525917843913)
        ·
          refine ⟨18585301385024644438382935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24780401846699525917843913 18585301385024644438382935)
          ·
            refine ⟨27877952077536966657574403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585301385024644438382935 27877952077536966657574403)
            ·
              refine ⟨41816928116305449986361605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27877952077536966657574403 41816928116305449986361605)
              ·
                refine ⟨7840674021807271872442801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41816928116305449986361605 7840674021807271872442801)
                ·
                  refine ⟨5880505516355453904332101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840674021807271872442801 5880505516355453904332101)
                  ·
                    refine ⟨1102594784316647607062269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880505516355453904332101 1102594784316647607062269)
                    ·
                      rfl

theorem cell23_6441887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_6441887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441887 prefixEnd_6441887 := by exact prefixLift 6441887
  have htrace : WordTrace (prefixWord ++ tailWord_6441887) baseStart_6441887 baseEnd_6441887 := by
    simpa [prefixWord, tailWord_6441887, baseEnd_6441887] using wordTrace_append hprefix tailTrace_6441887
  have hstable : (prefixWord ++ tailWord_6441887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441887).length < 2 ^ (prefixWord ++ tailWord_6441887).sum := by decide
  have hdescent : baseEnd_6441887 < baseStart_6441887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441917 : List Nat := [1, 4, 1, 2, 4, 1, 3, 7]
def baseStart_6441917 : Nat := 118140960795 + 6441917 * 2 ^ 59
def prefixEnd_6441917 : Nat := 4983230072969 + 3 ^ 40 * 6441917 * 2
def baseEnd_6441917 : Nat := 122511102124799174215247

theorem tailTrace_6441917 : CollatzResearch.WordTrace tailWord_6441917 prefixEnd_6441917 122511102124799174215247 := by
  unfold tailWord_6441917
  simp only [CollatzResearch.WordTrace]
  refine ⟨234956015403042375677964005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156637343602028250451976003 234956015403042375677964005)
  ·
    refine ⟨44054252888070445439618251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234956015403042375677964005 44054252888070445439618251)
    ·
      refine ⟨66081379332105668159427377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44054252888070445439618251 66081379332105668159427377)
      ·
        refine ⟨49561034499079251119570533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66081379332105668159427377 49561034499079251119570533)
        ·
          refine ⟨9292693968577359584919475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49561034499079251119570533 9292693968577359584919475)
          ·
            refine ⟨13939040952866039377379213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9292693968577359584919475 13939040952866039377379213)
            ·
              refine ⟨5227140357324764766517205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13939040952866039377379213 5227140357324764766517205)
              ·
                refine ⟨122511102124799174215247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5227140357324764766517205 122511102124799174215247)
                ·
                  rfl

theorem cell23_6441917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 7].length) (baseStart_6441917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441917 prefixEnd_6441917 := by exact prefixLift 6441917
  have htrace : WordTrace (prefixWord ++ tailWord_6441917) baseStart_6441917 baseEnd_6441917 := by
    simpa [prefixWord, tailWord_6441917, baseEnd_6441917] using wordTrace_append hprefix tailTrace_6441917
  have hstable : (prefixWord ++ tailWord_6441917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441917).length < 2 ^ (prefixWord ++ tailWord_6441917).sum := by decide
  have hdescent : baseEnd_6441917 < baseStart_6441917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441923 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_6441923 : Nat := 118140960795 + 6441923 * 2 ^ 59
def prefixEnd_6441923 : Nat := 4983230072969 + 3 ^ 40 * 6441923 * 2
def baseEnd_6441923 : Nat := 3307802838253504680336641

theorem tailTrace_6441923 : CollatzResearch.WordTrace tailWord_6441923 prefixEnd_6441923 3307802838253504680336641 := by
  unfold tailWord_6441923
  simp only [CollatzResearch.WordTrace]
  refine ⟨234956234241020638702682423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156637489494013759135121615 234956234241020638702682423)
  ·
    refine ⟨352434351361530958054023635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234956234241020638702682423 352434351361530958054023635)
    ·
      refine ⟨528651527042296437081035453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352434351361530958054023635 528651527042296437081035453)
      ·
        refine ⟨198244322640861163905388295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 528651527042296437081035453 198244322640861163905388295)
        ·
          refine ⟨297366483961291745858082443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198244322640861163905388295 297366483961291745858082443)
          ·
            refine ⟨446049725941937618787123665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297366483961291745858082443 446049725941937618787123665)
            ·
              refine ⟨334537294456453214090342749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446049725941937618787123665 334537294456453214090342749)
              ·
                refine ⟨125451485421169955283878531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334537294456453214090342749 125451485421169955283878531)
                ·
                  refine ⟨188177228131754932925817797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125451485421169955283878531 188177228131754932925817797)
                  ·
                    refine ⟨35283230274704049923590837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188177228131754932925817797 35283230274704049923590837)
                    ·
                      refine ⟨3307802838253504680336641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35283230274704049923590837 3307802838253504680336641)
                      ·
                        rfl

theorem cell23_6441923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_6441923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441923 prefixEnd_6441923 := by exact prefixLift 6441923
  have htrace : WordTrace (prefixWord ++ tailWord_6441923) baseStart_6441923 baseEnd_6441923 := by
    simpa [prefixWord, tailWord_6441923, baseEnd_6441923] using wordTrace_append hprefix tailTrace_6441923
  have hstable : (prefixWord ++ tailWord_6441923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441923).length < 2 ^ (prefixWord ++ tailWord_6441923).sum := by decide
  have hdescent : baseEnd_6441923 < baseStart_6441923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441928 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_6441928 : Nat := 118140960795 + 6441928 * 2 ^ 59
def prefixEnd_6441928 : Nat := 4983230072969 + 3 ^ 40 * 6441928 * 2
def baseEnd_6441928 : Nat := 3307805405656777160774119

theorem tailTrace_6441928 : CollatzResearch.WordTrace tailWord_6441928 prefixEnd_6441928 3307805405656777160774119 := by
  unfold tailWord_6441928
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478208303001262278307219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156637611070668349704409625 117478208303001262278307219)
  ·
    refine ⟨176217312454501893417460829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117478208303001262278307219 176217312454501893417460829)
    ·
      refine ⟨66081492170438210031547811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176217312454501893417460829 66081492170438210031547811)
      ·
        refine ⟨99122238255657315047321717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66081492170438210031547811 99122238255657315047321717)
        ·
          refine ⟨9292709836467873285686411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99122238255657315047321717 9292709836467873285686411)
          ·
            refine ⟨13939064754701809928529617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9292709836467873285686411 13939064754701809928529617)
            ·
              refine ⟨10454298566026357446397213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13939064754701809928529617 10454298566026357446397213)
              ·
                refine ⟨3920361962259884042398955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10454298566026357446397213 3920361962259884042398955)
                ·
                  refine ⟨5880542943389826063598433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920361962259884042398955 5880542943389826063598433)
                  ·
                    refine ⟨4410407207542369547698825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880542943389826063598433 4410407207542369547698825)
                    ·
                      refine ⟨3307805405656777160774119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410407207542369547698825 3307805405656777160774119)
                      ·
                        rfl

theorem cell23_6441928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_6441928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441928 prefixEnd_6441928 := by exact prefixLift 6441928
  have htrace : WordTrace (prefixWord ++ tailWord_6441928) baseStart_6441928 baseEnd_6441928 := by
    simpa [prefixWord, tailWord_6441928, baseEnd_6441928] using wordTrace_append hprefix tailTrace_6441928
  have hstable : (prefixWord ++ tailWord_6441928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441928).length < 2 ^ (prefixWord ++ tailWord_6441928).sum := by decide
  have hdescent : baseEnd_6441928 < baseStart_6441928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441944 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_6441944 : Nat := 118140960795 + 6441944 * 2 ^ 59
def prefixEnd_6441944 : Nat := 4983230072969 + 3 ^ 40 * 6441944 * 2
def baseEnd_6441944 : Nat := 3307813621347249098174045

theorem tailTrace_6441944 : CollatzResearch.WordTrace tailWord_6441944 prefixEnd_6441944 3307813621347249098174045 := by
  unfold tailWord_6441944
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478500086972279644598443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156638000115963039526131257 117478500086972279644598443)
  ·
    refine ⟨176217750130458419466897665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117478500086972279644598443 176217750130458419466897665)
    ·
      refine ⟨132163312597843814600173249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176217750130458419466897665 132163312597843814600173249)
      ·
        refine ⟨99122484448382860950129937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132163312597843814600173249 99122484448382860950129937)
        ·
          refine ⟨74341863336287145712597453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99122484448382860950129937 74341863336287145712597453)
          ·
            refine ⟨27878198751107679642224045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74341863336287145712597453 27878198751107679642224045)
            ·
              refine ⟨10454324531665379865834017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27878198751107679642224045 10454324531665379865834017)
              ·
                refine ⟨7840743398749034899375513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10454324531665379865834017 7840743398749034899375513)
                ·
                  refine ⟨5880557549061776174531635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840743398749034899375513 5880557549061776174531635)
                  ·
                    refine ⟨8820836323592664261797453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5880557549061776174531635 8820836323592664261797453)
                    ·
                      refine ⟨3307813621347249098174045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8820836323592664261797453 3307813621347249098174045)
                      ·
                        rfl

theorem cell23_6441944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_6441944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441944 prefixEnd_6441944 := by exact prefixLift 6441944
  have htrace : WordTrace (prefixWord ++ tailWord_6441944) baseStart_6441944 baseEnd_6441944 := by
    simpa [prefixWord, tailWord_6441944, baseEnd_6441944] using wordTrace_append hprefix tailTrace_6441944
  have hstable : (prefixWord ++ tailWord_6441944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441944).length < 2 ^ (prefixWord ++ tailWord_6441944).sum := by decide
  have hdescent : baseEnd_6441944 < baseStart_6441944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6441960 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6441960 : Nat := 118140960795 + 6441960 * 2 ^ 59
def prefixEnd_6441960 : Nat := 4983230072969 + 3 ^ 40 * 6441960 * 2
def baseEnd_6441960 : Nat := 1102607279012573678524657

theorem tailTrace_6441960 : CollatzResearch.WordTrace tailWord_6441960 prefixEnd_6441960 1102607279012573678524657 := by
  unfold tailWord_6441960
  simp only [CollatzResearch.WordTrace]
  refine ⟨117478791870943297010889667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156638389161257729347852889 117478791870943297010889667)
  ·
    refine ⟨176218187806414945516334501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117478791870943297010889667 176218187806414945516334501)
    ·
      refine ⟨33040910213702802284312719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176218187806414945516334501 33040910213702802284312719)
      ·
        refine ⟨49561365320554203426469079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33040910213702802284312719 49561365320554203426469079)
        ·
          refine ⟨74342047980831305139703619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49561365320554203426469079 74342047980831305139703619)
          ·
            refine ⟨111513071971246957709555429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74342047980831305139703619 111513071971246957709555429)
            ·
              refine ⟨20908700994608804570541643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111513071971246957709555429 20908700994608804570541643)
              ·
                refine ⟨31363051491913206855812465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20908700994608804570541643 31363051491913206855812465)
                ·
                  refine ⟨23522288618934905141859349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31363051491913206855812465 23522288618934905141859349)
                  ·
                    refine ⟨1102607279012573678524657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23522288618934905141859349 1102607279012573678524657)
                    ·
                      rfl

theorem cell23_6441960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6441960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6441960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6441960 prefixEnd_6441960 := by exact prefixLift 6441960
  have htrace : WordTrace (prefixWord ++ tailWord_6441960) baseStart_6441960 baseEnd_6441960 := by
    simpa [prefixWord, tailWord_6441960, baseEnd_6441960] using wordTrace_append hprefix tailTrace_6441960
  have hstable : (prefixWord ++ tailWord_6441960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6441960).length < 2 ^ (prefixWord ++ tailWord_6441960).sum := by decide
  have hdescent : baseEnd_6441960 < baseStart_6441960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6441960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442007 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 7]
def baseStart_6442007 : Nat := 118140960795 + 6442007 * 2 ^ 59
def prefixEnd_6442007 : Nat := 4983230072969 + 3 ^ 40 * 6442007 * 2
def baseEnd_6442007 : Nat := 367538441180942483520695

theorem tailTrace_6442007 : CollatzResearch.WordTrace tailWord_6442007 prefixEnd_6442007 367538441180942483520695 := by
  unfold tailWord_6442007
  simp only [CollatzResearch.WordTrace]
  refine ⟨234959297972716321048740275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156639531981810880699160183 234959297972716321048740275)
  ·
    refine ⟨352438946959074481573110413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234959297972716321048740275 352438946959074481573110413)
    ·
      refine ⟨132164605109652930589916405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352438946959074481573110413 132164605109652930589916405)
      ·
        refine ⟨12390431729029962242804663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132164605109652930589916405 12390431729029962242804663)
        ·
          refine ⟨18585647593544943364206995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390431729029962242804663 18585647593544943364206995)
          ·
            refine ⟨27878471390317415046310493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585647593544943364206995 27878471390317415046310493)
            ·
              refine ⟨10454426771369030642366435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27878471390317415046310493 10454426771369030642366435)
              ·
                refine ⟨15681640157053545963549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10454426771369030642366435 15681640157053545963549653)
                ·
                  refine ⟨367538441180942483520695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15681640157053545963549653 367538441180942483520695)
                  ·
                    rfl

theorem cell23_6442007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 7].length) (baseStart_6442007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442007 prefixEnd_6442007 := by exact prefixLift 6442007
  have htrace : WordTrace (prefixWord ++ tailWord_6442007) baseStart_6442007 baseEnd_6442007 := by
    simpa [prefixWord, tailWord_6442007, baseEnd_6442007] using wordTrace_append hprefix tailTrace_6442007
  have hstable : (prefixWord ++ tailWord_6442007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442007).length < 2 ^ (prefixWord ++ tailWord_6442007).sum := by decide
  have hdescent : baseEnd_6442007 < baseStart_6442007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442018 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_6442018 : Nat := 118140960795 + 6442018 * 2 ^ 59
def prefixEnd_6442018 : Nat := 4983230072969 + 3 ^ 40 * 6442018 * 2
def baseEnd_6442018 : Nat := 3307851618915681808648705

theorem tailTrace_6442018 : CollatzResearch.WordTrace tailWord_6442018 prefixEnd_6442018 3307851618915681808648705 := by
  unfold tailWord_6442018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58739924793919117481847677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156639799450450979951593805 58739924793919117481847677)
  ·
    refine ⟨22027471797719669055692879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58739924793919117481847677 22027471797719669055692879)
    ·
      refine ⟨33041207696579503583539319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22027471797719669055692879 33041207696579503583539319)
      ·
        refine ⟨49561811544869255375308979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33041207696579503583539319 49561811544869255375308979)
        ·
          refine ⟨74342717317303883062963469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49561811544869255375308979 74342717317303883062963469)
          ·
            refine ⟨27878518993988956148611301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74342717317303883062963469 27878518993988956148611301)
            ·
              refine ⟨5227222311372929277864619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27878518993988956148611301 5227222311372929277864619)
              ·
                refine ⟨7840833467059393916796929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227222311372929277864619 7840833467059393916796929)
                ·
                  refine ⟨5880625100294545437597697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840833467059393916796929 5880625100294545437597697)
                  ·
                    refine ⟨4410468825220909078198273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5880625100294545437597697 4410468825220909078198273)
                    ·
                      refine ⟨3307851618915681808648705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4410468825220909078198273 3307851618915681808648705)
                      ·
                        rfl

theorem cell23_6442018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_6442018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442018 prefixEnd_6442018 := by exact prefixLift 6442018
  have htrace : WordTrace (prefixWord ++ tailWord_6442018) baseStart_6442018 baseEnd_6442018 := by
    simpa [prefixWord, tailWord_6442018, baseEnd_6442018] using wordTrace_append hprefix tailTrace_6442018
  have hstable : (prefixWord ++ tailWord_6442018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442018).length < 2 ^ (prefixWord ++ tailWord_6442018).sum := by decide
  have hdescent : baseEnd_6442018 < baseStart_6442018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442060 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6442060 : Nat := 118140960795 + 6442060 * 2 ^ 59
def prefixEnd_6442060 : Nat := 4983230072969 + 3 ^ 40 * 6442060 * 2
def baseEnd_6442060 : Nat := 3307873185103170644323511

theorem tailTrace_6442060 : CollatzResearch.WordTrace tailWord_6442060 prefixEnd_6442060 3307873185103170644323511 := by
  unfold tailWord_6442060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117480615520762155550209817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156640820694349540733613089 117480615520762155550209817)
  ·
    refine ⟨88110461640571616662657363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117480615520762155550209817 88110461640571616662657363)
    ·
      refine ⟨132165692460857424993986045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88110461640571616662657363 132165692460857424993986045)
      ·
        refine ⟨49562134672821534372744767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132165692460857424993986045 49562134672821534372744767)
        ·
          refine ⟨74343202009232301559117151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49562134672821534372744767 74343202009232301559117151)
          ·
            refine ⟨111514803013848452338675727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74343202009232301559117151 111514803013848452338675727)
            ·
              refine ⟨167272204520772678508013591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111514803013848452338675727 167272204520772678508013591)
              ·
                refine ⟨250908306781159017762020387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167272204520772678508013591 250908306781159017762020387)
                ·
                  refine ⟨376362460171738526643030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250908306781159017762020387 376362460171738526643030581)
                  ·
                    refine ⟨35283980641100486872784117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 376362460171738526643030581 35283980641100486872784117)
                    ·
                      refine ⟨3307873185103170644323511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35283980641100486872784117 3307873185103170644323511)
                      ·
                        rfl

theorem cell23_6442060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6442060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442060 prefixEnd_6442060 := by exact prefixLift 6442060
  have htrace : WordTrace (prefixWord ++ tailWord_6442060) baseStart_6442060 baseEnd_6442060 := by
    simpa [prefixWord, tailWord_6442060, baseEnd_6442060] using wordTrace_append hprefix tailTrace_6442060
  have hstable : (prefixWord ++ tailWord_6442060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442060).length < 2 ^ (prefixWord ++ tailWord_6442060).sum := by decide
  have hdescent : baseEnd_6442060 < baseStart_6442060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442088 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6442088 : Nat := 118140960795 + 6442088 * 2 ^ 59
def prefixEnd_6442088 : Nat := 4983230072969 + 3 ^ 40 * 6442088 * 2
def baseEnd_6442088 : Nat := 1102629187520498844924461

theorem tailTrace_6442088 : CollatzResearch.WordTrace tailWord_6442088 prefixEnd_6442088 1102629187520498844924461 := by
  unfold tailWord_6442088
  simp only [CollatzResearch.WordTrace]
  refine ⟨117481126142711435941219459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156641501523615247921625945 117481126142711435941219459)
  ·
    refine ⟨176221689214067153911829189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117481126142711435941219459 176221689214067153911829189)
    ·
      refine ⟨33041566727637591358467973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176221689214067153911829189 33041566727637591358467973)
      ·
        refine ⟨6195293761432048379712745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33041566727637591358467973 6195293761432048379712745)
        ·
          refine ⟨4646470321074036284784559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195293761432048379712745 4646470321074036284784559)
          ·
            refine ⟨6969705481611054427176839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646470321074036284784559 6969705481611054427176839)
            ·
              refine ⟨10454558222416581640765259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969705481611054427176839 10454558222416581640765259)
              ·
                refine ⟨15681837333624872461147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10454558222416581640765259 15681837333624872461147889)
                ·
                  refine ⟨11761378000218654345860917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15681837333624872461147889 11761378000218654345860917)
                  ·
                    refine ⟨1102629187520498844924461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11761378000218654345860917 1102629187520498844924461)
                    ·
                      rfl

theorem cell23_6442088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6442088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442088 prefixEnd_6442088 := by exact prefixLift 6442088
  have htrace : WordTrace (prefixWord ++ tailWord_6442088) baseStart_6442088 baseEnd_6442088 := by
    simpa [prefixWord, tailWord_6442088, baseEnd_6442088] using wordTrace_append hprefix tailTrace_6442088
  have hstable : (prefixWord ++ tailWord_6442088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442088).length < 2 ^ (prefixWord ++ tailWord_6442088).sum := by decide
  have hdescent : baseEnd_6442088 < baseStart_6442088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442094 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6442094 : Nat := 118140960795 + 6442094 * 2 ^ 59
def prefixEnd_6442094 : Nat := 4983230072969 + 3 ^ 40 * 6442094 * 2
def baseEnd_6442094 : Nat := 3307890643445423511298355

theorem tailTrace_6442094 : CollatzResearch.WordTrace tailWord_6442094 prefixEnd_6442094 3307890643445423511298355 := by
  unfold tailWord_6442094
  simp only [CollatzResearch.WordTrace]
  refine ⟨29370308890425141863394667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156641647415600756604771557 29370308890425141863394667)
  ·
    refine ⟨44055463335637712795092001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29370308890425141863394667 44055463335637712795092001)
    ·
      refine ⟨33041597501728284596319001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44055463335637712795092001 33041597501728284596319001)
      ·
        refine ⟨24781198126296213447239251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33041597501728284596319001 24781198126296213447239251)
        ·
          refine ⟨37171797189444320170858877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24781198126296213447239251 37171797189444320170858877)
          ·
            refine ⟨13939423946041620064072079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37171797189444320170858877 13939423946041620064072079)
            ·
              refine ⟨20909135919062430096108119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13939423946041620064072079 20909135919062430096108119)
              ·
                refine ⟨31363703878593645144162179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20909135919062430096108119 31363703878593645144162179)
                ·
                  refine ⟨47045555817890467716243269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31363703878593645144162179 47045555817890467716243269)
                  ·
                    refine ⟨8821041715854462696795613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47045555817890467716243269 8821041715854462696795613)
                    ·
                      refine ⟨3307890643445423511298355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8821041715854462696795613 3307890643445423511298355)
                      ·
                        rfl

theorem cell23_6442094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6442094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442094 prefixEnd_6442094 := by exact prefixLift 6442094
  have htrace : WordTrace (prefixWord ++ tailWord_6442094) baseStart_6442094 baseEnd_6442094 := by
    simpa [prefixWord, tailWord_6442094, baseEnd_6442094] using wordTrace_append hprefix tailTrace_6442094
  have hstable : (prefixWord ++ tailWord_6442094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442094).length < 2 ^ (prefixWord ++ tailWord_6442094).sum := by decide
  have hdescent : baseEnd_6442094 < baseStart_6442094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6442144 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_6442144 : Nat := 118140960795 + 6442144 * 2 ^ 59
def prefixEnd_6442144 : Nat := 4983230072969 + 3 ^ 40 * 6442144 * 2
def baseEnd_6442144 : Nat := 1102638772492716105224375

theorem tailTrace_6442144 : CollatzResearch.WordTrace tailWord_6442144 prefixEnd_6442144 1102638772492716105224375 := by
  unfold tailWord_6442144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117482147386609996723238743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156642863182146662297651657 117482147386609996723238743)
  ·
    refine ⟨176223221079914995084858115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117482147386609996723238743 176223221079914995084858115)
    ·
      refine ⟨264334831619872492627287173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176223221079914995084858115 264334831619872492627287173)
      ·
        refine ⟨49562780928726092367616345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264334831619872492627287173 49562780928726092367616345)
        ·
          refine ⟨37172085696544569275712259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49562780928726092367616345 37172085696544569275712259)
          ·
            refine ⟨55758128544816853913568389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37172085696544569275712259 55758128544816853913568389)
            ·
              refine ⟨10454649102153160108794073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55758128544816853913568389 10454649102153160108794073)
              ·
                refine ⟨7840986826614870081595555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10454649102153160108794073 7840986826614870081595555)
                ·
                  refine ⟨11761480239922305122393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7840986826614870081595555 11761480239922305122393333)
                  ·
                    refine ⟨1102638772492716105224375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11761480239922305122393333 1102638772492716105224375)
                    ·
                      rfl

theorem cell23_6442144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_6442144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6442144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6442144 prefixEnd_6442144 := by exact prefixLift 6442144
  have htrace : WordTrace (prefixWord ++ tailWord_6442144) baseStart_6442144 baseEnd_6442144 := by
    simpa [prefixWord, tailWord_6442144, baseEnd_6442144] using wordTrace_append hprefix tailTrace_6442144
  have hstable : (prefixWord ++ tailWord_6442144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6442144).length < 2 ^ (prefixWord ++ tailWord_6442144).sum := by decide
  have hdescent : baseEnd_6442144 < baseStart_6442144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6442144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
