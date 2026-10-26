import V185TrunkScan21Chunk082

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1007857 : List Nat := [1, 2, 2, 2, 2, 1, 5, 6]
def baseStart_1007857 : Nat := 118140960795 + 1007857 * 2 ^ 59
def prefixEnd_1007857 : Nat := 4983230072969 + 3 ^ 40 * 1007857 * 2
def baseEnd_1007857 : Nat := 76668899555343479785549

theorem tailTrace_1007857 : CollatzResearch.WordTrace tailWord_1007857 prefixEnd_1007857 76668899555343479785549 := by
  unfold tailWord_1007857
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759564709713692116877825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24506376473142461411251883 36759564709713692116877825)
  ·
    refine ⟨27569673532285269087658369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36759564709713692116877825 27569673532285269087658369)
    ·
      refine ⟨20677255149213951815743777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569673532285269087658369 20677255149213951815743777)
      ·
        refine ⟨15507941361910463861807833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20677255149213951815743777 15507941361910463861807833)
        ·
          refine ⟨11630956021432847896355875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15507941361910463861807833 11630956021432847896355875)
          ·
            refine ⟨17446434032149271844533813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630956021432847896355875 17446434032149271844533813)
            ·
              refine ⟨1635603190513994235425045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17446434032149271844533813 1635603190513994235425045)
              ·
                refine ⟨76668899555343479785549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1635603190513994235425045 76668899555343479785549)
                ·
                  rfl

theorem cell21_1007857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_1007857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007857 prefixEnd_1007857 := by exact prefixLift 1007857
  have htrace : WordTrace (prefixWord ++ tailWord_1007857) baseStart_1007857 baseEnd_1007857 := by
    simpa [prefixWord, tailWord_1007857, baseEnd_1007857] using wordTrace_append hprefix tailTrace_1007857
  have hstable : (prefixWord ++ tailWord_1007857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007857).length < 2 ^ (prefixWord ++ tailWord_1007857).sum := by decide
  have hdescent : baseEnd_1007857 < baseStart_1007857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007905 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 3]
def baseStart_1007905 : Nat := 118140960795 + 1007905 * 2 ^ 59
def prefixEnd_1007905 : Nat := 4983230072969 + 3 ^ 40 * 1007905 * 2
def baseEnd_1007905 : Nat := 230017652919993022556549

theorem tailTrace_1007905 : CollatzResearch.WordTrace tailWord_1007905 prefixEnd_1007905 230017652919993022556549 := by
  unfold tailWord_1007905
  simp only [CollatzResearch.WordTrace]
  refine ⟨36761315413539796314625169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507543609026530876416779 36761315413539796314625169)
  ·
    refine ⟨27570986560154847235968877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36761315413539796314625169 27570986560154847235968877)
    ·
      refine ⟨10339119960058067713488329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27570986560154847235968877 10339119960058067713488329)
      ·
        refine ⟨7754339970043550785116247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10339119960058067713488329 7754339970043550785116247)
        ·
          refine ⟨11631509955065326177674371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754339970043550785116247 11631509955065326177674371)
          ·
            refine ⟨17447264932597989266511557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11631509955065326177674371 17447264932597989266511557)
            ·
              refine ⟨3271362174862122987470917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17447264932597989266511557 3271362174862122987470917)
              ·
                refine ⟨613380407786648060150797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3271362174862122987470917 613380407786648060150797)
                ·
                  refine ⟨230017652919993022556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613380407786648060150797 230017652919993022556549)
                  ·
                    rfl

theorem cell21_1007905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_1007905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007905 prefixEnd_1007905 := by exact prefixLift 1007905
  have htrace : WordTrace (prefixWord ++ tailWord_1007905) baseStart_1007905 baseEnd_1007905 := by
    simpa [prefixWord, tailWord_1007905, baseEnd_1007905] using wordTrace_append hprefix tailTrace_1007905
  have hstable : (prefixWord ++ tailWord_1007905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007905).length < 2 ^ (prefixWord ++ tailWord_1007905).sum := by decide
  have hdescent : baseEnd_1007905 < baseStart_1007905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007911 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 4]
def baseStart_1007911 : Nat := 118140960795 + 1007911 * 2 ^ 59
def prefixEnd_1007911 : Nat := 4983230072969 + 3 ^ 40 * 1007911 * 2
def baseEnd_1007911 : Nat := 230019022201738345456537

theorem tailTrace_1007911 : CollatzResearch.WordTrace tailWord_1007911 prefixEnd_1007911 230019022201738345456537 := by
  unfold tailWord_1007911
  simp only [CollatzResearch.WordTrace]
  refine ⟨36761534251518059339343587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507689501012039559562391 36761534251518059339343587)
  ·
    refine ⟨55142301377277089009015381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36761534251518059339343587 55142301377277089009015381)
    ·
      refine ⟨646198844264965886824399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 55142301377277089009015381 646198844264965886824399)
      ·
        refine ⟨969298266397448830236599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646198844264965886824399 969298266397448830236599)
        ·
          refine ⟨1453947399596173245354899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969298266397448830236599 1453947399596173245354899)
          ·
            refine ⟨2180921099394259868032349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453947399596173245354899 2180921099394259868032349)
            ·
              refine ⟨817845412272847450512131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2180921099394259868032349 817845412272847450512131)
              ·
                refine ⟨1226768118409271175768197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817845412272847450512131 1226768118409271175768197)
                ·
                  refine ⟨230019022201738345456537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226768118409271175768197 230019022201738345456537)
                  ·
                    rfl

theorem cell21_1007911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 4].length) (baseStart_1007911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1007911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1007911 prefixEnd_1007911 := by exact prefixLift 1007911
  have htrace : WordTrace (prefixWord ++ tailWord_1007911) baseStart_1007911 baseEnd_1007911 := by
    simpa [prefixWord, tailWord_1007911, baseEnd_1007911] using wordTrace_append hprefix tailTrace_1007911
  have hstable : (prefixWord ++ tailWord_1007911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007911).length < 2 ^ (prefixWord ++ tailWord_1007911).sum := by decide
  have hdescent : baseEnd_1007911 < baseStart_1007911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008026 : List Nat := [3, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1008026 : Nat := 118140960795 + 1008026 * 2 ^ 59
def prefixEnd_1008026 : Nat := 4983230072969 + 3 ^ 40 * 1008026 * 2
def baseEnd_1008026 : Nat := 76681755589507900346545

theorem tailTrace_1008026 : CollatzResearch.WordTrace tailWord_1008026 prefixEnd_1008026 76681755589507900346545 := by
  unfold tailWord_1008026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191432161525358494944983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24510485764067622653186621 9191432161525358494944983)
  ·
    refine ⟨13787148242288037742417475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191432161525358494944983 13787148242288037742417475)
    ·
      refine ⟨20680722363432056613626213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787148242288037742417475 20680722363432056613626213)
      ·
        refine ⟨3877635443143510615054915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20680722363432056613626213 3877635443143510615054915)
        ·
          refine ⟨5816453164715265922582373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877635443143510615054915 5816453164715265922582373)
          ·
            refine ⟨1090584968384112360484195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5816453164715265922582373 1090584968384112360484195)
            ·
              refine ⟨1635877452576168540726293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090584968384112360484195 1635877452576168540726293)
              ·
                refine ⟨76681755589507900346545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1635877452576168540726293 76681755589507900346545)
                ·
                  rfl

theorem cell21_1008026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1008026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008026 prefixEnd_1008026 := by exact prefixLift 1008026
  have htrace : WordTrace (prefixWord ++ tailWord_1008026) baseStart_1008026 baseEnd_1008026 := by
    simpa [prefixWord, tailWord_1008026, baseEnd_1008026] using wordTrace_append hprefix tailTrace_1008026
  have hstable : (prefixWord ++ tailWord_1008026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008026).length < 2 ^ (prefixWord ++ tailWord_1008026).sum := by decide
  have hdescent : baseEnd_1008026 < baseStart_1008026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008057 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 3]
def baseStart_1008057 : Nat := 118140960795 + 1008057 * 2 ^ 59
def prefixEnd_1008057 : Nat := 4983230072969 + 3 ^ 40 * 1008057 * 2
def baseEnd_1008057 : Nat := 230052341390874536022905

theorem tailTrace_1008057 : CollatzResearch.WordTrace tailWord_1008057 prefixEnd_1008057 230052341390874536022905 := by
  unfold tailWord_1008057
  simp only [CollatzResearch.WordTrace]
  refine ⟨36766859308989126274158425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24511239539326084182772283 36766859308989126274158425)
  ·
    refine ⟨27575144481741844705618819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36766859308989126274158425 27575144481741844705618819)
    ·
      refine ⟨41362716722612767058428229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27575144481741844705618819 41362716722612767058428229)
      ·
        refine ⟨7755509385489893823455293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41362716722612767058428229 7755509385489893823455293)
        ·
          refine ⟨2908316019558710183795735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7755509385489893823455293 2908316019558710183795735)
          ·
            refine ⟨4362474029338065275693603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908316019558710183795735 4362474029338065275693603)
            ·
              refine ⟨6543711044007097913540405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362474029338065275693603 6543711044007097913540405)
              ·
                refine ⟨613472910375665429394413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6543711044007097913540405 613472910375665429394413)
                ·
                  refine ⟨230052341390874536022905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613472910375665429394413 230052341390874536022905)
                  ·
                    rfl

theorem cell21_1008057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_1008057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008057 prefixEnd_1008057 := by exact prefixLift 1008057
  have htrace : WordTrace (prefixWord ++ tailWord_1008057) baseStart_1008057 baseEnd_1008057 := by
    simpa [prefixWord, tailWord_1008057, baseEnd_1008057] using wordTrace_append hprefix tailTrace_1008057
  have hstable : (prefixWord ++ tailWord_1008057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008057).length < 2 ^ (prefixWord ++ tailWord_1008057).sum := by decide
  have hdescent : baseEnd_1008057 < baseStart_1008057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008071 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_1008071 : Nat := 118140960795 + 1008071 * 2 ^ 59
def prefixEnd_1008071 : Nat := 4983230072969 + 3 ^ 40 * 1008071 * 2
def baseEnd_1008071 : Nat := 230055536381613622789543

theorem tailTrace_1008071 : CollatzResearch.WordTrace tailWord_1008071 prefixEnd_1008071 230055536381613622789543 := by
  unfold tailWord_1008071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36767369930938406665168067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24511579953958937776778711 36767369930938406665168067)
  ·
    refine ⟨55151054896407609997752101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36767369930938406665168067 55151054896407609997752101)
    ·
      refine ⟨10340822793076426874578519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55151054896407609997752101 10340822793076426874578519)
      ·
        refine ⟨15511234189614640311867779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340822793076426874578519 15511234189614640311867779)
        ·
          refine ⟨23266851284421960467801669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15511234189614640311867779 23266851284421960467801669)
          ·
            refine ⟨4362534615829117587712813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23266851284421960467801669 4362534615829117587712813)
            ·
              refine ⟨1635950480935919095392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362534615829117587712813 1635950480935919095392305)
              ·
                refine ⟨1226962860701939321544229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635950480935919095392305 1226962860701939321544229)
                ·
                  refine ⟨230055536381613622789543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226962860701939321544229 230055536381613622789543)
                  ·
                    rfl

theorem cell21_1008071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_1008071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008071 prefixEnd_1008071 := by exact prefixLift 1008071
  have htrace : WordTrace (prefixWord ++ tailWord_1008071) baseStart_1008071 baseEnd_1008071 := by
    simpa [prefixWord, tailWord_1008071, baseEnd_1008071] using wordTrace_append hprefix tailTrace_1008071
  have hstable : (prefixWord ++ tailWord_1008071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008071).length < 2 ^ (prefixWord ++ tailWord_1008071).sum := by decide
  have hdescent : baseEnd_1008071 < baseStart_1008071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008237 : List Nat := [1, 5, 1, 1, 3, 2, 8]
def baseStart_1008237 : Nat := 118140960795 + 1008237 * 2 ^ 59
def prefixEnd_1008237 : Nat := 4983230072969 + 3 ^ 40 * 1008237 * 2
def baseEnd_1008237 : Nat := 25565935538137135891393

theorem tailTrace_1008237 : CollatzResearch.WordTrace tailWord_1008237 prefixEnd_1008237 25565935538137135891393 := by
  unfold tailWord_1008237
  simp only [CollatzResearch.WordTrace]
  refine ⟨36773424448337017015710965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24515616298891344677140643 36773424448337017015710965)
  ·
    refine ⟨3447508542031595345222903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36773424448337017015710965 3447508542031595345222903)
    ·
      refine ⟨5171262813047393017834355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447508542031595345222903 5171262813047393017834355)
      ·
        refine ⟨7756894219571089526751533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171262813047393017834355 7756894219571089526751533)
        ·
          refine ⟨2908835332339158572531825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7756894219571089526751533 2908835332339158572531825)
          ·
            refine ⟨2181626499254368929398869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908835332339158572531825 2181626499254368929398869)
            ·
              refine ⟨25565935538137135891393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2181626499254368929398869 25565935538137135891393)
              ·
                rfl

theorem cell21_1008237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 8].length) (baseStart_1008237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008237 prefixEnd_1008237 := by exact prefixLift 1008237
  have htrace : WordTrace (prefixWord ++ tailWord_1008237) baseStart_1008237 baseEnd_1008237 := by
    simpa [prefixWord, tailWord_1008237, baseEnd_1008237] using wordTrace_append hprefix tailTrace_1008237
  have hstable : (prefixWord ++ tailWord_1008237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008237).length < 2 ^ (prefixWord ++ tailWord_1008237).sum := by decide
  have hdescent : baseEnd_1008237 < baseStart_1008237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008240 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_1008240 : Nat := 118140960795 + 1008240 * 2 ^ 59
def prefixEnd_1008240 : Nat := 4983230072969 + 3 ^ 40 * 1008240 * 2
def baseEnd_1008240 : Nat := 230094104484106884472531

theorem tailTrace_1008240 : CollatzResearch.WordTrace tailWord_1008240 prefixEnd_1008240 230094104484106884472531 := by
  unfold tailWord_1008240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386766933663074264035087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24515689244884099018713449 18386766933663074264035087)
  ·
    refine ⟨27580150400494611396052631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18386766933663074264035087 27580150400494611396052631)
    ·
      refine ⟨41370225600741917094078947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27580150400494611396052631 41370225600741917094078947)
      ·
        refine ⟨62055338401112875641118421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41370225600741917094078947 62055338401112875641118421)
        ·
          refine ⟨1454421993776083022838713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62055338401112875641118421 1454421993776083022838713)
          ·
            refine ⟨1090816495332062267129035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454421993776083022838713 1090816495332062267129035)
            ·
              refine ⟨1636224742998093400693553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090816495332062267129035 1636224742998093400693553)
              ·
                refine ⟨1227168557248570050520165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636224742998093400693553 1227168557248570050520165)
                ·
                  refine ⟨230094104484106884472531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227168557248570050520165 230094104484106884472531)
                  ·
                    rfl

theorem cell21_1008240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_1008240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008240 prefixEnd_1008240 := by exact prefixLift 1008240
  have htrace : WordTrace (prefixWord ++ tailWord_1008240) baseStart_1008240 baseEnd_1008240 := by
    simpa [prefixWord, tailWord_1008240, baseEnd_1008240] using wordTrace_append hprefix tailTrace_1008240
  have hstable : (prefixWord ++ tailWord_1008240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008240).length < 2 ^ (prefixWord ++ tailWord_1008240).sum := by decide
  have hdescent : baseEnd_1008240 < baseStart_1008240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008285 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1008285 : Nat := 118140960795 + 1008285 * 2 ^ 59
def prefixEnd_1008285 : Nat := 4983230072969 + 3 ^ 40 * 1008285 * 2
def baseEnd_1008285 : Nat := 230104374097196806222439

theorem tailTrace_1008285 : CollatzResearch.WordTrace tailWord_1008285 prefixEnd_1008285 230104374097196806222439 := by
  unfold tailWord_1008285
  simp only [CollatzResearch.WordTrace]
  refine ⟨36775175152163121213458309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24516783434775414142305539 36775175152163121213458309)
  ·
    refine ⟨6895345341030585227523433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36775175152163121213458309 6895345341030585227523433)
    ·
      refine ⟨5171509005772938920642575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6895345341030585227523433 5171509005772938920642575)
      ·
        refine ⟨7757263508659408380963863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171509005772938920642575 7757263508659408380963863)
        ·
          refine ⟨11635895262989112571445795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757263508659408380963863 11635895262989112571445795)
          ·
            refine ⟨17453842894483668857168693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635895262989112571445795 17453842894483668857168693)
            ·
              refine ⟨1636297771357843955359565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17453842894483668857168693 1636297771357843955359565)
              ·
                refine ⟨613611664259191483259837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636297771357843955359565 613611664259191483259837)
                ·
                  refine ⟨230104374097196806222439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613611664259191483259837 230104374097196806222439)
                  ·
                    rfl

theorem cell21_1008285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1008285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008285 prefixEnd_1008285 := by exact prefixLift 1008285
  have htrace : WordTrace (prefixWord ++ tailWord_1008285) baseStart_1008285 baseEnd_1008285 := by
    simpa [prefixWord, tailWord_1008285, baseEnd_1008285] using wordTrace_append hprefix tailTrace_1008285
  have hstable : (prefixWord ++ tailWord_1008285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008285).length < 2 ^ (prefixWord ++ tailWord_1008285).sum := by decide
  have hdescent : baseEnd_1008285 < baseStart_1008285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008302 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_1008302 : Nat := 118140960795 + 1008302 * 2 ^ 59
def prefixEnd_1008302 : Nat := 4983230072969 + 3 ^ 40 * 1008302 * 2
def baseEnd_1008302 : Nat := 230108253728808554439071

theorem tailTrace_1008302 : CollatzResearch.WordTrace tailWord_1008302 prefixEnd_1008302 230108253728808554439071 := by
  unfold tailWord_1008302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596974399137691639603395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24517196795401022077884773 4596974399137691639603395)
  ·
    refine ⟨6895461598706537459405093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596974399137691639603395 6895461598706537459405093)
    ·
      refine ⟨1292899049757475773638455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6895461598706537459405093 1292899049757475773638455)
      ·
        refine ⟨1939348574636213660457683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292899049757475773638455 1939348574636213660457683)
        ·
          refine ⟨2909022861954320490686525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939348574636213660457683 2909022861954320490686525)
          ·
            refine ⟨1090883573232870184007447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2909022861954320490686525 1090883573232870184007447)
            ·
              refine ⟨1636325359849305276011171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090883573232870184007447 1636325359849305276011171)
              ·
                refine ⟨2454488039773957914016757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636325359849305276011171 2454488039773957914016757)
                ·
                  refine ⟨230108253728808554439071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454488039773957914016757 230108253728808554439071)
                  ·
                    rfl

theorem cell21_1008302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_1008302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008302 prefixEnd_1008302 := by exact prefixLift 1008302
  have htrace : WordTrace (prefixWord ++ tailWord_1008302) baseStart_1008302 baseEnd_1008302 := by
    simpa [prefixWord, tailWord_1008302, baseEnd_1008302] using wordTrace_append hprefix tailTrace_1008302
  have hstable : (prefixWord ++ tailWord_1008302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008302).length < 2 ^ (prefixWord ++ tailWord_1008302).sum := by decide
  have hdescent : baseEnd_1008302 < baseStart_1008302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008361 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 3]
def baseStart_1008361 : Nat := 118140960795 + 1008361 * 2 ^ 59
def prefixEnd_1008361 : Nat := 4983230072969 + 3 ^ 40 * 1008361 * 2
def baseEnd_1008361 : Nat := 230121718332637562955617

theorem tailTrace_1008361 : CollatzResearch.WordTrace tailWord_1008361 prefixEnd_1008361 230121718332637562955617 := by
  unfold tailWord_1008361
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777947099887786193224937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24518631399925190795483291 36777947099887786193224937)
  ·
    refine ⟨27583460324915839644918703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36777947099887786193224937 27583460324915839644918703)
    ·
      refine ⟨41375190487373759467378055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27583460324915839644918703 41375190487373759467378055)
      ·
        refine ⟨62062785731060639201067083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41375190487373759467378055 62062785731060639201067083)
        ·
          refine ⟨93094178596590958801600625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62062785731060639201067083 93094178596590958801600625)
          ·
            refine ⟨69820633947443219101200469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93094178596590958801600625 69820633947443219101200469)
            ·
              refine ⟨818210554071600223842193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69820633947443219101200469 818210554071600223842193)
              ·
                refine ⟨613657915553700167881645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818210554071600223842193 613657915553700167881645)
                ·
                  refine ⟨230121718332637562955617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613657915553700167881645 230121718332637562955617)
                  ·
                    rfl

theorem cell21_1008361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_1008361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008361 prefixEnd_1008361 := by exact prefixLift 1008361
  have htrace : WordTrace (prefixWord ++ tailWord_1008361) baseStart_1008361 baseEnd_1008361 := by
    simpa [prefixWord, tailWord_1008361, baseEnd_1008361] using wordTrace_append hprefix tailTrace_1008361
  have hstable : (prefixWord ++ tailWord_1008361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008361).length < 2 ^ (prefixWord ++ tailWord_1008361).sum := by decide
  have hdescent : baseEnd_1008361 < baseStart_1008361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008465 : List Nat := [1, 2, 2, 1, 6, 2, 7]
def baseStart_1008465 : Nat := 118140960795 + 1008465 * 2 ^ 59
def prefixEnd_1008465 : Nat := 4983230072969 + 3 ^ 40 * 1008465 * 2
def baseEnd_1008465 : Nat := 25571716949950721469119

theorem tailTrace_1008465 : CollatzResearch.WordTrace tailWord_1008465 prefixEnd_1008465 25571716949950721469119 := by
  unfold tailWord_1008465
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781740291511011955010849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521160194340674636673899 36781740291511011955010849)
  ·
    refine ⟨27586305218633258966258137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36781740291511011955010849 27586305218633258966258137)
    ·
      refine ⟨20689728913974944224693603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27586305218633258966258137 20689728913974944224693603)
      ·
        refine ⟨31034593370962416337040405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20689728913974944224693603 31034593370962416337040405)
        ·
          refine ⟨1454746564263863265798769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31034593370962416337040405 1454746564263863265798769)
          ·
            refine ⟨1091059923197897449349077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454746564263863265798769 1091059923197897449349077)
            ·
              refine ⟨25571716949950721469119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1091059923197897449349077 25571716949950721469119)
              ·
                rfl

theorem cell21_1008465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 7].length) (baseStart_1008465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008465 prefixEnd_1008465 := by exact prefixLift 1008465
  have htrace : WordTrace (prefixWord ++ tailWord_1008465) baseStart_1008465 baseEnd_1008465 := by
    simpa [prefixWord, tailWord_1008465, baseEnd_1008465] using wordTrace_append hprefix tailTrace_1008465
  have hstable : (prefixWord ++ tailWord_1008465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008465).length < 2 ^ (prefixWord ++ tailWord_1008465).sum := by decide
  have hdescent : baseEnd_1008465 < baseStart_1008465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008482 : List Nat := [3, 3, 2, 1, 3, 1, 2, 6]
def baseStart_1008482 : Nat := 118140960795 + 1008482 * 2 ^ 59
def prefixEnd_1008482 : Nat := 4983230072969 + 3 ^ 40 * 1008482 * 2
def baseEnd_1008482 : Nat := 76716444060389413812901

theorem tailTrace_1008482 : CollatzResearch.WordTrace tailWord_1008482 prefixEnd_1008482 76716444060389413812901 := by
  unfold tailWord_1008482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195590083112355964594925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24521573554966282572253133 9195590083112355964594925)
  ·
    refine ⟨3448346281167133486723097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9195590083112355964594925 3448346281167133486723097)
    ·
      refine ⟨2586259710875350115042323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448346281167133486723097 2586259710875350115042323)
      ·
        refine ⟨3879389566313025172563485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586259710875350115042323 3879389566313025172563485)
        ·
          refine ⟨1454771087367384439711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3879389566313025172563485 1454771087367384439711307)
          ·
            refine ⟨2182156631051076659566961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454771087367384439711307 2182156631051076659566961)
            ·
              refine ⟨1636617473288307494675221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182156631051076659566961 1636617473288307494675221)
              ·
                refine ⟨76716444060389413812901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1636617473288307494675221 76716444060389413812901)
                ·
                  rfl

theorem cell21_1008482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_1008482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008482 prefixEnd_1008482 := by exact prefixLift 1008482
  have htrace : WordTrace (prefixWord ++ tailWord_1008482) baseStart_1008482 baseEnd_1008482 := by
    simpa [prefixWord, tailWord_1008482, baseEnd_1008482] using wordTrace_append hprefix tailTrace_1008482
  have hstable : (prefixWord ++ tailWord_1008482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008482).length < 2 ^ (prefixWord ++ tailWord_1008482).sum := by decide
  have hdescent : baseEnd_1008482 < baseStart_1008482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008530 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_1008530 : Nat := 118140960795 + 1008530 * 2 ^ 59
def prefixEnd_1008530 : Nat := 4983230072969 + 3 ^ 40 * 1008530 * 2
def baseEnd_1008530 : Nat := 230160286435130824638605

theorem tailTrace_1008530 : CollatzResearch.WordTrace tailWord_1008530 prefixEnd_1008530 230160286435130824638605 := by
  unfold tailWord_1008530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196027759068882014031761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24522740690850352037418029 9196027759068882014031761)
  ·
    refine ⟨6897020819301661510523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9196027759068882014031761 6897020819301661510523821)
    ·
      refine ⟨2586382807238123066446433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6897020819301661510523821 2586382807238123066446433)
      ·
        refine ⟨1939787105428592299834825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586382807238123066446433 1939787105428592299834825)
        ·
          refine ⟨1454840329071444224876119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939787105428592299834825 1454840329071444224876119)
          ·
            refine ⟨2182260493607166337314179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454840329071444224876119 2182260493607166337314179)
            ·
              refine ⟨3273390740410749505971269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182260493607166337314179 3273390740410749505971269)
              ·
                refine ⟨613760763827015532369613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3273390740410749505971269 613760763827015532369613)
                ·
                  refine ⟨230160286435130824638605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613760763827015532369613 230160286435130824638605)
                  ·
                    rfl

theorem cell21_1008530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_1008530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008530 prefixEnd_1008530 := by exact prefixLift 1008530
  have htrace : WordTrace (prefixWord ++ tailWord_1008530) baseStart_1008530 baseEnd_1008530 := by
    simpa [prefixWord, tailWord_1008530, baseEnd_1008530] using wordTrace_append hprefix tailTrace_1008530
  have hstable : (prefixWord ++ tailWord_1008530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008530).length < 2 ^ (prefixWord ++ tailWord_1008530).sum := by decide
  have hdescent : baseEnd_1008530 < baseStart_1008530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008645 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1008645 : Nat := 118140960795 + 1008645 * 2 ^ 59
def prefixEnd_1008645 : Nat := 4983230072969 + 3 ^ 40 * 1008645 * 2
def baseEnd_1008645 : Nat := 230186531001916180221703

theorem tailTrace_1008645 : CollatzResearch.WordTrace tailWord_1008645 prefixEnd_1008645 230186531001916180221703 := by
  unfold tailWord_1008645
  simp only [CollatzResearch.WordTrace]
  refine ⟨36788305430858902696563389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24525536953905935131042259 36788305430858902696563389)
  ·
    refine ⟨13795614536572088511211271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36788305430858902696563389 13795614536572088511211271)
    ·
      refine ⟨20693421804858132766816907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795614536572088511211271 20693421804858132766816907)
      ·
        refine ⟨31040132707287199150225361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20693421804858132766816907 31040132707287199150225361)
        ·
          refine ⟨23280099530465399362669021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31040132707287199150225361 23280099530465399362669021)
          ·
            refine ⟨8730037323924524761000883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23280099530465399362669021 8730037323924524761000883)
            ·
              refine ⟨13095055985886787141501325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730037323924524761000883 13095055985886787141501325)
              ·
                refine ⟨4910645994707545178062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13095055985886787141501325 4910645994707545178062997)
                ·
                  refine ⟨230186531001916180221703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4910645994707545178062997 230186531001916180221703)
                  ·
                    rfl

theorem cell21_1008645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1008645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008645 prefixEnd_1008645 := by exact prefixLift 1008645
  have htrace : WordTrace (prefixWord ++ tailWord_1008645) baseStart_1008645 baseEnd_1008645 := by
    simpa [prefixWord, tailWord_1008645, baseEnd_1008645] using wordTrace_append hprefix tailTrace_1008645
  have hstable : (prefixWord ++ tailWord_1008645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008645).length < 2 ^ (prefixWord ++ tailWord_1008645).sum := by decide
  have hdescent : baseEnd_1008645 < baseStart_1008645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008648 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_1008648 : Nat := 118140960795 + 1008648 * 2 ^ 59
def prefixEnd_1008648 : Nat := 4983230072969 + 3 ^ 40 * 1008648 * 2
def baseEnd_1008648 : Nat := 230187215642788841671697

theorem tailTrace_1008648 : CollatzResearch.WordTrace tailWord_1008648 prefixEnd_1008648 230187215642788841671697 := by
  unfold tailWord_1008648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394207424924017104461299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24525609899898689472615065 18394207424924017104461299)
  ·
    refine ⟨27591311137386025656691949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394207424924017104461299 27591311137386025656691949)
    ·
      refine ⟨10346741676519759621259481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27591311137386025656691949 10346741676519759621259481)
      ·
        refine ⟨7760056257389819715944611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10346741676519759621259481 7760056257389819715944611)
        ·
          refine ⟨11640084386084729573916917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760056257389819715944611 11640084386084729573916917)
          ·
            refine ⟨1091257911195443397554711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11640084386084729573916917 1091257911195443397554711)
            ·
              refine ⟨1636886866793165096332067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091257911195443397554711 1636886866793165096332067)
              ·
                refine ⟨2455330300189747644498101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636886866793165096332067 2455330300189747644498101)
                ·
                  refine ⟨230187215642788841671697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455330300189747644498101 230187215642788841671697)
                  ·
                    rfl

theorem cell21_1008648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_1008648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008648 prefixEnd_1008648 := by exact prefixLift 1008648
  have htrace : WordTrace (prefixWord ++ tailWord_1008648) baseStart_1008648 baseEnd_1008648 := by
    simpa [prefixWord, tailWord_1008648, baseEnd_1008648] using wordTrace_append hprefix tailTrace_1008648
  have hstable : (prefixWord ++ tailWord_1008648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008648).length < 2 ^ (prefixWord ++ tailWord_1008648).sum := by decide
  have hdescent : baseEnd_1008648 < baseStart_1008648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008710 : List Nat := [6, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1008710 : Nat := 118140960795 + 1008710 * 2 ^ 59
def prefixEnd_1008710 : Nat := 4983230072969 + 3 ^ 40 * 1008710 * 2
def baseEnd_1008710 : Nat := 76733788295830170546079

theorem tailTrace_1008710 : CollatzResearch.WordTrace tailWord_1008710 prefixEnd_1008710 76733788295830170546079 := by
  unfold tailWord_1008710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149708630488231837427487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24527117450415612531786389 1149708630488231837427487)
  ·
    refine ⟨1724562945732347756141231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149708630488231837427487 1724562945732347756141231)
    ·
      refine ⟨2586844418598521634211847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724562945732347756141231 2586844418598521634211847)
      ·
        refine ⟨3880266627897782451317771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586844418598521634211847 3880266627897782451317771)
        ·
          refine ⟨5820399941846673676976657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880266627897782451317771 5820399941846673676976657)
          ·
            refine ⟨4365299956385005257732493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820399941846673676976657 4365299956385005257732493)
            ·
              refine ⟨1636987483644376971649685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4365299956385005257732493 1636987483644376971649685)
              ·
                refine ⟨76733788295830170546079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1636987483644376971649685 76733788295830170546079)
                ·
                  rfl

theorem cell21_1008710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1008710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008710 prefixEnd_1008710 := by exact prefixLift 1008710
  have htrace : WordTrace (prefixWord ++ tailWord_1008710) baseStart_1008710 baseEnd_1008710 := by
    simpa [prefixWord, tailWord_1008710, baseEnd_1008710] using wordTrace_append hprefix tailTrace_1008710
  have hstable : (prefixWord ++ tailWord_1008710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008710).length < 2 ^ (prefixWord ++ tailWord_1008710).sum := by decide
  have hdescent : baseEnd_1008710 < baseStart_1008710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008786 : List Nat := [3, 2, 3, 1, 1, 4, 2, 5]
def baseStart_1008786 : Nat := 118140960795 + 1008786 * 2 ^ 59
def prefixEnd_1008786 : Nat := 4983230072969 + 3 ^ 40 * 1008786 * 2
def baseEnd_1008786 : Nat := 76739569707643756123805

theorem tailTrace_1008786 : CollatzResearch.WordTrace tailWord_1008786 prefixEnd_1008786 76739569707643756123805 := by
  unfold tailWord_1008786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198362030837020944361553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24528965415565389184964141 9198362030837020944361553)
  ·
    refine ⟨6898771523127765708271165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9198362030837020944361553 6898771523127765708271165)
    ·
      refine ⟨2587039321172912140601687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6898771523127765708271165 2587039321172912140601687)
      ·
        refine ⟨3880558981759368210902531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587039321172912140601687 3880558981759368210902531)
        ·
          refine ⟨5820838472639052316353797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880558981759368210902531 5820838472639052316353797)
          ·
            refine ⟨1091407213619822309316337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5820838472639052316353797 1091407213619822309316337)
            ·
              refine ⟨818555410214866731987253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091407213619822309316337 818555410214866731987253)
              ·
                refine ⟨76739569707643756123805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 818555410214866731987253 76739569707643756123805)
                ·
                  rfl

theorem cell21_1008786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_1008786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008786 prefixEnd_1008786 := by exact prefixLift 1008786
  have htrace : WordTrace (prefixWord ++ tailWord_1008786) baseStart_1008786 baseEnd_1008786 := by
    simpa [prefixWord, tailWord_1008786, baseEnd_1008786] using wordTrace_append hprefix tailTrace_1008786
  have hstable : (prefixWord ++ tailWord_1008786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008786).length < 2 ^ (prefixWord ++ tailWord_1008786).sum := by decide
  have hdescent : baseEnd_1008786 < baseStart_1008786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008797 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1008797 : Nat := 118140960795 + 1008797 * 2 ^ 59
def prefixEnd_1008797 : Nat := 4983230072969 + 3 ^ 40 * 1008797 * 2
def baseEnd_1008797 : Nat := 230221219472797693688059

theorem tailTrace_1008797 : CollatzResearch.WordTrace tailWord_1008797 prefixEnd_1008797 230221219472797693688059 := by
  unfold tailWord_1008797
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793849326308232656096645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24529232884205488437397763 36793849326308232656096645)
  ·
    refine ⟨6898846748682793623018121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36793849326308232656096645 6898846748682793623018121)
    ·
      refine ⟨5174135061512095217263591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6898846748682793623018121 5174135061512095217263591)
      ·
        refine ⟨7761202592268142825895387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174135061512095217263591 7761202592268142825895387)
        ·
          refine ⟨11641803888402214238843081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761202592268142825895387 11641803888402214238843081)
          ·
            refine ⟨8731352916301660679132311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11641803888402214238843081 8731352916301660679132311)
            ·
              refine ⟨13097029374452491018698467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731352916301660679132311 13097029374452491018698467)
              ·
                refine ⟨19645544061678736528047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13097029374452491018698467 19645544061678736528047701)
                ·
                  refine ⟨230221219472797693688059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19645544061678736528047701 230221219472797693688059)
                  ·
                    rfl

theorem cell21_1008797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1008797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008797 prefixEnd_1008797 := by exact prefixLift 1008797
  have htrace : WordTrace (prefixWord ++ tailWord_1008797) baseStart_1008797 baseEnd_1008797 := by
    simpa [prefixWord, tailWord_1008797, baseEnd_1008797] using wordTrace_append hprefix tailTrace_1008797
  have hstable : (prefixWord ++ tailWord_1008797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008797).length < 2 ^ (prefixWord ++ tailWord_1008797).sum := by decide
  have hdescent : baseEnd_1008797 < baseStart_1008797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008828 : List Nat := [2, 2, 2, 3, 2, 1, 1, 8]
def baseStart_1008828 : Nat := 118140960795 + 1008828 * 2 ^ 59
def prefixEnd_1008828 : Nat := 4983230072969 + 3 ^ 40 * 1008828 * 2
def baseEnd_1008828 : Nat := 76742764698382842890443

theorem tailTrace_1008828 : CollatzResearch.WordTrace tailWord_1008828 prefixEnd_1008828 76742764698382842890443 := by
  unfold tailWord_1008828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397489994597962475237569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24529986659463949966983425 18397489994597962475237569)
  ·
    refine ⟨13798117495948471856428177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18397489994597962475237569 13798117495948471856428177)
    ·
      refine ⟨10348588121961353892321133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13798117495948471856428177 10348588121961353892321133)
      ·
        refine ⟨3880720545735507709620425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10348588121961353892321133 3880720545735507709620425)
        ·
          refine ⟨2910540409301630782215319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880720545735507709620425 2910540409301630782215319)
          ·
            refine ⟨4365810613952446173322979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910540409301630782215319 4365810613952446173322979)
            ·
              refine ⟨6548715920928669259984469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365810613952446173322979 6548715920928669259984469)
              ·
                refine ⟨76742764698382842890443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6548715920928669259984469 76742764698382842890443)
                ·
                  rfl

theorem cell21_1008828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_1008828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008828 prefixEnd_1008828 := by exact prefixLift 1008828
  have htrace : WordTrace (prefixWord ++ tailWord_1008828) baseStart_1008828 baseEnd_1008828 := by
    simpa [prefixWord, tailWord_1008828, baseEnd_1008828] using wordTrace_append hprefix tailTrace_1008828
  have hstable : (prefixWord ++ tailWord_1008828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008828).length < 2 ^ (prefixWord ++ tailWord_1008828).sum := by decide
  have hdescent : baseEnd_1008828 < baseStart_1008828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008876 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_1008876 : Nat := 118140960795 + 1008876 * 2 ^ 59
def prefixEnd_1008876 : Nat := 4983230072969 + 3 ^ 40 * 1008876 * 2
def baseEnd_1008876 : Nat := 230239248349111111871231

theorem tailTrace_1008876 : CollatzResearch.WordTrace tailWord_1008876 prefixEnd_1008876 230239248349111111871231 := by
  unfold tailWord_1008876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398365346511014574111241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24531153795348019432148321 18398365346511014574111241)
  ·
    refine ⟨13798774009883260930583431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18398365346511014574111241 13798774009883260930583431)
    ·
      refine ⟨20698161014824891395875147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13798774009883260930583431 20698161014824891395875147)
      ·
        refine ⟨31047241522237337093812721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20698161014824891395875147 31047241522237337093812721)
        ·
          refine ⟨23285431141678002820359541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31047241522237337093812721 23285431141678002820359541)
          ·
            refine ⟨2183009169532312764408707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23285431141678002820359541 2183009169532312764408707)
            ·
              refine ⟨3274513754298469146613061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183009169532312764408707 3274513754298469146613061)
              ·
                refine ⟨613971328930962964989949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3274513754298469146613061 613971328930962964989949)
                ·
                  refine ⟨230239248349111111871231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613971328930962964989949 230239248349111111871231)
                  ·
                    rfl

theorem cell21_1008876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_1008876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1008876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1008876 prefixEnd_1008876 := by exact prefixLift 1008876
  have htrace : WordTrace (prefixWord ++ tailWord_1008876) baseStart_1008876 baseEnd_1008876 := by
    simpa [prefixWord, tailWord_1008876, baseEnd_1008876] using wordTrace_append hprefix tailTrace_1008876
  have hstable : (prefixWord ++ tailWord_1008876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008876).length < 2 ^ (prefixWord ++ tailWord_1008876).sum := by decide
  have hdescent : baseEnd_1008876 < baseStart_1008876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009000 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_1009000 : Nat := 118140960795 + 1009000 * 2 ^ 59
def prefixEnd_1009000 : Nat := 4983230072969 + 3 ^ 40 * 1009000 * 2
def baseEnd_1009000 : Nat := 230267546838514451804311

theorem tailTrace_1009000 : CollatzResearch.WordTrace tailWord_1009000 prefixEnd_1009000 230267546838514451804311 := by
  unfold tailWord_1009000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400626672286399162868227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24534168896381865550490969 18400626672286399162868227)
  ·
    refine ⟨27600940008429598744302341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400626672286399162868227 27600940008429598744302341)
    ·
      refine ⟨5175176251580549764556689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27600940008429598744302341 5175176251580549764556689)
      ·
        refine ⟨3881382188685412323417517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175176251580549764556689 3881382188685412323417517)
        ·
          refine ⟨1455518320757029621281569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3881382188685412323417517 1455518320757029621281569)
          ·
            refine ⟨1091638740567772215961177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455518320757029621281569 1091638740567772215961177)
            ·
              refine ⟨818729055425829161970883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091638740567772215961177 818729055425829161970883)
              ·
                refine ⟨1228093583138743742956325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818729055425829161970883 1228093583138743742956325)
                ·
                  refine ⟨230267546838514451804311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228093583138743742956325 230267546838514451804311)
                  ·
                    rfl

theorem cell21_1009000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_1009000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009000 prefixEnd_1009000 := by exact prefixLift 1009000
  have htrace : WordTrace (prefixWord ++ tailWord_1009000) baseStart_1009000 baseEnd_1009000 := by
    simpa [prefixWord, tailWord_1009000, baseEnd_1009000] using wordTrace_append hprefix tailTrace_1009000
  have hstable : (prefixWord ++ tailWord_1009000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009000).length < 2 ^ (prefixWord ++ tailWord_1009000).sum := by decide
  have hdescent : baseEnd_1009000 < baseStart_1009000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009256 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_1009256 : Nat := 118140960795 + 1009256 * 2 ^ 59
def prefixEnd_1009256 : Nat := 4983230072969 + 3 ^ 40 * 1009256 * 2
def baseEnd_1009256 : Nat := 230325969526314895537121

theorem tailTrace_1009256 : CollatzResearch.WordTrace tailWord_1009256 prefixEnd_1009256 230325969526314895537121 := by
  unfold tailWord_1009256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405295215822677023527811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24540393621096902698037081 18405295215822677023527811)
  ·
    refine ⟨27607942823734015535291717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18405295215822677023527811 27607942823734015535291717)
    ·
      refine ⟨5176489279450127912867197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27607942823734015535291717 5176489279450127912867197)
      ·
        refine ⟨1941183479793797967325199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5176489279450127912867197 1941183479793797967325199)
        ·
          refine ⟨2911775219690696950987799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941183479793797967325199 2911775219690696950987799)
          ·
            refine ⟨4367662829536045426481699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911775219690696950987799 4367662829536045426481699)
            ·
              refine ⟨6551494244304068139722549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367662829536045426481699 6551494244304068139722549)
              ·
                refine ⟨614202585403506388098989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6551494244304068139722549 614202585403506388098989)
                ·
                  refine ⟨230325969526314895537121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614202585403506388098989 230325969526314895537121)
                  ·
                    rfl

theorem cell21_1009256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_1009256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009256 prefixEnd_1009256 := by exact prefixLift 1009256
  have htrace : WordTrace (prefixWord ++ tailWord_1009256) baseStart_1009256 baseEnd_1009256 := by
    simpa [prefixWord, tailWord_1009256, baseEnd_1009256] using wordTrace_append hprefix tailTrace_1009256
  have hstable : (prefixWord ++ tailWord_1009256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009256).length < 2 ^ (prefixWord ++ tailWord_1009256).sum := by decide
  have hdescent : baseEnd_1009256 < baseStart_1009256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009270 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1009270 : Nat := 118140960795 + 1009270 * 2 ^ 59
def prefixEnd_1009270 : Nat := 4983230072969 + 3 ^ 40 * 1009270 * 2
def baseEnd_1009270 : Nat := 230329164517053982303759

theorem tailTrace_1009270 : CollatzResearch.WordTrace tailWord_1009270 prefixEnd_1009270 230329164517053982303759 := by
  unfold tailWord_1009270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300693815849664652379079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24540734035729756292043509 2300693815849664652379079)
  ·
    refine ⟨3451040723774496978568619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300693815849664652379079 3451040723774496978568619)
    ·
      refine ⟨5176561085661745467852929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451040723774496978568619 5176561085661745467852929)
      ·
        refine ⟨3882420814246309100889697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176561085661745467852929 3882420814246309100889697)
        ·
          refine ⟨2911815610684731825667273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882420814246309100889697 2911815610684731825667273)
          ·
            refine ⟨2183861708013548869250455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911815610684731825667273 2183861708013548869250455)
            ·
              refine ⟨3275792562020323303875683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183861708013548869250455 3275792562020323303875683)
              ·
                refine ⟨4913688843030484955813525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275792562020323303875683 4913688843030484955813525)
                ·
                  refine ⟨230329164517053982303759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4913688843030484955813525 230329164517053982303759)
                  ·
                    rfl

theorem cell21_1009270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1009270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009270 prefixEnd_1009270 := by exact prefixLift 1009270
  have htrace : WordTrace (prefixWord ++ tailWord_1009270) baseStart_1009270 baseEnd_1009270 := by
    simpa [prefixWord, tailWord_1009270, baseEnd_1009270] using wordTrace_append hprefix tailTrace_1009270
  have hstable : (prefixWord ++ tailWord_1009270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009270).length < 2 ^ (prefixWord ++ tailWord_1009270).sum := by decide
  have hdescent : baseEnd_1009270 < baseStart_1009270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009343 : List Nat := [1, 1, 2, 2, 2, 3, 4, 6]
def baseStart_1009343 : Nat := 118140960795 + 1009343 * 2 ^ 59
def prefixEnd_1009343 : Nat := 4983230072969 + 3 ^ 40 * 1009343 * 2
def baseEnd_1009343 : Nat := 76781941370540692528981

theorem tailTrace_1009343 : CollatzResearch.WordTrace tailWord_1009343 prefixEnd_1009343 76781941370540692528981 := by
  unfold tailWord_1009343
  simp only [CollatzResearch.WordTrace]
  refine ⟨36813763582330167905472683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24542509054886778603648455 36813763582330167905472683)
  ·
    refine ⟨55220645373495251858209025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36813763582330167905472683 55220645373495251858209025)
    ·
      refine ⟨41415484030121438893656769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55220645373495251858209025 41415484030121438893656769)
      ·
        refine ⟨31061613022591079170242577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41415484030121438893656769 31061613022591079170242577)
        ·
          refine ⟨23296209766943309377681933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31061613022591079170242577 23296209766943309377681933)
          ·
            refine ⟨8736078662603741016630725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23296209766943309377681933 8736078662603741016630725)
            ·
              refine ⟨1638014749238201440618261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8736078662603741016630725 1638014749238201440618261)
              ·
                refine ⟨76781941370540692528981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1638014749238201440618261 76781941370540692528981)
                ·
                  rfl

theorem cell21_1009343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_1009343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009343 prefixEnd_1009343 := by exact prefixLift 1009343
  have htrace : WordTrace (prefixWord ++ tailWord_1009343) baseStart_1009343 baseEnd_1009343 := by
    simpa [prefixWord, tailWord_1009343, baseEnd_1009343] using wordTrace_append hprefix tailTrace_1009343
  have hstable : (prefixWord ++ tailWord_1009343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009343).length < 2 ^ (prefixWord ++ tailWord_1009343).sum := by decide
  have hdescent : baseEnd_1009343 < baseStart_1009343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009383 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 3]
def baseStart_1009383 : Nat := 118140960795 + 1009383 * 2 ^ 59
def prefixEnd_1009383 : Nat := 4983230072969 + 3 ^ 40 * 1009383 * 2
def baseEnd_1009383 : Nat := 230354952656590896920195

theorem tailTrace_1009383 : CollatzResearch.WordTrace tailWord_1009383 prefixEnd_1009383 230354952656590896920195 := by
  unfold tailWord_1009383
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815222502185254736928803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24543481668123503157952535 36815222502185254736928803)
  ·
    refine ⟨55222833753277882105393205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36815222502185254736928803 55222833753277882105393205)
    ·
      refine ⟨5177140664369801447380613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55222833753277882105393205 5177140664369801447380613)
      ·
        refine ⟨970713874569337771383865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5177140664369801447380613 970713874569337771383865)
        ·
          refine ⟨728035405927003328537899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970713874569337771383865 728035405927003328537899)
          ·
            refine ⟨1092053108890504992806849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728035405927003328537899 1092053108890504992806849)
            ·
              refine ⟨819039831667878744605137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092053108890504992806849 819039831667878744605137)
              ·
                refine ⟨614279873750909058453853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819039831667878744605137 614279873750909058453853)
                ·
                  refine ⟨230354952656590896920195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614279873750909058453853 230354952656590896920195)
                  ·
                    rfl

theorem cell21_1009383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].length) (baseStart_1009383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009383 prefixEnd_1009383 := by exact prefixLift 1009383
  have htrace : WordTrace (prefixWord ++ tailWord_1009383) baseStart_1009383 baseEnd_1009383 := by
    simpa [prefixWord, tailWord_1009383, baseEnd_1009383] using wordTrace_append hprefix tailTrace_1009383
  have hstable : (prefixWord ++ tailWord_1009383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009383).length < 2 ^ (prefixWord ++ tailWord_1009383).sum := by decide
  have hdescent : baseEnd_1009383 < baseStart_1009383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009388 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1009388 : Nat := 118140960795 + 1009388 * 2 ^ 59
def prefixEnd_1009388 : Nat := 4983230072969 + 3 ^ 40 * 1009388 * 2
def baseEnd_1009388 : Nat := 230356093724711999336851

theorem tailTrace_1009388 : CollatzResearch.WordTrace tailWord_1009388 prefixEnd_1009388 230356093724711999336851 := by
  unfold tailWord_1009388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407702433583570295430409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24543603244778093727240545 18407702433583570295430409)
  ·
    refine ⟨13805776825187677721572807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18407702433583570295430409 13805776825187677721572807)
    ·
      refine ⟨20708665237781516582359211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805776825187677721572807 20708665237781516582359211)
      ·
        refine ⟨31062997856672274873538817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20708665237781516582359211 31062997856672274873538817)
        ·
          refine ⟨23297248392504206155154113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31062997856672274873538817 23297248392504206155154113)
          ·
            refine ⟨17472936294378154616365585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23297248392504206155154113 17472936294378154616365585)
            ·
              refine ⟨13104702220783615962274189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17472936294378154616365585 13104702220783615962274189)
              ·
                refine ⟨4914263332793855985852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13104702220783615962274189 4914263332793855985852821)
                ·
                  refine ⟨230356093724711999336851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4914263332793855985852821 230356093724711999336851)
                  ·
                    rfl

theorem cell21_1009388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1009388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009388 prefixEnd_1009388 := by exact prefixLift 1009388
  have htrace : WordTrace (prefixWord ++ tailWord_1009388) baseStart_1009388 baseEnd_1009388 := by
    simpa [prefixWord, tailWord_1009388, baseEnd_1009388] using wordTrace_append hprefix tailTrace_1009388
  have hstable : (prefixWord ++ tailWord_1009388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009388).length < 2 ^ (prefixWord ++ tailWord_1009388).sum := by decide
  have hdescent : baseEnd_1009388 < baseStart_1009388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009391 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 3]
def baseStart_1009391 : Nat := 118140960795 + 1009391 * 2 ^ 59
def prefixEnd_1009391 : Nat := 4983230072969 + 3 ^ 40 * 1009391 * 2
def baseEnd_1009391 : Nat := 230356778365584660786845

theorem tailTrace_1009391 : CollatzResearch.WordTrace tailWord_1009391 prefixEnd_1009391 230356778365584660786845 := by
  unfold tailWord_1009391
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815514286156272103220027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24543676190770848068813351 36815514286156272103220027)
  ·
    refine ⟨55223271429234408154830041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36815514286156272103220027 55223271429234408154830041)
    ·
      refine ⟨41417453571925806116122531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55223271429234408154830041 41417453571925806116122531)
      ·
        refine ⟨62126180357888709174183797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41417453571925806116122531 62126180357888709174183797)
        ·
          refine ⟨5824329408552066485079731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62126180357888709174183797 5824329408552066485079731)
          ·
            refine ⟨8736494112828099727619597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824329408552066485079731 8736494112828099727619597)
            ·
              refine ⟨3276185292310537397857349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8736494112828099727619597 3276185292310537397857349)
              ·
                refine ⟨614284742308225762098253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3276185292310537397857349 614284742308225762098253)
                ·
                  refine ⟨230356778365584660786845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614284742308225762098253 230356778365584660786845)
                  ·
                    rfl

theorem cell21_1009391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].length) (baseStart_1009391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009391 prefixEnd_1009391 := by exact prefixLift 1009391
  have htrace : WordTrace (prefixWord ++ tailWord_1009391) baseStart_1009391 baseEnd_1009391 := by
    simpa [prefixWord, tailWord_1009391, baseEnd_1009391] using wordTrace_append hprefix tailTrace_1009391
  have hstable : (prefixWord ++ tailWord_1009391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009391).length < 2 ^ (prefixWord ++ tailWord_1009391).sum := by decide
  have hdescent : baseEnd_1009391 < baseStart_1009391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009540 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1009540 : Nat := 118140960795 + 1009540 * 2 ^ 59
def prefixEnd_1009540 : Nat := 4983230072969 + 3 ^ 40 * 1009540 * 2
def baseEnd_1009540 : Nat := 230390782195593512803207

theorem tailTrace_1009540 : CollatzResearch.WordTrace tailWord_1009540 prefixEnd_1009540 230390782195593512803207 := by
  unfold tailWord_1009540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410474381308235275197037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24547299175077647033596049 18410474381308235275197037)
  ·
    refine ⟨6903927892990588228198889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18410474381308235275197037 6903927892990588228198889)
    ·
      refine ⟨5177945919742941171149167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6903927892990588228198889 5177945919742941171149167)
      ·
        refine ⟨7766918879614411756723751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177945919742941171149167 7766918879614411756723751)
        ·
          refine ⟨11650378319421617635085627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766918879614411756723751 11650378319421617635085627)
          ·
            refine ⟨17475567479132426452628441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650378319421617635085627 17475567479132426452628441)
            ·
              refine ⟨13106675609349319839471331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17475567479132426452628441 13106675609349319839471331)
              ·
                refine ⟨19660013414023979759206997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106675609349319839471331 19660013414023979759206997)
                ·
                  refine ⟨230390782195593512803207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19660013414023979759206997 230390782195593512803207)
                  ·
                    rfl

theorem cell21_1009540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1009540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009540 prefixEnd_1009540 := by exact prefixLift 1009540
  have htrace : WordTrace (prefixWord ++ tailWord_1009540) baseStart_1009540 baseEnd_1009540 := by
    simpa [prefixWord, tailWord_1009540, baseEnd_1009540] using wordTrace_append hprefix tailTrace_1009540
  have hstable : (prefixWord ++ tailWord_1009540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009540).length < 2 ^ (prefixWord ++ tailWord_1009540).sum := by decide
  have hdescent : baseEnd_1009540 < baseStart_1009540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009557 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1009557 : Nat := 118140960795 + 1009557 * 2 ^ 59
def prefixEnd_1009557 : Nat := 4983230072969 + 3 ^ 40 * 1009557 * 2
def baseEnd_1009557 : Nat := 230394661827205261019839

theorem tailTrace_1009557 : CollatzResearch.WordTrace tailWord_1009557 prefixEnd_1009557 230394661827205261019839 := by
  unfold tailWord_1009557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36821568803554882453762925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24547712535703254969175283 36821568803554882453762925)
  ·
    refine ⟨13808088301333080920161097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36821568803554882453762925 13808088301333080920161097)
    ·
      refine ⟨10356066225999810690120823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13808088301333080920161097 10356066225999810690120823)
      ·
        refine ⟨15534099338999716035181235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10356066225999810690120823 15534099338999716035181235)
        ·
          refine ⟨23301149008499574052771853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15534099338999716035181235 23301149008499574052771853)
          ·
            refine ⟨8737930878187340269789445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23301149008499574052771853 8737930878187340269789445)
            ·
              refine ⟨1638362039660126300585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8737930878187340269789445 1638362039660126300585521)
              ·
                refine ⟨1228771529745094725439141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638362039660126300585521 1228771529745094725439141)
                ·
                  refine ⟨230394661827205261019839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228771529745094725439141 230394661827205261019839)
                  ·
                    rfl

theorem cell21_1009557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1009557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009557 prefixEnd_1009557 := by exact prefixLift 1009557
  have htrace : WordTrace (prefixWord ++ tailWord_1009557) baseStart_1009557 baseEnd_1009557 := by
    simpa [prefixWord, tailWord_1009557, baseEnd_1009557] using wordTrace_append hprefix tailTrace_1009557
  have hstable : (prefixWord ++ tailWord_1009557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009557).length < 2 ^ (prefixWord ++ tailWord_1009557).sum := by decide
  have hdescent : baseEnd_1009557 < baseStart_1009557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009661 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1009661 : Nat := 118140960795 + 1009661 * 2 ^ 59
def prefixEnd_1009661 : Nat := 4983230072969 + 3 ^ 40 * 1009661 * 2
def baseEnd_1009661 : Nat := 230418396044124191286293

theorem tailTrace_1009661 : CollatzResearch.WordTrace tailWord_1009661 prefixEnd_1009661 230418396044124191286293 := by
  unfold tailWord_1009661
  simp only [CollatzResearch.WordTrace]
  refine ⟨36825361995178108215548837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24550241330118738810365891 36825361995178108215548837)
  ·
    refine ⟨6904755374095895290415407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36825361995178108215548837 6904755374095895290415407)
    ·
      refine ⟨10357133061143842935623111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6904755374095895290415407 10357133061143842935623111)
      ·
        refine ⟨15535699591715764403434667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357133061143842935623111 15535699591715764403434667)
        ·
          refine ⟨23303549387573646605152001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535699591715764403434667 23303549387573646605152001)
          ·
            refine ⟨17477662040680234953864001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23303549387573646605152001 17477662040680234953864001)
            ·
              refine ⟨13108246530510176215398001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17477662040680234953864001 13108246530510176215398001)
              ·
                refine ⟨9831184897882632161548501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13108246530510176215398001 9831184897882632161548501)
                ·
                  refine ⟨230418396044124191286293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9831184897882632161548501 230418396044124191286293)
                  ·
                    rfl

theorem cell21_1009661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1009661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009661 prefixEnd_1009661 := by exact prefixLift 1009661
  have htrace : WordTrace (prefixWord ++ tailWord_1009661) baseStart_1009661 baseEnd_1009661 := by
    simpa [prefixWord, tailWord_1009661, baseEnd_1009661] using wordTrace_append hprefix tailTrace_1009661
  have hstable : (prefixWord ++ tailWord_1009661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009661).length < 2 ^ (prefixWord ++ tailWord_1009661).sum := by decide
  have hdescent : baseEnd_1009661 < baseStart_1009661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009729 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 3]
def baseStart_1009729 : Nat := 118140960795 + 1009729 * 2 ^ 59
def prefixEnd_1009729 : Nat := 4983230072969 + 3 ^ 40 * 1009729 * 2
def baseEnd_1009729 : Nat := 230433914570571184152821

theorem tailTrace_1009729 : CollatzResearch.WordTrace tailWord_1009729 prefixEnd_1009729 230433914570571184152821 := by
  unfold tailWord_1009729
  simp only [CollatzResearch.WordTrace]
  refine ⟨36827842158931755829024241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24551894772621170552682827 36827842158931755829024241)
  ·
    refine ⟨27620881619198816871768181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36827842158931755829024241 27620881619198816871768181)
    ·
      refine ⟨2589457651799889081728267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27620881619198816871768181 2589457651799889081728267)
      ·
        refine ⟨3884186477699833622592401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589457651799889081728267 3884186477699833622592401)
        ·
          refine ⟨2913139858274875216944301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884186477699833622592401 2913139858274875216944301)
          ·
            refine ⟨1092427446853078206354113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2913139858274875216944301 1092427446853078206354113)
            ·
              refine ⟨819320585139808654765585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092427446853078206354113 819320585139808654765585)
              ·
                refine ⟨614490438854856491074189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819320585139808654765585 614490438854856491074189)
                ·
                  refine ⟨230433914570571184152821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614490438854856491074189 230433914570571184152821)
                  ·
                    rfl

theorem cell21_1009729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_1009729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009729 prefixEnd_1009729 := by exact prefixLift 1009729
  have htrace : WordTrace (prefixWord ++ tailWord_1009729) baseStart_1009729 baseEnd_1009729 := by
    simpa [prefixWord, tailWord_1009729, baseEnd_1009729] using wordTrace_append hprefix tailTrace_1009729
  have hstable : (prefixWord ++ tailWord_1009729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009729).length < 2 ^ (prefixWord ++ tailWord_1009729).sum := by decide
  have hdescent : baseEnd_1009729 < baseStart_1009729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009737 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1009737 : Nat := 118140960795 + 1009737 * 2 ^ 59
def prefixEnd_1009737 : Nat := 4983230072969 + 3 ^ 40 * 1009737 * 2
def baseEnd_1009737 : Nat := 230435740279564948019471

theorem tailTrace_1009737 : CollatzResearch.WordTrace tailWord_1009737 prefixEnd_1009737 230435740279564948019471 := by
  unfold tailWord_1009737
  simp only [CollatzResearch.WordTrace]
  refine ⟨36828133942902773195315465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552089295268515463543643 36828133942902773195315465)
  ·
    refine ⟨27621100457177079896486599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36828133942902773195315465 27621100457177079896486599)
    ·
      refine ⟨41431650685765619844729899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27621100457177079896486599 41431650685765619844729899)
      ·
        refine ⟨62147476028648429767094849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41431650685765619844729899 62147476028648429767094849)
        ·
          refine ⟨46610607021486322325321137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62147476028648429767094849 46610607021486322325321137)
          ·
            refine ⟨34957955266114741743990853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46610607021486322325321137 34957955266114741743990853)
            ·
              refine ⟨6554616612396514076998285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34957955266114741743990853 6554616612396514076998285)
              ·
                refine ⟨2457981229648692778874357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6554616612396514076998285 2457981229648692778874357)
                ·
                  refine ⟨230435740279564948019471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457981229648692778874357 230435740279564948019471)
                  ·
                    rfl

theorem cell21_1009737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1009737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009737 prefixEnd_1009737 := by exact prefixLift 1009737
  have htrace : WordTrace (prefixWord ++ tailWord_1009737) baseStart_1009737 baseEnd_1009737 := by
    simpa [prefixWord, tailWord_1009737, baseEnd_1009737] using wordTrace_append hprefix tailTrace_1009737
  have hstable : (prefixWord ++ tailWord_1009737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009737).length < 2 ^ (prefixWord ++ tailWord_1009737).sum := by decide
  have hdescent : baseEnd_1009737 < baseStart_1009737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009757 : List Nat := [1, 4, 4, 1, 1, 2, 3, 5]
def baseStart_1009757 : Nat := 118140960795 + 1009757 * 2 ^ 59
def prefixEnd_1009757 : Nat := 4983230072969 + 3 ^ 40 * 1009757 * 2
def baseEnd_1009757 : Nat := 76813434850683119228699

theorem tailTrace_1009757 : CollatzResearch.WordTrace tailWord_1009757 prefixEnd_1009757 76813434850683119228699 := by
  unfold tailWord_1009757
  simp only [CollatzResearch.WordTrace]
  refine ⟨36828863402830316611043525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552575601886877740695683 36828863402830316611043525)
  ·
    refine ⟨6905411888030684364570661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36828863402830316611043525 6905411888030684364570661)
    ·
      refine ⟨1294764729005753318356999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6905411888030684364570661 1294764729005753318356999)
      ·
        refine ⟨1942147093508629977535499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294764729005753318356999 1942147093508629977535499)
        ·
          refine ⟨2913220640262944966303249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942147093508629977535499 2913220640262944966303249)
          ·
            refine ⟨2184915480197208724727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913220640262944966303249 2184915480197208724727437)
            ·
              refine ⟨819343305073953271772789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184915480197208724727437 819343305073953271772789)
              ·
                refine ⟨76813434850683119228699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819343305073953271772789 76813434850683119228699)
                ·
                  rfl

theorem cell21_1009757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].length) (baseStart_1009757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009757 prefixEnd_1009757 := by exact prefixLift 1009757
  have htrace : WordTrace (prefixWord ++ tailWord_1009757) baseStart_1009757 baseEnd_1009757 := by
    simpa [prefixWord, tailWord_1009757, baseEnd_1009757] using wordTrace_append hprefix tailTrace_1009757
  have hstable : (prefixWord ++ tailWord_1009757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009757).length < 2 ^ (prefixWord ++ tailWord_1009757).sum := by decide
  have hdescent : baseEnd_1009757 < baseStart_1009757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009785 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1009785 : Nat := 118140960795 + 1009785 * 2 ^ 59
def prefixEnd_1009785 : Nat := 4983230072969 + 3 ^ 40 * 1009785 * 2
def baseEnd_1009785 : Nat := 230446694533527531219373

theorem tailTrace_1009785 : CollatzResearch.WordTrace tailWord_1009785 prefixEnd_1009785 230446694533527531219373 := by
  unfold tailWord_1009785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829884646728877393062809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24553256431152584928708539 36829884646728877393062809)
  ·
    refine ⟨27622413485046658044797107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36829884646728877393062809 27622413485046658044797107)
    ·
      refine ⟨41433620227569987067195661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27622413485046658044797107 41433620227569987067195661)
      ·
        refine ⟨15537607585338745150198373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41433620227569987067195661 15537607585338745150198373)
        ·
          refine ⟨2913301422251014715662195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15537607585338745150198373 2913301422251014715662195)
          ·
            refine ⟨4369952133376522073493293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913301422251014715662195 4369952133376522073493293)
            ·
              refine ⟨1638732050016195777559985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4369952133376522073493293 1638732050016195777559985)
              ·
                refine ⟨1229049037512146833169989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638732050016195777559985 1229049037512146833169989)
                ·
                  refine ⟨230446694533527531219373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229049037512146833169989 230446694533527531219373)
                  ·
                    rfl

theorem cell21_1009785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1009785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009785 prefixEnd_1009785 := by exact prefixLift 1009785
  have htrace : WordTrace (prefixWord ++ tailWord_1009785) baseStart_1009785 baseEnd_1009785 := by
    simpa [prefixWord, tailWord_1009785, baseEnd_1009785] using wordTrace_append hprefix tailTrace_1009785
  have hstable : (prefixWord ++ tailWord_1009785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009785).length < 2 ^ (prefixWord ++ tailWord_1009785).sum := by decide
  have hdescent : baseEnd_1009785 < baseStart_1009785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009802 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_1009802 : Nat := 118140960795 + 1009802 * 2 ^ 59
def prefixEnd_1009802 : Nat := 4983230072969 + 3 ^ 40 * 1009802 * 2
def baseEnd_1009802 : Nat := 230450574165139279436005

theorem tailTrace_1009802 : CollatzResearch.WordTrace tailWord_1009802 prefixEnd_1009802 230450574165139279436005 := by
  unfold tailWord_1009802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207626171916822324107915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24553669791778192864287773 9207626171916822324107915)
  ·
    refine ⟨13811439257875233486161873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9207626171916822324107915 13811439257875233486161873)
    ·
      refine ⟨10358579443406425114621405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13811439257875233486161873 10358579443406425114621405)
      ·
        refine ⟨3884467291277409417983027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10358579443406425114621405 3884467291277409417983027)
        ·
          refine ⟨5826700936916114126974541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884467291277409417983027 5826700936916114126974541)
          ·
            refine ⟨2185012851343542797615453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5826700936916114126974541 2185012851343542797615453)
            ·
              refine ⟨819379819253828549105795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185012851343542797615453 819379819253828549105795)
              ·
                refine ⟨1229069728880742823658693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819379819253828549105795 1229069728880742823658693)
                ·
                  refine ⟨230450574165139279436005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229069728880742823658693 230450574165139279436005)
                  ·
                    rfl

theorem cell21_1009802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_1009802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009802 prefixEnd_1009802 := by exact prefixLift 1009802
  have htrace : WordTrace (prefixWord ++ tailWord_1009802) baseStart_1009802 baseEnd_1009802 := by
    simpa [prefixWord, tailWord_1009802, baseEnd_1009802] using wordTrace_append hprefix tailTrace_1009802
  have hstable : (prefixWord ++ tailWord_1009802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009802).length < 2 ^ (prefixWord ++ tailWord_1009802).sum := by decide
  have hdescent : baseEnd_1009802 < baseStart_1009802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009813 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1009813 : Nat := 118140960795 + 1009813 * 2 ^ 59
def prefixEnd_1009813 : Nat := 4983230072969 + 3 ^ 40 * 1009813 * 2
def baseEnd_1009813 : Nat := 230453084515005704752649

theorem tailTrace_1009813 : CollatzResearch.WordTrace tailWord_1009813 prefixEnd_1009813 230453084515005704752649 := by
  unfold tailWord_1009813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36830905890627438175082093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24553937260418292116721395 36830905890627438175082093)
  ·
    refine ⟨13811589708985289315655785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36830905890627438175082093 13811589708985289315655785)
    ·
      refine ⟨10358692281738966986741839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13811589708985289315655785 10358692281738966986741839)
      ·
        refine ⟨15538038422608450480112759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358692281738966986741839 15538038422608450480112759)
        ·
          refine ⟨23307057633912675720169139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15538038422608450480112759 23307057633912675720169139)
          ·
            refine ⟨34960586450869013580253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23307057633912675720169139 34960586450869013580253709)
            ·
              refine ⟨13110219919075880092595141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34960586450869013580253709 13110219919075880092595141)
              ·
                refine ⟨2458166234826727517361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13110219919075880092595141 2458166234826727517361589)
                ·
                  refine ⟨230453084515005704752649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458166234826727517361589 230453084515005704752649)
                  ·
                    rfl

theorem cell21_1009813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1009813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009813 prefixEnd_1009813 := by exact prefixLift 1009813
  have htrace : WordTrace (prefixWord ++ tailWord_1009813) baseStart_1009813 baseEnd_1009813 := by
    simpa [prefixWord, tailWord_1009813, baseEnd_1009813] using wordTrace_append hprefix tailTrace_1009813
  have hstable : (prefixWord ++ tailWord_1009813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009813).length < 2 ^ (prefixWord ++ tailWord_1009813).sum := by decide
  have hdescent : baseEnd_1009813 < baseStart_1009813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009822 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1009822 : Nat := 118140960795 + 1009822 * 2 ^ 59
def prefixEnd_1009822 : Nat := 4983230072969 + 3 ^ 40 * 1009822 * 2
def baseEnd_1009822 : Nat := 230455138437623689102631

theorem tailTrace_1009822 : CollatzResearch.WordTrace tailWord_1009822 prefixEnd_1009822 230455138437623689102631 := by
  unfold tailWord_1009822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603904268449354089019965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24554156098396555141439813 4603904268449354089019965)
  ·
    refine ⟨1726464100668507783382487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4603904268449354089019965 1726464100668507783382487)
    ·
      refine ⟨2589696151002761675073731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726464100668507783382487 2589696151002761675073731)
      ·
        refine ⟨3884544226504142512610597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589696151002761675073731 3884544226504142512610597)
        ·
          refine ⟨728352042469526721114487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3884544226504142512610597 728352042469526721114487)
          ·
            refine ⟨1092528063704290081671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728352042469526721114487 1092528063704290081671731)
            ·
              refine ⟨1638792095556435122507597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092528063704290081671731 1638792095556435122507597)
              ·
                refine ⟨614547035833663170940349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638792095556435122507597 614547035833663170940349)
                ·
                  refine ⟨230455138437623689102631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614547035833663170940349 230455138437623689102631)
                  ·
                    rfl

theorem cell21_1009822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1009822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009822 prefixEnd_1009822 := by exact prefixLift 1009822
  have htrace : WordTrace (prefixWord ++ tailWord_1009822) baseStart_1009822 baseEnd_1009822 := by
    simpa [prefixWord, tailWord_1009822, baseEnd_1009822] using wordTrace_append hprefix tailTrace_1009822
  have hstable : (prefixWord ++ tailWord_1009822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009822).length < 2 ^ (prefixWord ++ tailWord_1009822).sum := by decide
  have hdescent : baseEnd_1009822 < baseStart_1009822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009861 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1009861 : Nat := 118140960795 + 1009861 * 2 ^ 59
def prefixEnd_1009861 : Nat := 4983230072969 + 3 ^ 40 * 1009861 * 2
def baseEnd_1009861 : Nat := 230464038768968287952551

theorem tailTrace_1009861 : CollatzResearch.WordTrace tailWord_1009861 prefixEnd_1009861 230464038768968287952551 := by
  unfold tailWord_1009861
  simp only [CollatzResearch.WordTrace]
  refine ⟨36832656594453542372829437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24555104396302361581886291 36832656594453542372829437)
  ·
    refine ⟨13812246222920078389811039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36832656594453542372829437 13812246222920078389811039)
    ·
      refine ⟨20718369334380117584716559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13812246222920078389811039 20718369334380117584716559)
      ·
        refine ⟨31077554001570176377074839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20718369334380117584716559 31077554001570176377074839)
        ·
          refine ⟨46616331002355264565612259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31077554001570176377074839 46616331002355264565612259)
          ·
            refine ⟨69924496503532896848418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46616331002355264565612259 69924496503532896848418389)
            ·
              refine ⟨819427693400776134942403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69924496503532896848418389 819427693400776134942403)
              ·
                refine ⟨1229141540101164202413605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819427693400776134942403 1229141540101164202413605)
                ·
                  refine ⟨230464038768968287952551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229141540101164202413605 230464038768968287952551)
                  ·
                    rfl

theorem cell21_1009861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1009861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009861 prefixEnd_1009861 := by exact prefixLift 1009861
  have htrace : WordTrace (prefixWord ++ tailWord_1009861) baseStart_1009861 baseEnd_1009861 := by
    simpa [prefixWord, tailWord_1009861, baseEnd_1009861] using wordTrace_append hprefix tailTrace_1009861
  have hstable : (prefixWord ++ tailWord_1009861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009861).length < 2 ^ (prefixWord ++ tailWord_1009861).sum := by decide
  have hdescent : baseEnd_1009861 < baseStart_1009861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009920 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_1009920 : Nat := 118140960795 + 1009920 * 2 ^ 59
def prefixEnd_1009920 : Nat := 4983230072969 + 3 ^ 40 * 1009920 * 2
def baseEnd_1009920 : Nat := 230477503372797296469097

theorem tailTrace_1009920 : CollatzResearch.WordTrace tailWord_1009920 prefixEnd_1009920 230477503372797296469097 := by
  unfold tailWord_1009920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417404250619897724613607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24556539000826530299484809 18417404250619897724613607)
  ·
    refine ⟨27626106375929846586920411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18417404250619897724613607 27626106375929846586920411)
    ·
      refine ⟨41439159563894769880380617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27626106375929846586920411 41439159563894769880380617)
      ·
        refine ⟨31079369672921077410285463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41439159563894769880380617 31079369672921077410285463)
        ·
          refine ⟨46619054509381616115428195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31079369672921077410285463 46619054509381616115428195)
          ·
            refine ⟨69928581764072424173142293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46619054509381616115428195 69928581764072424173142293)
            ·
              refine ⟨3277902270190894883116045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69928581764072424173142293 3277902270190894883116045)
              ·
                refine ⟨1229213351321585581168517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3277902270190894883116045 1229213351321585581168517)
                ·
                  refine ⟨230477503372797296469097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229213351321585581168517 230477503372797296469097)
                  ·
                    rfl

theorem cell21_1009920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_1009920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009920 prefixEnd_1009920 := by exact prefixLift 1009920
  have htrace : WordTrace (prefixWord ++ tailWord_1009920) baseStart_1009920 baseEnd_1009920 := by
    simpa [prefixWord, tailWord_1009920, baseEnd_1009920] using wordTrace_append hprefix tailTrace_1009920
  have hstable : (prefixWord ++ tailWord_1009920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009920).length < 2 ^ (prefixWord ++ tailWord_1009920).sum := by decide
  have hdescent : baseEnd_1009920 < baseStart_1009920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009954 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1009954 : Nat := 118140960795 + 1009954 * 2 ^ 59
def prefixEnd_1009954 : Nat := 4983230072969 + 3 ^ 40 * 1009954 * 2
def baseEnd_1009954 : Nat := 230485262636020792902361

theorem tailTrace_1009954 : CollatzResearch.WordTrace tailWord_1009954 prefixEnd_1009954 230485262636020792902361 := by
  unfold tailWord_1009954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209012145779154813991229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24557365722077746170643277 9209012145779154813991229)
  ·
    refine ⟨3453379554667183055246711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9209012145779154813991229 3453379554667183055246711)
    ·
      refine ⟨5180069332000774582870067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453379554667183055246711 5180069332000774582870067)
      ·
        refine ⟨7770103998001161874305101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180069332000774582870067 7770103998001161874305101)
        ·
          refine ⟨2913788999250435702864413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7770103998001161874305101 2913788999250435702864413)
          ·
            refine ⟨1092670874718913388574155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2913788999250435702864413 1092670874718913388574155)
            ·
              refine ⟨1639006312078370082861233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092670874718913388574155 1639006312078370082861233)
              ·
                refine ⟨1229254734058777562145925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639006312078370082861233 1229254734058777562145925)
                ·
                  refine ⟨230485262636020792902361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229254734058777562145925 230485262636020792902361)
                  ·
                    rfl

theorem cell21_1009954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1009954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009954 prefixEnd_1009954 := by exact prefixLift 1009954
  have htrace : WordTrace (prefixWord ++ tailWord_1009954) baseStart_1009954 baseEnd_1009954 := by
    simpa [prefixWord, tailWord_1009954, baseEnd_1009954] using wordTrace_append hprefix tailTrace_1009954
  have hstable : (prefixWord ++ tailWord_1009954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009954).length < 2 ^ (prefixWord ++ tailWord_1009954).sum := by decide
  have hdescent : baseEnd_1009954 < baseStart_1009954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009982 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1009982 : Nat := 118140960795 + 1009982 * 2 ^ 59
def prefixEnd_1009982 : Nat := 4983230072969 + 3 ^ 40 * 1009982 * 2
def baseEnd_1009982 : Nat := 230491652617498966435637

theorem tailTrace_1009982 : CollatzResearch.WordTrace tailWord_1009982 prefixEnd_1009982 230491652617498966435637 := by
  unfold tailWord_1009982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604633728376897504748025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24558046551343453358656133 4604633728376897504748025)
  ·
    refine ⟨3453475296282673128561019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4604633728376897504748025 3453475296282673128561019)
    ·
      refine ⟨5180212944424009692841529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453475296282673128561019 5180212944424009692841529)
      ·
        refine ⟨3885159708318007269631147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180212944424009692841529 3885159708318007269631147)
        ·
          refine ⟨5827739562477010904446721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885159708318007269631147 5827739562477010904446721)
          ·
            refine ⟨4370804671857758178335041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827739562477010904446721 4370804671857758178335041)
            ·
              refine ⟨3278103503893318633751281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370804671857758178335041 3278103503893318633751281)
              ·
                refine ⟨2458577627919988975313461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278103503893318633751281 2458577627919988975313461)
                ·
                  refine ⟨230491652617498966435637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458577627919988975313461 230491652617498966435637)
                  ·
                    rfl

theorem cell21_1009982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1009982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009982 prefixEnd_1009982 := by exact prefixLift 1009982
  have htrace : WordTrace (prefixWord ++ tailWord_1009982) baseStart_1009982 baseEnd_1009982 := by
    simpa [prefixWord, tailWord_1009982, baseEnd_1009982] using wordTrace_append hprefix tailTrace_1009982
  have hstable : (prefixWord ++ tailWord_1009982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009982).length < 2 ^ (prefixWord ++ tailWord_1009982).sum := by decide
  have hdescent : baseEnd_1009982 < baseStart_1009982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009985 : List Nat := [1, 2, 5, 2, 2, 2, 2, 5]
def baseStart_1009985 : Nat := 118140960795 + 1009985 * 2 ^ 59
def prefixEnd_1009985 : Nat := 4983230072969 + 3 ^ 40 * 1009985 * 2
def baseEnd_1009985 : Nat := 76830779086123875961877

theorem tailTrace_1009985 : CollatzResearch.WordTrace tailWord_1009985 prefixEnd_1009985 76830779086123875961877 := by
  unfold tailWord_1009985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837179246004311550343409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24558119497336207700228939 36837179246004311550343409)
  ·
    refine ⟨27627884434503233662757557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36837179246004311550343409 27627884434503233662757557)
    ·
      refine ⟨2590114165734678155883521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27627884434503233662757557 2590114165734678155883521)
      ·
        refine ⟨1942585624301008616912641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2590114165734678155883521 1942585624301008616912641)
        ·
          refine ⟨1456939218225756462684481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942585624301008616912641 1456939218225756462684481)
          ·
            refine ⟨1092704413669317347013361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456939218225756462684481 1092704413669317347013361)
            ·
              refine ⟨819528310251988010260021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092704413669317347013361 819528310251988010260021)
              ·
                refine ⟨76830779086123875961877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819528310251988010260021 76830779086123875961877)
                ·
                  rfl

theorem cell21_1009985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].length) (baseStart_1009985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1009985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1009985 prefixEnd_1009985 := by exact prefixLift 1009985
  have htrace : WordTrace (prefixWord ++ tailWord_1009985) baseStart_1009985 baseEnd_1009985 := by
    simpa [prefixWord, tailWord_1009985, baseEnd_1009985] using wordTrace_append hprefix tailTrace_1009985
  have hstable : (prefixWord ++ tailWord_1009985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009985).length < 2 ^ (prefixWord ++ tailWord_1009985).sum := by decide
  have hdescent : baseEnd_1009985 < baseStart_1009985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010016 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_1010016 : Nat := 118140960795 + 1010016 * 2 ^ 59
def prefixEnd_1010016 : Nat := 4983230072969 + 3 ^ 40 * 1010016 * 2
def baseEnd_1010016 : Nat := 230499411880722462868901

theorem tailTrace_1010016 : CollatzResearch.WordTrace tailWord_1010016 prefixEnd_1010016 230499411880722462868901 := by
  unfold tailWord_1010016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419154954446001922360951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24558873272594669229814601 18419154954446001922360951)
  ·
    refine ⟨27628732431669002883541427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419154954446001922360951 27628732431669002883541427)
    ·
      refine ⟨41443098647503504325312141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628732431669002883541427 41443098647503504325312141)
      ·
        refine ⟨15541161992813814121992053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41443098647503504325312141 15541161992813814121992053)
        ·
          refine ⟨1456983936826295073936755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15541161992813814121992053 1456983936826295073936755)
          ·
            refine ⟨2185475905239442610905133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456983936826295073936755 2185475905239442610905133)
            ·
              refine ⟨819553464464790979089425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185475905239442610905133 819553464464790979089425)
              ·
                refine ⟨614665098348593234317069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819553464464790979089425 614665098348593234317069)
                ·
                  refine ⟨230499411880722462868901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614665098348593234317069 230499411880722462868901)
                  ·
                    rfl

theorem cell21_1010016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_1010016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010016 prefixEnd_1010016 := by exact prefixLift 1010016
  have htrace : WordTrace (prefixWord ++ tailWord_1010016) baseStart_1010016 baseEnd_1010016 := by
    simpa [prefixWord, tailWord_1010016, baseEnd_1010016] using wordTrace_append hprefix tailTrace_1010016
  have hstable : (prefixWord ++ tailWord_1010016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010016).length < 2 ^ (prefixWord ++ tailWord_1010016).sum := by decide
  have hdescent : baseEnd_1010016 < baseStart_1010016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010103 : List Nat := [1, 1, 3, 1, 3, 4, 3, 5]
def baseStart_1010103 : Nat := 118140960795 + 1010103 * 2 ^ 59
def prefixEnd_1010103 : Nat := 4983230072969 + 3 ^ 40 * 1010103 * 2
def baseEnd_1010103 : Nat := 76839755488676548306241

theorem tailTrace_1010103 : CollatzResearch.WordTrace tailWord_1010103 prefixEnd_1010103 76839755488676548306241 := by
  unfold tailWord_1010103
  simp only [CollatzResearch.WordTrace]
  refine ⟨36841483059576817703138963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24560988706384545135425975 36841483059576817703138963)
  ·
    refine ⟨55262224589365226554708445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36841483059576817703138963 55262224589365226554708445)
    ·
      refine ⟨20723334221011959958015667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55262224589365226554708445 20723334221011959958015667)
      ·
        refine ⟨31085001331517939937023501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20723334221011959958015667 31085001331517939937023501)
        ·
          refine ⟨11656875499319227476383813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31085001331517939937023501 11656875499319227476383813)
          ·
            refine ⟨2185664156122355151821965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11656875499319227476383813 2185664156122355151821965)
            ·
              refine ⟨819624058545883181933237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185664156122355151821965 819624058545883181933237)
              ·
                refine ⟨76839755488676548306241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819624058545883181933237 76839755488676548306241)
                ·
                  rfl

theorem cell21_1010103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].length) (baseStart_1010103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010103 prefixEnd_1010103 := by exact prefixLift 1010103
  have htrace : WordTrace (prefixWord ++ tailWord_1010103) baseStart_1010103 baseEnd_1010103 := by
    simpa [prefixWord, tailWord_1010103, baseEnd_1010103] using wordTrace_append hprefix tailTrace_1010103
  have hstable : (prefixWord ++ tailWord_1010103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010103).length < 2 ^ (prefixWord ++ tailWord_1010103).sum := by decide
  have hdescent : baseEnd_1010103 < baseStart_1010103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010196 : List Nat := [2, 4, 3, 1, 1, 2, 2, 6]
def baseStart_1010196 : Nat := 118140960795 + 1010196 * 2 ^ 59
def prefixEnd_1010196 : Nat := 4983230072969 + 3 ^ 40 * 1010196 * 2
def baseEnd_1010196 : Nat := 76846830111027383289511

theorem tailTrace_1010196 : CollatzResearch.WordTrace tailWord_1010196 prefixEnd_1010196 76846830111027383289511 := by
  unfold tailWord_1010196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18422437524119947293137221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24563250032159929724182961 18422437524119947293137221)
  ·
    refine ⟨3454207035772490117463229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18422437524119947293137221 3454207035772490117463229)
    ·
      refine ⟨1295327638414683794048711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3454207035772490117463229 1295327638414683794048711)
      ·
        refine ⟨1942991457622025691073067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295327638414683794048711 1942991457622025691073067)
        ·
          refine ⟨2914487186433038536609601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942991457622025691073067 2914487186433038536609601)
          ·
            refine ⟨2185865389824778902457201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914487186433038536609601 2185865389824778902457201)
            ·
              refine ⟨1639399042368584176842901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185865389824778902457201 1639399042368584176842901)
              ·
                refine ⟨76846830111027383289511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639399042368584176842901 76846830111027383289511)
                ·
                  rfl

theorem cell21_1010196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_1010196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010196 prefixEnd_1010196 := by exact prefixLift 1010196
  have htrace : WordTrace (prefixWord ++ tailWord_1010196) baseStart_1010196 baseEnd_1010196 := by
    simpa [prefixWord, tailWord_1010196, baseEnd_1010196] using wordTrace_append hprefix tailTrace_1010196
  have hstable : (prefixWord ++ tailWord_1010196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010196).length < 2 ^ (prefixWord ++ tailWord_1010196).sum := by decide
  have hdescent : baseEnd_1010196 < baseStart_1010196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010199 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 4]
def baseStart_1010199 : Nat := 118140960795 + 1010199 * 2 ^ 59
def prefixEnd_1010199 : Nat := 4983230072969 + 3 ^ 40 * 1010199 * 2
def baseEnd_1010199 : Nat := 230541174973954811318527

theorem tailTrace_1010199 : CollatzResearch.WordTrace tailWord_1010199 prefixEnd_1010199 230541174973954811318527 := by
  unfold tailWord_1010199
  simp only [CollatzResearch.WordTrace]
  refine ⟨36844984467229026098633651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24563322978152684065755767 36844984467229026098633651)
  ·
    refine ⟨55267476700843539147950477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36844984467229026098633651 55267476700843539147950477)
    ·
      refine ⟨20725303762816327180481429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55267476700843539147950477 20725303762816327180481429)
      ·
        refine ⟨971498613882015336585067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20725303762816327180481429 971498613882015336585067)
        ·
          refine ⟨1457247920823023004877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971498613882015336585067 1457247920823023004877601)
          ·
            refine ⟨1092935940617267253658201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457247920823023004877601 1092935940617267253658201)
            ·
              refine ⟨819701955462950440243651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092935940617267253658201 819701955462950440243651)
              ·
                refine ⟨1229552933194425660365477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819701955462950440243651 1229552933194425660365477)
                ·
                  refine ⟨230541174973954811318527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229552933194425660365477 230541174973954811318527)
                  ·
                    rfl

theorem cell21_1010199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_1010199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010199 prefixEnd_1010199 := by exact prefixLift 1010199
  have htrace : WordTrace (prefixWord ++ tailWord_1010199) baseStart_1010199 baseEnd_1010199 := by
    simpa [prefixWord, tailWord_1010199, baseEnd_1010199] using wordTrace_append hprefix tailTrace_1010199
  have hstable : (prefixWord ++ tailWord_1010199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010199).length < 2 ^ (prefixWord ++ tailWord_1010199).sum := by decide
  have hdescent : baseEnd_1010199 < baseStart_1010199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010241 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1010241 : Nat := 118140960795 + 1010241 * 2 ^ 59
def prefixEnd_1010241 : Nat := 4983230072969 + 3 ^ 40 * 1010241 * 2
def baseEnd_1010241 : Nat := 230550759946172071618441

theorem tailTrace_1010241 : CollatzResearch.WordTrace tailWord_1010241 prefixEnd_1010241 230550759946172071618441 := by
  unfold tailWord_1010241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846516333076867271662577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564344222051244847775051 36846516333076867271662577)
  ·
    refine ⟨27634887249807650453746933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36846516333076867271662577 27634887249807650453746933)
    ·
      refine ⟨2590770679669467230038775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27634887249807650453746933 2590770679669467230038775)
      ·
        refine ⟨3886156019504200845058163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590770679669467230038775 3886156019504200845058163)
        ·
          refine ⟨5829234029256301267587245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886156019504200845058163 5829234029256301267587245)
          ·
            refine ⟨2185962760971112975345217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5829234029256301267587245 2185962760971112975345217)
            ·
              refine ⟨1639472070728334731508913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185962760971112975345217 1639472070728334731508913)
              ·
                refine ⟨1229604053046251048631685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639472070728334731508913 1229604053046251048631685)
                ·
                  refine ⟨230550759946172071618441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229604053046251048631685 230550759946172071618441)
                  ·
                    rfl

theorem cell21_1010241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1010241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010241 prefixEnd_1010241 := by exact prefixLift 1010241
  have htrace : WordTrace (prefixWord ++ tailWord_1010241) baseStart_1010241 baseEnd_1010241 := by
    simpa [prefixWord, tailWord_1010241, baseEnd_1010241] using wordTrace_append hprefix tailTrace_1010241
  have hstable : (prefixWord ++ tailWord_1010241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010241).length < 2 ^ (prefixWord ++ tailWord_1010241).sum := by decide
  have hdescent : baseEnd_1010241 < baseStart_1010241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010300 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_1010300 : Nat := 118140960795 + 1010300 * 2 ^ 59
def prefixEnd_1010300 : Nat := 4983230072969 + 3 ^ 40 * 1010300 * 2
def baseEnd_1010300 : Nat := 230564224550001080134987

theorem tailTrace_1010300 : CollatzResearch.WordTrace tailWord_1010300 prefixEnd_1010300 230564224550001080134987 := by
  unfold tailWord_1010300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424334119931560174030177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24565778826575413565373569 18424334119931560174030177)
  ·
    refine ⟨13818250589948670130522633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18424334119931560174030177 13818250589948670130522633)
    ·
      refine ⟨10363687942461502597891975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13818250589948670130522633 10363687942461502597891975)
      ·
        refine ⟨15545531913692253896837963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363687942461502597891975 15545531913692253896837963)
        ·
          refine ⟨23318297870538380845256945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15545531913692253896837963 23318297870538380845256945)
          ·
            refine ⟨17488723402903785633942709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23318297870538380845256945 17488723402903785633942709)
            ·
              refine ⟨1639567819022229903182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17488723402903785633942709 1639567819022229903182129)
              ·
                refine ⟨1229675864266672427386597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639567819022229903182129 1229675864266672427386597)
                ·
                  refine ⟨230564224550001080134987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229675864266672427386597 230564224550001080134987)
                  ·
                    rfl

theorem cell21_1010300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_1010300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010300 prefixEnd_1010300 := by exact prefixLift 1010300
  have htrace : WordTrace (prefixWord ++ tailWord_1010300) baseStart_1010300 baseEnd_1010300 := by
    simpa [prefixWord, tailWord_1010300, baseEnd_1010300] using wordTrace_append hprefix tailTrace_1010300
  have hstable : (prefixWord ++ tailWord_1010300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010300).length < 2 ^ (prefixWord ++ tailWord_1010300).sum := by decide
  have hdescent : baseEnd_1010300 < baseStart_1010300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010376 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_1010376 : Nat := 118140960795 + 1010376 * 2 ^ 59
def prefixEnd_1010376 : Nat := 4983230072969 + 3 ^ 40 * 1010376 * 2
def baseEnd_1010376 : Nat := 230581568785441836868165

theorem tailTrace_1010376 : CollatzResearch.WordTrace tailWord_1010376 prefixEnd_1010376 230581568785441836868165 := by
  unfold tailWord_1010376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425720093793892663913491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24567626791725190218551321 18425720093793892663913491)
  ·
    refine ⟨27638580140690838995870237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18425720093793892663913491 27638580140690838995870237)
    ·
      refine ⟨10364467552759064623451339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27638580140690838995870237 10364467552759064623451339)
      ·
        refine ⟨15546701329138596935177009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364467552759064623451339 15546701329138596935177009)
        ·
          refine ⟨11660025996853947701382757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15546701329138596935177009 11660025996853947701382757)
          ·
            refine ⟨2186254874410115194009267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11660025996853947701382757 2186254874410115194009267)
            ·
              refine ⟨3279382311615172791013901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186254874410115194009267 3279382311615172791013901)
              ·
                refine ⟨1229768366855689796630213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279382311615172791013901 1229768366855689796630213)
                ·
                  refine ⟨230581568785441836868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229768366855689796630213 230581568785441836868165)
                  ·
                    rfl

theorem cell21_1010376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_1010376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010376 prefixEnd_1010376 := by exact prefixLift 1010376
  have htrace : WordTrace (prefixWord ++ tailWord_1010376) baseStart_1010376 baseEnd_1010376 := by
    simpa [prefixWord, tailWord_1010376, baseEnd_1010376] using wordTrace_append hprefix tailTrace_1010376
  have hstable : (prefixWord ++ tailWord_1010376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010376).length < 2 ^ (prefixWord ++ tailWord_1010376).sum := by decide
  have hdescent : baseEnd_1010376 < baseStart_1010376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010449 : List Nat := [1, 2, 2, 1, 1, 3, 2, 9]
def baseStart_1010449 : Nat := 118140960795 + 1010449 * 2 ^ 59
def prefixEnd_1010449 : Nat := 4983230072969 + 3 ^ 40 * 1010449 * 2
def baseEnd_1010449 : Nat := 76866076126669977383783

theorem tailTrace_1010449 : CollatzResearch.WordTrace tailWord_1010449 prefixEnd_1010449 76866076126669977383783 := by
  unfold tailWord_1010449
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854102716323318795234401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569401810882212530156267 36854102716323318795234401)
  ·
    refine ⟨27640577037242489096425801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36854102716323318795234401 27640577037242489096425801)
    ·
      refine ⟨20730432777931866822319351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27640577037242489096425801 20730432777931866822319351)
      ·
        refine ⟨31095649166897800233479027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20730432777931866822319351 31095649166897800233479027)
        ·
          refine ⟨46643473750346700350218541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31095649166897800233479027 46643473750346700350218541)
          ·
            refine ⟨17491302656380012631331953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46643473750346700350218541 17491302656380012631331953)
            ·
              refine ⟨13118476992285009473498965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17491302656380012631331953 13118476992285009473498965)
              ·
                refine ⟨76866076126669977383783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13118476992285009473498965 76866076126669977383783)
                ·
                  rfl

theorem cell21_1010449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_1010449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010449 prefixEnd_1010449 := by exact prefixLift 1010449
  have htrace : WordTrace (prefixWord ++ tailWord_1010449) baseStart_1010449 baseEnd_1010449 := by
    simpa [prefixWord, tailWord_1010449, baseEnd_1010449] using wordTrace_append hprefix tailTrace_1010449
  have hstable : (prefixWord ++ tailWord_1010449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010449).length < 2 ^ (prefixWord ++ tailWord_1010449).sum := by decide
  have hdescent : baseEnd_1010449 < baseStart_1010449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010455 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 3]
def baseStart_1010455 : Nat := 118140960795 + 1010455 * 2 ^ 59
def prefixEnd_1010455 : Nat := 4983230072969 + 3 ^ 40 * 1010455 * 2
def baseEnd_1010455 : Nat := 230599597661755255051337

theorem tailTrace_1010455 : CollatzResearch.WordTrace tailWord_1010455 prefixEnd_1010455 230599597661755255051337 := by
  unfold tailWord_1010455
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854321554301581819952819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569547702867721213301879 36854321554301581819952819)
  ·
    refine ⟨55281482331452372729929229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36854321554301581819952819 55281482331452372729929229)
    ·
      refine ⟨20730555874294639773723461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55281482331452372729929229 20730555874294639773723461)
      ·
        refine ⟨3886979226430244957573149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20730555874294639773723461 3886979226430244957573149)
        ·
          refine ⟨1457617209911341859089931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3886979226430244957573149 1457617209911341859089931)
          ·
            refine ⟨2186425814867012788634897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457617209911341859089931 2186425814867012788634897)
            ·
              refine ⟨1639819361150259591476173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186425814867012788634897 1639819361150259591476173)
              ·
                refine ⟨614932260431347346803565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639819361150259591476173 614932260431347346803565)
                ·
                  refine ⟨230599597661755255051337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614932260431347346803565 230599597661755255051337)
                  ·
                    rfl

theorem cell21_1010455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].length) (baseStart_1010455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010455 prefixEnd_1010455 := by exact prefixLift 1010455
  have htrace : WordTrace (prefixWord ++ tailWord_1010455) baseStart_1010455 baseEnd_1010455 := by
    simpa [prefixWord, tailWord_1010455, baseEnd_1010455] using wordTrace_append hprefix tailTrace_1010455
  have hstable : (prefixWord ++ tailWord_1010455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010455).length < 2 ^ (prefixWord ++ tailWord_1010455).sum := by decide
  have hdescent : baseEnd_1010455 < baseStart_1010455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010466 : List Nat := [3, 3, 1, 1, 2, 3, 8]
def baseStart_1010466 : Nat := 118140960795 + 1010466 * 2 ^ 59
def prefixEnd_1010466 : Nat := 4983230072969 + 3 ^ 40 * 1010466 * 2
def baseEnd_1010466 : Nat := 25622456445735742263109

theorem tailTrace_1010466 : CollatzResearch.WordTrace tailWord_1010466 prefixEnd_1010466 25622456445735742263109 := by
  unfold tailWord_1010466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213680689315432674650813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24569815171507820465735501 9213680689315432674650813)
  ·
    refine ⟨3455130258493287252994055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9213680689315432674650813 3455130258493287252994055)
    ·
      refine ⟨5182695387739930879491083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455130258493287252994055 5182695387739930879491083)
      ·
        refine ⟨7774043081609896319236625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182695387739930879491083 7774043081609896319236625)
        ·
          refine ⟨5830532311207422239427469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774043081609896319236625 5830532311207422239427469)
          ·
            refine ⟨2186449616702783339785301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5830532311207422239427469 2186449616702783339785301)
            ·
              refine ⟨25622456445735742263109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2186449616702783339785301 25622456445735742263109)
              ·
                rfl

theorem cell21_1010466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 8].length) (baseStart_1010466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010466 prefixEnd_1010466 := by exact prefixLift 1010466
  have htrace : WordTrace (prefixWord ++ tailWord_1010466) baseStart_1010466 baseEnd_1010466 := by
    simpa [prefixWord, tailWord_1010466, baseEnd_1010466] using wordTrace_append hprefix tailTrace_1010466
  have hstable : (prefixWord ++ tailWord_1010466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010466).length < 2 ^ (prefixWord ++ tailWord_1010466).sum := by decide
  have hdescent : baseEnd_1010466 < baseStart_1010466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010500 : List Nat := [2, 3, 4, 2, 1, 1, 1, 7]
def baseStart_1010500 : Nat := 118140960795 + 1010500 * 2 ^ 59
def prefixEnd_1010500 : Nat := 4983230072969 + 3 ^ 40 * 1010500 * 2
def baseEnd_1010500 : Nat := 76869955758281725600415

theorem tailTrace_1010500 : CollatzResearch.WordTrace tailWord_1010500 prefixEnd_1010500 76869955758281725600415 := by
  unfold tailWord_1010500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427981419569277252670477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24570641892759036336893969 18427981419569277252670477)
  ·
    refine ⟨6910493032338478969751429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18427981419569277252670477 6910493032338478969751429)
    ·
      refine ⟨1295717443563464806828393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6910493032338478969751429 1295717443563464806828393)
      ·
        refine ⟨971788082672598605121295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295717443563464806828393 971788082672598605121295)
        ·
          refine ⟨1457682124008897907681943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971788082672598605121295 1457682124008897907681943)
          ·
            refine ⟨2186523186013346861522915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457682124008897907681943 2186523186013346861522915)
            ·
              refine ⟨3279784779020020292284373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186523186013346861522915 3279784779020020292284373)
              ·
                refine ⟨76869955758281725600415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3279784779020020292284373 76869955758281725600415)
                ·
                  rfl

theorem cell21_1010500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_1010500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010500 prefixEnd_1010500 := by exact prefixLift 1010500
  have htrace : WordTrace (prefixWord ++ tailWord_1010500) baseStart_1010500 baseEnd_1010500 := by
    simpa [prefixWord, tailWord_1010500, baseEnd_1010500] using wordTrace_append hprefix tailTrace_1010500
  have hstable : (prefixWord ++ tailWord_1010500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010500).length < 2 ^ (prefixWord ++ tailWord_1010500).sum := by decide
  have hdescent : baseEnd_1010500 < baseStart_1010500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010531 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 3]
def baseStart_1010531 : Nat := 118140960795 + 1010531 * 2 ^ 59
def prefixEnd_1010531 : Nat := 4983230072969 + 3 ^ 40 * 1010531 * 2
def baseEnd_1010531 : Nat := 230616941897196011784515

theorem tailTrace_1010531 : CollatzResearch.WordTrace tailWord_1010531 prefixEnd_1010531 230616941897196011784515 := by
  unfold tailWord_1010531
  simp only [CollatzResearch.WordTrace]
  refine ⟨36857093502026246799719447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24571395668017497866479631 36857093502026246799719447)
  ·
    refine ⟨55285640253039370199579171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36857093502026246799719447 55285640253039370199579171)
    ·
      refine ⟨82928460379559055299368757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55285640253039370199579171 82928460379559055299368757)
      ·
        refine ⟨7774543160583661434315821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82928460379559055299368757 7774543160583661434315821)
        ·
          refine ⟨2915453685218873037868433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7774543160583661434315821 2915453685218873037868433)
          ·
            refine ⟨2186590263914154778401325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915453685218873037868433 2186590263914154778401325)
            ·
              refine ⟨819971348967808041900497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2186590263914154778401325 819971348967808041900497)
              ·
                refine ⟨614978511725856031425373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819971348967808041900497 614978511725856031425373)
                ·
                  refine ⟨230616941897196011784515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614978511725856031425373 230616941897196011784515)
                  ·
                    rfl

theorem cell21_1010531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].length) (baseStart_1010531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010531 prefixEnd_1010531 := by exact prefixLift 1010531
  have htrace : WordTrace (prefixWord ++ tailWord_1010531) baseStart_1010531 baseEnd_1010531 := by
    simpa [prefixWord, tailWord_1010531, baseEnd_1010531] using wordTrace_append hprefix tailTrace_1010531
  have hstable : (prefixWord ++ tailWord_1010531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010531).length < 2 ^ (prefixWord ++ tailWord_1010531).sum := by decide
  have hdescent : baseEnd_1010531 < baseStart_1010531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010545 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 4]
def baseStart_1010545 : Nat := 118140960795 + 1010545 * 2 ^ 59
def prefixEnd_1010545 : Nat := 4983230072969 + 3 ^ 40 * 1010545 * 2
def baseEnd_1010545 : Nat := 230620136887935098551153

theorem tailTrace_1010545 : CollatzResearch.WordTrace tailWord_1010545 prefixEnd_1010545 230620136887935098551153 := by
  unfold tailWord_1010545
  simp only [CollatzResearch.WordTrace]
  refine ⟨36857604123975527190729089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24571736082650351460486059 36857604123975527190729089)
  ·
    refine ⟨27643203092981645393046817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36857604123975527190729089 27643203092981645393046817)
    ·
      refine ⟨20732402319736234044785113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27643203092981645393046817 20732402319736234044785113)
      ·
        refine ⟨15549301739802175533588835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20732402319736234044785113 15549301739802175533588835)
        ·
          refine ⟨23323952609703263300383253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549301739802175533588835 23323952609703263300383253)
          ·
            refine ⟨1093310278579840467205465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23323952609703263300383253 1093310278579840467205465)
            ·
              refine ⟨819982708934880350404099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093310278579840467205465 819982708934880350404099)
              ·
                refine ⟨1229974063402320525606149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819982708934880350404099 1229974063402320525606149)
                ·
                  refine ⟨230620136887935098551153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229974063402320525606149 230620136887935098551153)
                  ·
                    rfl

theorem cell21_1010545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_1010545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010545 prefixEnd_1010545 := by exact prefixLift 1010545
  have htrace : WordTrace (prefixWord ++ tailWord_1010545) baseStart_1010545 baseEnd_1010545 := by
    simpa [prefixWord, tailWord_1010545, baseEnd_1010545] using wordTrace_append hprefix tailTrace_1010545
  have hstable : (prefixWord ++ tailWord_1010545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010545).length < 2 ^ (prefixWord ++ tailWord_1010545).sum := by decide
  have hdescent : baseEnd_1010545 < baseStart_1010545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010556 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1010556 : Nat := 118140960795 + 1010556 * 2 ^ 59
def prefixEnd_1010556 : Nat := 4983230072969 + 3 ^ 40 * 1010556 * 2
def baseEnd_1010556 : Nat := 230622647237801523867797

theorem tailTrace_1010556 : CollatzResearch.WordTrace tailWord_1010556 prefixEnd_1010556 230622647237801523867797 := by
  unfold tailWord_1010556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429002663467838034689761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24572003551290450712919681 18429002663467838034689761)
  ·
    refine ⟨13821751997600878526017321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18429002663467838034689761 13821751997600878526017321)
    ·
      refine ⟨10366313998200658894512991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13821751997600878526017321 10366313998200658894512991)
      ·
        refine ⟨15549470997300988341769487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366313998200658894512991 15549470997300988341769487)
        ·
          refine ⟨23324206495951482512654231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549470997300988341769487 23324206495951482512654231)
          ·
            refine ⟨34986309743927223768981347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23324206495951482512654231 34986309743927223768981347)
            ·
              refine ⟨52479464615890835653472021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34986309743927223768981347 52479464615890835653472021)
              ·
                refine ⟨2459974903869882921256501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52479464615890835653472021 2459974903869882921256501)
                ·
                  refine ⟨230622647237801523867797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2459974903869882921256501 230622647237801523867797)
                  ·
                    rfl

theorem cell21_1010556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1010556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010556 prefixEnd_1010556 := by exact prefixLift 1010556
  have htrace : WordTrace (prefixWord ++ tailWord_1010556) baseStart_1010556 baseEnd_1010556 := by
    simpa [prefixWord, tailWord_1010556, baseEnd_1010556] using wordTrace_append hprefix tailTrace_1010556
  have hstable : (prefixWord ++ tailWord_1010556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010556).length < 2 ^ (prefixWord ++ tailWord_1010556).sum := by decide
  have hdescent : baseEnd_1010556 < baseStart_1010556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010582 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1010582 : Nat := 118140960795 + 1010582 * 2 ^ 59
def prefixEnd_1010582 : Nat := 4983230072969 + 3 ^ 40 * 1010582 * 2
def baseEnd_1010582 : Nat := 230628580792031256434411

theorem tailTrace_1010582 : CollatzResearch.WordTrace tailWord_1010582 prefixEnd_1010582 230628580792031256434411 := by
  unfold tailWord_1010582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303684601552592656864125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24572635749894321673217333 2303684601552592656864125)
  ·
    refine ⟨863881725582222246324047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2303684601552592656864125 863881725582222246324047)
    ·
      refine ⟨1295822588373333369486071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863881725582222246324047 1295822588373333369486071)
      ·
        refine ⟨1943733882560000054229107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295822588373333369486071 1943733882560000054229107)
        ·
          refine ⟨2915600823840000081343661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943733882560000054229107 2915600823840000081343661)
          ·
            refine ⟨1093350308940000030503873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2915600823840000081343661 1093350308940000030503873)
            ·
              refine ⟨820012731705000022877905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093350308940000030503873 820012731705000022877905)
              ·
                refine ⟨615009548778750017158429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820012731705000022877905 615009548778750017158429)
                ·
                  refine ⟨230628580792031256434411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615009548778750017158429 230628580792031256434411)
                  ·
                    rfl

theorem cell21_1010582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1010582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010582 prefixEnd_1010582 := by exact prefixLift 1010582
  have htrace : WordTrace (prefixWord ++ tailWord_1010582) baseStart_1010582 baseEnd_1010582 := by
    simpa [prefixWord, tailWord_1010582, baseEnd_1010582] using wordTrace_append hprefix tailTrace_1010582
  have hstable : (prefixWord ++ tailWord_1010582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010582).length < 2 ^ (prefixWord ++ tailWord_1010582).sum := by decide
  have hdescent : baseEnd_1010582 < baseStart_1010582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010618 : List Nat := [3, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1010618 : Nat := 118140960795 + 1010618 * 2 ^ 59
def prefixEnd_1010618 : Nat := 4983230072969 + 3 ^ 40 * 1010618 * 2
def baseEnd_1010618 : Nat := 76878932160834397944779

theorem tailTrace_1010618 : CollatzResearch.WordTrace tailWord_1010618 prefixEnd_1010618 76878932160834397944779 := by
  unfold tailWord_1010618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215066663177765164534127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24573511101807373772091005 9215066663177765164534127)
  ·
    refine ⟨13822599994766647746801191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9215066663177765164534127 13822599994766647746801191)
    ·
      refine ⟨20733899992149971620201787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13822599994766647746801191 20733899992149971620201787)
      ·
        refine ⟨31100849988224957430302681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20733899992149971620201787 31100849988224957430302681)
        ·
          refine ⟨23325637491168718072727011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31100849988224957430302681 23325637491168718072727011)
          ·
            refine ⟨34988456236753077109090517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325637491168718072727011 34988456236753077109090517)
            ·
              refine ⟨820041943048900244744309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34988456236753077109090517 820041943048900244744309)
              ·
                refine ⟨76878932160834397944779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820041943048900244744309 76878932160834397944779)
                ·
                  rfl

theorem cell21_1010618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1010618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010618 prefixEnd_1010618 := by exact prefixLift 1010618
  have htrace : WordTrace (prefixWord ++ tailWord_1010618) baseStart_1010618 baseEnd_1010618 := by
    simpa [prefixWord, tailWord_1010618, baseEnd_1010618] using wordTrace_append hprefix tailTrace_1010618
  have hstable : (prefixWord ++ tailWord_1010618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010618).length < 2 ^ (prefixWord ++ tailWord_1010618).sum := by decide
  have hdescent : baseEnd_1010618 < baseStart_1010618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010649 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1010649 : Nat := 118140960795 + 1010649 * 2 ^ 59
def prefixEnd_1010649 : Nat := 4983230072969 + 3 ^ 40 * 1010649 * 2
def baseEnd_1010649 : Nat := 230643871104854028817607

theorem tailTrace_1010649 : CollatzResearch.WordTrace tailWord_1010649 prefixEnd_1010649 230643871104854028817607 := by
  unfold tailWord_1010649
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861397315598752952515001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24574264877065835301676667 36861397315598752952515001)
  ·
    refine ⟨27646047986699064714386251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36861397315598752952515001 27646047986699064714386251)
    ·
      refine ⟨41469071980048597071579377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27646047986699064714386251 41469071980048597071579377)
      ·
        refine ⟨31101803985036447803684533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41469071980048597071579377 31101803985036447803684533)
        ·
          refine ⟨2915794123597166981595425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31101803985036447803684533 2915794123597166981595425)
          ·
            refine ⟨2186845592697875236196569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915794123597166981595425 2186845592697875236196569)
            ·
              refine ⟨1640134194523406427147427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186845592697875236196569 1640134194523406427147427)
              ·
                refine ⟨2460201291785109640721141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640134194523406427147427 2460201291785109640721141)
                ·
                  refine ⟨230643871104854028817607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2460201291785109640721141 230643871104854028817607)
                  ·
                    rfl

theorem cell21_1010649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1010649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010649 prefixEnd_1010649 := by exact prefixLift 1010649
  have htrace : WordTrace (prefixWord ++ tailWord_1010649) baseStart_1010649 baseEnd_1010649 := by
    simpa [prefixWord, tailWord_1010649, baseEnd_1010649] using wordTrace_append hprefix tailTrace_1010649
  have hstable : (prefixWord ++ tailWord_1010649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010649).length < 2 ^ (prefixWord ++ tailWord_1010649).sum := by decide
  have hdescent : baseEnd_1010649 < baseStart_1010649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010753 : List Nat := [1, 2, 5, 1, 12]
def baseStart_1010753 : Nat := 118140960795 + 1010753 * 2 ^ 59
def prefixEnd_1010753 : Nat := 4983230072969 + 3 ^ 40 * 1010753 * 2
def baseEnd_1010753 : Nat := 2847748213849048877581

theorem tailTrace_1010753 : CollatzResearch.WordTrace tailWord_1010753 prefixEnd_1010753 2847748213849048877581 := by
  unfold tailWord_1010753
  simp only [CollatzResearch.WordTrace]
  refine ⟨36865190507221978714300913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24576793671481319142867275 36865190507221978714300913)
  ·
    refine ⟨27648892880416484035725685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36865190507221978714300913 27648892880416484035725685)
    ·
      refine ⟨2592083707539045378349283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27648892880416484035725685 2592083707539045378349283)
      ·
        refine ⟨3888125561308568067523925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592083707539045378349283 3888125561308568067523925)
        ·
          refine ⟨2847748213849048877581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3888125561308568067523925 2847748213849048877581)
          ·
            rfl

theorem cell21_1010753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 12].length) (baseStart_1010753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010753 prefixEnd_1010753 := by exact prefixLift 1010753
  have htrace : WordTrace (prefixWord ++ tailWord_1010753) baseStart_1010753 baseEnd_1010753 := by
    simpa [prefixWord, tailWord_1010753, baseEnd_1010753] using wordTrace_append hprefix tailTrace_1010753
  have hstable : (prefixWord ++ tailWord_1010753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010753).length < 2 ^ (prefixWord ++ tailWord_1010753).sum := by decide
  have hdescent : baseEnd_1010753 < baseStart_1010753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010759 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 3]
def baseStart_1010759 : Nat := 118140960795 + 1010759 * 2 ^ 59
def prefixEnd_1010759 : Nat := 4983230072969 + 3 ^ 40 * 1010759 * 2
def baseEnd_1010759 : Nat := 230668974603518281984049

theorem tailTrace_1010759 : CollatzResearch.WordTrace tailWord_1010759 prefixEnd_1010759 230668974603518281984049 := by
  unfold tailWord_1010759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36865409345200241739019331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24576939563466827826012887 36865409345200241739019331)
  ·
    refine ⟨55298114017800362608528997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36865409345200241739019331 55298114017800362608528997)
    ·
      refine ⟨10368396378337567989099187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55298114017800362608528997 10368396378337567989099187)
      ·
        refine ⟨15552594567506351983648781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368396378337567989099187 15552594567506351983648781)
        ·
          refine ⟨5832222962814881993868293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15552594567506351983648781 5832222962814881993868293)
          ·
            refine ⟨1093541805527790373850305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5832222962814881993868293 1093541805527790373850305)
            ·
              refine ⟨820156354145842780387729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093541805527790373850305 820156354145842780387729)
              ·
                refine ⟨615117265609382085290797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820156354145842780387729 615117265609382085290797)
                ·
                  refine ⟨230668974603518281984049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615117265609382085290797 230668974603518281984049)
                  ·
                    rfl

theorem cell21_1010759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].length) (baseStart_1010759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010759 prefixEnd_1010759 := by exact prefixLift 1010759
  have htrace : WordTrace (prefixWord ++ tailWord_1010759) baseStart_1010759 baseEnd_1010759 := by
    simpa [prefixWord, tailWord_1010759, baseEnd_1010759] using wordTrace_append hprefix tailTrace_1010759
  have hstable : (prefixWord ++ tailWord_1010759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010759).length < 2 ^ (prefixWord ++ tailWord_1010759).sum := by decide
  have hdescent : baseEnd_1010759 < baseStart_1010759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010770 : List Nat := [3, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1010770 : Nat := 118140960795 + 1010770 * 2 ^ 59
def prefixEnd_1010770 : Nat := 4983230072969 + 3 ^ 40 * 1010770 * 2
def baseEnd_1010770 : Nat := 76890494984461569100231

theorem tailTrace_1010770 : CollatzResearch.WordTrace tailWord_1010770 prefixEnd_1010770 76890494984461569100231 := by
  unfold tailWord_1010770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216452637040097654417441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24577207032106927078446509 9216452637040097654417441)
  ·
    refine ⟨6912339477780073240813081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9216452637040097654417441 6912339477780073240813081)
    ·
      refine ⟨5184254608335054930609811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912339477780073240813081 5184254608335054930609811)
      ·
        refine ⟨7776381912502582395914717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184254608335054930609811 7776381912502582395914717)
        ·
          refine ⟨2916143217188468398468019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7776381912502582395914717 2916143217188468398468019)
          ·
            refine ⟨4374214825782702597702029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916143217188468398468019 4374214825782702597702029)
            ·
              refine ⟨1640330559668513474138261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374214825782702597702029 1640330559668513474138261)
              ·
                refine ⟨76890494984461569100231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1640330559668513474138261 76890494984461569100231)
                ·
                  rfl

theorem cell21_1010770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1010770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010770 prefixEnd_1010770 := by exact prefixLift 1010770
  have htrace : WordTrace (prefixWord ++ tailWord_1010770) baseStart_1010770 baseEnd_1010770 := by
    simpa [prefixWord, tailWord_1010770, baseEnd_1010770] using wordTrace_append hprefix tailTrace_1010770
  have hstable : (prefixWord ++ tailWord_1010770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010770).length < 2 ^ (prefixWord ++ tailWord_1010770).sum := by decide
  have hdescent : baseEnd_1010770 < baseStart_1010770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010784 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1010784 : Nat := 118140960795 + 1010784 * 2 ^ 59
def prefixEnd_1010784 : Nat := 4983230072969 + 3 ^ 40 * 1010784 * 2
def baseEnd_1010784 : Nat := 230674679944123794067331

theorem tailTrace_1010784 : CollatzResearch.WordTrace tailWord_1010784 prefixEnd_1010784 230674679944123794067331 := by
  unfold tailWord_1010784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433160585054835504339703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24577547446739780672452937 18433160585054835504339703)
  ·
    refine ⟨27649740877582253256509555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18433160585054835504339703 27649740877582253256509555)
    ·
      refine ⟨41474611316373379884764333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27649740877582253256509555 41474611316373379884764333)
      ·
        refine ⟨15552979243640017456786625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41474611316373379884764333 15552979243640017456786625)
        ·
          refine ⟨11664734432730013092589969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15552979243640017456786625 11664734432730013092589969)
          ·
            refine ⟨8748550824547509819442477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11664734432730013092589969 8748550824547509819442477)
            ·
              refine ⟨3280706559205316182290929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8748550824547509819442477 3280706559205316182290929)
              ·
                refine ⟨2460529919403987136718197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280706559205316182290929 2460529919403987136718197)
                ·
                  refine ⟨230674679944123794067331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2460529919403987136718197 230674679944123794067331)
                  ·
                    rfl

theorem cell21_1010784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1010784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010784 prefixEnd_1010784 := by exact prefixLift 1010784
  have htrace : WordTrace (prefixWord ++ tailWord_1010784) baseStart_1010784 baseEnd_1010784 := by
    simpa [prefixWord, tailWord_1010784, baseEnd_1010784] using wordTrace_append hprefix tailTrace_1010784
  have hstable : (prefixWord ++ tailWord_1010784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010784).length < 2 ^ (prefixWord ++ tailWord_1010784).sum := by decide
  have hdescent : baseEnd_1010784 < baseStart_1010784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010877 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1010877 : Nat := 118140960795 + 1010877 * 2 ^ 59
def prefixEnd_1010877 : Nat := 4983230072969 + 3 ^ 40 * 1010877 * 2
def baseEnd_1010877 : Nat := 230695903811176299017141

theorem tailTrace_1010877 : CollatzResearch.WordTrace tailWord_1010877 prefixEnd_1010877 230695903811176299017141 := by
  unfold tailWord_1010877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869713158772747891814885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579808772515165261209923 36869713158772747891814885)
  ·
    refine ⟨6913071217269890229715291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36869713158772747891814885 6913071217269890229715291)
    ·
      refine ⟨10369606825904835344572937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913071217269890229715291 10369606825904835344572937)
      ·
        refine ⟨7777205119428626508429703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10369606825904835344572937 7777205119428626508429703)
        ·
          refine ⟨11665807679142939762644555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777205119428626508429703 11665807679142939762644555)
          ·
            refine ⟨17498711518714409643966833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11665807679142939762644555 17498711518714409643966833)
            ·
              refine ⟨13124033639035807232975125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17498711518714409643966833 13124033639035807232975125)
              ·
                refine ⟨615189076829803464045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13124033639035807232975125 615189076829803464045709)
                ·
                  refine ⟨230695903811176299017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615189076829803464045709 230695903811176299017141)
                  ·
                    rfl

theorem cell21_1010877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1010877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010877 prefixEnd_1010877 := by exact prefixLift 1010877
  have htrace : WordTrace (prefixWord ++ tailWord_1010877) baseStart_1010877 baseEnd_1010877 := by
    simpa [prefixWord, tailWord_1010877, baseEnd_1010877] using wordTrace_append hprefix tailTrace_1010877
  have hstable : (prefixWord ++ tailWord_1010877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010877).length < 2 ^ (prefixWord ++ tailWord_1010877).sum := by decide
  have hdescent : baseEnd_1010877 < baseStart_1010877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010970 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_1010970 : Nat := 118140960795 + 1010970 * 2 ^ 59
def prefixEnd_1010970 : Nat := 4983230072969 + 3 ^ 40 * 1010970 * 2
def baseEnd_1010970 : Nat := 230717127678228803966951

theorem tailTrace_1010970 : CollatzResearch.WordTrace tailWord_1010970 prefixEnd_1010970 230717127678228803966951 := by
  unfold tailWord_1010970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218276286858956193737591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24582070098290549849966909 9218276286858956193737591)
  ·
    refine ⟨13827414430288434290606387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218276286858956193737591 13827414430288434290606387)
    ·
      refine ⟨20741121645432651435909581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827414430288434290606387 20741121645432651435909581)
      ·
        refine ⟨7777920617037244288466093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20741121645432651435909581 7777920617037244288466093)
        ·
          refine ⟨2916720231388966608174785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7777920617037244288466093 2916720231388966608174785)
          ·
            refine ⟨2187540173541724956131089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916720231388966608174785 2187540173541724956131089)
            ·
              refine ⟨1640655130156293717098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187540173541724956131089 1640655130156293717098317)
              ·
                refine ⟨615245673808610143911869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640655130156293717098317 615245673808610143911869)
                ·
                  refine ⟨230717127678228803966951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615245673808610143911869 230717127678228803966951)
                  ·
                    rfl

theorem cell21_1010970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_1010970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010970 prefixEnd_1010970 := by exact prefixLift 1010970
  have htrace : WordTrace (prefixWord ++ tailWord_1010970) baseStart_1010970 baseEnd_1010970 := by
    simpa [prefixWord, tailWord_1010970, baseEnd_1010970] using wordTrace_append hprefix tailTrace_1010970
  have hstable : (prefixWord ++ tailWord_1010970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010970).length < 2 ^ (prefixWord ++ tailWord_1010970).sum := by decide
  have hdescent : baseEnd_1010970 < baseStart_1010970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010981 : List Nat := [1, 3, 1, 2, 4, 2, 8]
def baseStart_1010981 : Nat := 118140960795 + 1010981 * 2 ^ 59
def prefixEnd_1010981 : Nat := 4983230072969 + 3 ^ 40 * 1010981 * 2
def baseEnd_1010981 : Nat := 25635515336455025475955

theorem tailTrace_1010981 : CollatzResearch.WordTrace tailWord_1010981 prefixEnd_1010981 25635515336455025475955 := by
  unfold tailWord_1010981
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873506350395973653600797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24582337566930649102400531 36873506350395973653600797)
  ·
    refine ⟨13827564881398490120100299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36873506350395973653600797 13827564881398490120100299)
    ·
      refine ⟨20741347322097735180150449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827564881398490120100299 20741347322097735180150449)
      ·
        refine ⟨15556010491573301385112837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741347322097735180150449 15556010491573301385112837)
        ·
          refine ⟨2916751967169994009708657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15556010491573301385112837 2916751967169994009708657)
          ·
            refine ⟨2187563975377495507281493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916751967169994009708657 2187563975377495507281493)
            ·
              refine ⟨25635515336455025475955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2187563975377495507281493 25635515336455025475955)
              ·
                rfl

theorem cell21_1010981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 8].length) (baseStart_1010981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010981 prefixEnd_1010981 := by exact prefixLift 1010981
  have htrace : WordTrace (prefixWord ++ tailWord_1010981) baseStart_1010981 baseEnd_1010981 := by
    simpa [prefixWord, tailWord_1010981, baseEnd_1010981] using wordTrace_append hprefix tailTrace_1010981
  have hstable : (prefixWord ++ tailWord_1010981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010981).length < 2 ^ (prefixWord ++ tailWord_1010981).sum := by decide
  have hdescent : baseEnd_1010981 < baseStart_1010981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010984 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_1010984 : Nat := 118140960795 + 1010984 * 2 ^ 59
def prefixEnd_1010984 : Nat := 4983230072969 + 3 ^ 40 * 1010984 * 2
def baseEnd_1010984 : Nat := 230720322668967890733589

theorem tailTrace_1010984 : CollatzResearch.WordTrace tailWord_1010984 prefixEnd_1010984 230720322668967890733589 := by
  unfold tailWord_1010984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436807884692552582980003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24582410512923403443973337 18436807884692552582980003)
  ·
    refine ⟨27655211827038828874470005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18436807884692552582980003 27655211827038828874470005)
    ·
      refine ⟨2592676108784890206981563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27655211827038828874470005 2592676108784890206981563)
      ·
        refine ⟨3889014163177335310472345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592676108784890206981563 3889014163177335310472345)
        ·
          refine ⟨2916760622383001482854259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3889014163177335310472345 2916760622383001482854259)
          ·
            refine ⟨4375140933574502224281389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916760622383001482854259 4375140933574502224281389)
            ·
              refine ⟨1640677850090438334105521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4375140933574502224281389 1640677850090438334105521)
              ·
                refine ⟨1230508387567828750579141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640677850090438334105521 1230508387567828750579141)
                ·
                  refine ⟨230720322668967890733589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230508387567828750579141 230720322668967890733589)
                  ·
                    rfl

theorem cell21_1010984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_1010984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1010984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1010984 prefixEnd_1010984 := by exact prefixLift 1010984
  have htrace : WordTrace (prefixWord ++ tailWord_1010984) baseStart_1010984 baseEnd_1010984 := by
    simpa [prefixWord, tailWord_1010984, baseEnd_1010984] using wordTrace_append hprefix tailTrace_1010984
  have hstable : (prefixWord ++ tailWord_1010984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010984).length < 2 ^ (prefixWord ++ tailWord_1010984).sum := by decide
  have hdescent : baseEnd_1010984 < baseStart_1010984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011001 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 4]
def baseStart_1011001 : Nat := 118140960795 + 1011001 * 2 ^ 59
def prefixEnd_1011001 : Nat := 4983230072969 + 3 ^ 40 * 1011001 * 2
def baseEnd_1011001 : Nat := 230724202300579638950221

theorem tailTrace_1011001 : CollatzResearch.WordTrace tailWord_1011001 prefixEnd_1011001 230724202300579638950221 := by
  unfold tailWord_1011001
  simp only [CollatzResearch.WordTrace]
  refine ⟨36874235810323517069328857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24582823873549011379552571 36874235810323517069328857)
  ·
    refine ⟨27655676857742637801996643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36874235810323517069328857 27655676857742637801996643)
    ·
      refine ⟨41483515286613956702994965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655676857742637801996643 41483515286613956702994965)
      ·
        refine ⟨1944539779060029220452889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41483515286613956702994965 1944539779060029220452889)
        ·
          refine ⟨1458404834295021915339667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944539779060029220452889 1458404834295021915339667)
          ·
            refine ⟨2187607251442532873009501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458404834295021915339667 2187607251442532873009501)
            ·
              refine ⟨820352719290949827378563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187607251442532873009501 820352719290949827378563)
              ·
                refine ⟨1230529078936424741067845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820352719290949827378563 1230529078936424741067845)
                ·
                  refine ⟨230724202300579638950221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230529078936424741067845 230724202300579638950221)
                  ·
                    rfl

theorem cell21_1011001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_1011001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011001 prefixEnd_1011001 := by exact prefixLift 1011001
  have htrace : WordTrace (prefixWord ++ tailWord_1011001) baseStart_1011001 baseEnd_1011001 := by
    simpa [prefixWord, tailWord_1011001, baseEnd_1011001] using wordTrace_append hprefix tailTrace_1011001
  have hstable : (prefixWord ++ tailWord_1011001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011001).length < 2 ^ (prefixWord ++ tailWord_1011001).sum := by decide
  have hdescent : baseEnd_1011001 < baseStart_1011001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011021 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1011021 : Nat := 118140960795 + 1011021 * 2 ^ 59
def prefixEnd_1011021 : Nat := 4983230072969 + 3 ^ 40 * 1011021 * 2
def baseEnd_1011021 : Nat := 230728766573064048616847

theorem tailTrace_1011021 : CollatzResearch.WordTrace tailWord_1011021 prefixEnd_1011021 230728766573064048616847 := by
  unfold tailWord_1011021
  simp only [CollatzResearch.WordTrace]
  refine ⟨36874965270251060485056917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24583310180167373656704611 36874965270251060485056917)
  ·
    refine ⟨1728513997043018460237043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36874965270251060485056917 1728513997043018460237043)
    ·
      refine ⟨2592770995564527690355565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728513997043018460237043 2592770995564527690355565)
      ·
        refine ⟨972289123336697883883337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2592770995564527690355565 972289123336697883883337)
        ·
          refine ⟨729216842502523412912503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972289123336697883883337 729216842502523412912503)
          ·
            refine ⟨1093825263753785119368755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729216842502523412912503 1093825263753785119368755)
            ·
              refine ⟨1640737895630677679053133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093825263753785119368755 1640737895630677679053133)
              ·
                refine ⟨615276710861504129644925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640737895630677679053133 615276710861504129644925)
                ·
                  refine ⟨230728766573064048616847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615276710861504129644925 230728766573064048616847)
                  ·
                    rfl

theorem cell21_1011021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1011021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011021 prefixEnd_1011021 := by exact prefixLift 1011021
  have htrace : WordTrace (prefixWord ++ tailWord_1011021) baseStart_1011021 baseEnd_1011021 := by
    simpa [prefixWord, tailWord_1011021, baseEnd_1011021] using wordTrace_append hprefix tailTrace_1011021
  have hstable : (prefixWord ++ tailWord_1011021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011021).length < 2 ^ (prefixWord ++ tailWord_1011021).sum := by decide
  have hdescent : baseEnd_1011021 < baseStart_1011021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011299 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_1011299 : Nat := 118140960795 + 1011299 * 2 ^ 59
def prefixEnd_1011299 : Nat := 4983230072969 + 3 ^ 40 * 1011299 * 2
def baseEnd_1011299 : Nat := 230792209960597342982945

theorem tailTrace_1011299 : CollatzResearch.WordTrace tailWord_1011299 prefixEnd_1011299 230792209960597342982945 := by
  unfold tailWord_1011299
  simp only [CollatzResearch.WordTrace]
  refine ⟨36885104763243913963676951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24590069842162609309117967 36885104763243913963676951)
  ·
    refine ⟨55327657144865870945515427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36885104763243913963676951 55327657144865870945515427)
    ·
      refine ⟨82991485717298806418273141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55327657144865870945515427 82991485717298806418273141)
      ·
        refine ⟨7780451785996763101713107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82991485717298806418273141 7780451785996763101713107)
        ·
          refine ⟨11670677678995144652569661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780451785996763101713107 11670677678995144652569661)
          ·
            refine ⟨4376504129623179244713623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11670677678995144652569661 4376504129623179244713623)
            ·
              refine ⟨6564756194434768867070435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376504129623179244713623 6564756194434768867070435)
              ·
                refine ⟨9847134291652153300605653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564756194434768867070435 9847134291652153300605653)
                ·
                  refine ⟨230792209960597342982945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9847134291652153300605653 230792209960597342982945)
                  ·
                    rfl

theorem cell21_1011299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_1011299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011299 prefixEnd_1011299 := by exact prefixLift 1011299
  have htrace : WordTrace (prefixWord ++ tailWord_1011299) baseStart_1011299 baseEnd_1011299 := by
    simpa [prefixWord, tailWord_1011299, baseEnd_1011299] using wordTrace_append hprefix tailTrace_1011299
  have hstable : (prefixWord ++ tailWord_1011299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011299).length < 2 ^ (prefixWord ++ tailWord_1011299).sum := by decide
  have hdescent : baseEnd_1011299 < baseStart_1011299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011361 : List Nat := [1, 2, 3, 3, 2, 2, 1, 7]
def baseStart_1011361 : Nat := 118140960795 + 1011361 * 2 ^ 59
def prefixEnd_1011361 : Nat := 4983230072969 + 3 ^ 40 * 1011361 * 2
def baseEnd_1011361 : Nat := 76935453068433004316495

theorem tailTrace_1011361 : CollatzResearch.WordTrace tailWord_1011361 prefixEnd_1011361 76935453068433004316495 := by
  unfold tailWord_1011361
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887366089019298552433937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24591577392679532368289291 36887366089019298552433937)
  ·
    refine ⟨27665524566764473914325453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36887366089019298552433937 27665524566764473914325453)
    ·
      refine ⟨10374571712536677717872045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27665524566764473914325453 10374571712536677717872045)
      ·
        refine ⟨3890464392201254144202017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10374571712536677717872045 3890464392201254144202017)
        ·
          refine ⟨2917848294150940608151513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3890464392201254144202017 2917848294150940608151513)
          ·
            refine ⟨2188386220613205456113635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2917848294150940608151513 2188386220613205456113635)
            ·
              refine ⟨3282579330919808184170453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188386220613205456113635 3282579330919808184170453)
              ·
                refine ⟨76935453068433004316495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3282579330919808184170453 76935453068433004316495)
                ·
                  rfl

theorem cell21_1011361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_1011361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011361 prefixEnd_1011361 := by exact prefixLift 1011361
  have htrace : WordTrace (prefixWord ++ tailWord_1011361) baseStart_1011361 baseEnd_1011361 := by
    simpa [prefixWord, tailWord_1011361, baseEnd_1011361] using wordTrace_append hprefix tailTrace_1011361
  have hstable : (prefixWord ++ tailWord_1011361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011361).length < 2 ^ (prefixWord ++ tailWord_1011361).sum := by decide
  have hdescent : baseEnd_1011361 < baseStart_1011361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011398 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1011398 : Nat := 118140960795 + 1011398 * 2 ^ 59
def prefixEnd_1011398 : Nat := 4983230072969 + 3 ^ 40 * 1011398 * 2
def baseEnd_1011398 : Nat := 230814803109395170832743

theorem tailTrace_1011398 : CollatzResearch.WordTrace tailWord_1011398 prefixEnd_1011398 230814803109395170832743 := by
  unfold tailWord_1011398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152772362183914183485339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24592477059923502581020565 1152772362183914183485339)
  ·
    refine ⟨1729158543275871275228009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1152772362183914183485339 1729158543275871275228009)
    ·
      refine ⟨1296868907456903456421007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1729158543275871275228009 1296868907456903456421007)
      ·
        refine ⟨1945303361185355184631511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296868907456903456421007 1945303361185355184631511)
        ·
          refine ⟨2917955041778032776947267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945303361185355184631511 2917955041778032776947267)
          ·
            refine ⟨4376932562667049165420901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917955041778032776947267 4376932562667049165420901)
            ·
              refine ⟨820674855500071718516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4376932562667049165420901 820674855500071718516419)
              ·
                refine ⟨1231012283250107577774629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820674855500071718516419 1231012283250107577774629)
                ·
                  refine ⟨230814803109395170832743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231012283250107577774629 230814803109395170832743)
                  ·
                    rfl

theorem cell21_1011398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1011398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011398 prefixEnd_1011398 := by exact prefixLift 1011398
  have htrace : WordTrace (prefixWord ++ tailWord_1011398) baseStart_1011398 baseEnd_1011398 := by
    simpa [prefixWord, tailWord_1011398, baseEnd_1011398] using wordTrace_append hprefix tailTrace_1011398
  have hstable : (prefixWord ++ tailWord_1011398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011398).length < 2 ^ (prefixWord ++ tailWord_1011398).sum := by decide
  have hdescent : baseEnd_1011398 < baseStart_1011398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011465 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1011465 : Nat := 118140960795 + 1011465 * 2 ^ 59
def prefixEnd_1011465 : Nat := 4983230072969 + 3 ^ 40 * 1011465 * 2
def baseEnd_1011465 : Nat := 230830093422217943215939

theorem tailTrace_1011465 : CollatzResearch.WordTrace tailWord_1011465 prefixEnd_1011465 230830093422217943215939 := by
  unfold tailWord_1011465
  simp only [CollatzResearch.WordTrace]
  refine ⟨36891159280642524314219849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24594106187095016209479899 36891159280642524314219849)
  ·
    refine ⟨27668369460481893235664887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36891159280642524314219849 27668369460481893235664887)
    ·
      refine ⟨41502554190722839853497331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27668369460481893235664887 41502554190722839853497331)
      ·
        refine ⟨62253831286084259780245997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41502554190722839853497331 62253831286084259780245997)
        ·
          refine ⟨23345186732281597417592249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62253831286084259780245997 23345186732281597417592249)
          ·
            refine ⟨17508890049211198063194187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23345186732281597417592249 17508890049211198063194187)
            ·
              refine ⟨26263335073816797094791281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508890049211198063194187 26263335073816797094791281)
              ·
                refine ⟨19697501305362597821093461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26263335073816797094791281 19697501305362597821093461)
                ·
                  refine ⟨230830093422217943215939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19697501305362597821093461 230830093422217943215939)
                  ·
                    rfl

theorem cell21_1011465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1011465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011465 prefixEnd_1011465 := by exact prefixLift 1011465
  have htrace : WordTrace (prefixWord ++ tailWord_1011465) baseStart_1011465 baseEnd_1011465 := by
    simpa [prefixWord, tailWord_1011465, baseEnd_1011465] using wordTrace_append hprefix tailTrace_1011465
  have hstable : (prefixWord ++ tailWord_1011465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011465).length < 2 ^ (prefixWord ++ tailWord_1011465).sum := by decide
  have hdescent : baseEnd_1011465 < baseStart_1011465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011527 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_1011527 : Nat := 118140960795 + 1011527 * 2 ^ 59
def prefixEnd_1011527 : Nat := 4983230072969 + 3 ^ 40 * 1011527 * 2
def baseEnd_1011527 : Nat := 230844242666919613182479

theorem tailTrace_1011527 : CollatzResearch.WordTrace tailWord_1011527 prefixEnd_1011527 230844242666919613182479 := by
  unfold tailWord_1011527
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893420606417908902976835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24595613737611939268651223 36893420606417908902976835)
  ·
    refine ⟨55340130909626863354465253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36893420606417908902976835 55340130909626863354465253)
    ·
      refine ⟨10376274545555036878962235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55340130909626863354465253 10376274545555036878962235)
      ·
        refine ⟨15564411818332555318443353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376274545555036878962235 15564411818332555318443353)
        ·
          refine ⟨11673308863749416488832515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15564411818332555318443353 11673308863749416488832515)
          ·
            refine ⟨17509963295624124733248773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673308863749416488832515 17509963295624124733248773)
            ·
              refine ⟨3283118117929523387484145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17509963295624124733248773 3283118117929523387484145)
              ·
                refine ⟨2462338588447142540613109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283118117929523387484145 2462338588447142540613109)
                ·
                  refine ⟨230844242666919613182479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2462338588447142540613109 230844242666919613182479)
                  ·
                    rfl

theorem cell21_1011527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_1011527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011527 prefixEnd_1011527 := by exact prefixLift 1011527
  have htrace : WordTrace (prefixWord ++ tailWord_1011527) baseStart_1011527 baseEnd_1011527 := by
    simpa [prefixWord, tailWord_1011527, baseEnd_1011527] using wordTrace_append hprefix tailTrace_1011527
  have hstable : (prefixWord ++ tailWord_1011527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011527).length < 2 ^ (prefixWord ++ tailWord_1011527).sum := by decide
  have hdescent : baseEnd_1011527 < baseStart_1011527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011606 : List Nat := [5, 3, 1, 1, 11]
def baseStart_1011606 : Nat := 118140960795 + 1011606 * 2 ^ 59
def prefixEnd_1011606 : Nat := 4983230072969 + 3 ^ 40 * 1011606 * 2
def baseEnd_1011606 : Nat := 2850151500533741127971

theorem tailTrace_1011606 : CollatzResearch.WordTrace tailWord_1011606 prefixEnd_1011606 2850151500533741127971 := by
  unfold tailWord_1011606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306018873320731587193917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24597534648754470263401781 2306018873320731587193917)
  ·
    refine ⟨864757077495274345197719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2306018873320731587193917 864757077495274345197719)
    ·
      refine ⟨1297135616242911517796579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864757077495274345197719 1297135616242911517796579)
      ·
        refine ⟨1945703424364367276694869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297135616242911517796579 1945703424364367276694869)
        ·
          refine ⟨2850151500533741127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1945703424364367276694869 2850151500533741127971)
          ·
            rfl

theorem cell21_1011606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 11].length) (baseStart_1011606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011606 prefixEnd_1011606 := by exact prefixLift 1011606
  have htrace : WordTrace (prefixWord ++ tailWord_1011606) baseStart_1011606 baseEnd_1011606 := by
    simpa [prefixWord, tailWord_1011606, baseEnd_1011606] using wordTrace_append hprefix tailTrace_1011606
  have hstable : (prefixWord ++ tailWord_1011606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011606).length < 2 ^ (prefixWord ++ tailWord_1011606).sum := by decide
  have hdescent : baseEnd_1011606 < baseStart_1011606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011679 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_1011679 : Nat := 118140960795 + 1011679 * 2 ^ 59
def prefixEnd_1011679 : Nat := 4983230072969 + 3 ^ 40 * 1011679 * 2
def baseEnd_1011679 : Nat := 230878931137801126648835

theorem tailTrace_1011679 : CollatzResearch.WordTrace tailWord_1011679 prefixEnd_1011679 230878931137801126648835 := by
  unfold tailWord_1011679
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898964501867238862510091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24599309667911492575006727 36898964501867238862510091)
  ·
    refine ⟨55348446752800858293765137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898964501867238862510091 55348446752800858293765137)
    ·
      refine ⟨41511335064600643720323853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55348446752800858293765137 41511335064600643720323853)
      ·
        refine ⟨15566750649225241395121445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41511335064600643720323853 15566750649225241395121445)
        ·
          refine ⟨2918765746729732761585271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15566750649225241395121445 2918765746729732761585271)
          ·
            refine ⟨4378148620094599142377907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918765746729732761585271 4378148620094599142377907)
            ·
              refine ⟨6567222930141898713566861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378148620094599142377907 6567222930141898713566861)
              ·
                refine ⟨2462708598803212017587573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6567222930141898713566861 2462708598803212017587573)
                ·
                  refine ⟨230878931137801126648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2462708598803212017587573 230878931137801126648835)
                  ·
                    rfl

theorem cell21_1011679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_1011679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011679 prefixEnd_1011679 := by exact prefixLift 1011679
  have htrace : WordTrace (prefixWord ++ tailWord_1011679) baseStart_1011679 baseEnd_1011679 := by
    simpa [prefixWord, tailWord_1011679, baseEnd_1011679] using wordTrace_append hprefix tailTrace_1011679
  have hstable : (prefixWord ++ tailWord_1011679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011679).length < 2 ^ (prefixWord ++ tailWord_1011679).sum := by decide
  have hdescent : baseEnd_1011679 < baseStart_1011679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011741 : List Nat := [1, 4, 2, 2, 2, 2, 2, 6]
def baseStart_1011741 : Nat := 118140960795 + 1011741 * 2 ^ 59
def prefixEnd_1011741 : Nat := 4983230072969 + 3 ^ 40 * 1011741 * 2
def baseEnd_1011741 : Nat := 76964360127500932205125

theorem tailTrace_1011741 : CollatzResearch.WordTrace tailWord_1011741 prefixEnd_1011741 76964360127500932205125 := by
  unfold tailWord_1011741
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901225827642623451267077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600817218428415634178051 36901225827642623451267077)
  ·
    refine ⟨6918979842682991897112577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36901225827642623451267077 6918979842682991897112577)
    ·
      refine ⟨5189234882012243922834433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6918979842682991897112577 5189234882012243922834433)
      ·
        refine ⟨3891926161509182942125825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189234882012243922834433 3891926161509182942125825)
        ·
          refine ⟨2918944621131887206594369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891926161509182942125825 2918944621131887206594369)
          ·
            refine ⟨2189208465848915404945777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918944621131887206594369 2189208465848915404945777)
            ·
              refine ⟨1641906349386686553709333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189208465848915404945777 1641906349386686553709333)
              ·
                refine ⟨76964360127500932205125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1641906349386686553709333 76964360127500932205125)
                ·
                  rfl

theorem cell21_1011741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_1011741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011741 prefixEnd_1011741 := by exact prefixLift 1011741
  have htrace : WordTrace (prefixWord ++ tailWord_1011741) baseStart_1011741 baseEnd_1011741 := by
    simpa [prefixWord, tailWord_1011741, baseEnd_1011741] using wordTrace_append hprefix tailTrace_1011741
  have hstable : (prefixWord ++ tailWord_1011741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011741).length < 2 ^ (prefixWord ++ tailWord_1011741).sum := by decide
  have hdescent : baseEnd_1011741 < baseStart_1011741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011772 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_1011772 : Nat := 118140960795 + 1011772 * 2 ^ 59
def prefixEnd_1011772 : Nat := 4983230072969 + 3 ^ 40 * 1011772 * 2
def baseEnd_1011772 : Nat := 230900155004853631598645

theorem tailTrace_1011772 : CollatzResearch.WordTrace tailWord_1011772 prefixEnd_1011772 230900155004853631598645 := by
  unfold tailWord_1011772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451178245265157872822785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24601570993686877163763713 18451178245265157872822785)
  ·
    refine ⟨13838383683948868404617089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18451178245265157872822785 13838383683948868404617089)
    ·
      refine ⟨10378787762961651303462817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13838383683948868404617089 10378787762961651303462817)
      ·
        refine ⟨7784090822221238477597113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378787762961651303462817 7784090822221238477597113)
        ·
          refine ⟨5838068116665928858197835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7784090822221238477597113 5838068116665928858197835)
          ·
            refine ⟨8757102174998893287296753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838068116665928858197835 8757102174998893287296753)
            ·
              refine ⟨6567826631249169965472565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8757102174998893287296753 6567826631249169965472565)
              ·
                refine ⟨615733746679609684263053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6567826631249169965472565 615733746679609684263053)
                ·
                  refine ⟨230900155004853631598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615733746679609684263053 230900155004853631598645)
                  ·
                    rfl

theorem cell21_1011772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_1011772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011772 prefixEnd_1011772 := by exact prefixLift 1011772
  have htrace : WordTrace (prefixWord ++ tailWord_1011772) baseStart_1011772 baseEnd_1011772 := by
    simpa [prefixWord, tailWord_1011772, baseEnd_1011772] using wordTrace_append hprefix tailTrace_1011772
  have hstable : (prefixWord ++ tailWord_1011772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011772).length < 2 ^ (prefixWord ++ tailWord_1011772).sum := by decide
  have hdescent : baseEnd_1011772 < baseStart_1011772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011789 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1011789 : Nat := 118140960795 + 1011789 * 2 ^ 59
def prefixEnd_1011789 : Nat := 4983230072969 + 3 ^ 40 * 1011789 * 2
def baseEnd_1011789 : Nat := 230904034636465379815277

theorem tailTrace_1011789 : CollatzResearch.WordTrace tailWord_1011789 prefixEnd_1011789 230904034636465379815277 := by
  unfold tailWord_1011789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36902976531468727649014421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24601984354312485099342947 36902976531468727649014421)
  ·
    refine ⟨1729827024912596608547551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36902976531468727649014421 1729827024912596608547551)
    ·
      refine ⟨2594740537368894912821327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729827024912596608547551 2594740537368894912821327)
      ·
        refine ⟨3892110806053342369231991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594740537368894912821327 3892110806053342369231991)
        ·
          refine ⟨5838166209080013553847987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892110806053342369231991 5838166209080013553847987)
          ·
            refine ⟨8757249313620020330771981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838166209080013553847987 8757249313620020330771981)
            ·
              refine ⟨3283968492607507624039493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8757249313620020330771981 3283968492607507624039493)
              ·
                refine ⟨615744092363907679507405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3283968492607507624039493 615744092363907679507405)
                ·
                  refine ⟨230904034636465379815277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615744092363907679507405 230904034636465379815277)
                  ·
                    rfl

theorem cell21_1011789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1011789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011789 prefixEnd_1011789 := by exact prefixLift 1011789
  have htrace : WordTrace (prefixWord ++ tailWord_1011789) baseStart_1011789 baseEnd_1011789 := by
    simpa [prefixWord, tailWord_1011789, baseEnd_1011789] using wordTrace_append hprefix tailTrace_1011789
  have hstable : (prefixWord ++ tailWord_1011789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011789).length < 2 ^ (prefixWord ++ tailWord_1011789).sum := by decide
  have hdescent : baseEnd_1011789 < baseStart_1011789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011800 : List Nat := [2, 1, 2, 2, 1, 4, 3, 6]
def baseStart_1011800 : Nat := 118140960795 + 1011800 * 2 ^ 59
def prefixEnd_1011800 : Nat := 4983230072969 + 3 ^ 40 * 1011800 * 2
def baseEnd_1011800 : Nat := 76968848328777268377307

theorem tailTrace_1011800 : CollatzResearch.WordTrace tailWord_1011800 prefixEnd_1011800 76968848328777268377307 := by
  unfold tailWord_1011800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451688867214438263832427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24602251822952584351776569 18451688867214438263832427)
  ·
    refine ⟨27677533300821657395748641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18451688867214438263832427 27677533300821657395748641)
    ·
      refine ⟨20758149975616243046811481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27677533300821657395748641 20758149975616243046811481)
      ·
        refine ⟨15568612481712182285108611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20758149975616243046811481 15568612481712182285108611)
        ·
          refine ⟨23352918722568273427662917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568612481712182285108611 23352918722568273427662917)
          ·
            refine ⟨4378672260481551267686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23352918722568273427662917 4378672260481551267686797)
            ·
              refine ⟨1642002097680581725382549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4378672260481551267686797 1642002097680581725382549)
              ·
                refine ⟨76968848328777268377307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1642002097680581725382549 76968848328777268377307)
                ·
                  rfl

theorem cell21_1011800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_1011800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011800 prefixEnd_1011800 := by exact prefixLift 1011800
  have htrace : WordTrace (prefixWord ++ tailWord_1011800) baseStart_1011800 baseEnd_1011800 := by
    simpa [prefixWord, tailWord_1011800, baseEnd_1011800] using wordTrace_append hprefix tailTrace_1011800
  have hstable : (prefixWord ++ tailWord_1011800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011800).length < 2 ^ (prefixWord ++ tailWord_1011800).sum := by decide
  have hdescent : baseEnd_1011800 < baseStart_1011800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011806 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1011806 : Nat := 118140960795 + 1011806 * 2 ^ 59
def prefixEnd_1011806 : Nat := 4983230072969 + 3 ^ 40 * 1011806 * 2
def baseEnd_1011806 : Nat := 230907914268077128031909

theorem tailTrace_1011806 : CollatzResearch.WordTrace tailWord_1011806 prefixEnd_1011806 230907914268077128031909 := by
  unfold tailWord_1011806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612949571550892444047909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24602397714938093034922181 4612949571550892444047909)
  ·
    refine ⟨864928044665792333258983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4612949571550892444047909 864928044665792333258983)
    ·
      refine ⟨1297392066998688499888475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864928044665792333258983 1297392066998688499888475)
      ·
        refine ⟨1946088100498032749832713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297392066998688499888475 1946088100498032749832713)
        ·
          refine ⟨1459566075373524562374535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946088100498032749832713 1459566075373524562374535)
          ·
            refine ⟨2189349113060286843561803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459566075373524562374535 2189349113060286843561803)
            ·
              refine ⟨3284023669590430265342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189349113060286843561803 3284023669590430265342705)
              ·
                refine ⟨2463017752192822699007029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3284023669590430265342705 2463017752192822699007029)
                ·
                  refine ⟨230907914268077128031909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463017752192822699007029 230907914268077128031909)
                  ·
                    rfl

theorem cell21_1011806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1011806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011806 prefixEnd_1011806 := by exact prefixLift 1011806
  have htrace : WordTrace (prefixWord ++ tailWord_1011806) baseStart_1011806 baseEnd_1011806 := by
    simpa [prefixWord, tailWord_1011806, baseEnd_1011806] using wordTrace_append hprefix tailTrace_1011806
  have hstable : (prefixWord ++ tailWord_1011806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011806).length < 2 ^ (prefixWord ++ tailWord_1011806).sum := by decide
  have hdescent : baseEnd_1011806 < baseStart_1011806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011848 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_1011848 : Nat := 118140960795 + 1011848 * 2 ^ 59
def prefixEnd_1011848 : Nat := 4983230072969 + 3 ^ 40 * 1011848 * 2
def baseEnd_1011848 : Nat := 230917499240294388331823

theorem tailTrace_1011848 : CollatzResearch.WordTrace tailWord_1011848 prefixEnd_1011848 230917499240294388331823 := by
  unfold tailWord_1011848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452564219127490362706099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24603418958836653816941465 18452564219127490362706099)
  ·
    refine ⟨27678846328691235544059149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18452564219127490362706099 27678846328691235544059149)
    ·
      refine ⟨10379567373259213329022181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27678846328691235544059149 10379567373259213329022181)
      ·
        refine ⟨1946168882486102499191659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10379567373259213329022181 1946168882486102499191659)
        ·
          refine ⟨2919253323729153748787489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946168882486102499191659 2919253323729153748787489)
          ·
            refine ⟨2189439992796865311590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919253323729153748787489 2189439992796865311590617)
            ·
              refine ⟨1642079994597648983692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189439992796865311590617 1642079994597648983692963)
              ·
                refine ⟨2463119991896473475539445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642079994597648983692963 2463119991896473475539445)
                ·
                  refine ⟨230917499240294388331823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463119991896473475539445 230917499240294388331823)
                  ·
                    rfl

theorem cell21_1011848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_1011848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011848 prefixEnd_1011848 := by exact prefixLift 1011848
  have htrace : WordTrace (prefixWord ++ tailWord_1011848) baseStart_1011848 baseEnd_1011848 := by
    simpa [prefixWord, tailWord_1011848, baseEnd_1011848] using wordTrace_append hprefix tailTrace_1011848
  have hstable : (prefixWord ++ tailWord_1011848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011848).length < 2 ^ (prefixWord ++ tailWord_1011848).sum := by decide
  have hdescent : baseEnd_1011848 < baseStart_1011848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011859 : List Nat := [1, 1, 1, 2, 1, 2, 3, 10]
def baseStart_1011859 : Nat := 118140960795 + 1011859 * 2 ^ 59
def prefixEnd_1011859 : Nat := 4983230072969 + 3 ^ 40 * 1011859 * 2
def baseEnd_1011859 : Nat := 76973336530053604549489

theorem tailTrace_1011859 : CollatzResearch.WordTrace tailWord_1011859 prefixEnd_1011859 76973336530053604549489 := by
  unfold tailWord_1011859
  simp only [CollatzResearch.WordTrace]
  refine ⟨36905529641215129604062631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24603686427476753069375087 36905529641215129604062631)
  ·
    refine ⟨55358294461822694406093947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36905529641215129604062631 55358294461822694406093947)
    ·
      refine ⟨83037441692734041609140921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55358294461822694406093947 83037441692734041609140921)
      ·
        refine ⟨62278081269550531206855691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83037441692734041609140921 62278081269550531206855691)
        ·
          refine ⟨93417121904325796810283537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62278081269550531206855691 93417121904325796810283537)
          ·
            refine ⟨70062841428244347607712653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93417121904325796810283537 70062841428244347607712653)
            ·
              refine ⟨26273565535591630352892245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70062841428244347607712653 26273565535591630352892245)
              ·
                refine ⟨76973336530053604549489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26273565535591630352892245 76973336530053604549489)
                ·
                  rfl

theorem cell21_1011859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_1011859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1011859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1011859 prefixEnd_1011859 := by exact prefixLift 1011859
  have htrace : WordTrace (prefixWord ++ tailWord_1011859) baseStart_1011859 baseEnd_1011859 := by
    simpa [prefixWord, tailWord_1011859, baseEnd_1011859] using wordTrace_append hprefix tailTrace_1011859
  have hstable : (prefixWord ++ tailWord_1011859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011859).length < 2 ^ (prefixWord ++ tailWord_1011859).sum := by decide
  have hdescent : baseEnd_1011859 < baseStart_1011859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012000 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_1012000 : Nat := 118140960795 + 1012000 * 2 ^ 59
def prefixEnd_1012000 : Nat := 4983230072969 + 3 ^ 40 * 1012000 * 2
def baseEnd_1012000 : Nat := 230952187711175901798179

theorem tailTrace_1012000 : CollatzResearch.WordTrace tailWord_1012000 prefixEnd_1012000 230952187711175901798179 := by
  unfold tailWord_1012000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455336166852155342472727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24607114889136207123296969 18455336166852155342472727)
  ·
    refine ⟨27683004250278233013709091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455336166852155342472727 27683004250278233013709091)
    ·
      refine ⟨41524506375417349520563637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27683004250278233013709091 41524506375417349520563637)
      ·
        refine ⟨3892922472695376517552841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41524506375417349520563637 3892922472695376517552841)
        ·
          refine ⟨2919691854521532388164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3892922472695376517552841 2919691854521532388164631)
          ·
            refine ⟨4379537781782298582246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919691854521532388164631 4379537781782298582246947)
            ·
              refine ⟨6569306672673447873370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379537781782298582246947 6569306672673447873370421)
              ·
                refine ⟨615872500563135738128477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6569306672673447873370421 615872500563135738128477)
                ·
                  refine ⟨230952187711175901798179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615872500563135738128477 230952187711175901798179)
                  ·
                    rfl

theorem cell21_1012000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_1012000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012000 prefixEnd_1012000 := by exact prefixLift 1012000
  have htrace : WordTrace (prefixWord ++ tailWord_1012000) baseStart_1012000 baseEnd_1012000 := by
    simpa [prefixWord, tailWord_1012000, baseEnd_1012000] using wordTrace_append hprefix tailTrace_1012000
  have hstable : (prefixWord ++ tailWord_1012000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012000).length < 2 ^ (prefixWord ++ tailWord_1012000).sum := by decide
  have hdescent : baseEnd_1012000 < baseStart_1012000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012073 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1012073 : Nat := 118140960795 + 1012073 * 2 ^ 59
def prefixEnd_1012073 : Nat := 4983230072969 + 3 ^ 40 * 1012073 * 2
def baseEnd_1012073 : Nat := 230968847305743997081363

theorem tailTrace_1012073 : CollatzResearch.WordTrace tailWord_1012073 prefixEnd_1012073 230968847305743997081363 := by
  unfold tailWord_1012073
  simp only [CollatzResearch.WordTrace]
  refine ⟨36913334862439844152352873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24608889908293229434901915 36913334862439844152352873)
  ·
    refine ⟨27685001146829883114264655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36913334862439844152352873 27685001146829883114264655)
    ·
      refine ⟨41527501720244824671396983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27685001146829883114264655 41527501720244824671396983)
      ·
        refine ⟨62291252580367237007095475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41527501720244824671396983 62291252580367237007095475)
        ·
          refine ⟨93436878870550855510643213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62291252580367237007095475 93436878870550855510643213)
          ·
            refine ⟨35038829576456570816491205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93436878870550855510643213 35038829576456570816491205)
            ·
              refine ⟨6569780545585607028092101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35038829576456570816491205 6569780545585607028092101)
              ·
                refine ⟨1231833852297301317767269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6569780545585607028092101 1231833852297301317767269)
                ·
                  refine ⟨230968847305743997081363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231833852297301317767269 230968847305743997081363)
                  ·
                    rfl

theorem cell21_1012073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1012073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012073 prefixEnd_1012073 := by exact prefixLift 1012073
  have htrace : WordTrace (prefixWord ++ tailWord_1012073) baseStart_1012073 baseEnd_1012073 := by
    simpa [prefixWord, tailWord_1012073, baseEnd_1012073] using wordTrace_append hprefix tailTrace_1012073
  have hstable : (prefixWord ++ tailWord_1012073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012073).length < 2 ^ (prefixWord ++ tailWord_1012073).sum := by decide
  have hdescent : baseEnd_1012073 < baseStart_1012073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012076 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_1012076 : Nat := 118140960795 + 1012076 * 2 ^ 59
def prefixEnd_1012076 : Nat := 4983230072969 + 3 ^ 40 * 1012076 * 2
def baseEnd_1012076 : Nat := 230969531946616658531357

theorem tailTrace_1012076 : CollatzResearch.WordTrace tailWord_1012076 prefixEnd_1012076 230969531946616658531357 := by
  unfold tailWord_1012076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456722140714487832356041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24608962854285983776474721 18456722140714487832356041)
  ·
    refine ⟨13842541605535865874267031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18456722140714487832356041 13842541605535865874267031)
    ·
      refine ⟨20763812408303798811400547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842541605535865874267031 20763812408303798811400547)
      ·
        refine ⟨31145718612455698217100821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763812408303798811400547 31145718612455698217100821)
        ·
          refine ⟨1459955559958860853926601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31145718612455698217100821 1459955559958860853926601)
          ·
            refine ⟨1094966669969145640444951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459955559958860853926601 1094966669969145640444951)
            ·
              refine ⟨1642450004953718460667427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094966669969145640444951 1642450004953718460667427)
              ·
                refine ⟨2463675007430577691001141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642450004953718460667427 2463675007430577691001141)
                ·
                  refine ⟨230969531946616658531357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463675007430577691001141 230969531946616658531357)
                  ·
                    rfl

theorem cell21_1012076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_1012076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012076 prefixEnd_1012076 := by exact prefixLift 1012076
  have htrace : WordTrace (prefixWord ++ tailWord_1012076) baseStart_1012076 baseEnd_1012076 := by
    simpa [prefixWord, tailWord_1012076, baseEnd_1012076] using wordTrace_append hprefix tailTrace_1012076
  have hstable : (prefixWord ++ tailWord_1012076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012076).length < 2 ^ (prefixWord ++ tailWord_1012076).sum := by decide
  have hdescent : baseEnd_1012076 < baseStart_1012076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012180 : List Nat := [2, 4, 1, 2, 2, 2, 8]
def baseStart_1012180 : Nat := 118140960795 + 1012180 * 2 ^ 59
def prefixEnd_1012180 : Nat := 4983230072969 + 3 ^ 40 * 1012180 * 2
def baseEnd_1012180 : Nat := 25665918462615065421979

theorem tailTrace_1012180 : CollatzResearch.WordTrace tailWord_1012180 prefixEnd_1012180 25665918462615065421979 := by
  unfold tailWord_1012180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458618736526100713248997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24611491648701467617665329 18458618736526100713248997)
  ·
    refine ⟨3460991013098643883734187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18458618736526100713248997 3460991013098643883734187)
    ·
      refine ⟨5191486519647965825601281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460991013098643883734187 5191486519647965825601281)
      ·
        refine ⟨3893614889735974369200961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5191486519647965825601281 3893614889735974369200961)
        ·
          refine ⟨2920211167301980776900721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893614889735974369200961 2920211167301980776900721)
          ·
            refine ⟨2190158375476485582675541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920211167301980776900721 2190158375476485582675541)
            ·
              refine ⟨25665918462615065421979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2190158375476485582675541 25665918462615065421979)
              ·
                rfl

theorem cell21_1012180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 8].length) (baseStart_1012180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012180 prefixEnd_1012180 := by exact prefixLift 1012180
  have htrace : WordTrace (prefixWord ++ tailWord_1012180) baseStart_1012180 baseEnd_1012180 := by
    simpa [prefixWord, tailWord_1012180, baseEnd_1012180] using wordTrace_append hprefix tailTrace_1012180
  have hstable : (prefixWord ++ tailWord_1012180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012180).length < 2 ^ (prefixWord ++ tailWord_1012180).sum := by decide
  have hdescent : baseEnd_1012180 < baseStart_1012180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012225 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1012225 : Nat := 118140960795 + 1012225 * 2 ^ 59
def prefixEnd_1012225 : Nat := 4983230072969 + 3 ^ 40 * 1012225 * 2
def baseEnd_1012225 : Nat := 231003535776625510547719

theorem tailTrace_1012225 : CollatzResearch.WordTrace tailWord_1012225 prefixEnd_1012225 231003535776625510547719 := by
  unfold tailWord_1012225
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918878757889174111886129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24612585838592782741257419 36918878757889174111886129)
  ·
    refine ⟨27689159068416880583914597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36918878757889174111886129 27689159068416880583914597)
    ·
      refine ⟨5191717325328165109483987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27689159068416880583914597 5191717325328165109483987)
      ·
        refine ⟨7787575987992247664225981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191717325328165109483987 7787575987992247664225981)
        ·
          refine ⟨2920340995497092874084743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7787575987992247664225981 2920340995497092874084743)
          ·
            refine ⟨4380511493245639311127115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920340995497092874084743 4380511493245639311127115)
            ·
              refine ⟨6570767239868458966690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380511493245639311127115 6570767239868458966690673)
              ·
                refine ⟨4928075429901344225018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570767239868458966690673 4928075429901344225018005)
                ·
                  refine ⟨231003535776625510547719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4928075429901344225018005 231003535776625510547719)
                  ·
                    rfl

theorem cell21_1012225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1012225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012225 prefixEnd_1012225 := by exact prefixLift 1012225
  have htrace : WordTrace (prefixWord ++ tailWord_1012225) baseStart_1012225 baseEnd_1012225 := by
    simpa [prefixWord, tailWord_1012225, baseEnd_1012225] using wordTrace_append hprefix tailTrace_1012225
  have hstable : (prefixWord ++ tailWord_1012225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012225).length < 2 ^ (prefixWord ++ tailWord_1012225).sum := by decide
  have hdescent : baseEnd_1012225 < baseStart_1012225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012259 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 4]
def baseStart_1012259 : Nat := 118140960795 + 1012259 * 2 ^ 59
def prefixEnd_1012259 : Nat := 4983230072969 + 3 ^ 40 * 1012259 * 2
def baseEnd_1012259 : Nat := 231011295039849006980983

theorem tailTrace_1012259 : CollatzResearch.WordTrace tailWord_1012259 prefixEnd_1012259 231011295039849006980983 := by
  unfold tailWord_1012259
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920118839765997918623831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24613412559843998612415887 36920118839765997918623831)
  ·
    refine ⟨55380178259648996877935747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36920118839765997918623831 55380178259648996877935747)
    ·
      refine ⟨83070267389473495316903621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55380178259648996877935747 83070267389473495316903621)
      ·
        refine ⟨15575675135526280371919429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83070267389473495316903621 15575675135526280371919429)
        ·
          refine ⟨2920439087911177569734893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15575675135526280371919429 2920439087911177569734893)
          ·
            refine ⟨1095164657966691588650585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2920439087911177569734893 1095164657966691588650585)
            ·
              refine ⟨821373493475018691487939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095164657966691588650585 821373493475018691487939)
              ·
                refine ⟨1232060240212528037231909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821373493475018691487939 1232060240212528037231909)
                ·
                  refine ⟨231011295039849006980983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232060240212528037231909 231011295039849006980983)
                  ·
                    rfl

theorem cell21_1012259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_1012259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012259 prefixEnd_1012259 := by exact prefixLift 1012259
  have htrace : WordTrace (prefixWord ++ tailWord_1012259) baseStart_1012259 baseEnd_1012259 := by
    simpa [prefixWord, tailWord_1012259, baseEnd_1012259] using wordTrace_append hprefix tailTrace_1012259
  have hstable : (prefixWord ++ tailWord_1012259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012259).length < 2 ^ (prefixWord ++ tailWord_1012259).sum := by decide
  have hdescent : baseEnd_1012259 < baseStart_1012259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012287 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 3]
def baseStart_1012287 : Nat := 118140960795 + 1012287 * 2 ^ 59
def prefixEnd_1012287 : Nat := 4983230072969 + 3 ^ 40 * 1012287 * 2
def baseEnd_1012287 : Nat := 231017685021327180514259

theorem tailTrace_1012287 : CollatzResearch.WordTrace tailWord_1012287 prefixEnd_1012287 231017685021327180514259 := by
  unfold tailWord_1012287
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921140083664558700643115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24614093389109705800428743 36921140083664558700643115)
  ·
    refine ⟨55381710125496838050964673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36921140083664558700643115 55381710125496838050964673)
    ·
      refine ⟨41536282594122628538223505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55381710125496838050964673 41536282594122628538223505)
      ·
        refine ⟨31152211945591971403667629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41536282594122628538223505 31152211945591971403667629)
        ·
          refine ⟨11682079479596989276375361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31152211945591971403667629 11682079479596989276375361)
          ·
            refine ⟨8761559609697741957281521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11682079479596989276375361 8761559609697741957281521)
            ·
              refine ⟨6571169707273306467961141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761559609697741957281521 6571169707273306467961141)
              ·
                refine ⟨616047160056872481371357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6571169707273306467961141 616047160056872481371357)
                ·
                  refine ⟨231017685021327180514259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616047160056872481371357 231017685021327180514259)
                  ·
                    rfl

theorem cell21_1012287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].length) (baseStart_1012287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012287 prefixEnd_1012287 := by exact prefixLift 1012287
  have htrace : WordTrace (prefixWord ++ tailWord_1012287) baseStart_1012287 baseEnd_1012287 := by
    simpa [prefixWord, tailWord_1012287, baseEnd_1012287] using wordTrace_append hprefix tailTrace_1012287
  have hstable : (prefixWord ++ tailWord_1012287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012287).length < 2 ^ (prefixWord ++ tailWord_1012287).sum := by decide
  have hdescent : baseEnd_1012287 < baseStart_1012287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012397 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1012397 : Nat := 118140960795 + 1012397 * 2 ^ 59
def prefixEnd_1012397 : Nat := 4983230072969 + 3 ^ 40 * 1012397 * 2
def baseEnd_1012397 : Nat := 231042788519991433680701

theorem tailTrace_1012397 : CollatzResearch.WordTrace tailWord_1012397 prefixEnd_1012397 231042788519991433680701 := by
  unfold tailWord_1012397
  simp only [CollatzResearch.WordTrace]
  refine ⟨36925152113266047487147445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24616768075510698324764963 36925152113266047487147445)
  ·
    refine ⟨3461733010618691951920073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36925152113266047487147445 3461733010618691951920073)
    ·
      refine ⟨2596299757964018963940055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3461733010618691951920073 2596299757964018963940055)
      ·
        refine ⟨3894449636946028445910083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596299757964018963940055 3894449636946028445910083)
        ·
          refine ⟨5841674455419042668865125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894449636946028445910083 5841674455419042668865125)
          ·
            refine ⟨1095313960391070500412211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5841674455419042668865125 1095313960391070500412211)
            ·
              refine ⟨1642970940586605750618317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095313960391070500412211 1642970940586605750618317)
              ·
                refine ⟨616114102719977156481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642970940586605750618317 616114102719977156481869)
                ·
                  refine ⟨231042788519991433680701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616114102719977156481869 231042788519991433680701)
                  ·
                    rfl

theorem cell21_1012397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1012397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012397 prefixEnd_1012397 := by exact prefixLift 1012397
  have htrace : WordTrace (prefixWord ++ tailWord_1012397) baseStart_1012397 baseEnd_1012397 := by
    simpa [prefixWord, tailWord_1012397, baseEnd_1012397] using wordTrace_append hprefix tailTrace_1012397
  have hstable : (prefixWord ++ tailWord_1012397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012397).length < 2 ^ (prefixWord ++ tailWord_1012397).sum := by decide
  have hdescent : baseEnd_1012397 < baseStart_1012397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012470 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1012470 : Nat := 118140960795 + 1012470 * 2 ^ 59
def prefixEnd_1012470 : Nat := 4983230072969 + 3 ^ 40 * 1012470 * 2
def baseEnd_1012470 : Nat := 231059448114559528963885

theorem tailTrace_1012470 : CollatzResearch.WordTrace tailWord_1012470 prefixEnd_1012470 231059448114559528963885 := by
  unfold tailWord_1012470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307988415125098809659679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24618543094667720636369909 2307988415125098809659679)
  ·
    refine ⟨3461982622687648214489519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2307988415125098809659679 3461982622687648214489519)
    ·
      refine ⟨5192973934031472321734279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3461982622687648214489519 5192973934031472321734279)
      ·
        refine ⟨7789460901047208482601419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192973934031472321734279 7789460901047208482601419)
        ·
          refine ⟨11684191351570812723902129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789460901047208482601419 11684191351570812723902129)
          ·
            refine ⟨8763143513678109542926597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11684191351570812723902129 8763143513678109542926597)
            ·
              refine ⟨1643089408814645539298737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8763143513678109542926597 1643089408814645539298737)
              ·
                refine ⟨1232317056610984154474053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643089408814645539298737 1232317056610984154474053)
                ·
                  refine ⟨231059448114559528963885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232317056610984154474053 231059448114559528963885)
                  ·
                    rfl

theorem cell21_1012470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1012470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012470 prefixEnd_1012470 := by exact prefixLift 1012470
  have htrace : WordTrace (prefixWord ++ tailWord_1012470) baseStart_1012470 baseEnd_1012470 := by
    simpa [prefixWord, tailWord_1012470, baseEnd_1012470] using wordTrace_append hprefix tailTrace_1012470
  have hstable : (prefixWord ++ tailWord_1012470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012470).length < 2 ^ (prefixWord ++ tailWord_1012470).sum := by decide
  have hdescent : baseEnd_1012470 < baseStart_1012470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012532 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1012532 : Nat := 118140960795 + 1012532 * 2 ^ 59
def prefixEnd_1012532 : Nat := 4983230072969 + 3 ^ 40 * 1012532 * 2
def baseEnd_1012532 : Nat := 231073597359261198930425

theorem tailTrace_1012532 : CollatzResearch.WordTrace tailWord_1012532 prefixEnd_1012532 231073597359261198930425 := by
  unfold tailWord_1012532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465037983888482771655925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24620050645184643695541233 18465037983888482771655925)
  ·
    refine ⟨1731097310989545259842743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18465037983888482771655925 1731097310989545259842743)
    ·
      refine ⟨2596645966484317889764115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731097310989545259842743 2596645966484317889764115)
      ·
        refine ⟨3894968949726476834646173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596645966484317889764115 3894968949726476834646173)
        ·
          refine ⟨1460613356147428812992315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3894968949726476834646173 1460613356147428812992315)
          ·
            refine ⟨2190920034221143219488473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460613356147428812992315 2190920034221143219488473)
            ·
              refine ⟨1643190025665857414616355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190920034221143219488473 1643190025665857414616355)
              ·
                refine ⟨2464785038498786121924533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643190025665857414616355 2464785038498786121924533)
                ·
                  refine ⟨231073597359261198930425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2464785038498786121924533 231073597359261198930425)
                  ·
                    rfl

theorem cell21_1012532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1012532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012532 prefixEnd_1012532 := by exact prefixLift 1012532
  have htrace : WordTrace (prefixWord ++ tailWord_1012532) baseStart_1012532 baseEnd_1012532 := by
    simpa [prefixWord, tailWord_1012532, baseEnd_1012532] using wordTrace_append hprefix tailTrace_1012532
  have hstable : (prefixWord ++ tailWord_1012532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012532).length < 2 ^ (prefixWord ++ tailWord_1012532).sum := by decide
  have hdescent : baseEnd_1012532 < baseStart_1012532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012588 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1012588 : Nat := 118140960795 + 1012588 * 2 ^ 59
def prefixEnd_1012588 : Nat := 4983230072969 + 3 ^ 40 * 1012588 * 2
def baseEnd_1012588 : Nat := 231086377322217545996977

theorem tailTrace_1012588 : CollatzResearch.WordTrace tailWord_1012588 prefixEnd_1012588 231086377322217545996977 := by
  unfold tailWord_1012588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466059227787043553675209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24621412303716058071566945 18466059227787043553675209)
  ·
    refine ⟨13849544420840282665256407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18466059227787043553675209 13849544420840282665256407)
    ·
      refine ⟨20774316631260423997884611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13849544420840282665256407 20774316631260423997884611)
      ·
        refine ⟨31161474946890635996826917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20774316631260423997884611 31161474946890635996826917)
        ·
          refine ⟨5842776552541994249405047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31161474946890635996826917 5842776552541994249405047)
          ·
            refine ⟨8764164828812991374107571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842776552541994249405047 8764164828812991374107571)
            ·
              refine ⟨13146247243219487061161357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764164828812991374107571 13146247243219487061161357)
              ·
                refine ⟨4929842716207307647935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146247243219487061161357 4929842716207307647935509)
                ·
                  refine ⟨231086377322217545996977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4929842716207307647935509 231086377322217545996977)
                  ·
                    rfl

theorem cell21_1012588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1012588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012588 prefixEnd_1012588 := by exact prefixLift 1012588
  have htrace : WordTrace (prefixWord ++ tailWord_1012588) baseStart_1012588 baseEnd_1012588 := by
    simpa [prefixWord, tailWord_1012588, baseEnd_1012588] using wordTrace_append hprefix tailTrace_1012588
  have hstable : (prefixWord ++ tailWord_1012588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012588).length < 2 ^ (prefixWord ++ tailWord_1012588).sum := by decide
  have hdescent : baseEnd_1012588 < baseStart_1012588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012636 : List Nat := [2, 2, 3, 3, 3, 8]
def baseStart_1012636 : Nat := 118140960795 + 1012636 * 2 ^ 59
def prefixEnd_1012636 : Nat := 4983230072969 + 3 ^ 40 * 1012636 * 2
def baseEnd_1012636 : Nat := 8559160428747412192477

theorem tailTrace_1012636 : CollatzResearch.WordTrace tailWord_1012636 prefixEnd_1012636 8559160428747412192477 := by
  unfold tailWord_1012636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466934579700095652548881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24622579439600127536731841 18466934579700095652548881)
  ·
    refine ⟨13850200934775071739411661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18466934579700095652548881 13850200934775071739411661)
    ·
      refine ⟨5193825350540651902279373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13850200934775071739411661 5193825350540651902279373)
      ·
        refine ⟨1947684506452744463354765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5193825350540651902279373 1947684506452744463354765)
        ·
          refine ⟨730381689919779173758037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1947684506452744463354765 730381689919779173758037)
          ·
            refine ⟨8559160428747412192477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 730381689919779173758037 8559160428747412192477)
            ·
              rfl

theorem cell21_1012636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 8].length) (baseStart_1012636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012636 prefixEnd_1012636 := by exact prefixLift 1012636
  have htrace : WordTrace (prefixWord ++ tailWord_1012636) baseStart_1012636 baseEnd_1012636 := by
    simpa [prefixWord, tailWord_1012636, baseEnd_1012636] using wordTrace_append hprefix tailTrace_1012636
  have hstable : (prefixWord ++ tailWord_1012636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012636).length < 2 ^ (prefixWord ++ tailWord_1012636).sum := by decide
  have hdescent : baseEnd_1012636 < baseStart_1012636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012698 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_1012698 : Nat := 118140960795 + 1012698 * 2 ^ 59
def prefixEnd_1012698 : Nat := 4983230072969 + 3 ^ 40 * 1012698 * 2
def baseEnd_1012698 : Nat := 231111480820881799163419

theorem tailTrace_1012698 : CollatzResearch.WordTrace tailWord_1012698 prefixEnd_1012698 231111480820881799163419 := by
  unfold tailWord_1012698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234032621293893973463687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24624086990117050595903165 9234032621293893973463687)
  ·
    refine ⟨13851048931940840960195531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234032621293893973463687 13851048931940840960195531)
    ·
      refine ⟨20776573397911261440293297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851048931940840960195531 20776573397911261440293297)
      ·
        refine ⟨15582430048433446080219973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20776573397911261440293297 15582430048433446080219973)
        ·
          refine ⟨2921705634081271140041245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15582430048433446080219973 2921705634081271140041245)
          ·
            refine ⟨1095639612780476677515467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2921705634081271140041245 1095639612780476677515467)
            ·
              refine ⟨1643459419170715016273201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095639612780476677515467 1643459419170715016273201)
              ·
                refine ⟨1232594564378036262204901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643459419170715016273201 1232594564378036262204901)
                ·
                  refine ⟨231111480820881799163419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232594564378036262204901 231111480820881799163419)
                  ·
                    rfl

theorem cell21_1012698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_1012698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012698 prefixEnd_1012698 := by exact prefixLift 1012698
  have htrace : WordTrace (prefixWord ++ tailWord_1012698) baseStart_1012698 baseEnd_1012698 := by
    simpa [prefixWord, tailWord_1012698, baseEnd_1012698] using wordTrace_append hprefix tailTrace_1012698
  have hstable : (prefixWord ++ tailWord_1012698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012698).length < 2 ^ (prefixWord ++ tailWord_1012698).sum := by decide
  have hdescent : baseEnd_1012698 < baseStart_1012698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012760 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_1012760 : Nat := 118140960795 + 1012760 * 2 ^ 59
def prefixEnd_1012760 : Nat := 4983230072969 + 3 ^ 40 * 1012760 * 2
def baseEnd_1012760 : Nat := 231125630065583469129959

theorem tailTrace_1012760 : CollatzResearch.WordTrace tailWord_1012760 prefixEnd_1012760 231125630065583469129959 := by
  unfold tailWord_1012760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469195905475480241305867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24625594540633973655074489 18469195905475480241305867)
  ·
    refine ⟨27703793858213220361958801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18469195905475480241305867 27703793858213220361958801)
    ·
      refine ⟨20777845393659915271469101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27703793858213220361958801 20777845393659915271469101)
      ·
        refine ⟨7791692022622468226800913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20777845393659915271469101 7791692022622468226800913)
        ·
          refine ⟨5843769016966851170100685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791692022622468226800913 5843769016966851170100685)
          ·
            refine ⟨2191413381362569188787757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5843769016966851170100685 2191413381362569188787757)
            ·
              refine ⟨821780018010963445795409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191413381362569188787757 821780018010963445795409)
              ·
                refine ⟨616335013508222584346557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821780018010963445795409 616335013508222584346557)
                ·
                  refine ⟨231125630065583469129959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616335013508222584346557 231125630065583469129959)
                  ·
                    rfl

theorem cell21_1012760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_1012760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012760 prefixEnd_1012760 := by exact prefixLift 1012760
  have htrace : WordTrace (prefixWord ++ tailWord_1012760) baseStart_1012760 baseEnd_1012760 := by
    simpa [prefixWord, tailWord_1012760, baseEnd_1012760] using wordTrace_append hprefix tailTrace_1012760
  have hstable : (prefixWord ++ tailWord_1012760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012760).length < 2 ^ (prefixWord ++ tailWord_1012760).sum := by decide
  have hdescent : baseEnd_1012760 < baseStart_1012760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012771 : List Nat := [1, 1, 1, 4, 3, 3, 2, 6]
def baseStart_1012771 : Nat := 118140960795 + 1012771 * 2 ^ 59
def prefixEnd_1012771 : Nat := 4983230072969 + 3 ^ 40 * 1012771 * 2
def baseEnd_1012771 : Nat := 77042713471816631482201

theorem tailTrace_1012771 : CollatzResearch.WordTrace tailWord_1012771 prefixEnd_1012771 77042713471816631482201 := by
  unfold tailWord_1012771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36938793013911109361262167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24625862009274072907508111 36938793013911109361262167)
  ·
    refine ⟨55408189520866664041893251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36938793013911109361262167 55408189520866664041893251)
    ·
      refine ⟨83112284281299996062839877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55408189520866664041893251 83112284281299996062839877)
      ·
        refine ⟨15583553302743749261782477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83112284281299996062839877 15583553302743749261782477)
        ·
          refine ⟨5843832488528905973168429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15583553302743749261782477 5843832488528905973168429)
          ·
            refine ⟨2191437183198339739938161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5843832488528905973168429 2191437183198339739938161)
            ·
              refine ⟨1643577887398754804953621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191437183198339739938161 1643577887398754804953621)
              ·
                refine ⟨77042713471816631482201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1643577887398754804953621 77042713471816631482201)
                ·
                  rfl

theorem cell21_1012771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_1012771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012771 prefixEnd_1012771 := by exact prefixLift 1012771
  have htrace : WordTrace (prefixWord ++ tailWord_1012771) baseStart_1012771 baseEnd_1012771 := by
    simpa [prefixWord, tailWord_1012771, baseEnd_1012771] using wordTrace_append hprefix tailTrace_1012771
  have hstable : (prefixWord ++ tailWord_1012771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012771).length < 2 ^ (prefixWord ++ tailWord_1012771).sum := by decide
  have hdescent : baseEnd_1012771 < baseStart_1012771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012785 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1012785 : Nat := 118140960795 + 1012785 * 2 ^ 59
def prefixEnd_1012785 : Nat := 4983230072969 + 3 ^ 40 * 1012785 * 2
def baseEnd_1012785 : Nat := 231131335406188981213241

theorem tailTrace_1012785 : CollatzResearch.WordTrace tailWord_1012785 prefixEnd_1012785 231131335406188981213241 := by
  unfold tailWord_1012785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939303635860389752271809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24626202423906926501514539 36939303635860389752271809)
  ·
    refine ⟨27704477726895292314203857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36939303635860389752271809 27704477726895292314203857)
    ·
      refine ⟨20778358295171469235652893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27704477726895292314203857 20778358295171469235652893)
      ·
        refine ⟨7791884360689300963369835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20778358295171469235652893 7791884360689300963369835)
        ·
          refine ⟨11687826541033951445054753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791884360689300963369835 11687826541033951445054753)
          ·
            refine ⟨8765869905775463583791065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11687826541033951445054753 8765869905775463583791065)
            ·
              refine ⟨6574402429331597687843299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765869905775463583791065 6574402429331597687843299)
              ·
                refine ⟨9861603643997396531764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574402429331597687843299 9861603643997396531764949)
                ·
                  refine ⟨231131335406188981213241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9861603643997396531764949 231131335406188981213241)
                  ·
                    rfl

theorem cell21_1012785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1012785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012785 prefixEnd_1012785 := by exact prefixLift 1012785
  have htrace : WordTrace (prefixWord ++ tailWord_1012785) baseStart_1012785 baseEnd_1012785 := by
    simpa [prefixWord, tailWord_1012785, baseEnd_1012785] using wordTrace_append hprefix tailTrace_1012785
  have hstable : (prefixWord ++ tailWord_1012785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012785).length < 2 ^ (prefixWord ++ tailWord_1012785).sum := by decide
  have hdescent : baseEnd_1012785 < baseStart_1012785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012788 : List Nat := [2, 5, 1, 2, 1, 1, 2, 7]
def baseStart_1012788 : Nat := 118140960795 + 1012788 * 2 ^ 59
def prefixEnd_1012788 : Nat := 4983230072969 + 3 ^ 40 * 1012788 * 2
def baseEnd_1012788 : Nat := 77044006682353880887745

theorem tailTrace_1012788 : CollatzResearch.WordTrace tailWord_1012788 prefixEnd_1012788 77044006682353880887745 := by
  unfold tailWord_1012788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469706527424760632315509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24626275369899680843087345 18469706527424760632315509)
  ·
    refine ⟨1731534986946071309279579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18469706527424760632315509 1731534986946071309279579)
    ·
      refine ⟨2597302480419106963919369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731534986946071309279579 2597302480419106963919369)
      ·
        refine ⟨1947976860314330222939527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2597302480419106963919369 1947976860314330222939527)
        ·
          refine ⟨2921965290471495334409291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947976860314330222939527 2921965290471495334409291)
          ·
            refine ⟨4382947935707243001613937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921965290471495334409291 4382947935707243001613937)
            ·
              refine ⟨3287210951780432251210453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382947935707243001613937 3287210951780432251210453)
              ·
                refine ⟨77044006682353880887745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3287210951780432251210453 77044006682353880887745)
                ·
                  rfl

theorem cell21_1012788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_1012788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012788 prefixEnd_1012788 := by exact prefixLift 1012788
  have htrace : WordTrace (prefixWord ++ tailWord_1012788) baseStart_1012788 baseEnd_1012788 := by
    simpa [prefixWord, tailWord_1012788, baseEnd_1012788] using wordTrace_append hprefix tailTrace_1012788
  have hstable : (prefixWord ++ tailWord_1012788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012788).length < 2 ^ (prefixWord ++ tailWord_1012788).sum := by decide
  have hdescent : baseEnd_1012788 < baseStart_1012788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012822 : List Nat := [5, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1012822 : Nat := 118140960795 + 1012822 * 2 ^ 59
def prefixEnd_1012822 : Nat := 4983230072969 + 3 ^ 40 * 1012822 * 2
def baseEnd_1012822 : Nat := 77046593103428379698833

theorem tailTrace_1012822 : CollatzResearch.WordTrace tailWord_1012822 prefixEnd_1012822 77046593103428379698833 := by
  unfold tailWord_1012822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308790821045396566960545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24627102091150896714245813 2308790821045396566960545)
  ·
    refine ⟨1731593115784047425220409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2308790821045396566960545 1731593115784047425220409)
    ·
      refine ⟨1298694836838035568915307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1731593115784047425220409 1298694836838035568915307)
      ·
        refine ⟨1948042255257053353372961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298694836838035568915307 1948042255257053353372961)
        ·
          refine ⟨1461031691442790015029721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948042255257053353372961 1461031691442790015029721)
          ·
            refine ⟨1095773768582092511272291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461031691442790015029721 1095773768582092511272291)
            ·
              refine ⟨1643660652873138766908437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095773768582092511272291 1643660652873138766908437)
              ·
                refine ⟨77046593103428379698833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1643660652873138766908437 77046593103428379698833)
                ·
                  rfl

theorem cell21_1012822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1012822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012822 prefixEnd_1012822 := by exact prefixLift 1012822
  have htrace : WordTrace (prefixWord ++ tailWord_1012822) baseStart_1012822 baseEnd_1012822 := by
    simpa [prefixWord, tailWord_1012822, baseEnd_1012822] using wordTrace_append hprefix tailTrace_1012822
  have hstable : (prefixWord ++ tailWord_1012822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012822).length < 2 ^ (prefixWord ++ tailWord_1012822).sum := by decide
  have hdescent : baseEnd_1012822 < baseStart_1012822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012847 : List Nat := [1, 1, 2, 1, 3, 3, 5, 5]
def baseStart_1012847 : Nat := 118140960795 + 1012847 * 2 ^ 59
def prefixEnd_1012847 : Nat := 4983230072969 + 3 ^ 40 * 1012847 * 2
def baseEnd_1012847 : Nat := 77048494883630217059927

theorem tailTrace_1012847 : CollatzResearch.WordTrace tailWord_1012847 prefixEnd_1012847 77048494883630217059927 := by
  unfold tailWord_1012847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941564961635774341028795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627709974423849560685863 36941564961635774341028795)
  ·
    refine ⟨55412347442453661511543193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36941564961635774341028795 55412347442453661511543193)
    ·
      refine ⟨41559260581840246133657395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55412347442453661511543193 41559260581840246133657395)
      ·
        refine ⟨62338890872760369200486093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41559260581840246133657395 62338890872760369200486093)
        ·
          refine ⟨23377084077285138450182285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62338890872760369200486093 23377084077285138450182285)
          ·
            refine ⟨8766406528981926918818357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23377084077285138450182285 8766406528981926918818357)
            ·
              refine ⟨821850612092055648639221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8766406528981926918818357 821850612092055648639221)
              ·
                refine ⟨77048494883630217059927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 821850612092055648639221 77048494883630217059927)
                ·
                  rfl

theorem cell21_1012847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].length) (baseStart_1012847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012847 prefixEnd_1012847 := by exact prefixLift 1012847
  have htrace : WordTrace (prefixWord ++ tailWord_1012847) baseStart_1012847 baseEnd_1012847 := by
    simpa [prefixWord, tailWord_1012847, baseEnd_1012847] using wordTrace_append hprefix tailTrace_1012847
  have hstable : (prefixWord ++ tailWord_1012847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012847).length < 2 ^ (prefixWord ++ tailWord_1012847).sum := by decide
  have hdescent : baseEnd_1012847 < baseStart_1012847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012853 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 3]
def baseStart_1012853 : Nat := 118140960795 + 1012853 * 2 ^ 59
def prefixEnd_1012853 : Nat := 4983230072969 + 3 ^ 40 * 1012853 * 2
def baseEnd_1012853 : Nat := 231146853932635974079769

theorem tailTrace_1012853 : CollatzResearch.WordTrace tailWord_1012853 prefixEnd_1012853 231146853932635974079769 := by
  unfold tailWord_1012853
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941783799614037365747213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24627855866409358243831475 36941783799614037365747213)
  ·
    refine ⟨13853168924855264012155205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36941783799614037365747213 13853168924855264012155205)
    ·
      refine ⟨2597469173410362002279101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13853168924855264012155205 2597469173410362002279101)
      ·
        refine ⟨974050940028885750854663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2597469173410362002279101 974050940028885750854663)
        ·
          refine ⟨1461076410043328626281995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974050940028885750854663 1461076410043328626281995)
          ·
            refine ⟨2191614615064992939422993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461076410043328626281995 2191614615064992939422993)
            ·
              refine ⟨1643710961298744704567245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191614615064992939422993 1643710961298744704567245)
              ·
                refine ⟨616391610487029264212717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643710961298744704567245 616391610487029264212717)
                ·
                  refine ⟨231146853932635974079769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616391610487029264212717 231146853932635974079769)
                  ·
                    rfl

theorem cell21_1012853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_1012853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012853 prefixEnd_1012853 := by exact prefixLift 1012853
  have htrace : WordTrace (prefixWord ++ tailWord_1012853) baseStart_1012853 baseEnd_1012853 := by
    simpa [prefixWord, tailWord_1012853, baseEnd_1012853] using wordTrace_append hprefix tailTrace_1012853
  have hstable : (prefixWord ++ tailWord_1012853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012853).length < 2 ^ (prefixWord ++ tailWord_1012853).sum := by decide
  have hdescent : baseEnd_1012853 < baseStart_1012853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012861 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1012861 : Nat := 118140960795 + 1012861 * 2 ^ 59
def prefixEnd_1012861 : Nat := 4983230072969 + 3 ^ 40 * 1012861 * 2
def baseEnd_1012861 : Nat := 231148679641629737946419

theorem tailTrace_1012861 : CollatzResearch.WordTrace tailWord_1012861 prefixEnd_1012861 231148679641629737946419 := by
  unfold tailWord_1012861
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942075583585054732038437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24628050389056703154692291 36942075583585054732038437)
  ·
    refine ⟨6926639171922197762257207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36942075583585054732038437 6926639171922197762257207)
    ·
      refine ⟨10389958757883296643385811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926639171922197762257207 10389958757883296643385811)
      ·
        refine ⟨15584938136824944965078717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389958757883296643385811 15584938136824944965078717)
        ·
          refine ⟨5844351801309354361904519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15584938136824944965078717 5844351801309354361904519)
          ·
            refine ⟨8766527701964031542856779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844351801309354361904519 8766527701964031542856779)
            ·
              refine ⟨13149791552946047314285169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766527701964031542856779 13149791552946047314285169)
              ·
                refine ⟨9862343664709535485713877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13149791552946047314285169 9862343664709535485713877)
                ·
                  refine ⟨231148679641629737946419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9862343664709535485713877 231148679641629737946419)
                  ·
                    rfl

theorem cell21_1012861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1012861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012861 prefixEnd_1012861 := by exact prefixLift 1012861
  have htrace : WordTrace (prefixWord ++ tailWord_1012861) baseStart_1012861 baseEnd_1012861 := by
    simpa [prefixWord, tailWord_1012861, baseEnd_1012861] using wordTrace_append hprefix tailTrace_1012861
  have hstable : (prefixWord ++ tailWord_1012861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012861).length < 2 ^ (prefixWord ++ tailWord_1012861).sum := by decide
  have hdescent : baseEnd_1012861 < baseStart_1012861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012878 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1012878 : Nat := 118140960795 + 1012878 * 2 ^ 59
def prefixEnd_1012878 : Nat := 4983230072969 + 3 ^ 40 * 1012878 * 2
def baseEnd_1012878 : Nat := 231152559273241486163051

theorem tailTrace_1012878 : CollatzResearch.WordTrace tailWord_1012878 prefixEnd_1012878 231152559273241486163051 := by
  unfold tailWord_1012878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617836953065433329425911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24628463749682311090271525 4617836953065433329425911)
  ·
    refine ⟨6926755429598149994138867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617836953065433329425911 6926755429598149994138867)
    ·
      refine ⟨10390133144397224991208301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926755429598149994138867 10390133144397224991208301)
      ·
        refine ⟨3896299929148959371703113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10390133144397224991208301 3896299929148959371703113)
        ·
          refine ⟨2922224946861719528777335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896299929148959371703113 2922224946861719528777335)
          ·
            refine ⟨4383337420292579293166003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922224946861719528777335 4383337420292579293166003)
            ·
              refine ⟨6575006130438868939749005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383337420292579293166003 6575006130438868939749005)
              ·
                refine ⟨2465627298914575852405877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6575006130438868939749005 2465627298914575852405877)
                ·
                  refine ⟨231152559273241486163051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465627298914575852405877 231152559273241486163051)
                  ·
                    rfl

theorem cell21_1012878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1012878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012878 prefixEnd_1012878 := by exact prefixLift 1012878
  have htrace : WordTrace (prefixWord ++ tailWord_1012878) baseStart_1012878 baseEnd_1012878 := by
    simpa [prefixWord, tailWord_1012878, baseEnd_1012878] using wordTrace_append hprefix tailTrace_1012878
  have hstable : (prefixWord ++ tailWord_1012878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012878).length < 2 ^ (prefixWord ++ tailWord_1012878).sum := by decide
  have hdescent : baseEnd_1012878 < baseStart_1012878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012898 : List Nat := [3, 3, 1, 3, 3, 1, 2, 5]
def baseStart_1012898 : Nat := 118140960795 + 1012898 * 2 ^ 59
def prefixEnd_1012898 : Nat := 4983230072969 + 3 ^ 40 * 1012898 * 2
def baseEnd_1012898 : Nat := 77052374515241965276559

theorem tailTrace_1012898 : CollatzResearch.WordTrace tailWord_1012898 prefixEnd_1012898 77052374515241965276559 := by
  unfold tailWord_1012898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235856271112752512783837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24628950056300673367423565 9235856271112752512783837)
  ·
    refine ⟨3463446101667282192293939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9235856271112752512783837 3463446101667282192293939)
    ·
      refine ⟨5195169152500923288440909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463446101667282192293939 5195169152500923288440909)
      ·
        refine ⟨1948188432187846233165341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5195169152500923288440909 1948188432187846233165341)
        ·
          refine ⟨730570662070442337437003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1948188432187846233165341 730570662070442337437003)
          ·
            refine ⟨1095855993105663506155505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730570662070442337437003 1095855993105663506155505)
            ·
              refine ⟨821891994829247629616629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095855993105663506155505 821891994829247629616629)
              ·
                refine ⟨77052374515241965276559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 821891994829247629616629 77052374515241965276559)
                ·
                  rfl

theorem cell21_1012898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_1012898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012898 prefixEnd_1012898 := by exact prefixLift 1012898
  have htrace : WordTrace (prefixWord ++ tailWord_1012898) baseStart_1012898 baseEnd_1012898 := by
    simpa [prefixWord, tailWord_1012898, baseEnd_1012898] using wordTrace_append hprefix tailTrace_1012898
  have hstable : (prefixWord ++ tailWord_1012898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012898).length < 2 ^ (prefixWord ++ tailWord_1012898).sum := by decide
  have hdescent : baseEnd_1012898 < baseStart_1012898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012929 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 3]
def baseStart_1012929 : Nat := 118140960795 + 1012929 * 2 ^ 59
def prefixEnd_1012929 : Nat := 4983230072969 + 3 ^ 40 * 1012929 * 2
def baseEnd_1012929 : Nat := 231164198168076730812947

theorem tailTrace_1012929 : CollatzResearch.WordTrace tailWord_1012929 prefixEnd_1012929 231164198168076730812947 := by
  unfold tailWord_1012929
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944555747338702345513841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24629703831559134897009227 36944555747338702345513841)
  ·
    refine ⟨27708416810504026759135381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36944555747338702345513841 27708416810504026759135381)
    ·
      refine ⟨1298832037992376254334471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27708416810504026759135381 1298832037992376254334471)
      ·
        refine ⟨1948248056988564381501707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298832037992376254334471 1948248056988564381501707)
        ·
          refine ⟨2922372085482846572252561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948248056988564381501707 2922372085482846572252561)
          ·
            refine ⟨2191779064112134929189421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922372085482846572252561 2191779064112134929189421)
            ·
              refine ⟨821917149042050598446033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191779064112134929189421 821917149042050598446033)
              ·
                refine ⟨616437861781537948834525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821917149042050598446033 616437861781537948834525)
                ·
                  refine ⟨231164198168076730812947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616437861781537948834525 231164198168076730812947)
                  ·
                    rfl

theorem cell21_1012929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_1012929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012929 prefixEnd_1012929 := by exact prefixLift 1012929
  have htrace : WordTrace (prefixWord ++ tailWord_1012929) baseStart_1012929 baseEnd_1012929 := by
    simpa [prefixWord, tailWord_1012929, baseEnd_1012929] using wordTrace_append hprefix tailTrace_1012929
  have hstable : (prefixWord ++ tailWord_1012929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012929).length < 2 ^ (prefixWord ++ tailWord_1012929).sum := by decide
  have hdescent : baseEnd_1012929 < baseStart_1012929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1012980 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1012980 : Nat := 118140960795 + 1012980 * 2 ^ 59
def prefixEnd_1012980 : Nat := 4983230072969 + 3 ^ 40 * 1012980 * 2
def baseEnd_1012980 : Nat := 231175837062911975462843

theorem tailTrace_1012980 : CollatzResearch.WordTrace tailWord_1012980 prefixEnd_1012980 231175837062911975462843 := by
  unfold tailWord_1012980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473207935076969027810197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24630943913435958703746929 18473207935076969027810197)
  ·
    refine ⟨865931621956732923178603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18473207935076969027810197 865931621956732923178603)
    ·
      refine ⟨1298897432935099384767905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865931621956732923178603 1298897432935099384767905)
      ·
        refine ⟨974173074701324538575929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298897432935099384767905 974173074701324538575929)
        ·
          refine ⟨730629806025993403931947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974173074701324538575929 730629806025993403931947)
          ·
            refine ⟨1095944709038990105897921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730629806025993403931947 1095944709038990105897921)
            ·
              refine ⟨821958531779242579423441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095944709038990105897921 821958531779242579423441)
              ·
                refine ⟨616468898834431934567581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821958531779242579423441 616468898834431934567581)
                ·
                  refine ⟨231175837062911975462843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616468898834431934567581 231175837062911975462843)
                  ·
                    rfl

theorem cell21_1012980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1012980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1012980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1012980 prefixEnd_1012980 := by exact prefixLift 1012980
  have htrace : WordTrace (prefixWord ++ tailWord_1012980) baseStart_1012980 baseEnd_1012980 := by
    simpa [prefixWord, tailWord_1012980, baseEnd_1012980] using wordTrace_append hprefix tailTrace_1012980
  have hstable : (prefixWord ++ tailWord_1012980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1012980).length < 2 ^ (prefixWord ++ tailWord_1012980).sum := by decide
  have hdescent : baseEnd_1012980 < baseStart_1012980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1012980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013103 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_1013103 : Nat := 118140960795 + 1013103 * 2 ^ 59
def prefixEnd_1013103 : Nat := 4983230072969 + 3 ^ 40 * 1013103 * 2
def baseEnd_1013103 : Nat := 231203907338691094912591

theorem tailTrace_1013103 : CollatzResearch.WordTrace tailWord_1013103 prefixEnd_1013103 231203907338691094912591 := by
  unfold tailWord_1013103
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950902048708330062347963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24633934699138886708231975 36950902048708330062347963)
  ·
    refine ⟨55426353073062495093521945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36950902048708330062347963 55426353073062495093521945)
    ·
      refine ⟨41569764804796871320141459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55426353073062495093521945 41569764804796871320141459)
      ·
        refine ⟨62354647207195306980212189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41569764804796871320141459 62354647207195306980212189)
        ·
          refine ⟨23382992702698240117579571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62354647207195306980212189 23382992702698240117579571)
          ·
            refine ⟨35074489054047360176369357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382992702698240117579571 35074489054047360176369357)
            ·
              refine ⟨13152933395267760066138509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35074489054047360176369357 13152933395267760066138509)
              ·
                refine ⟨4932350023225410024801941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13152933395267760066138509 4932350023225410024801941)
                ·
                  refine ⟨231203907338691094912591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4932350023225410024801941 231203907338691094912591)
                  ·
                    rfl

theorem cell21_1013103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_1013103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013103 prefixEnd_1013103 := by exact prefixLift 1013103
  have htrace : WordTrace (prefixWord ++ tailWord_1013103) baseStart_1013103 baseEnd_1013103 := by
    simpa [prefixWord, tailWord_1013103, baseEnd_1013103] using wordTrace_append hprefix tailTrace_1013103
  have hstable : (prefixWord ++ tailWord_1013103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013103).length < 2 ^ (prefixWord ++ tailWord_1013103).sum := by decide
  have hdescent : baseEnd_1013103 < baseStart_1013103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013210 : List Nat := [3, 1, 1, 2, 3, 3, 8]
def baseStart_1013210 : Nat := 118140960795 + 1013210 * 2 ^ 59
def prefixEnd_1013210 : Nat := 4983230072969 + 3 ^ 40 * 1013210 * 2
def baseEnd_1013210 : Nat := 25692036244053631847671

theorem tailTrace_1013210 : CollatzResearch.WordTrace tailWord_1013210 prefixEnd_1013210 25692036244053631847671 := by
  unfold tailWord_1013210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238701164830171834123271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24636536439547124890995389 9238701164830171834123271)
  ·
    refine ⟨13858051747245257751184907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238701164830171834123271 13858051747245257751184907)
    ·
      refine ⟨20787077620867886626777361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13858051747245257751184907 20787077620867886626777361)
      ·
        refine ⟨15590308215650914970083021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20787077620867886626777361 15590308215650914970083021)
        ·
          refine ⟨5846365580869093113781133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15590308215650914970083021 5846365580869093113781133)
          ·
            refine ⟨2192387092825909917667925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5846365580869093113781133 2192387092825909917667925)
            ·
              refine ⟨25692036244053631847671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2192387092825909917667925 25692036244053631847671)
              ·
                rfl

theorem cell21_1013210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 8].length) (baseStart_1013210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013210 prefixEnd_1013210 := by exact prefixLift 1013210
  have htrace : WordTrace (prefixWord ++ tailWord_1013210) baseStart_1013210 baseEnd_1013210 := by
    simpa [prefixWord, tailWord_1013210, baseEnd_1013210] using wordTrace_append hprefix tailTrace_1013210
  have hstable : (prefixWord ++ tailWord_1013210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013210).length < 2 ^ (prefixWord ++ tailWord_1013210).sum := by decide
  have hdescent : baseEnd_1013210 < baseStart_1013210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013213 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1013213 : Nat := 118140960795 + 1013213 * 2 ^ 59
def prefixEnd_1013213 : Nat := 4983230072969 + 3 ^ 40 * 1013213 * 2
def baseEnd_1013213 : Nat := 231229010837355348079033

theorem tailTrace_1013213 : CollatzResearch.WordTrace tailWord_1013213 prefixEnd_1013213 231229010837355348079033 := by
  unfold tailWord_1013213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36954914078309818848852293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24636609385539879232568195 36954914078309818848852293)
  ·
    refine ⟨6929046389683091034159805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36954914078309818848852293 6929046389683091034159805)
    ·
      refine ⟨2598392396131159137809927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6929046389683091034159805 2598392396131159137809927)
      ·
        refine ⟨3897588594196738706714891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598392396131159137809927 3897588594196738706714891)
        ·
          refine ⟨5846382891295108060072337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897588594196738706714891 5846382891295108060072337)
          ·
            refine ⟨4384787168471331045054253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846382891295108060072337 4384787168471331045054253)
            ·
              refine ⟨1644295188176749141895345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4384787168471331045054253 1644295188176749141895345)
              ·
                refine ⟨1233221391132561856421509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644295188176749141895345 1233221391132561856421509)
                ·
                  refine ⟨231229010837355348079033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233221391132561856421509 231229010837355348079033)
                  ·
                    rfl

theorem cell21_1013213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1013213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013213 prefixEnd_1013213 := by exact prefixLift 1013213
  have htrace : WordTrace (prefixWord ++ tailWord_1013213) baseStart_1013213 baseEnd_1013213 := by
    simpa [prefixWord, tailWord_1013213, baseEnd_1013213] using wordTrace_append hprefix tailTrace_1013213
  have hstable : (prefixWord ++ tailWord_1013213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013213).length < 2 ^ (prefixWord ++ tailWord_1013213).sum := by decide
  have hdescent : baseEnd_1013213 < baseStart_1013213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013261 : List Nat := [1, 7, 1, 1, 2, 2, 7]
def baseStart_1013261 : Nat := 118140960795 + 1013261 * 2 ^ 59
def prefixEnd_1013261 : Nat := 4983230072969 + 3 ^ 40 * 1013261 * 2
def baseEnd_1013261 : Nat := 25693329454590881253215

theorem tailTrace_1013261 : CollatzResearch.WordTrace tailWord_1013261 prefixEnd_1013261 25693329454590881253215 := by
  unfold tailWord_1013261
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956664782135923046599637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24637776521423948697733091 36956664782135923046599637)
  ·
    refine ⟨866171830831310696404679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36956664782135923046599637 866171830831310696404679)
    ·
      refine ⟨1299257746246966044607019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866171830831310696404679 1299257746246966044607019)
      ·
        refine ⟨1948886619370449066910529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299257746246966044607019 1948886619370449066910529)
        ·
          refine ⟨1461664964527836800182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948886619370449066910529 1461664964527836800182897)
          ·
            refine ⟨1096248723395877600137173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461664964527836800182897 1096248723395877600137173)
            ·
              refine ⟨25693329454590881253215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1096248723395877600137173 25693329454590881253215)
              ·
                rfl

theorem cell21_1013261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 7].length) (baseStart_1013261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013261 prefixEnd_1013261 := by exact prefixLift 1013261
  have htrace : WordTrace (prefixWord ++ tailWord_1013261) baseStart_1013261 baseEnd_1013261 := by
    simpa [prefixWord, tailWord_1013261, baseEnd_1013261] using wordTrace_append hprefix tailTrace_1013261
  have hstable : (prefixWord ++ tailWord_1013261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013261).length < 2 ^ (prefixWord ++ tailWord_1013261).sum := by decide
  have hdescent : baseEnd_1013261 < baseStart_1013261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013278 : List Nat := [4, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1013278 : Nat := 118140960795 + 1013278 * 2 ^ 59
def prefixEnd_1013278 : Nat := 4983230072969 + 3 ^ 40 * 1013278 * 2
def baseEnd_1013278 : Nat := 77081281574309893165189

theorem tailTrace_1013278 : CollatzResearch.WordTrace tailWord_1013278 prefixEnd_1013278 77081281574309893165189 := by
  unfold tailWord_1013278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619660602884291868746061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24638189882049556633312325 4619660602884291868746061)
  ·
    refine ⟨1732372726081609450779773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4619660602884291868746061 1732372726081609450779773)
    ·
      refine ⟨649639772280603544042415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1732372726081609450779773 649639772280603544042415)
      ·
        refine ⟨974459658420905316063623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649639772280603544042415 974459658420905316063623)
        ·
          refine ⟨1461689487631357974095435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974459658420905316063623 1461689487631357974095435)
          ·
            refine ⟨2192534231447036961143153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461689487631357974095435 2192534231447036961143153)
            ·
              refine ⟨1644400673585277720857365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192534231447036961143153 1644400673585277720857365)
              ·
                refine ⟨77081281574309893165189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1644400673585277720857365 77081281574309893165189)
                ·
                  rfl

theorem cell21_1013278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1013278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013278 prefixEnd_1013278 := by exact prefixLift 1013278
  have htrace : WordTrace (prefixWord ++ tailWord_1013278) baseStart_1013278 baseEnd_1013278 := by
    simpa [prefixWord, tailWord_1013278, baseEnd_1013278] using wordTrace_append hprefix tailTrace_1013278
  have hstable : (prefixWord ++ tailWord_1013278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013278).length < 2 ^ (prefixWord ++ tailWord_1013278).sum := by decide
  have hdescent : baseEnd_1013278 < baseStart_1013278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013348 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1013348 : Nat := 118140960795 + 1013348 * 2 ^ 59
def prefixEnd_1013348 : Nat := 4983230072969 + 3 ^ 40 * 1013348 * 2
def baseEnd_1013348 : Nat := 231259819676625113328757

theorem tailTrace_1013348 : CollatzResearch.WordTrace tailWord_1013348 prefixEnd_1013348 231259819676625113328757 := by
  unfold tailWord_1013348
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479918966410368452508349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24639891955213824603344465 18479918966410368452508349)
  ·
    refine ⟨6929969612403888169690631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18479918966410368452508349 6929969612403888169690631)
    ·
      refine ⟨10394954418605832254535947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929969612403888169690631 10394954418605832254535947)
      ·
        refine ⟨15592431627908748381803921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10394954418605832254535947 15592431627908748381803921)
        ·
          refine ⟨11694323720931561286352941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15592431627908748381803921 11694323720931561286352941)
          ·
            refine ⟨4385371395349335482382353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11694323720931561286352941 4385371395349335482382353)
            ·
              refine ⟨3289028546512001611786765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385371395349335482382353 3289028546512001611786765)
              ·
                refine ⟨1233385704942000604420037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3289028546512001611786765 1233385704942000604420037)
                ·
                  refine ⟨231259819676625113328757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233385704942000604420037 231259819676625113328757)
                  ·
                    rfl

theorem cell21_1013348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1013348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013348 prefixEnd_1013348 := by exact prefixLift 1013348
  have htrace : WordTrace (prefixWord ++ tailWord_1013348) baseStart_1013348 baseEnd_1013348 := by
    simpa [prefixWord, tailWord_1013348, baseEnd_1013348] using wordTrace_append hprefix tailTrace_1013348
  have hstable : (prefixWord ++ tailWord_1013348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013348).length < 2 ^ (prefixWord ++ tailWord_1013348).sum := by decide
  have hdescent : baseEnd_1013348 < baseStart_1013348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013376 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1013376 : Nat := 118140960795 + 1013376 * 2 ^ 59
def prefixEnd_1013376 : Nat := 4983230072969 + 3 ^ 40 * 1013376 * 2
def baseEnd_1013376 : Nat := 231266209658103286862033

theorem tailTrace_1013376 : CollatzResearch.WordTrace tailWord_1013376 prefixEnd_1013376 231266209658103286862033 := by
  unfold tailWord_1013376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480429588359648843517991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24640572784479531791357321 18480429588359648843517991)
  ·
    refine ⟨27720644382539473265276987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18480429588359648843517991 27720644382539473265276987)
    ·
      refine ⟨41580966573809209897915481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720644382539473265276987 41580966573809209897915481)
      ·
        refine ⟨31185724930356907423436611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41580966573809209897915481 31185724930356907423436611)
        ·
          refine ⟨46778587395535361135154917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185724930356907423436611 46778587395535361135154917)
          ·
            refine ⟨8770985136662880212841547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46778587395535361135154917 8770985136662880212841547)
            ·
              refine ⟨13156477704994320319262321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770985136662880212841547 13156477704994320319262321)
              ·
                refine ⟨9867358278745740239446741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13156477704994320319262321 9867358278745740239446741)
                ·
                  refine ⟨231266209658103286862033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9867358278745740239446741 231266209658103286862033)
                  ·
                    rfl

theorem cell21_1013376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1013376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013376 prefixEnd_1013376 := by exact prefixLift 1013376
  have htrace : WordTrace (prefixWord ++ tailWord_1013376) baseStart_1013376 baseEnd_1013376 := by
    simpa [prefixWord, tailWord_1013376, baseEnd_1013376] using wordTrace_append hprefix tailTrace_1013376
  have hstable : (prefixWord ++ tailWord_1013376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013376).length < 2 ^ (prefixWord ++ tailWord_1013376).sum := by decide
  have hdescent : baseEnd_1013376 < baseStart_1013376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013438 : List Nat := [4, 2, 1, 1, 2, 2, 9]
def baseStart_1013438 : Nat := 118140960795 + 1013438 * 2 ^ 59
def prefixEnd_1013438 : Nat := 4983230072969 + 3 ^ 40 * 1013438 * 2
def baseEnd_1013438 : Nat := 25697817655867217425397

theorem tailTrace_1013438 : CollatzResearch.WordTrace tailWord_1013438 prefixEnd_1013438 25697817655867217425397 := by
  unfold tailWord_1013438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620390062811835284474121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24642080334996454850528645 4620390062811835284474121)
  ·
    refine ⟨3465292547108876463355591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4620390062811835284474121 3465292547108876463355591)
    ·
      refine ⟨5197938820663314695033387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465292547108876463355591 5197938820663314695033387)
      ·
        refine ⟨7796908230994972042550081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197938820663314695033387 7796908230994972042550081)
        ·
          refine ⟨5847681173246229031912561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7796908230994972042550081 5847681173246229031912561)
          ·
            refine ⟨4385760879934671773934421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847681173246229031912561 4385760879934671773934421)
            ·
              refine ⟨25697817655867217425397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4385760879934671773934421 25697817655867217425397)
              ·
                rfl

theorem cell21_1013438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 9].length) (baseStart_1013438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013438 prefixEnd_1013438 := by exact prefixLift 1013438
  have htrace : WordTrace (prefixWord ++ tailWord_1013438) baseStart_1013438 baseEnd_1013438 := by
    simpa [prefixWord, tailWord_1013438, baseEnd_1013438] using wordTrace_append hprefix tailTrace_1013438
  have hstable : (prefixWord ++ tailWord_1013438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013438).length < 2 ^ (prefixWord ++ tailWord_1013438).sum := by decide
  have hdescent : baseEnd_1013438 < baseStart_1013438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013458 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1013458 : Nat := 118140960795 + 1013458 * 2 ^ 59
def prefixEnd_1013458 : Nat := 4983230072969 + 3 ^ 40 * 1013458 * 2
def baseEnd_1013458 : Nat := 231284923175289366495199

theorem tailTrace_1013458 : CollatzResearch.WordTrace tailWord_1013458 prefixEnd_1013458 231284923175289366495199 := by
  unfold tailWord_1013458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240962490605556422880257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24642566641614817127680685 9240962490605556422880257)
  ·
    refine ⟨6930721867954167317160193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9240962490605556422880257 6930721867954167317160193)
    ·
      refine ⟨5198041400965625487870145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930721867954167317160193 5198041400965625487870145)
      ·
        refine ⟨3898531050724219115902609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198041400965625487870145 3898531050724219115902609)
        ·
          refine ⟨2923898288043164336926957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898531050724219115902609 2923898288043164336926957)
          ·
            refine ⟨1096461858016186626347609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2923898288043164336926957 1096461858016186626347609)
            ·
              refine ⟨822346393512139969760707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096461858016186626347609 822346393512139969760707)
              ·
                refine ⟨1233519590268209954641061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822346393512139969760707 1233519590268209954641061)
                ·
                  refine ⟨231284923175289366495199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233519590268209954641061 231284923175289366495199)
                  ·
                    rfl

theorem cell21_1013458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1013458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013458 prefixEnd_1013458 := by exact prefixLift 1013458
  have htrace : WordTrace (prefixWord ++ tailWord_1013458) baseStart_1013458 baseEnd_1013458 := by
    simpa [prefixWord, tailWord_1013458, baseEnd_1013458] using wordTrace_append hprefix tailTrace_1013458
  have hstable : (prefixWord ++ tailWord_1013458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013458).length < 2 ^ (prefixWord ++ tailWord_1013458).sum := by decide
  have hdescent : baseEnd_1013458 < baseStart_1013458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013486 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_1013486 : Nat := 118140960795 + 1013486 * 2 ^ 59
def prefixEnd_1013486 : Nat := 4983230072969 + 3 ^ 40 * 1013486 * 2
def baseEnd_1013486 : Nat := 231291313156767540028475

theorem tailTrace_1013486 : CollatzResearch.WordTrace tailWord_1013486 prefixEnd_1013486 231291313156767540028475 := by
  unfold tailWord_1013486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620608900790098309192539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24643247470880524315693541 4620608900790098309192539)
  ·
    refine ⟨6930913351185147463788809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620608900790098309192539 6930913351185147463788809)
    ·
      refine ⟨5198185013388860597841607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930913351185147463788809 5198185013388860597841607)
      ·
        refine ⟨7797277520083290896762411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198185013388860597841607 7797277520083290896762411)
        ·
          refine ⟨11695916280124936345143617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797277520083290896762411 11695916280124936345143617)
          ·
            refine ⟨8771937210093702258857713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11695916280124936345143617 8771937210093702258857713)
            ·
              refine ⟨6578952907570276694143285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771937210093702258857713 6578952907570276694143285)
              ·
                refine ⟨616776835084713440075933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6578952907570276694143285 616776835084713440075933)
                ·
                  refine ⟨231291313156767540028475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616776835084713440075933 231291313156767540028475)
                  ·
                    rfl

theorem cell21_1013486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_1013486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013486 prefixEnd_1013486 := by exact prefixLift 1013486
  have htrace : WordTrace (prefixWord ++ tailWord_1013486) baseStart_1013486 baseEnd_1013486 := by
    simpa [prefixWord, tailWord_1013486, baseEnd_1013486] using wordTrace_append hprefix tailTrace_1013486
  have hstable : (prefixWord ++ tailWord_1013486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013486).length < 2 ^ (prefixWord ++ tailWord_1013486).sum := by decide
  have hdescent : baseEnd_1013486 < baseStart_1013486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013500 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1013500 : Nat := 118140960795 + 1013500 * 2 ^ 59
def prefixEnd_1013500 : Nat := 4983230072969 + 3 ^ 40 * 1013500 * 2
def baseEnd_1013500 : Nat := 231294508147506626795113

theorem tailTrace_1013500 : CollatzResearch.WordTrace tailWord_1013500 prefixEnd_1013500 231294508147506626795113 := by
  unfold tailWord_1013500
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482690914135033432274977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24643587885513377909699969 18482690914135033432274977)
  ·
    refine ⟨13862018185601275074206233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18482690914135033432274977 13862018185601275074206233)
    ·
      refine ⟨10396513639200956305654675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13862018185601275074206233 10396513639200956305654675)
      ·
        refine ⟨15594770458801434458482013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396513639200956305654675 15594770458801434458482013)
        ·
          refine ⟨5848038922050537921930755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15594770458801434458482013 5848038922050537921930755)
          ·
            refine ⟨8772058383075806882896133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848038922050537921930755 8772058383075806882896133)
            ·
              refine ⟨1644760946826713790543025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8772058383075806882896133 1644760946826713790543025)
              ·
                refine ⟨1233570710120035342907269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644760946826713790543025 1233570710120035342907269)
                ·
                  refine ⟨231294508147506626795113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233570710120035342907269 231294508147506626795113)
                  ·
                    rfl

theorem cell21_1013500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1013500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013500 prefixEnd_1013500 := by exact prefixLift 1013500
  have htrace : WordTrace (prefixWord ++ tailWord_1013500) baseStart_1013500 baseEnd_1013500 := by
    simpa [prefixWord, tailWord_1013500, baseEnd_1013500] using wordTrace_append hprefix tailTrace_1013500
  have hstable : (prefixWord ++ tailWord_1013500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013500).length < 2 ^ (prefixWord ++ tailWord_1013500).sum := by decide
  have hdescent : baseEnd_1013500 < baseStart_1013500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013514 : List Nat := [3, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1013514 : Nat := 118140960795 + 1013514 * 2 ^ 59
def prefixEnd_1013514 : Nat := 4983230072969 + 3 ^ 40 * 1013514 * 2
def baseEnd_1013514 : Nat := 77099234379415237853917

theorem tailTrace_1013514 : CollatzResearch.WordTrace tailWord_1013514 prefixEnd_1013514 77099234379415237853917 := by
  unfold tailWord_1013514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241473112554836813889899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24643928300146231503706397 9241473112554836813889899)
  ·
    refine ⟨13862209668832255220834849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9241473112554836813889899 13862209668832255220834849)
    ·
      refine ⟨10396657251624191415626137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13862209668832255220834849 10396657251624191415626137)
      ·
        refine ⟨7797492938718143561719603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10396657251624191415626137 7797492938718143561719603)
        ·
          refine ⟨11696239408077215342579405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797492938718143561719603 11696239408077215342579405)
          ·
            refine ⟨4386089778028955753467277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11696239408077215342579405 4386089778028955753467277)
            ·
              refine ⟨1644783666760858407550229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4386089778028955753467277 1644783666760858407550229)
              ·
                refine ⟨77099234379415237853917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1644783666760858407550229 77099234379415237853917)
                ·
                  rfl

theorem cell21_1013514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1013514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013514 prefixEnd_1013514 := by exact prefixLift 1013514
  have htrace : WordTrace (prefixWord ++ tailWord_1013514) baseStart_1013514 baseEnd_1013514 := by
    simpa [prefixWord, tailWord_1013514, baseEnd_1013514] using wordTrace_append hprefix tailTrace_1013514
  have hstable : (prefixWord ++ tailWord_1013514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013514).length < 2 ^ (prefixWord ++ tailWord_1013514).sum := by decide
  have hdescent : baseEnd_1013514 < baseStart_1013514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013528 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_1013528 : Nat := 118140960795 + 1013528 * 2 ^ 59
def prefixEnd_1013528 : Nat := 4983230072969 + 3 ^ 40 * 1013528 * 2
def baseEnd_1013528 : Nat := 231300898128984800328389

theorem tailTrace_1013528 : CollatzResearch.WordTrace tailWord_1013528 prefixEnd_1013528 231300898128984800328389 := by
  unfold tailWord_1013528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483201536084313823284619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24644268714779085097712825 18483201536084313823284619)
  ·
    refine ⟨27724802304126470734926929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483201536084313823284619 27724802304126470734926929)
    ·
      refine ⟨20793601728094853051195197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27724802304126470734926929 20793601728094853051195197)
      ·
        refine ⟨7797600648035569894198199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20793601728094853051195197 7797600648035569894198199)
        ·
          refine ⟨11696400972053354841297299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797600648035569894198199 11696400972053354841297299)
          ·
            refine ⟨17544601458080032261945949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696400972053354841297299 17544601458080032261945949)
            ·
              refine ⟨6579225546780012098229731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544601458080032261945949 6579225546780012098229731)
              ·
                refine ⟨9868838320170018147344597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579225546780012098229731 9868838320170018147344597)
                ·
                  refine ⟨231300898128984800328389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9868838320170018147344597 231300898128984800328389)
                  ·
                    rfl

theorem cell21_1013528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_1013528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013528 prefixEnd_1013528 := by exact prefixLift 1013528
  have htrace : WordTrace (prefixWord ++ tailWord_1013528) baseStart_1013528 baseEnd_1013528 := by
    simpa [prefixWord, tailWord_1013528, baseEnd_1013528] using wordTrace_append hprefix tailTrace_1013528
  have hstable : (prefixWord ++ tailWord_1013528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013528).length < 2 ^ (prefixWord ++ tailWord_1013528).sum := by decide
  have hdescent : baseEnd_1013528 < baseStart_1013528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013559 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_1013559 : Nat := 118140960795 + 1013559 * 2 ^ 59
def prefixEnd_1013559 : Nat := 4983230072969 + 3 ^ 40 * 1013559 * 2
def baseEnd_1013559 : Nat := 231307972751335635311659

theorem tailTrace_1013559 : CollatzResearch.WordTrace tailWord_1013559 prefixEnd_1013559 231307972751335635311659 := by
  unfold tailWord_1013559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36967533735056319940947731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24645022490037546627298487 36967533735056319940947731)
  ·
    refine ⟨55451300602584479911421597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36967533735056319940947731 55451300602584479911421597)
    ·
      refine ⟨20794237725969179966783099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55451300602584479911421597 20794237725969179966783099)
      ·
        refine ⟨31191356588953769950174649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794237725969179966783099 31191356588953769950174649)
        ·
          refine ⟨23393517441715327462630987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31191356588953769950174649 23393517441715327462630987)
          ·
            refine ⟨35090276162572991193946481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23393517441715327462630987 35090276162572991193946481)
            ·
              refine ⟨26317707121929743395459861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35090276162572991193946481 26317707121929743395459861)
              ·
                refine ⟨1233642521340456721662181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26317707121929743395459861 1233642521340456721662181)
                ·
                  refine ⟨231307972751335635311659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233642521340456721662181 231307972751335635311659)
                  ·
                    rfl

theorem cell21_1013559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_1013559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013559 prefixEnd_1013559 := by exact prefixLift 1013559
  have htrace : WordTrace (prefixWord ++ tailWord_1013559) baseStart_1013559 baseEnd_1013559 := by
    simpa [prefixWord, tailWord_1013559, baseEnd_1013559] using wordTrace_append hprefix tailTrace_1013559
  have hstable : (prefixWord ++ tailWord_1013559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013559).length < 2 ^ (prefixWord ++ tailWord_1013559).sum := by decide
  have hdescent : baseEnd_1013559 < baseStart_1013559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013562 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_1013562 : Nat := 118140960795 + 1013562 * 2 ^ 59
def prefixEnd_1013562 : Nat := 4983230072969 + 3 ^ 40 * 1013562 * 2
def baseEnd_1013562 : Nat := 231308657392208296761653

theorem tailTrace_1013562 : CollatzResearch.WordTrace tailWord_1013562 prefixEnd_1013562 231308657392208296761653 := by
  unfold tailWord_1013562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241910788511362863326735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24645095436030300968871293 9241910788511362863326735)
  ·
    refine ⟨13862866182767044294990103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9241910788511362863326735 13862866182767044294990103)
    ·
      refine ⟨20794299274150566442485155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862866182767044294990103 20794299274150566442485155)
      ·
        refine ⟨31191448911225849663727733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794299274150566442485155 31191448911225849663727733)
        ·
          refine ⟨2924198335427423405974475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31191448911225849663727733 2924198335427423405974475)
          ·
            refine ⟨4386297503141135108961713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924198335427423405974475 4386297503141135108961713)
            ·
              refine ⟨3289723127355851331721285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386297503141135108961713 3289723127355851331721285)
              ·
                refine ⟨616823086379222124697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289723127355851331721285 616823086379222124697741)
                ·
                  refine ⟨231308657392208296761653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616823086379222124697741 231308657392208296761653)
                  ·
                    rfl

theorem cell21_1013562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_1013562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013562 prefixEnd_1013562 := by exact prefixLift 1013562
  have htrace : WordTrace (prefixWord ++ tailWord_1013562) baseStart_1013562 baseEnd_1013562 := by
    simpa [prefixWord, tailWord_1013562, baseEnd_1013562] using wordTrace_append hprefix tailTrace_1013562
  have hstable : (prefixWord ++ tailWord_1013562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013562).length < 2 ^ (prefixWord ++ tailWord_1013562).sum := by decide
  have hdescent : baseEnd_1013562 < baseStart_1013562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013573 : List Nat := [1, 3, 1, 1, 1, 2, 4, 8]
def baseStart_1013573 : Nat := 118140960795 + 1013573 * 2 ^ 59
def prefixEnd_1013573 : Nat := 4983230072969 + 3 ^ 40 * 1013573 * 2
def baseEnd_1013573 : Nat := 77103722580691574026099

theorem tailTrace_1013573 : CollatzResearch.WordTrace tailWord_1013573 prefixEnd_1013573 77103722580691574026099 := by
  unfold tailWord_1013573
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968044357005600331957373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24645362904670400221304915 36968044357005600331957373)
  ·
    refine ⟨13863016633877100124484015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36968044357005600331957373 13863016633877100124484015)
    ·
      refine ⟨20794524950815650186726023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13863016633877100124484015 20794524950815650186726023)
      ·
        refine ⟨31191787426223475280089035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794524950815650186726023 31191787426223475280089035)
        ·
          refine ⟨46787681139335212920133553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31191787426223475280089035 46787681139335212920133553)
          ·
            refine ⟨35090760854501409690100165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46787681139335212920133553 35090760854501409690100165)
            ·
              refine ⟨6579517660219014316893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35090760854501409690100165 6579517660219014316893781)
              ·
                refine ⟨77103722580691574026099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6579517660219014316893781 77103722580691574026099)
                ·
                  rfl

theorem cell21_1013573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_1013573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013573 prefixEnd_1013573 := by exact prefixLift 1013573
  have htrace : WordTrace (prefixWord ++ tailWord_1013573) baseStart_1013573 baseEnd_1013573 := by
    simpa [prefixWord, tailWord_1013573, baseEnd_1013573] using wordTrace_append hprefix tailTrace_1013573
  have hstable : (prefixWord ++ tailWord_1013573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013573).length < 2 ^ (prefixWord ++ tailWord_1013573).sum := by decide
  have hdescent : baseEnd_1013573 < baseStart_1013573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013596 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1013596 : Nat := 118140960795 + 1013596 * 2 ^ 59
def prefixEnd_1013596 : Nat := 4983230072969 + 3 ^ 40 * 1013596 * 2
def baseEnd_1013596 : Nat := 231316416655431793194917

theorem tailTrace_1013596 : CollatzResearch.WordTrace tailWord_1013596 prefixEnd_1013596 231316416655431793194917 := by
  unfold tailWord_1013596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484441617961137630022321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24645922157281516840029761 18484441617961137630022321)
  ·
    refine ⟨13863331213470853222516741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18484441617961137630022321 13863331213470853222516741)
    ·
      refine ⟨2599374602525784979221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13863331213470853222516741 2599374602525784979221889)
      ·
        refine ⟨1949530951894338734416417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2599374602525784979221889 1949530951894338734416417)
        ·
          refine ⟨1462148213920754050812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949530951894338734416417 1462148213920754050812313)
          ·
            refine ⟨1096611160440565538109235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462148213920754050812313 1096611160440565538109235)
            ·
              refine ⟨1644916740660848307163853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096611160440565538109235 1644916740660848307163853)
              ·
                refine ⟨616843777747818115186445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644916740660848307163853 616843777747818115186445)
                ·
                  refine ⟨231316416655431793194917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616843777747818115186445 231316416655431793194917)
                  ·
                    rfl

theorem cell21_1013596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1013596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013596 prefixEnd_1013596 := by exact prefixLift 1013596
  have htrace : WordTrace (prefixWord ++ tailWord_1013596) baseStart_1013596 baseEnd_1013596 := by
    simpa [prefixWord, tailWord_1013596, baseEnd_1013596] using wordTrace_append hprefix tailTrace_1013596
  have hstable : (prefixWord ++ tailWord_1013596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013596).length < 2 ^ (prefixWord ++ tailWord_1013596).sum := by decide
  have hdescent : baseEnd_1013596 < baseStart_1013596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013649 : List Nat := [1, 2, 2, 1, 1, 1, 6, 7]
def baseStart_1013649 : Nat := 118140960795 + 1013649 * 2 ^ 59
def prefixEnd_1013649 : Nat := 4983230072969 + 3 ^ 40 * 1013649 * 2
def baseEnd_1013649 : Nat := 77109503992505159603825

theorem tailTrace_1013649 : CollatzResearch.WordTrace tailWord_1013649 prefixEnd_1013649 77109503992505159603825 := by
  unfold tailWord_1013649
  simp only [CollatzResearch.WordTrace]
  refine ⟨36970816304730265311724001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24647210869820176874482667 36970816304730265311724001)
  ·
    refine ⟨27728112228547698983793001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36970816304730265311724001 27728112228547698983793001)
    ·
      refine ⟨20796084171410774237844751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27728112228547698983793001 20796084171410774237844751)
      ·
        refine ⟨31194126257116161356767127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796084171410774237844751 31194126257116161356767127)
        ·
          refine ⟨46791189385674242035150691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31194126257116161356767127 46791189385674242035150691)
          ·
            refine ⟨70186784078511363052726037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46791189385674242035150691 70186784078511363052726037)
            ·
              refine ⟨3290005503680220143096533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70186784078511363052726037 3290005503680220143096533)
              ·
                refine ⟨77109503992505159603825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3290005503680220143096533 77109503992505159603825)
                ·
                  rfl

theorem cell21_1013649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_1013649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013649 prefixEnd_1013649 := by exact prefixLift 1013649
  have htrace : WordTrace (prefixWord ++ tailWord_1013649) baseStart_1013649 baseEnd_1013649 := by
    simpa [prefixWord, tailWord_1013649, baseEnd_1013649] using wordTrace_append hprefix tailTrace_1013649
  have hstable : (prefixWord ++ tailWord_1013649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013649).length < 2 ^ (prefixWord ++ tailWord_1013649).sum := by decide
  have hdescent : baseEnd_1013649 < baseStart_1013649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013666 : List Nat := [3, 3, 1, 2, 3, 9]
def baseStart_1013666 : Nat := 118140960795 + 1013666 * 2 ^ 59
def prefixEnd_1013666 : Nat := 4983230072969 + 3 ^ 40 * 1013666 * 2
def baseEnd_1013666 : Nat := 8567866355893601001041

theorem tailTrace_1013666 : CollatzResearch.WordTrace tailWord_1013666 prefixEnd_1013666 8567866355893601001041 := by
  unfold tailWord_1013666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242859086417169303773213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24647624230445784810061901 9242859086417169303773213)
  ·
    refine ⟨3466072157406438488914955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9242859086417169303773213 3466072157406438488914955)
    ·
      refine ⟨5199108236109657733372433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3466072157406438488914955 5199108236109657733372433)
      ·
        refine ⟨3899331177082243300029325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5199108236109657733372433 3899331177082243300029325)
        ·
          refine ⟨1462249191405841237510997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3899331177082243300029325 1462249191405841237510997)
          ·
            refine ⟨8567866355893601001041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1462249191405841237510997 8567866355893601001041)
            ·
              rfl

theorem cell21_1013666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 9].length) (baseStart_1013666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013666 prefixEnd_1013666 := by exact prefixLift 1013666
  have htrace : WordTrace (prefixWord ++ tailWord_1013666) baseStart_1013666 baseEnd_1013666 := by
    simpa [prefixWord, tailWord_1013666, baseEnd_1013666] using wordTrace_append hprefix tailTrace_1013666
  have hstable : (prefixWord ++ tailWord_1013666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013666).length < 2 ^ (prefixWord ++ tailWord_1013666).sum := by decide
  have hdescent : baseEnd_1013666 < baseStart_1013666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013672 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_1013672 : Nat := 118140960795 + 1013672 * 2 ^ 59
def prefixEnd_1013672 : Nat := 4983230072969 + 3 ^ 40 * 1013672 * 2
def baseEnd_1013672 : Nat := 231333760890872549928095

theorem tailTrace_1013672 : CollatzResearch.WordTrace tailWord_1013672 prefixEnd_1013672 231333760890872549928095 := by
  unfold tailWord_1013672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485827591823470119905635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24647770122431293493207513 18485827591823470119905635)
  ·
    refine ⟨27728741387735205179858453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18485827591823470119905635 27728741387735205179858453)
    ·
      refine ⟨1299784752550087742805865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27728741387735205179858453 1299784752550087742805865)
      ·
        refine ⟨974838564412565807104399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299784752550087742805865 974838564412565807104399)
        ·
          refine ⟨1462257846618848710656599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974838564412565807104399 1462257846618848710656599)
          ·
            refine ⟨2193386769928273065984899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462257846618848710656599 2193386769928273065984899)
            ·
              refine ⟨3290080154892409598977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193386769928273065984899 3290080154892409598977349)
              ·
                refine ⟨616890029042326799808253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3290080154892409598977349 616890029042326799808253)
                ·
                  refine ⟨231333760890872549928095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616890029042326799808253 231333760890872549928095)
                  ·
                    rfl

theorem cell21_1013672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_1013672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013672 prefixEnd_1013672 := by exact prefixLift 1013672
  have htrace : WordTrace (prefixWord ++ tailWord_1013672) baseStart_1013672 baseEnd_1013672 := by
    simpa [prefixWord, tailWord_1013672, baseEnd_1013672] using wordTrace_append hprefix tailTrace_1013672
  have hstable : (prefixWord ++ tailWord_1013672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013672).length < 2 ^ (prefixWord ++ tailWord_1013672).sum := by decide
  have hdescent : baseEnd_1013672 < baseStart_1013672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013745 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 4]
def baseStart_1013745 : Nat := 118140960795 + 1013745 * 2 ^ 59
def prefixEnd_1013745 : Nat := 4983230072969 + 3 ^ 40 * 1013745 * 2
def baseEnd_1013745 : Nat := 231350420485440645211279

theorem tailTrace_1013745 : CollatzResearch.WordTrace tailWord_1013745 prefixEnd_1013745 231350420485440645211279 := by
  unfold tailWord_1013745
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974317712382473707218689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24649545141588315804812459 36974317712382473707218689)
  ·
    refine ⟨27730738284286855280414017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36974317712382473707218689 27730738284286855280414017)
    ·
      refine ⟨20798053713215141460310513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27730738284286855280414017 20798053713215141460310513)
      ·
        refine ⟨15598540284911356095232885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20798053713215141460310513 15598540284911356095232885)
        ·
          refine ⟨1462363151710439633928083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15598540284911356095232885 1462363151710439633928083)
          ·
            refine ⟨2193544727565659450892125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462363151710439633928083 2193544727565659450892125)
            ·
              refine ⟨822579272837122294084547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2193544727565659450892125 822579272837122294084547)
              ·
                refine ⟨1233868909255683441126821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822579272837122294084547 1233868909255683441126821)
                ·
                  refine ⟨231350420485440645211279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233868909255683441126821 231350420485440645211279)
                  ·
                    rfl

theorem cell21_1013745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_1013745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013745 prefixEnd_1013745 := by exact prefixLift 1013745
  have htrace : WordTrace (prefixWord ++ tailWord_1013745) baseStart_1013745 baseEnd_1013745 := by
    simpa [prefixWord, tailWord_1013745, baseEnd_1013745] using wordTrace_append hprefix tailTrace_1013745
  have hstable : (prefixWord ++ tailWord_1013745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013745).length < 2 ^ (prefixWord ++ tailWord_1013745).sum := by decide
  have hdescent : baseEnd_1013745 < baseStart_1013745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013756 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1013756 : Nat := 118140960795 + 1013756 * 2 ^ 59
def prefixEnd_1013756 : Nat := 4983230072969 + 3 ^ 40 * 1013756 * 2
def baseEnd_1013756 : Nat := 231352930835307070527923

theorem tailTrace_1013756 : CollatzResearch.WordTrace tailWord_1013756 prefixEnd_1013756 231352930835307070527923 := by
  unfold tailWord_1013756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18487359457671311292934561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24649812610228415057246081 18487359457671311292934561)
  ·
    refine ⟨13865519593253483469700921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18487359457671311292934561 13865519593253483469700921)
    ·
      refine ⟨10399139694940112602275691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13865519593253483469700921 10399139694940112602275691)
      ·
        refine ⟨15598709542410168903413537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399139694940112602275691 15598709542410168903413537)
        ·
          refine ⟨11699032156807626677560153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15598709542410168903413537 11699032156807626677560153)
          ·
            refine ⟨8774274117605720008170115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11699032156807626677560153 8774274117605720008170115)
            ·
              refine ⟨13161411176408580012255173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774274117605720008170115 13161411176408580012255173)
              ·
                refine ⟨2467764595576608752297845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13161411176408580012255173 2467764595576608752297845)
                ·
                  refine ⟨231352930835307070527923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467764595576608752297845 231352930835307070527923)
                  ·
                    rfl

theorem cell21_1013756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1013756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013756 prefixEnd_1013756 := by exact prefixLift 1013756
  have htrace : WordTrace (prefixWord ++ tailWord_1013756) baseStart_1013756 baseEnd_1013756 := by
    simpa [prefixWord, tailWord_1013756, baseEnd_1013756] using wordTrace_append hprefix tailTrace_1013756
  have hstable : (prefixWord ++ tailWord_1013756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013756).length < 2 ^ (prefixWord ++ tailWord_1013756).sum := by decide
  have hdescent : baseEnd_1013756 < baseStart_1013756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013849 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 3]
def baseStart_1013849 : Nat := 118140960795 + 1013849 * 2 ^ 59
def prefixEnd_1013849 : Nat := 4983230072969 + 3 ^ 40 * 1013849 * 2
def baseEnd_1013849 : Nat := 231374154702359575477733

theorem tailTrace_1013849 : CollatzResearch.WordTrace tailWord_1013849 prefixEnd_1013849 231374154702359575477733 := by
  unfold tailWord_1013849
  simp only [CollatzResearch.WordTrace]
  refine ⟨36978110904005699469004601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24652073936003799646003067 36978110904005699469004601)
  ·
    refine ⟨27733583178004274601753451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36978110904005699469004601 27733583178004274601753451)
    ·
      refine ⟨41600374767006411902630177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27733583178004274601753451 41600374767006411902630177)
      ·
        refine ⟨31200281075254808926972633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41600374767006411902630177 31200281075254808926972633)
        ·
          refine ⟨23400210806441106695229475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31200281075254808926972633 23400210806441106695229475)
          ·
            refine ⟨35100316209661660042844213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23400210806441106695229475 35100316209661660042844213)
            ·
              refine ⟨3290654644655780629016645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35100316209661660042844213 3290654644655780629016645)
              ·
                refine ⟨616997745872958867940621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3290654644655780629016645 616997745872958867940621)
                ·
                  refine ⟨231374154702359575477733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616997745872958867940621 231374154702359575477733)
                  ·
                    rfl

theorem cell21_1013849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_1013849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013849 prefixEnd_1013849 := by exact prefixLift 1013849
  have htrace : WordTrace (prefixWord ++ tailWord_1013849) baseStart_1013849 baseEnd_1013849 := by
    simpa [prefixWord, tailWord_1013849, baseEnd_1013849] using wordTrace_append hprefix tailTrace_1013849
  have hstable : (prefixWord ++ tailWord_1013849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013849).length < 2 ^ (prefixWord ++ tailWord_1013849).sum := by decide
  have hdescent : baseEnd_1013849 < baseStart_1013849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013863 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_1013863 : Nat := 118140960795 + 1013863 * 2 ^ 59
def prefixEnd_1013863 : Nat := 4983230072969 + 3 ^ 40 * 1013863 * 2
def baseEnd_1013863 : Nat := 231377349693098662244371

theorem tailTrace_1013863 : CollatzResearch.WordTrace tailWord_1013863 prefixEnd_1013863 231377349693098662244371 := by
  unfold tailWord_1013863
  simp only [CollatzResearch.WordTrace]
  refine ⟨36978621525954979860014243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24652414350636653240009495 36978621525954979860014243)
  ·
    refine ⟨55467932288932469790021365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36978621525954979860014243 55467932288932469790021365)
    ·
      refine ⟨5200118652087419042814503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55467932288932469790021365 5200118652087419042814503)
      ·
        refine ⟨7800177978131128564221755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200118652087419042814503 7800177978131128564221755)
        ·
          refine ⟨11700266967196692846332633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800177978131128564221755 11700266967196692846332633)
          ·
            refine ⟨8775200225397519634749475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11700266967196692846332633 8775200225397519634749475)
            ·
              refine ⟨13162800338096279452124213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8775200225397519634749475 13162800338096279452124213)
              ·
                refine ⟨1234012531696526198636645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13162800338096279452124213 1234012531696526198636645)
                ·
                  refine ⟨231377349693098662244371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234012531696526198636645 231377349693098662244371)
                  ·
                    rfl

theorem cell21_1013863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_1013863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013863 prefixEnd_1013863 := by exact prefixLift 1013863
  have htrace : WordTrace (prefixWord ++ tailWord_1013863) baseStart_1013863 baseEnd_1013863 := by
    simpa [prefixWord, tailWord_1013863, baseEnd_1013863] using wordTrace_append hprefix tailTrace_1013863
  have hstable : (prefixWord ++ tailWord_1013863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013863).length < 2 ^ (prefixWord ++ tailWord_1013863).sum := by decide
  have hdescent : baseEnd_1013863 < baseStart_1013863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013970 : List Nat := [3, 2, 2, 2, 1, 3, 2, 6]
def baseStart_1013970 : Nat := 118140960795 + 1013970 * 2 ^ 59
def prefixEnd_1013970 : Nat := 4983230072969 + 3 ^ 40 * 1013970 * 2
def baseEnd_1013970 : Nat := 77133922850296751320273

theorem tailTrace_1013970 : CollatzResearch.WordTrace tailWord_1013970 prefixEnd_1013970 77133922850296751320273 := by
  unfold tailWord_1013970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245631034141834283539841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24655016091044891422772909 9245631034141834283539841)
  ·
    refine ⟨6934223275606375712654881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9245631034141834283539841 6934223275606375712654881)
    ·
      refine ⟨5200667456704781784491161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6934223275606375712654881 5200667456704781784491161)
      ·
        refine ⟨3900500592528586338368371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200667456704781784491161 3900500592528586338368371)
        ·
          refine ⟨5850750888792879507552557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900500592528586338368371 5850750888792879507552557)
          ·
            refine ⟨2194031583297329815332209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5850750888792879507552557 2194031583297329815332209)
            ·
              refine ⟨1645523687472997361499157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2194031583297329815332209 1645523687472997361499157)
              ·
                refine ⟨77133922850296751320273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1645523687472997361499157 77133922850296751320273)
                ·
                  rfl

theorem cell21_1013970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_1013970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1013970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1013970 prefixEnd_1013970 := by exact prefixLift 1013970
  have htrace : WordTrace (prefixWord ++ tailWord_1013970) baseStart_1013970 baseEnd_1013970 := by
    simpa [prefixWord, tailWord_1013970, baseEnd_1013970] using wordTrace_append hprefix tailTrace_1013970
  have hstable : (prefixWord ++ tailWord_1013970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013970).length < 2 ^ (prefixWord ++ tailWord_1013970).sum := by decide
  have hdescent : baseEnd_1013970 < baseStart_1013970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014015 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_1014015 : Nat := 118140960795 + 1014015 * 2 ^ 59
def prefixEnd_1014015 : Nat := 4983230072969 + 3 ^ 40 * 1014015 * 2
def baseEnd_1014015 : Nat := 231412038163980175710727

theorem tailTrace_1014015 : CollatzResearch.WordTrace tailWord_1014015 prefixEnd_1014015 231412038163980175710727 := by
  unfold tailWord_1014015
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984165421404309819547499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24656110280936206546364999 36984165421404309819547499)
  ·
    refine ⟨55476248132106464729321249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36984165421404309819547499 55476248132106464729321249)
    ·
      refine ⟨41607186099079848546990937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55476248132106464729321249 41607186099079848546990937)
      ·
        refine ⟨31205389574309886410243203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41607186099079848546990937 31205389574309886410243203)
        ·
          refine ⟨46808084361464829615364805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31205389574309886410243203 46808084361464829615364805)
          ·
            refine ⟨8776515817774655552880901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46808084361464829615364805 8776515817774655552880901)
            ·
              refine ⟨1645596715832747916165169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8776515817774655552880901 1645596715832747916165169)
              ·
                refine ⟨1234197536874560937123877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645596715832747916165169 1234197536874560937123877)
                ·
                  refine ⟨231412038163980175710727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234197536874560937123877 231412038163980175710727)
                  ·
                    rfl

theorem cell21_1014015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_1014015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014015 prefixEnd_1014015 := by exact prefixLift 1014015
  have htrace : WordTrace (prefixWord ++ tailWord_1014015) baseStart_1014015 baseEnd_1014015 := by
    simpa [prefixWord, tailWord_1014015, baseEnd_1014015] using wordTrace_append hprefix tailTrace_1014015
  have hstable : (prefixWord ++ tailWord_1014015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014015).length < 2 ^ (prefixWord ++ tailWord_1014015).sum := by decide
  have hdescent : baseEnd_1014015 < baseStart_1014015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014043 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_1014043 : Nat := 118140960795 + 1014043 * 2 ^ 59
def prefixEnd_1014043 : Nat := 4983230072969 + 3 ^ 40 * 1014043 * 2
def baseEnd_1014043 : Nat := 231418428145458349244003

theorem tailTrace_1014043 : CollatzResearch.WordTrace tailWord_1014043 prefixEnd_1014043 231418428145458349244003 := by
  unfold tailWord_1014043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36985186665302870601566783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24656791110201913734377855 36985186665302870601566783)
  ·
    refine ⟨55477779997954305902350175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36985186665302870601566783 55477779997954305902350175)
    ·
      refine ⟨83216669996931458853525263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55477779997954305902350175 83216669996931458853525263)
      ·
        refine ⟨124825004995397188280287895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83216669996931458853525263 124825004995397188280287895)
        ·
          refine ⟨187237507493095782420431843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124825004995397188280287895 187237507493095782420431843)
          ·
            refine ⟨280856261239643673630647765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187237507493095782420431843 280856261239643673630647765)
            ·
              refine ⟨6582568622804148600718307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 280856261239643673630647765 6582568622804148600718307)
              ·
                refine ⟨9873852934206222901077461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582568622804148600718307 9873852934206222901077461)
                ·
                  refine ⟨231418428145458349244003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9873852934206222901077461 231418428145458349244003)
                  ·
                    rfl

theorem cell21_1014043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_1014043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014043 prefixEnd_1014043 := by exact prefixLift 1014043
  have htrace : WordTrace (prefixWord ++ tailWord_1014043) baseStart_1014043 baseEnd_1014043 := by
    simpa [prefixWord, tailWord_1014043, baseEnd_1014043] using wordTrace_append hprefix tailTrace_1014043
  have hstable : (prefixWord ++ tailWord_1014043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014043).length < 2 ^ (prefixWord ++ tailWord_1014043).sum := by decide
  have hdescent : baseEnd_1014043 < baseStart_1014043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014122 : List Nat := [3, 1, 3, 3, 1, 3, 7]
def baseStart_1014122 : Nat := 118140960795 + 1014122 * 2 ^ 59
def prefixEnd_1014122 : Nat := 4983230072969 + 3 ^ 40 * 1014122 * 2
def baseEnd_1014122 : Nat := 25715161891307974158575

theorem tailTrace_1014122 : CollatzResearch.WordTrace tailWord_1014122 prefixEnd_1014122 25715161891307974158575 := by
  unfold tailWord_1014122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247017008004166773423155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24658712021344444729128413 9247017008004166773423155)
  ·
    refine ⟨13870525512006250160134733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9247017008004166773423155 13870525512006250160134733)
    ·
      refine ⟨5201447067002343810050525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13870525512006250160134733 5201447067002343810050525)
      ·
        refine ⟨1950542650125878928768947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5201447067002343810050525 1950542650125878928768947)
        ·
          refine ⟨2925813975188818393153421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950542650125878928768947 2925813975188818393153421)
          ·
            refine ⟨1097180240695806897432533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925813975188818393153421 1097180240695806897432533)
            ·
              refine ⟨25715161891307974158575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1097180240695806897432533 25715161891307974158575)
              ·
                rfl

theorem cell21_1014122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 7].length) (baseStart_1014122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014122 prefixEnd_1014122 := by exact prefixLift 1014122
  have htrace : WordTrace (prefixWord ++ tailWord_1014122) baseStart_1014122 baseEnd_1014122 := by
    simpa [prefixWord, tailWord_1014122, baseEnd_1014122] using wordTrace_append hprefix tailTrace_1014122
  have hstable : (prefixWord ++ tailWord_1014122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014122).length < 2 ^ (prefixWord ++ tailWord_1014122).sum := by decide
  have hdescent : baseEnd_1014122 < baseStart_1014122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014184 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_1014184 : Nat := 118140960795 + 1014184 * 2 ^ 59
def prefixEnd_1014184 : Nat := 4983230072969 + 3 ^ 40 * 1014184 * 2
def baseEnd_1014184 : Nat := 231450606266473437393715

theorem tailTrace_1014184 : CollatzResearch.WordTrace tailWord_1014184 prefixEnd_1014184 231450606266473437393715 := by
  unfold tailWord_1014184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495164678896025841224803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24660219571861367788299737 18495164678896025841224803)
  ·
    refine ⟨27742747018344038761837205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18495164678896025841224803 27742747018344038761837205)
    ·
      refine ⟨1300441266484876816961119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27742747018344038761837205 1300441266484876816961119)
      ·
        refine ⟨1950661899727315225441679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300441266484876816961119 1950661899727315225441679)
        ·
          refine ⟨2925992849590972838162519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950661899727315225441679 2925992849590972838162519)
          ·
            refine ⟨4388989274386459257243779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925992849590972838162519 4388989274386459257243779)
            ·
              refine ⟨6583483911579688885865669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388989274386459257243779 6583483911579688885865669)
              ·
                refine ⟨1234403233421191666099813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6583483911579688885865669 1234403233421191666099813)
                ·
                  refine ⟨231450606266473437393715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234403233421191666099813 231450606266473437393715)
                  ·
                    rfl

theorem cell21_1014184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_1014184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014184 prefixEnd_1014184 := by exact prefixLift 1014184
  have htrace : WordTrace (prefixWord ++ tailWord_1014184) baseStart_1014184 baseEnd_1014184 := by
    simpa [prefixWord, tailWord_1014184, baseEnd_1014184] using wordTrace_append hprefix tailTrace_1014184
  have hstable : (prefixWord ++ tailWord_1014184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014184).length < 2 ^ (prefixWord ++ tailWord_1014184).sum := by decide
  have hdescent : baseEnd_1014184 < baseStart_1014184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014229 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1014229 : Nat := 118140960795 + 1014229 * 2 ^ 59
def prefixEnd_1014229 : Nat := 4983230072969 + 3 ^ 40 * 1014229 * 2
def baseEnd_1014229 : Nat := 231460875879563359143623

theorem tailTrace_1014229 : CollatzResearch.WordTrace tailWord_1014229 prefixEnd_1014229 231460875879563359143623 := by
  unfold tailWord_1014229
  simp only [CollatzResearch.WordTrace]
  refine ⟨36991970642629024367837741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24661313761752682911891827 36991970642629024367837741)
  ·
    refine ⟨13871988990985884137939153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36991970642629024367837741 13871988990985884137939153)
    ·
      refine ⟨10403991743239413103454365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13871988990985884137939153 10403991743239413103454365)
      ·
        refine ⟨3901496903714779913795387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10403991743239413103454365 3901496903714779913795387)
        ·
          refine ⟨5852245355572169870693081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901496903714779913795387 5852245355572169870693081)
          ·
            refine ⟨4389184016679127403019811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852245355572169870693081 4389184016679127403019811)
            ·
              refine ⟨6583776025018691104529717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389184016679127403019811 6583776025018691104529717)
              ·
                refine ⟨617229002345502291049661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6583776025018691104529717 617229002345502291049661)
                ·
                  refine ⟨231460875879563359143623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617229002345502291049661 231460875879563359143623)
                  ·
                    rfl

theorem cell21_1014229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1014229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014229 prefixEnd_1014229 := by exact prefixLift 1014229
  have htrace : WordTrace (prefixWord ++ tailWord_1014229) baseStart_1014229 baseEnd_1014229 := by
    simpa [prefixWord, tailWord_1014229, baseEnd_1014229] using wordTrace_append hprefix tailTrace_1014229
  have hstable : (prefixWord ++ tailWord_1014229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014229).length < 2 ^ (prefixWord ++ tailWord_1014229).sum := by decide
  have hdescent : baseEnd_1014229 < baseStart_1014229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014240 : List Nat := [2, 1, 1, 3, 1, 1, 12]
def baseStart_1014240 : Nat := 118140960795 + 1014240 * 2 ^ 59
def prefixEnd_1014240 : Nat := 4983230072969 + 3 ^ 40 * 1014240 * 2
def baseEnd_1014240 : Nat := 25718154025492198273363

theorem tailTrace_1014240 : CollatzResearch.WordTrace tailWord_1014240 prefixEnd_1014240 25718154025492198273363 := by
  unfold tailWord_1014240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496185922794586623244087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24661581230392782164325449 18496185922794586623244087)
  ·
    refine ⟨27744278884191879934866131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18496185922794586623244087 27744278884191879934866131)
    ·
      refine ⟨41616418326287819902299197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27744278884191879934866131 41616418326287819902299197)
      ·
        refine ⟨15606156872357932463362199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41616418326287819902299197 15606156872357932463362199)
        ·
          refine ⟨23409235308536898695043299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15606156872357932463362199 23409235308536898695043299)
          ·
            refine ⟨35113852962805348042564949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409235308536898695043299 35113852962805348042564949)
            ·
              refine ⟨25718154025492198273363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35113852962805348042564949 25718154025492198273363)
              ·
                rfl

theorem cell21_1014240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 12].length) (baseStart_1014240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014240 prefixEnd_1014240 := by exact prefixLift 1014240
  have htrace : WordTrace (prefixWord ++ tailWord_1014240) baseStart_1014240 baseEnd_1014240 := by
    simpa [prefixWord, tailWord_1014240, baseEnd_1014240] using wordTrace_append hprefix tailTrace_1014240
  have hstable : (prefixWord ++ tailWord_1014240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014240).length < 2 ^ (prefixWord ++ tailWord_1014240).sum := by decide
  have hdescent : baseEnd_1014240 < baseStart_1014240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014243 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_1014243 : Nat := 118140960795 + 1014243 * 2 ^ 59
def prefixEnd_1014243 : Nat := 4983230072969 + 3 ^ 40 * 1014243 * 2
def baseEnd_1014243 : Nat := 231464070870302445910261

theorem tailTrace_1014243 : CollatzResearch.WordTrace tailWord_1014243 prefixEnd_1014243 231464070870302445910261 := by
  unfold tailWord_1014243
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992481264578304758847383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24661654176385536505898255 36992481264578304758847383)
  ·
    refine ⟨55488721896867457138271075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36992481264578304758847383 55488721896867457138271075)
    ·
      refine ⟨83233082845301185707406613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55488721896867457138271075 83233082845301185707406613)
      ·
        refine ⟨3901550758373493080034685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83233082845301185707406613 3901550758373493080034685)
        ·
          refine ⟨1463081534390059905013007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3901550758373493080034685 1463081534390059905013007)
          ·
            refine ⟨2194622301585089857519511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463081534390059905013007 2194622301585089857519511)
            ·
              refine ⟨3291933452377634786279267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194622301585089857519511 3291933452377634786279267)
              ·
                refine ⟨4937900178566452179418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291933452377634786279267 4937900178566452179418901)
                ·
                  refine ⟨231464070870302445910261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4937900178566452179418901 231464070870302445910261)
                  ·
                    rfl

theorem cell21_1014243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_1014243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014243 prefixEnd_1014243 := by exact prefixLift 1014243
  have htrace : WordTrace (prefixWord ++ tailWord_1014243) baseStart_1014243 baseEnd_1014243 := by
    simpa [prefixWord, tailWord_1014243, baseEnd_1014243] using wordTrace_append hprefix tailTrace_1014243
  have hstable : (prefixWord ++ tailWord_1014243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014243).length < 2 ^ (prefixWord ++ tailWord_1014243).sum := by decide
  have hdescent : baseEnd_1014243 < baseStart_1014243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014271 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_1014271 : Nat := 118140960795 + 1014271 * 2 ^ 59
def prefixEnd_1014271 : Nat := 4983230072969 + 3 ^ 40 * 1014271 * 2
def baseEnd_1014271 : Nat := 231470460851780619443537

theorem tailTrace_1014271 : CollatzResearch.WordTrace tailWord_1014271 prefixEnd_1014271 231470460851780619443537 := by
  unfold tailWord_1014271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993502508476865540866667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24662335005651243693911111 36993502508476865540866667)
  ·
    refine ⟨55490253762715298311300001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993502508476865540866667 55490253762715298311300001)
    ·
      refine ⟨41617690322036473733475001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55490253762715298311300001 41617690322036473733475001)
      ·
        refine ⟨31213267741527355300106251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41617690322036473733475001 31213267741527355300106251)
        ·
          refine ⟨46819901612291032950159377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31213267741527355300106251 46819901612291032950159377)
          ·
            refine ⟨35114926209218274712619533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46819901612291032950159377 35114926209218274712619533)
            ·
              refine ⟨13168097328456853017232325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35114926209218274712619533 13168097328456853017232325)
              ·
                refine ⟨2469018249085659940731061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13168097328456853017232325 2469018249085659940731061)
                ·
                  refine ⟨231470460851780619443537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469018249085659940731061 231470460851780619443537)
                  ·
                    rfl

theorem cell21_1014271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_1014271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014271 prefixEnd_1014271 := by exact prefixLift 1014271
  have htrace : WordTrace (prefixWord ++ tailWord_1014271) baseStart_1014271 baseEnd_1014271 := by
    simpa [prefixWord, tailWord_1014271, baseEnd_1014271] using wordTrace_append hprefix tailTrace_1014271
  have hstable : (prefixWord ++ tailWord_1014271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014271).length < 2 ^ (prefixWord ++ tailWord_1014271).sum := by decide
  have hdescent : baseEnd_1014271 < baseStart_1014271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014311 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 4]
def baseStart_1014311 : Nat := 118140960795 + 1014311 * 2 ^ 59
def prefixEnd_1014311 : Nat := 4983230072969 + 3 ^ 40 * 1014311 * 2
def baseEnd_1014311 : Nat := 231479589396749438776789

theorem tailTrace_1014311 : CollatzResearch.WordTrace tailWord_1014311 prefixEnd_1014311 231479589396749438776789 := by
  unfold tailWord_1014311
  simp only [CollatzResearch.WordTrace]
  refine ⟨36994961428331952372322787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24663307618887968248215191 36994961428331952372322787)
  ·
    refine ⟨55492442142497928558484181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36994961428331952372322787 55492442142497928558484181)
    ·
      refine ⟨1300604112714795200589473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55492442142497928558484181 1300604112714795200589473)
      ·
        refine ⟨975453084536096400442105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300604112714795200589473 975453084536096400442105)
        ·
          refine ⟨731589813402072300331579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975453084536096400442105 731589813402072300331579)
          ·
            refine ⟨1097384720103108450497369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731589813402072300331579 1097384720103108450497369)
            ·
              refine ⟨823038540077331337873027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097384720103108450497369 823038540077331337873027)
              ·
                refine ⟨1234557810115997006809541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823038540077331337873027 1234557810115997006809541)
                ·
                  refine ⟨231479589396749438776789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234557810115997006809541 231479589396749438776789)
                  ·
                    rfl

theorem cell21_1014311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].length) (baseStart_1014311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014311 prefixEnd_1014311 := by exact prefixLift 1014311
  have htrace : WordTrace (prefixWord ++ tailWord_1014311) baseStart_1014311 baseEnd_1014311 := by
    simpa [prefixWord, tailWord_1014311, baseEnd_1014311] using wordTrace_append hprefix tailTrace_1014311
  have hstable : (prefixWord ++ tailWord_1014311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014311).length < 2 ^ (prefixWord ++ tailWord_1014311).sum := by decide
  have hdescent : baseEnd_1014311 < baseStart_1014311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014333 : List Nat := [1, 4, 1, 3, 2, 1, 2, 7]
def baseStart_1014333 : Nat := 118140960795 + 1014333 * 2 ^ 59
def prefixEnd_1014333 : Nat := 4983230072969 + 3 ^ 40 * 1014333 * 2
def baseEnd_1014333 : Nat := 77161536698827429803359

theorem tailTrace_1014333 : CollatzResearch.WordTrace tailWord_1014333 prefixEnd_1014333 77161536698827429803359 := by
  unfold tailWord_1014333
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995763834252250129623653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24663842556168166753082435 36995763834252250129623653)
  ·
    refine ⟨6936705718922296899304435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36995763834252250129623653 6936705718922296899304435)
    ·
      refine ⟨10405058578383445348956653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936705718922296899304435 10405058578383445348956653)
      ·
        refine ⟨3901896966893792005858745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10405058578383445348956653 3901896966893792005858745)
        ·
          refine ⟨2926422725170344004394059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3901896966893792005858745 2926422725170344004394059)
          ·
            refine ⟨4389634087755516006591089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926422725170344004394059 4389634087755516006591089)
            ·
              refine ⟨3292225565816637004943317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389634087755516006591089 3292225565816637004943317)
              ·
                refine ⟨77161536698827429803359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3292225565816637004943317 77161536698827429803359)
                ·
                  rfl

theorem cell21_1014333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_1014333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014333 prefixEnd_1014333 := by exact prefixLift 1014333
  have htrace : WordTrace (prefixWord ++ tailWord_1014333) baseStart_1014333 baseEnd_1014333 := by
    simpa [prefixWord, tailWord_1014333, baseEnd_1014333] using wordTrace_append hprefix tailTrace_1014333
  have hstable : (prefixWord ++ tailWord_1014333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014333).length < 2 ^ (prefixWord ++ tailWord_1014333).sum := by decide
  have hdescent : baseEnd_1014333 < baseStart_1014333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014474 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_1014474 : Nat := 118140960795 + 1014474 * 2 ^ 59
def prefixEnd_1014474 : Nat := 4983230072969 + 3 ^ 40 * 1014474 * 2
def baseEnd_1014474 : Nat := 231516788217497377559789

theorem tailTrace_1014474 : CollatzResearch.WordTrace tailWord_1014474 prefixEnd_1014474 231516788217497377559789 := by
  unfold tailWord_1014474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250226631685357802626619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24667271017827620807004317 9250226631685357802626619)
  ·
    refine ⟨13875339947528036703939929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9250226631685357802626619 13875339947528036703939929)
    ·
      refine ⟨10406504960646027527954947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13875339947528036703939929 10406504960646027527954947)
      ·
        refine ⟨15609757440969041291932421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10406504960646027527954947 15609757440969041291932421)
        ·
          refine ⟨2926829520181695242237329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15609757440969041291932421 2926829520181695242237329)
          ·
            refine ⟨2195122140136271431677997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2926829520181695242237329 2195122140136271431677997)
            ·
              refine ⟨823170802551101786879249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195122140136271431677997 823170802551101786879249)
              ·
                refine ⟨617378101913326340159437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823170802551101786879249 617378101913326340159437)
                ·
                  refine ⟨231516788217497377559789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617378101913326340159437 231516788217497377559789)
                  ·
                    rfl

theorem cell21_1014474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_1014474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014474 prefixEnd_1014474 := by exact prefixLift 1014474
  have htrace : WordTrace (prefixWord ++ tailWord_1014474) baseStart_1014474 baseEnd_1014474 := by
    simpa [prefixWord, tailWord_1014474, baseEnd_1014474] using wordTrace_append hprefix tailTrace_1014474
  have hstable : (prefixWord ++ tailWord_1014474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014474).length < 2 ^ (prefixWord ++ tailWord_1014474).sum := by decide
  have hdescent : baseEnd_1014474 < baseStart_1014474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014488 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_1014488 : Nat := 118140960795 + 1014488 * 2 ^ 59
def prefixEnd_1014488 : Nat := 4983230072969 + 3 ^ 40 * 1014488 * 2
def baseEnd_1014488 : Nat := 231519983208236464326427

theorem tailTrace_1014488 : CollatzResearch.WordTrace tailWord_1014488 prefixEnd_1014488 231519983208236464326427 := by
  unfold tailWord_1014488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500708574345355800758059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24667611432460474401010745 18500708574345355800758059)
  ·
    refine ⟨27751062861518033701137089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500708574345355800758059 27751062861518033701137089)
    ·
      refine ⟨20813297146138525275852817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27751062861518033701137089 20813297146138525275852817)
      ·
        refine ⟨15609972859603893956889613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20813297146138525275852817 15609972859603893956889613)
        ·
          refine ⟨5853739822351460233833605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15609972859603893956889613 5853739822351460233833605)
          ·
            refine ⟨1097576216690898793843801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5853739822351460233833605 1097576216690898793843801)
            ·
              refine ⟨823182162518174095382851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097576216690898793843801 823182162518174095382851)
              ·
                refine ⟨1234773243777261143074277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823182162518174095382851 1234773243777261143074277)
                ·
                  refine ⟨231519983208236464326427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234773243777261143074277 231519983208236464326427)
                  ·
                    rfl

theorem cell21_1014488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_1014488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014488 prefixEnd_1014488 := by exact prefixLift 1014488
  have htrace : WordTrace (prefixWord ++ tailWord_1014488) baseStart_1014488 baseEnd_1014488 := by
    simpa [prefixWord, tailWord_1014488, baseEnd_1014488] using wordTrace_append hprefix tailTrace_1014488
  have hstable : (prefixWord ++ tailWord_1014488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014488).length < 2 ^ (prefixWord ++ tailWord_1014488).sum := by decide
  have hdescent : baseEnd_1014488 < baseStart_1014488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014561 : List Nat := [1, 2, 3, 2, 1, 2, 5, 5]
def baseStart_1014561 : Nat := 118140960795 + 1014561 * 2 ^ 59
def prefixEnd_1014561 : Nat := 4983230072969 + 3 ^ 40 * 1014561 * 2
def baseEnd_1014561 : Nat := 77178880934268186536537

theorem tailTrace_1014561 : CollatzResearch.WordTrace tailWord_1014561 prefixEnd_1014561 77178880934268186536537 := by
  unfold tailWord_1014561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37004079677426245068923537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24669386451617496712615691 37004079677426245068923537)
  ·
    refine ⟨27753059758069683801692653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37004079677426245068923537 27753059758069683801692653)
    ·
      refine ⟨10407397409276131425634745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27753059758069683801692653 10407397409276131425634745)
      ·
        refine ⟨7805548056957098569226059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10407397409276131425634745 7805548056957098569226059)
        ·
          refine ⟨11708322085435647853839089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805548056957098569226059 11708322085435647853839089)
          ·
            refine ⟨8781241564076735890379317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11708322085435647853839089 8781241564076735890379317)
            ·
              refine ⟨823241396632193989723061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8781241564076735890379317 823241396632193989723061)
              ·
                refine ⟨77178880934268186536537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823241396632193989723061 77178880934268186536537)
                ·
                  rfl

theorem cell21_1014561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].length) (baseStart_1014561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014561 prefixEnd_1014561 := by exact prefixLift 1014561
  have htrace : WordTrace (prefixWord ++ tailWord_1014561) baseStart_1014561 baseEnd_1014561 := by
    simpa [prefixWord, tailWord_1014561, baseEnd_1014561] using wordTrace_append hprefix tailTrace_1014561
  have hstable : (prefixWord ++ tailWord_1014561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014561).length < 2 ^ (prefixWord ++ tailWord_1014561).sum := by decide
  have hdescent : baseEnd_1014561 < baseStart_1014561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014598 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1014598 : Nat := 118140960795 + 1014598 * 2 ^ 59
def prefixEnd_1014598 : Nat := 4983230072969 + 3 ^ 40 * 1014598 * 2
def baseEnd_1014598 : Nat := 231545086706900717492869

theorem tailTrace_1014598 : CollatzResearch.WordTrace tailWord_1014598 prefixEnd_1014598 231545086706900717492869 := by
  unfold tailWord_1014598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156419661821631262125639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24670286118861466925346965 1156419661821631262125639)
  ·
    refine ⟨1734629492732446893188459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156419661821631262125639 1734629492732446893188459)
    ·
      refine ⟨2601944239098670339782689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734629492732446893188459 2601944239098670339782689)
      ·
        refine ⟨1951458179324002754837017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2601944239098670339782689 1951458179324002754837017)
        ·
          refine ⟨1463593634493002066127763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1951458179324002754837017 1463593634493002066127763)
          ·
            refine ⟨2195390451739503099191645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463593634493002066127763 2195390451739503099191645)
            ·
              refine ⟨823271419402313662196867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195390451739503099191645 823271419402313662196867)
              ·
                refine ⟨1234907129103470493295301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823271419402313662196867 1234907129103470493295301)
                ·
                  refine ⟨231545086706900717492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234907129103470493295301 231545086706900717492869)
                  ·
                    rfl

theorem cell21_1014598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1014598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014598 prefixEnd_1014598 := by exact prefixLift 1014598
  have htrace : WordTrace (prefixWord ++ tailWord_1014598) baseStart_1014598 baseEnd_1014598 := by
    simpa [prefixWord, tailWord_1014598, baseEnd_1014598] using wordTrace_append hprefix tailTrace_1014598
  have hstable : (prefixWord ++ tailWord_1014598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014598).length < 2 ^ (prefixWord ++ tailWord_1014598).sum := by decide
  have hdescent : baseEnd_1014598 < baseStart_1014598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014606 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1014606 : Nat := 118140960795 + 1014606 * 2 ^ 59
def prefixEnd_1014606 : Nat := 4983230072969 + 3 ^ 40 * 1014606 * 2
def baseEnd_1014606 : Nat := 231546912415894481359519

theorem tailTrace_1014606 : CollatzResearch.WordTrace tailWord_1014606 prefixEnd_1014606 231546912415894481359519 := by
  unfold tailWord_1014606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625715120282902219288959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24670480641508811836207781 4625715120282902219288959)
  ·
    refine ⟨6938572680424353328933439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625715120282902219288959 6938572680424353328933439)
    ·
      refine ⟨10407859020636529993400159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938572680424353328933439 10407859020636529993400159)
      ·
        refine ⟨15611788530954794990100239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407859020636529993400159 15611788530954794990100239)
        ·
          refine ⟨23417682796432192485150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15611788530954794990100239 23417682796432192485150359)
          ·
            refine ⟨35126524194648288727725539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23417682796432192485150359 35126524194648288727725539)
            ·
              refine ⟨52689786291972433091588309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35126524194648288727725539 52689786291972433091588309)
              ·
                refine ⟨1234916866218103900584101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52689786291972433091588309 1234916866218103900584101)
                ·
                  refine ⟨231546912415894481359519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234916866218103900584101 231546912415894481359519)
                  ·
                    rfl

theorem cell21_1014606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1014606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014606 prefixEnd_1014606 := by exact prefixLift 1014606
  have htrace : WordTrace (prefixWord ++ tailWord_1014606) baseStart_1014606 baseEnd_1014606 := by
    simpa [prefixWord, tailWord_1014606, baseEnd_1014606] using wordTrace_append hprefix tailTrace_1014606
  have hstable : (prefixWord ++ tailWord_1014606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014606).length < 2 ^ (prefixWord ++ tailWord_1014606).sum := by decide
  have hdescent : baseEnd_1014606 < baseStart_1014606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014651 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_1014651 : Nat := 118140960795 + 1014651 * 2 ^ 59
def prefixEnd_1014651 : Nat := 4983230072969 + 3 ^ 40 * 1014651 * 2
def baseEnd_1014651 : Nat := 231557182028984403109427

theorem tailTrace_1014651 : CollatzResearch.WordTrace tailWord_1014651 prefixEnd_1014651 231557182028984403109427 := by
  unfold tailWord_1014651
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007362247100190439699807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671574831400126959799871 37007362247100190439699807)
  ·
    refine ⟨55511043370650285659549711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37007362247100190439699807 55511043370650285659549711)
    ·
      refine ⟨83266565055975428489324567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55511043370650285659549711 83266565055975428489324567)
      ·
        refine ⟨124899847583963142733986851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83266565055975428489324567 124899847583963142733986851)
        ·
          refine ⟨187349771375944714100980277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124899847583963142733986851 187349771375944714100980277)
          ·
            refine ⟨17564041066494816946966901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187349771375944714100980277 17564041066494816946966901)
            ·
              refine ⟨1646628849983889088778147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17564041066494816946966901 1646628849983889088778147)
              ·
                refine ⟨2469943274975833633167221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646628849983889088778147 2469943274975833633167221)
                ·
                  refine ⟨231557182028984403109427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469943274975833633167221 231557182028984403109427)
                  ·
                    rfl

theorem cell21_1014651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_1014651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014651 prefixEnd_1014651 := by exact prefixLift 1014651
  have htrace : WordTrace (prefixWord ++ tailWord_1014651) baseStart_1014651 baseEnd_1014651 := by
    simpa [prefixWord, tailWord_1014651, baseEnd_1014651] using wordTrace_append hprefix tailTrace_1014651
  have hstable : (prefixWord ++ tailWord_1014651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014651).length < 2 ^ (prefixWord ++ tailWord_1014651).sum := by decide
  have hdescent : baseEnd_1014651 < baseStart_1014651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014696 : List Nat := [2, 1, 6, 12]
def baseStart_1014696 : Nat := 118140960795 + 1014696 * 2 ^ 59
def prefixEnd_1014696 : Nat := 4983230072969 + 3 ^ 40 * 1014696 * 2
def baseEnd_1014696 : Nat := 952952475893309978845

theorem tailTrace_1014696 : CollatzResearch.WordTrace tailWord_1014696 prefixEnd_1014696 952952475893309978845 := by
  unfold tailWord_1014696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504501765968581562543971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24672669021291442083391961 18504501765968581562543971)
  ·
    refine ⟨27756752648952872343815957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18504501765968581562543971 27756752648952872343815957)
    ·
      refine ⟨1301097780419665891116373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27756752648952872343815957 1301097780419665891116373)
      ·
        refine ⟨952952475893309978845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1301097780419665891116373 952952475893309978845)
        ·
          rfl

theorem cell21_1014696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 12].length) (baseStart_1014696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014696 prefixEnd_1014696 := by exact prefixLift 1014696
  have htrace : WordTrace (prefixWord ++ tailWord_1014696) baseStart_1014696 baseEnd_1014696 := by
    simpa [prefixWord, tailWord_1014696, baseEnd_1014696] using wordTrace_append hprefix tailTrace_1014696
  have hstable : (prefixWord ++ tailWord_1014696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014696).length < 2 ^ (prefixWord ++ tailWord_1014696).sum := by decide
  have hdescent : baseEnd_1014696 < baseStart_1014696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014713 : List Nat := [1, 2, 1, 4, 2, 4, 1, 6]
def baseStart_1014713 : Nat := 118140960795 + 1014713 * 2 ^ 59
def prefixEnd_1014713 : Nat := 4983230072969 + 3 ^ 40 * 1014713 * 2
def baseEnd_1014713 : Nat := 77190443757895357691989

theorem tailTrace_1014713 : CollatzResearch.WordTrace tailWord_1014713 prefixEnd_1014713 77190443757895357691989 := by
  unfold tailWord_1014713
  simp only [CollatzResearch.WordTrace]
  refine ⟨37009623572875575028456793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24673082381917050018971195 37009623572875575028456793)
  ·
    refine ⟨27757217679656681271342595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37009623572875575028456793 27757217679656681271342595)
    ·
      refine ⟨41635826519485021907013893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27757217679656681271342595 41635826519485021907013893)
      ·
        refine ⟨7806717472403441607565105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41635826519485021907013893 7806717472403441607565105)
        ·
          refine ⟨5855038104302581205673829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7806717472403441607565105 5855038104302581205673829)
          ·
            refine ⟨1097819644556733976063843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5855038104302581205673829 1097819644556733976063843)
            ·
              refine ⟨1646729466835100964095765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097819644556733976063843 1646729466835100964095765)
              ·
                refine ⟨77190443757895357691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1646729466835100964095765 77190443757895357691989)
                ·
                  rfl

theorem cell21_1014713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_1014713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014713 prefixEnd_1014713 := by exact prefixLift 1014713
  have htrace : WordTrace (prefixWord ++ tailWord_1014713) baseStart_1014713 baseEnd_1014713 := by
    simpa [prefixWord, tailWord_1014713, baseEnd_1014713] using wordTrace_append hprefix tailTrace_1014713
  have hstable : (prefixWord ++ tailWord_1014713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014713).length < 2 ^ (prefixWord ++ tailWord_1014713).sum := by decide
  have hdescent : baseEnd_1014713 < baseStart_1014713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014744 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_1014744 : Nat := 118140960795 + 1014744 * 2 ^ 59
def prefixEnd_1014744 : Nat := 4983230072969 + 3 ^ 40 * 1014744 * 2
def baseEnd_1014744 : Nat := 231578405896036908059237

theorem tailTrace_1014744 : CollatzResearch.WordTrace tailWord_1014744 prefixEnd_1014744 231578405896036908059237 := by
  unfold tailWord_1014744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18505377117881633661417643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24673836157175511548556857 18505377117881633661417643)
  ·
    refine ⟨27758065676822450492126465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18505377117881633661417643 27758065676822450492126465)
    ·
      refine ⟨20818549257616837869094849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27758065676822450492126465 20818549257616837869094849)
      ·
        refine ⟨15613911943212628401821137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20818549257616837869094849 15613911943212628401821137)
        ·
          refine ⟨11710433957409471301365853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15613911943212628401821137 11710433957409471301365853)
          ·
            refine ⟨4391412734028551738012195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11710433957409471301365853 4391412734028551738012195)
            ·
              refine ⟨6587119101042827607018293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391412734028551738012195 6587119101042827607018293)
              ·
                refine ⟨617542415722765088157965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6587119101042827607018293 617542415722765088157965)
                ·
                  refine ⟨231578405896036908059237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617542415722765088157965 231578405896036908059237)
                  ·
                    rfl

theorem cell21_1014744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_1014744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014744 prefixEnd_1014744 := by exact prefixLift 1014744
  have htrace : WordTrace (prefixWord ++ tailWord_1014744) baseStart_1014744 baseEnd_1014744 := by
    simpa [prefixWord, tailWord_1014744, baseEnd_1014744] using wordTrace_append hprefix tailTrace_1014744
  have hstable : (prefixWord ++ tailWord_1014744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014744).length < 2 ^ (prefixWord ++ tailWord_1014744).sum := by decide
  have hdescent : baseEnd_1014744 < baseStart_1014744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014820 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1014820 : Nat := 118140960795 + 1014820 * 2 ^ 59
def prefixEnd_1014820 : Nat := 4983230072969 + 3 ^ 40 * 1014820 * 2
def baseEnd_1014820 : Nat := 231595750131477664792415

theorem tailTrace_1014820 : CollatzResearch.WordTrace tailWord_1014820 prefixEnd_1014820 231595750131477664792415 := by
  unfold tailWord_1014820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506763091743966151300957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24675684122325288201734609 18506763091743966151300957)
  ·
    refine ⟨6940036159403987306737859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18506763091743966151300957 6940036159403987306737859)
    ·
      refine ⟨10410054239105980960106789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940036159403987306737859 10410054239105980960106789)
      ·
        refine ⟨1951885169832371430020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10410054239105980960106789 1951885169832371430020023)
        ·
          refine ⟨2927827754748557145030035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951885169832371430020023 2927827754748557145030035)
          ·
            refine ⟨4391741632122835717545053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927827754748557145030035 4391741632122835717545053)
            ·
              refine ⟨1646903112046063394079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4391741632122835717545053 1646903112046063394079395)
              ·
                refine ⟨2470354668069095091119093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646903112046063394079395 2470354668069095091119093)
                ·
                  refine ⟨231595750131477664792415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2470354668069095091119093 231595750131477664792415)
                  ·
                    rfl

theorem cell21_1014820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1014820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014820 prefixEnd_1014820 := by exact prefixLift 1014820
  have htrace : WordTrace (prefixWord ++ tailWord_1014820) baseStart_1014820 baseEnd_1014820 := by
    simpa [prefixWord, tailWord_1014820, baseEnd_1014820] using wordTrace_append hprefix tailTrace_1014820
  have hstable : (prefixWord ++ tailWord_1014820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014820).length < 2 ^ (prefixWord ++ tailWord_1014820).sum := by decide
  have hdescent : baseEnd_1014820 < baseStart_1014820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014834 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1014834 : Nat := 118140960795 + 1014834 * 2 ^ 59
def prefixEnd_1014834 : Nat := 4983230072969 + 3 ^ 40 * 1014834 * 2
def baseEnd_1014834 : Nat := 231598945122216751559053

theorem tailTrace_1014834 : CollatzResearch.WordTrace tailWord_1014834 prefixEnd_1014834 231598945122216751559053 := by
  unfold tailWord_1014834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253509201359303173402889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24676024536958141795741037 9253509201359303173402889)
  ·
    refine ⟨6940131901019477380052167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9253509201359303173402889 6940131901019477380052167)
    ·
      refine ⟨10410197851529216070078251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940131901019477380052167 10410197851529216070078251)
      ·
        refine ⟨15615296777293824105117377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410197851529216070078251 15615296777293824105117377)
        ·
          refine ⟨11711472582970368078838033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15615296777293824105117377 11711472582970368078838033)
          ·
            refine ⟨8783604437227776059128525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711472582970368078838033 8783604437227776059128525)
            ·
              refine ⟨3293851663960416022173197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8783604437227776059128525 3293851663960416022173197)
              ·
                refine ⟨1235194373985156008314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3293851663960416022173197 1235194373985156008314949)
                ·
                  refine ⟨231598945122216751559053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235194373985156008314949 231598945122216751559053)
                  ·
                    rfl

theorem cell21_1014834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1014834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014834 prefixEnd_1014834 := by exact prefixLift 1014834
  have htrace : WordTrace (prefixWord ++ tailWord_1014834) baseStart_1014834 baseEnd_1014834 := by
    simpa [prefixWord, tailWord_1014834, baseEnd_1014834] using wordTrace_append hprefix tailTrace_1014834
  have hstable : (prefixWord ++ tailWord_1014834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014834).length < 2 ^ (prefixWord ++ tailWord_1014834).sum := by decide
  have hdescent : baseEnd_1014834 < baseStart_1014834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014882 : List Nat := [3, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1014882 : Nat := 118140960795 + 1014882 * 2 ^ 59
def prefixEnd_1014882 : Nat := 4983230072969 + 3 ^ 40 * 1014882 * 2
def baseEnd_1014882 : Nat := 77203299792059778252985

theorem tailTrace_1014882 : CollatzResearch.WordTrace tailWord_1014882 prefixEnd_1014882 77203299792059778252985 := by
  unfold tailWord_1014882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253946877315829222839725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24677191672842211260905933 9253946877315829222839725)
  ·
    refine ⟨3470230078993435958564897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9253946877315829222839725 3470230078993435958564897)
    ·
      refine ⟨2602672559245076968923673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470230078993435958564897 2602672559245076968923673)
      ·
        refine ⟨1952004419433807726692755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2602672559245076968923673 1952004419433807726692755)
        ·
          refine ⟨2928006629150711590039133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952004419433807726692755 2928006629150711590039133)
          ·
            refine ⟨1098002485931516846264675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2928006629150711590039133 1098002485931516846264675)
            ·
              refine ⟨1647003728897275269397013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098002485931516846264675 1647003728897275269397013)
              ·
                refine ⟨77203299792059778252985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1647003728897275269397013 77203299792059778252985)
                ·
                  rfl

theorem cell21_1014882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1014882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014882 prefixEnd_1014882 := by exact prefixLift 1014882
  have htrace : WordTrace (prefixWord ++ tailWord_1014882) baseStart_1014882 baseEnd_1014882 := by
    simpa [prefixWord, tailWord_1014882, baseEnd_1014882] using wordTrace_append hprefix tailTrace_1014882
  have hstable : (prefixWord ++ tailWord_1014882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014882).length < 2 ^ (prefixWord ++ tailWord_1014882).sum := by decide
  have hdescent : baseEnd_1014882 < baseStart_1014882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014907 : List Nat := [1, 1, 1, 1, 1, 4, 1, 11]
def baseStart_1014907 : Nat := 118140960795 + 1014907 * 2 ^ 59
def prefixEnd_1014907 : Nat := 4983230072969 + 3 ^ 40 * 1014907 * 2
def baseEnd_1014907 : Nat := 77205201572261615614079

theorem tailTrace_1014907 : CollatzResearch.WordTrace tailWord_1014907 prefixEnd_1014907 77205201572261615614079 := by
  unfold tailWord_1014907
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016699334172746161018975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677799556115164107345983 37016699334172746161018975)
  ·
    refine ⟨55525049001259119241528463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37016699334172746161018975 55525049001259119241528463)
    ·
      refine ⟨83287573501888678862292695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55525049001259119241528463 83287573501888678862292695)
      ·
        refine ⟨124931360252833018293439043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83287573501888678862292695 124931360252833018293439043)
        ·
          refine ⟨187397040379249527440158565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124931360252833018293439043 187397040379249527440158565)
          ·
            refine ⟨35136945071109286395029731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187397040379249527440158565 35136945071109286395029731)
            ·
              refine ⟨52705417606663929592544597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35136945071109286395029731 52705417606663929592544597)
              ·
                refine ⟨77205201572261615614079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52705417606663929592544597 77205201572261615614079)
                ·
                  rfl

theorem cell21_1014907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_1014907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014907 prefixEnd_1014907 := by exact prefixLift 1014907
  have htrace : WordTrace (prefixWord ++ tailWord_1014907) baseStart_1014907 baseEnd_1014907 := by
    simpa [prefixWord, tailWord_1014907, baseEnd_1014907] using wordTrace_append hprefix tailTrace_1014907
  have hstable : (prefixWord ++ tailWord_1014907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014907).length < 2 ^ (prefixWord ++ tailWord_1014907).sum := by decide
  have hdescent : baseEnd_1014907 < baseStart_1014907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014913 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 3]
def baseStart_1014913 : Nat := 118140960795 + 1014913 * 2 ^ 59
def prefixEnd_1014913 : Nat := 4983230072969 + 3 ^ 40 * 1014913 * 2
def baseEnd_1014913 : Nat := 231616973998530169742225

theorem tailTrace_1014913 : CollatzResearch.WordTrace tailWord_1014913 prefixEnd_1014913 231616973998530169742225 := by
  unfold tailWord_1014913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016918172151009185737393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677945448100672790491595 37016918172151009185737393)
  ·
    refine ⟨27762688629113256889303045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37016918172151009185737393 27762688629113256889303045)
    ·
      refine ⟨5205504117958735666744321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27762688629113256889303045 5205504117958735666744321)
      ·
        refine ⟨3904128088469051750058241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5205504117958735666744321 3904128088469051750058241)
        ·
          refine ⟨2928096066351788812543681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3904128088469051750058241 2928096066351788812543681)
          ·
            refine ⟨2196072049763841609407761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928096066351788812543681 2196072049763841609407761)
            ·
              refine ⟨1647054037322881207055821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196072049763841609407761 1647054037322881207055821)
              ·
                refine ⟨617645263996080452645933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647054037322881207055821 617645263996080452645933)
                ·
                  refine ⟨231616973998530169742225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617645263996080452645933 231616973998530169742225)
                  ·
                    rfl

theorem cell21_1014913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_1014913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014913 prefixEnd_1014913 := by exact prefixLift 1014913
  have htrace : WordTrace (prefixWord ++ tailWord_1014913) baseStart_1014913 baseEnd_1014913 := by
    simpa [prefixWord, tailWord_1014913, baseEnd_1014913] using wordTrace_append hprefix tailTrace_1014913
  have hstable : (prefixWord ++ tailWord_1014913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014913).length < 2 ^ (prefixWord ++ tailWord_1014913).sum := by decide
  have hdescent : baseEnd_1014913 < baseStart_1014913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014969 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1014969 : Nat := 118140960795 + 1014969 * 2 ^ 59
def prefixEnd_1014969 : Nat := 4983230072969 + 3 ^ 40 * 1014969 * 2
def baseEnd_1014969 : Nat := 231629753961486516808777

theorem tailTrace_1014969 : CollatzResearch.WordTrace tailWord_1014969 prefixEnd_1014969 231629753961486516808777 := by
  unfold tailWord_1014969
  simp only [CollatzResearch.WordTrace]
  refine ⟨37018960659948130749775961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24679307106632087166517307 37018960659948130749775961)
  ·
    refine ⟨27764220494961098062331971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37018960659948130749775961 27764220494961098062331971)
    ·
      refine ⟨41646330742441647093497957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27764220494961098062331971 41646330742441647093497957)
      ·
        refine ⟨7808687014207808830030867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41646330742441647093497957 7808687014207808830030867)
        ·
          refine ⟨11713030521311713245046301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808687014207808830030867 11713030521311713245046301)
          ·
            refine ⟨4392386445491892466892363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11713030521311713245046301 4392386445491892466892363)
            ·
              refine ⟨6588579668237838700338545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392386445491892466892363 6588579668237838700338545)
              ·
                refine ⟨4941434751178379025253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588579668237838700338545 4941434751178379025253909)
                ·
                  refine ⟨231629753961486516808777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4941434751178379025253909 231629753961486516808777)
                  ·
                    rfl

theorem cell21_1014969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1014969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1014969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1014969 prefixEnd_1014969 := by exact prefixLift 1014969
  have htrace : WordTrace (prefixWord ++ tailWord_1014969) baseStart_1014969 baseEnd_1014969 := by
    simpa [prefixWord, tailWord_1014969, baseEnd_1014969] using wordTrace_append hprefix tailTrace_1014969
  have hstable : (prefixWord ++ tailWord_1014969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014969).length < 2 ^ (prefixWord ++ tailWord_1014969).sum := by decide
  have hdescent : baseEnd_1014969 < baseStart_1014969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015169 : List Nat := [1, 2, 4, 3, 2, 1, 2, 6]
def baseStart_1015169 : Nat := 118140960795 + 1015169 * 2 ^ 59
def prefixEnd_1015169 : Nat := 4983230072969 + 3 ^ 40 * 1015169 * 2
def baseEnd_1015169 : Nat := 77225132228776871158345

theorem tailTrace_1015169 : CollatzResearch.WordTrace tailWord_1015169 prefixEnd_1015169 77225132228776871158345 := by
  unfold tailWord_1015169
  simp only [CollatzResearch.WordTrace]
  refine ⟨37026255259223564907056561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24684170172815709938037707 37026255259223564907056561)
  ·
    refine ⟨27769691444417673680292421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37026255259223564907056561 27769691444417673680292421)
    ·
      refine ⟨5206817145828313815054829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27769691444417673680292421 5206817145828313815054829)
      ·
        refine ⟨1952556429685617680645561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5206817145828313815054829 1952556429685617680645561)
        ·
          refine ⟨1464417322264213260484171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952556429685617680645561 1464417322264213260484171)
          ·
            refine ⟨2196625983396319890726257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464417322264213260484171 2196625983396319890726257)
            ·
              refine ⟨1647469487547239918044693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196625983396319890726257 1647469487547239918044693)
              ·
                refine ⟨77225132228776871158345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1647469487547239918044693 77225132228776871158345)
                ·
                  rfl

theorem cell21_1015169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_1015169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015169 prefixEnd_1015169 := by exact prefixLift 1015169
  have htrace : WordTrace (prefixWord ++ tailWord_1015169) baseStart_1015169 baseEnd_1015169 := by
    simpa [prefixWord, tailWord_1015169, baseEnd_1015169] using wordTrace_append hprefix tailTrace_1015169
  have hstable : (prefixWord ++ tailWord_1015169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015169).length < 2 ^ (prefixWord ++ tailWord_1015169).sum := by decide
  have hdescent : baseEnd_1015169 < baseStart_1015169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015242 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1015242 : Nat := 118140960795 + 1015242 * 2 ^ 59
def prefixEnd_1015242 : Nat := 4983230072969 + 3 ^ 40 * 1015242 * 2
def baseEnd_1015242 : Nat := 231692056280898708758219

theorem tailTrace_1015242 : CollatzResearch.WordTrace tailWord_1015242 prefixEnd_1015242 231692056280898708758219 := by
  unfold tailWord_1015242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257229446989774593615995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24685945191972732249642653 9257229446989774593615995)
  ·
    refine ⟨13885844170484661890423993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9257229446989774593615995 13885844170484661890423993)
    ·
      refine ⟨10414383127863496417817995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13885844170484661890423993 10414383127863496417817995)
      ·
        refine ⟨15621574691795244626726993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414383127863496417817995 15621574691795244626726993)
        ·
          refine ⟨11716181018846433470045245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15621574691795244626726993 11716181018846433470045245)
          ·
            refine ⟨4393567882067412551266967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11716181018846433470045245 4393567882067412551266967)
            ·
              refine ⟨6590351823101118826900451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393567882067412551266967 6590351823101118826900451)
              ·
                refine ⟨9885527734651678240350677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590351823101118826900451 9885527734651678240350677)
                ·
                  refine ⟨231692056280898708758219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9885527734651678240350677 231692056280898708758219)
                  ·
                    rfl

theorem cell21_1015242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1015242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015242 prefixEnd_1015242 := by exact prefixLift 1015242
  have htrace : WordTrace (prefixWord ++ tailWord_1015242) baseStart_1015242 baseEnd_1015242 := by
    simpa [prefixWord, tailWord_1015242, baseEnd_1015242] using wordTrace_append hprefix tailTrace_1015242
  have hstable : (prefixWord ++ tailWord_1015242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015242).length < 2 ^ (prefixWord ++ tailWord_1015242).sum := by decide
  have hdescent : baseEnd_1015242 < baseStart_1015242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015290 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_1015290 : Nat := 118140960795 + 1015290 * 2 ^ 59
def prefixEnd_1015290 : Nat := 4983230072969 + 3 ^ 40 * 1015290 * 2
def baseEnd_1015290 : Nat := 231703010534861291958121

theorem tailTrace_1015290 : CollatzResearch.WordTrace tailWord_1015290 prefixEnd_1015290 231703010534861291958121 := by
  unfold tailWord_1015290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257667122946300643052831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24687112327856801714807549 9257667122946300643052831)
  ·
    refine ⟨13886500684419450964579247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9257667122946300643052831 13886500684419450964579247)
    ·
      refine ⟨20829751026629176446868871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886500684419450964579247 20829751026629176446868871)
      ·
        refine ⟨31244626539943764670303307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20829751026629176446868871 31244626539943764670303307)
        ·
          refine ⟨46866939809915647005454961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31244626539943764670303307 46866939809915647005454961)
          ·
            refine ⟨35150204857436735254091221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46866939809915647005454961 35150204857436735254091221)
            ·
              refine ⟨823832926346173482517763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35150204857436735254091221 823832926346173482517763)
              ·
                refine ⟨1235749389519260223776645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823832926346173482517763 1235749389519260223776645)
                ·
                  refine ⟨231703010534861291958121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235749389519260223776645 231703010534861291958121)
                  ·
                    rfl

theorem cell21_1015290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_1015290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015290 prefixEnd_1015290 := by exact prefixLift 1015290
  have htrace : WordTrace (prefixWord ++ tailWord_1015290) baseStart_1015290 baseEnd_1015290 := by
    simpa [prefixWord, tailWord_1015290, baseEnd_1015290] using wordTrace_append hprefix tailTrace_1015290
  have hstable : (prefixWord ++ tailWord_1015290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015290).length < 2 ^ (prefixWord ++ tailWord_1015290).sum := by decide
  have hdescent : baseEnd_1015290 < baseStart_1015290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015304 : List Nat := [2, 1, 3, 2, 1, 1, 6, 5]
def baseStart_1015304 : Nat := 118140960795 + 1015304 * 2 ^ 59
def prefixEnd_1015304 : Nat := 4983230072969 + 3 ^ 40 * 1015304 * 2
def baseEnd_1015304 : Nat := 77235401841866792908253

theorem tailTrace_1015304 : CollatzResearch.WordTrace tailWord_1015304 prefixEnd_1015304 77235401841866792908253 := by
  unfold tailWord_1015304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515589556867241481610483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24687452742489655308813977 18515589556867241481610483)
  ·
    refine ⟨27773384335300862222415725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18515589556867241481610483 27773384335300862222415725)
    ·
      refine ⟨10415019125737823333405897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27773384335300862222415725 10415019125737823333405897)
      ·
        refine ⟨7811264344303367500054423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10415019125737823333405897 7811264344303367500054423)
        ·
          refine ⟨11716896516455051250081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811264344303367500054423 11716896516455051250081635)
          ·
            refine ⟨17575344774682576875122453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11716896516455051250081635 17575344774682576875122453)
            ·
              refine ⟨823844286313245791021365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17575344774682576875122453 823844286313245791021365)
              ·
                refine ⟨77235401841866792908253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823844286313245791021365 77235401841866792908253)
                ·
                  rfl

theorem cell21_1015304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_1015304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015304 prefixEnd_1015304 := by exact prefixLift 1015304
  have htrace : WordTrace (prefixWord ++ tailWord_1015304) baseStart_1015304 baseEnd_1015304 := by
    simpa [prefixWord, tailWord_1015304, baseEnd_1015304] using wordTrace_append hprefix tailTrace_1015304
  have hstable : (prefixWord ++ tailWord_1015304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015304).length < 2 ^ (prefixWord ++ tailWord_1015304).sum := by decide
  have hdescent : baseEnd_1015304 < baseStart_1015304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015310 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_1015310 : Nat := 118140960795 + 1015310 * 2 ^ 59
def prefixEnd_1015310 : Nat := 4983230072969 + 3 ^ 40 * 1015310 * 2
def baseEnd_1015310 : Nat := 231707574807345701624747

theorem tailTrace_1015310 : CollatzResearch.WordTrace tailWord_1015310 prefixEnd_1015310 231707574807345701624747 := by
  unfold tailWord_1015310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628924743964093248492423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24687598634475163991959589 4628924743964093248492423)
  ·
    refine ⟨6943387115946139872738635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628924743964093248492423 6943387115946139872738635)
    ·
      refine ⟨10415080673919209809107953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943387115946139872738635 10415080673919209809107953)
      ·
        refine ⟨7811310505439407356830965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10415080673919209809107953 7811310505439407356830965)
        ·
          refine ⟨732310359884944439702903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7811310505439407356830965 732310359884944439702903)
          ·
            refine ⟨1098465539827416659554355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732310359884944439702903 1098465539827416659554355)
            ·
              refine ⟨1647698309741124989331533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098465539827416659554355 1647698309741124989331533)
              ·
                refine ⟨617886866152921870999325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647698309741124989331533 617886866152921870999325)
                ·
                  refine ⟨231707574807345701624747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617886866152921870999325 231707574807345701624747)
                  ·
                    rfl

theorem cell21_1015310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_1015310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015310 prefixEnd_1015310 := by exact prefixLift 1015310
  have htrace : WordTrace (prefixWord ++ tailWord_1015310) baseStart_1015310 baseEnd_1015310 := by
    simpa [prefixWord, tailWord_1015310, baseEnd_1015310] using wordTrace_append hprefix tailTrace_1015310
  have hstable : (prefixWord ++ tailWord_1015310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015310).length < 2 ^ (prefixWord ++ tailWord_1015310).sum := by decide
  have hdescent : baseEnd_1015310 < baseStart_1015310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015442 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1015442 : Nat := 118140960795 + 1015442 * 2 ^ 59
def prefixEnd_1015442 : Nat := 4983230072969 + 3 ^ 40 * 1015442 * 2
def baseEnd_1015442 : Nat := 231737699005742805424477

theorem tailTrace_1015442 : CollatzResearch.WordTrace tailWord_1015442 prefixEnd_1015442 231737699005742805424477 := by
  unfold tailWord_1015442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259053096808633132936145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24690808258156355021163053 9259053096808633132936145)
  ·
    refine ⟨6944289822606474849702109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9259053096808633132936145 6944289822606474849702109)
    ·
      refine ⟨2604108683477428068638291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6944289822606474849702109 2604108683477428068638291)
      ·
        refine ⟨3906163025216142102957437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604108683477428068638291 3906163025216142102957437)
        ·
          refine ⟨1464811134456053288609039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3906163025216142102957437 1464811134456053288609039)
          ·
            refine ⟨2197216701684079932913559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464811134456053288609039 2197216701684079932913559)
            ·
              refine ⟨3295825052526119899370339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197216701684079932913559 3295825052526119899370339)
              ·
                refine ⟨4943737578789179849055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295825052526119899370339 4943737578789179849055509)
                ·
                  refine ⟨231737699005742805424477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4943737578789179849055509 231737699005742805424477)
                  ·
                    rfl

theorem cell21_1015442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1015442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015442 prefixEnd_1015442 := by exact prefixLift 1015442
  have htrace : WordTrace (prefixWord ++ tailWord_1015442) baseStart_1015442 baseEnd_1015442 := by
    simpa [prefixWord, tailWord_1015442, baseEnd_1015442] using wordTrace_append hprefix tailTrace_1015442
  have hstable : (prefixWord ++ tailWord_1015442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015442).length < 2 ^ (prefixWord ++ tailWord_1015442).sum := by decide
  have hdescent : baseEnd_1015442 < baseStart_1015442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015510 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1015510 : Nat := 118140960795 + 1015510 * 2 ^ 59
def prefixEnd_1015510 : Nat := 4983230072969 + 3 ^ 40 * 1015510 * 2
def baseEnd_1015510 : Nat := 231753217532189798291005

theorem tailTrace_1015510 : CollatzResearch.WordTrace tailWord_1015510 prefixEnd_1015510 231753217532189798291005 := by
  unfold tailWord_1015510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314918284436761259076249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24692461700658786763479989 2314918284436761259076249)
  ·
    refine ⟨1736188713327570944307187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2314918284436761259076249 1736188713327570944307187)
    ·
      refine ⟨2604283069991356416460781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736188713327570944307187 2604283069991356416460781)
      ·
        refine ⟨976606151246758656172793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2604283069991356416460781 976606151246758656172793)
        ·
          refine ⟨732454613435068992129595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976606151246758656172793 732454613435068992129595)
          ·
            refine ⟨1098681920152603488194393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732454613435068992129595 1098681920152603488194393)
            ·
              refine ⟨824011440114452616145795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098681920152603488194393 824011440114452616145795)
              ·
                refine ⟨1236017160171678924218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824011440114452616145795 1236017160171678924218693)
                ·
                  refine ⟨231753217532189798291005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236017160171678924218693 231753217532189798291005)
                  ·
                    rfl

theorem cell21_1015510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1015510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015510 prefixEnd_1015510 := by exact prefixLift 1015510
  have htrace : WordTrace (prefixWord ++ tailWord_1015510) baseStart_1015510 baseEnd_1015510 := by
    simpa [prefixWord, tailWord_1015510, baseEnd_1015510] using wordTrace_append hprefix tailTrace_1015510
  have hstable : (prefixWord ++ tailWord_1015510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015510).length < 2 ^ (prefixWord ++ tailWord_1015510).sum := by decide
  have hdescent : baseEnd_1015510 < baseStart_1015510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015529 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1015529 : Nat := 118140960795 + 1015529 * 2 ^ 59
def prefixEnd_1015529 : Nat := 4983230072969 + 3 ^ 40 * 1015529 * 2
def baseEnd_1015529 : Nat := 231757553591049987474299

theorem tailTrace_1015529 : CollatzResearch.WordTrace tailWord_1015529 prefixEnd_1015529 231757553591049987474299 := by
  unfold tailWord_1015529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039385537919346390161641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24692923691946230926774427 37039385537919346390161641)
  ·
    refine ⟨27779539153439509792621231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37039385537919346390161641 27779539153439509792621231)
    ·
      refine ⟨41669308730159264688931847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27779539153439509792621231 41669308730159264688931847)
      ·
        refine ⟨62503963095238897033397771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41669308730159264688931847 62503963095238897033397771)
        ·
          refine ⟨93755944642858345550096657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62503963095238897033397771 93755944642858345550096657)
          ·
            refine ⟨70316958482143759162572493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93755944642858345550096657 70316958482143759162572493)
            ·
              refine ⟨26368859430803909685964685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70316958482143759162572493 26368859430803909685964685)
              ·
                refine ⟨9888322286551466132236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26368859430803909685964685 9888322286551466132236757)
                ·
                  refine ⟨231757553591049987474299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9888322286551466132236757 231757553591049987474299)
                  ·
                    rfl

theorem cell21_1015529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1015529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015529 prefixEnd_1015529 := by exact prefixLift 1015529
  have htrace : WordTrace (prefixWord ++ tailWord_1015529) baseStart_1015529 baseEnd_1015529 := by
    simpa [prefixWord, tailWord_1015529, baseEnd_1015529] using wordTrace_append hprefix tailTrace_1015529
  have hstable : (prefixWord ++ tailWord_1015529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015529).length < 2 ^ (prefixWord ++ tailWord_1015529).sum := by decide
  have hdescent : baseEnd_1015529 < baseStart_1015529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015687 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 4]
def baseStart_1015687 : Nat := 118140960795 + 1015687 * 2 ^ 59
def prefixEnd_1015687 : Nat := 4983230072969 + 3 ^ 40 * 1015687 * 2
def baseEnd_1015687 : Nat := 231793611343676823840643

theorem tailTrace_1015687 : CollatzResearch.WordTrace tailWord_1015687 prefixEnd_1015687 231793611343676823840643 := by
  unfold tailWord_1015687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37045148271346939374413315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24696765514231292916275543 37045148271346939374413315)
  ·
    refine ⟨55567722407020409061619973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37045148271346939374413315 55567722407020409061619973)
    ·
      refine ⟨10418947951316326699053745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55567722407020409061619973 10418947951316326699053745)
      ·
        refine ⟨7814210963487245024290309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10418947951316326699053745 7814210963487245024290309)
        ·
          refine ⟨1465164555653858442054433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7814210963487245024290309 1465164555653858442054433)
          ·
            refine ⟨1098873416740393831540825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465164555653858442054433 1098873416740393831540825)
            ·
              refine ⟨824155062555295373655619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098873416740393831540825 824155062555295373655619)
              ·
                refine ⟨1236232593832943060483429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824155062555295373655619 1236232593832943060483429)
                ·
                  refine ⟨231793611343676823840643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236232593832943060483429 231793611343676823840643)
                  ·
                    rfl

theorem cell21_1015687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_1015687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015687 prefixEnd_1015687 := by exact prefixLift 1015687
  have htrace : WordTrace (prefixWord ++ tailWord_1015687) baseStart_1015687 baseEnd_1015687 := by
    simpa [prefixWord, tailWord_1015687, baseEnd_1015687] using wordTrace_append hprefix tailTrace_1015687
  have hstable : (prefixWord ++ tailWord_1015687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015687).length < 2 ^ (prefixWord ++ tailWord_1015687).sum := by decide
  have hdescent : baseEnd_1015687 < baseStart_1015687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015729 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_1015729 : Nat := 118140960795 + 1015729 * 2 ^ 59
def prefixEnd_1015729 : Nat := 4983230072969 + 3 ^ 40 * 1015729 * 2
def baseEnd_1015729 : Nat := 231803196315894084140557

theorem tailTrace_1015729 : CollatzResearch.WordTrace tailWord_1015729 prefixEnd_1015729 231803196315894084140557 := by
  unfold tailWord_1015729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37046680137194780547442241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24697786758129853698294827 37046680137194780547442241)
  ·
    refine ⟨27785010102896085410581681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37046680137194780547442241 27785010102896085410581681)
    ·
      refine ⟨20838757577172064057936261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27785010102896085410581681 20838757577172064057936261)
      ·
        refine ⟨3907267045719762010863049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20838757577172064057936261 3907267045719762010863049)
        ·
          refine ⟨2930450284289821508147287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3907267045719762010863049 2930450284289821508147287)
          ·
            refine ⟨4395675426434732262220931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930450284289821508147287 4395675426434732262220931)
            ·
              refine ⟨6593513139652098393331397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395675426434732262220931 6593513139652098393331397)
              ·
                refine ⟨1236283713684768448749637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6593513139652098393331397 1236283713684768448749637)
                ·
                  refine ⟨231803196315894084140557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236283713684768448749637 231803196315894084140557)
                  ·
                    rfl

theorem cell21_1015729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_1015729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015729 prefixEnd_1015729 := by exact prefixLift 1015729
  have htrace : WordTrace (prefixWord ++ tailWord_1015729) baseStart_1015729 baseEnd_1015729 := by
    simpa [prefixWord, tailWord_1015729, baseEnd_1015729] using wordTrace_append hprefix tailTrace_1015729
  have hstable : (prefixWord ++ tailWord_1015729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015729).length < 2 ^ (prefixWord ++ tailWord_1015729).sum := by decide
  have hdescent : baseEnd_1015729 < baseStart_1015729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015901 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1015901 : Nat := 118140960795 + 1015901 * 2 ^ 59
def prefixEnd_1015901 : Nat := 4983230072969 + 3 ^ 40 * 1015901 * 2
def baseEnd_1015901 : Nat := 231842449059260007273539

theorem tailTrace_1015901 : CollatzResearch.WordTrace tailWord_1015901 prefixEnd_1015901 231842449059260007273539 := by
  unfold tailWord_1015901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37052953492571653922703557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24701968995047769281802371 37052953492571653922703557)
  ·
    refine ⟨6947428779857185110506917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37052953492571653922703557 6947428779857185110506917)
    ·
      refine ⟨1302642896223222208220047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6947428779857185110506917 1302642896223222208220047)
      ·
        refine ⟨1953964344334833312330071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302642896223222208220047 1953964344334833312330071)
        ·
          refine ⟨2930946516502249968495107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953964344334833312330071 2930946516502249968495107)
          ·
            refine ⟨4396419774753374952742661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930946516502249968495107 4396419774753374952742661)
            ·
              refine ⟨824328707766257803639249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4396419774753374952742661 824328707766257803639249)
              ·
                refine ⟨618246530824693352729437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824328707766257803639249 618246530824693352729437)
                ·
                  refine ⟨231842449059260007273539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618246530824693352729437 231842449059260007273539)
                  ·
                    rfl

theorem cell21_1015901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1015901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015901 prefixEnd_1015901 := by exact prefixLift 1015901
  have htrace : WordTrace (prefixWord ++ tailWord_1015901) baseStart_1015901 baseEnd_1015901 := by
    simpa [prefixWord, tailWord_1015901, baseEnd_1015901] using wordTrace_append hprefix tailTrace_1015901
  have hstable : (prefixWord ++ tailWord_1015901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015901).length < 2 ^ (prefixWord ++ tailWord_1015901).sum := by decide
  have hdescent : baseEnd_1015901 < baseStart_1015901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015926 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1015926 : Nat := 118140960795 + 1015926 * 2 ^ 59
def prefixEnd_1015926 : Nat := 4983230072969 + 3 ^ 40 * 1015926 * 2
def baseEnd_1015926 : Nat := 231848154399865519356821

theorem tailTrace_1015926 : CollatzResearch.WordTrace tailWord_1015926 prefixEnd_1015926 231848154399865519356821 := by
  unfold tailWord_1015926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315866582342567699522727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24702576878320722128242421 2315866582342567699522727)
  ·
    refine ⟨3473799873513851549284091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2315866582342567699522727 3473799873513851549284091)
    ·
      refine ⟨5210699810270777323926137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473799873513851549284091 5210699810270777323926137)
      ·
        refine ⟨3908024857703082992944603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210699810270777323926137 3908024857703082992944603)
        ·
          refine ⟨5862037286554624489416905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908024857703082992944603 5862037286554624489416905)
          ·
            refine ⟨4396527964915968367062679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862037286554624489416905 4396527964915968367062679)
            ·
              refine ⟨6594791947373952550594019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396527964915968367062679 6594791947373952550594019)
              ·
                refine ⟨9892187921060928825891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594791947373952550594019 9892187921060928825891029)
                ·
                  refine ⟨231848154399865519356821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9892187921060928825891029 231848154399865519356821)
                  ·
                    rfl

theorem cell21_1015926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1015926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015926 prefixEnd_1015926 := by exact prefixLift 1015926
  have htrace : WordTrace (prefixWord ++ tailWord_1015926) baseStart_1015926 baseEnd_1015926 := by
    simpa [prefixWord, tailWord_1015926, baseEnd_1015926] using wordTrace_append hprefix tailTrace_1015926
  have hstable : (prefixWord ++ tailWord_1015926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015926).length < 2 ^ (prefixWord ++ tailWord_1015926).sum := by decide
  have hdescent : baseEnd_1015926 < baseStart_1015926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015940 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1015940 : Nat := 118140960795 + 1015940 * 2 ^ 59
def prefixEnd_1015940 : Nat := 4983230072969 + 3 ^ 40 * 1015940 * 2
def baseEnd_1015940 : Nat := 231851349390604606123459

theorem tailTrace_1015940 : CollatzResearch.WordTrace tailWord_1015940 prefixEnd_1015940 231851349390604606123459 := by
  unfold tailWord_1015940
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527187969715181791686637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24702917292953575722248849 18527187969715181791686637)
  ·
    refine ⟨6947695488643193171882489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18527187969715181791686637 6947695488643193171882489)
    ·
      refine ⟨5210771616482394878911867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6947695488643193171882489 5210771616482394878911867)
      ·
        refine ⟨7816157424723592318367801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210771616482394878911867 7816157424723592318367801)
        ·
          refine ⟨5862118068542694238775851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7816157424723592318367801 5862118068542694238775851)
          ·
            refine ⟨8793177102814041358163777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862118068542694238775851 8793177102814041358163777)
            ·
              refine ⟨6594882827110531018622833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793177102814041358163777 6594882827110531018622833)
              ·
                refine ⟨4946162120332898263967125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594882827110531018622833 4946162120332898263967125)
                ·
                  refine ⟨231851349390604606123459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4946162120332898263967125 231851349390604606123459)
                  ·
                    rfl

theorem cell21_1015940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1015940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1015940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1015940 prefixEnd_1015940 := by exact prefixLift 1015940
  have htrace : WordTrace (prefixWord ++ tailWord_1015940) baseStart_1015940 baseEnd_1015940 := by
    simpa [prefixWord, tailWord_1015940, baseEnd_1015940] using wordTrace_append hprefix tailTrace_1015940
  have hstable : (prefixWord ++ tailWord_1015940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015940).length < 2 ^ (prefixWord ++ tailWord_1015940).sum := by decide
  have hdescent : baseEnd_1015940 < baseStart_1015940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016126 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1016126 : Nat := 118140960795 + 1016126 * 2 ^ 59
def prefixEnd_1016126 : Nat := 4983230072969 + 3 ^ 40 * 1016126 * 2
def baseEnd_1016126 : Nat := 231893797124709616023079

theorem tailTrace_1016126 : CollatzResearch.WordTrace tailWord_1016126 prefixEnd_1016126 231893797124709616023079 := by
  unfold tailWord_1016126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632644989594564668705529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24707439944504344899762821 4632644989594564668705529)
  ·
    refine ⟨3474483742195923501529147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4632644989594564668705529 3474483742195923501529147)
    ·
      refine ⟨5211725613293885252293721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474483742195923501529147 5211725613293885252293721)
      ·
        refine ⟨3908794209970413939220291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5211725613293885252293721 3908794209970413939220291)
        ·
          refine ⟨5863191314955620908830437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908794209970413939220291 5863191314955620908830437)
          ·
            refine ⟨1099348371554178920405707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5863191314955620908830437 1099348371554178920405707)
            ·
              refine ⟨1649022557331268380608561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099348371554178920405707 1649022557331268380608561)
              ·
                refine ⟨1236766917998451285456421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649022557331268380608561 1236766917998451285456421)
                ·
                  refine ⟨231893797124709616023079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236766917998451285456421 231893797124709616023079)
                  ·
                    rfl

theorem cell21_1016126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1016126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016126 prefixEnd_1016126 := by exact prefixLift 1016126
  have htrace : WordTrace (prefixWord ++ tailWord_1016126) baseStart_1016126 baseEnd_1016126 := by
    simpa [prefixWord, tailWord_1016126, baseEnd_1016126] using wordTrace_append hprefix tailTrace_1016126
  have hstable : (prefixWord ++ tailWord_1016126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016126).length < 2 ^ (prefixWord ++ tailWord_1016126).sum := by decide
  have hdescent : baseEnd_1016126 < baseStart_1016126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016168 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_1016168 : Nat := 118140960795 + 1016168 * 2 ^ 59
def prefixEnd_1016168 : Nat := 4983230072969 + 3 ^ 40 * 1016168 * 2
def baseEnd_1016168 : Nat := 231903382096926876322993

theorem tailTrace_1016168 : CollatzResearch.WordTrace tailWord_1016168 prefixEnd_1016168 231903382096926876322993 := by
  unfold tailWord_1016168
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531345891302179261336579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24708461188402905681782105 18531345891302179261336579)
  ·
    refine ⟨27797018836953268892004869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18531345891302179261336579 27797018836953268892004869)
    ·
      refine ⟨5211941031928737917250913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27797018836953268892004869 5211941031928737917250913)
      ·
        refine ⟨3908955773946553437938185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5211941031928737917250913 3908955773946553437938185)
        ·
          refine ⟨2931716830459915078453639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3908955773946553437938185 2931716830459915078453639)
          ·
            refine ⟨4397575245689872617680459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931716830459915078453639 4397575245689872617680459)
            ·
              refine ⟨6596362868534808926520689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397575245689872617680459 6596362868534808926520689)
              ·
                refine ⟨4947272151401106694890517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596362868534808926520689 4947272151401106694890517)
                ·
                  refine ⟨231903382096926876322993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4947272151401106694890517 231903382096926876322993)
                  ·
                    rfl

theorem cell21_1016168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_1016168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016168 prefixEnd_1016168 := by exact prefixLift 1016168
  have htrace : WordTrace (prefixWord ++ tailWord_1016168) baseStart_1016168 baseEnd_1016168 := by
    simpa [prefixWord, tailWord_1016168, baseEnd_1016168] using wordTrace_append hprefix tailTrace_1016168
  have hstable : (prefixWord ++ tailWord_1016168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016168).length < 2 ^ (prefixWord ++ tailWord_1016168).sum := by decide
  have hdescent : baseEnd_1016168 < baseStart_1016168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016202 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_1016202 : Nat := 118140960795 + 1016202 * 2 ^ 59
def prefixEnd_1016202 : Nat := 4983230072969 + 3 ^ 40 * 1016202 * 2
def baseEnd_1016202 : Nat := 231911141360150372756257

theorem tailTrace_1016202 : CollatzResearch.WordTrace tailWord_1016202 prefixEnd_1016202 231911141360150372756257 := by
  unfold tailWord_1016202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265982966120295582352715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24709287909654121552940573 9265982966120295582352715)
  ·
    refine ⟨13898974449180443373529073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9265982966120295582352715 13898974449180443373529073)
    ·
      refine ⟨10424230836885332530146805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13898974449180443373529073 10424230836885332530146805)
      ·
        refine ⟨977271640957999924701263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10424230836885332530146805 977271640957999924701263)
        ·
          refine ⟨1465907461436999887051895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977271640957999924701263 1465907461436999887051895)
          ·
            refine ⟨2198861192155499830577843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465907461436999887051895 2198861192155499830577843)
            ·
              refine ⟨3298291788233249745866765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198861192155499830577843 3298291788233249745866765)
              ·
                refine ⟨1236859420587468654700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298291788233249745866765 1236859420587468654700037)
                ·
                  refine ⟨231911141360150372756257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236859420587468654700037 231911141360150372756257)
                  ·
                    rfl

theorem cell21_1016202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_1016202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016202 prefixEnd_1016202 := by exact prefixLift 1016202
  have htrace : WordTrace (prefixWord ++ tailWord_1016202) baseStart_1016202 baseEnd_1016202 := by
    simpa [prefixWord, tailWord_1016202, baseEnd_1016202] using wordTrace_append hprefix tailTrace_1016202
  have hstable : (prefixWord ++ tailWord_1016202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016202).length < 2 ^ (prefixWord ++ tailWord_1016202).sum := by decide
  have hdescent : baseEnd_1016202 < baseStart_1016202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016247 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 3]
def baseStart_1016247 : Nat := 118140960795 + 1016247 * 2 ^ 59
def prefixEnd_1016247 : Nat := 4983230072969 + 3 ^ 40 * 1016247 * 2
def baseEnd_1016247 : Nat := 231921410973240294506165

theorem tailTrace_1016247 : CollatzResearch.WordTrace tailWord_1016247 prefixEnd_1016247 231921410973240294506165 := by
  unfold tailWord_1016247
  simp only [CollatzResearch.WordTrace]
  refine ⟨37065573149318155014798995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24710382099545436676532663 37065573149318155014798995)
  ·
    refine ⟨55598359723977232522198493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37065573149318155014798995 55598359723977232522198493)
    ·
      refine ⟨20849384896491462195824435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55598359723977232522198493 20849384896491462195824435)
      ·
        refine ⟨31274077344737193293736653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20849384896491462195824435 31274077344737193293736653)
        ·
          refine ⟨11727779004276447485151245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31274077344737193293736653 11727779004276447485151245)
          ·
            refine ⟨4397917126603667806931717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11727779004276447485151245 4397917126603667806931717)
            ·
              refine ⟨824609461238187713799697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4397917126603667806931717 824609461238187713799697)
              ·
                refine ⟨618457095928640785349773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824609461238187713799697 618457095928640785349773)
                ·
                  refine ⟨231921410973240294506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618457095928640785349773 231921410973240294506165)
                  ·
                    rfl

theorem cell21_1016247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].length) (baseStart_1016247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016247 prefixEnd_1016247 := by exact prefixLift 1016247
  have htrace : WordTrace (prefixWord ++ tailWord_1016247) baseStart_1016247 baseEnd_1016247 := by
    simpa [prefixWord, tailWord_1016247, baseEnd_1016247] using wordTrace_append hprefix tailTrace_1016247
  have hstable : (prefixWord ++ tailWord_1016247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016247).length < 2 ^ (prefixWord ++ tailWord_1016247).sum := by decide
  have hdescent : baseEnd_1016247 < baseStart_1016247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016326 : List Nat := [6, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1016326 : Nat := 118140960795 + 1016326 * 2 ^ 59
def prefixEnd_1016326 : Nat := 4983230072969 + 3 ^ 40 * 1016326 * 2
def baseEnd_1016326 : Nat := 77313146616517904229779

theorem tailTrace_1016326 : CollatzResearch.WordTrace tailWord_1016326 prefixEnd_1016326 77313146616517904229779 := by
  unfold tailWord_1016326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158389203625998484591401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24712303010687967671283221 1158389203625998484591401)
  ·
    refine ⟨868791902719498863443551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158389203625998484591401 868791902719498863443551)
    ·
      refine ⟨1303187854079248295165327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868791902719498863443551 1303187854079248295165327)
      ·
        refine ⟨1954781781118872442747991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303187854079248295165327 1954781781118872442747991)
        ·
          refine ⟨2932172671678308664121987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954781781118872442747991 2932172671678308664121987)
          ·
            refine ⟨4398259007517462996182981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932172671678308664121987 4398259007517462996182981)
            ·
              refine ⟨824673563909524311784309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4398259007517462996182981 824673563909524311784309)
              ·
                refine ⟨77313146616517904229779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 824673563909524311784309 77313146616517904229779)
                ·
                  rfl

theorem cell21_1016326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1016326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016326 prefixEnd_1016326 := by exact prefixLift 1016326
  have htrace : WordTrace (prefixWord ++ tailWord_1016326) baseStart_1016326 baseEnd_1016326 := by
    simpa [prefixWord, tailWord_1016326, baseEnd_1016326] using wordTrace_append hprefix tailTrace_1016326
  have hstable : (prefixWord ++ tailWord_1016326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016326).length < 2 ^ (prefixWord ++ tailWord_1016326).sum := by decide
  have hdescent : baseEnd_1016326 < baseStart_1016326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016340 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1016340 : Nat := 118140960795 + 1016340 * 2 ^ 59
def prefixEnd_1016340 : Nat := 4983230072969 + 3 ^ 40 * 1016340 * 2
def baseEnd_1016340 : Nat := 231942634840292799455975

theorem tailTrace_1016340 : CollatzResearch.WordTrace tailWord_1016340 prefixEnd_1016340 231942634840292799455975 := by
  unfold tailWord_1016340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534482568990615948967237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24712643425320821265289649 18534482568990615948967237)
  ·
    refine ⟨3475215481685740490431357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18534482568990615948967237 3475215481685740490431357)
    ·
      refine ⟨1303205805632152683911759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3475215481685740490431357 1303205805632152683911759)
      ·
        refine ⟨1954808708448229025867639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303205805632152683911759 1954808708448229025867639)
        ·
          refine ⟨2932213062672343538801459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954808708448229025867639 2932213062672343538801459)
          ·
            refine ⟨4398319594008515308202189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932213062672343538801459 4398319594008515308202189)
            ·
              refine ⟨1649369847753193240575821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4398319594008515308202189 1649369847753193240575821)
              ·
                refine ⟨618513692907447465215933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1649369847753193240575821 618513692907447465215933)
                ·
                  refine ⟨231942634840292799455975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618513692907447465215933 231942634840292799455975)
                  ·
                    rfl

theorem cell21_1016340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1016340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016340 prefixEnd_1016340 := by exact prefixLift 1016340
  have htrace : WordTrace (prefixWord ++ tailWord_1016340) baseStart_1016340 baseEnd_1016340 := by
    simpa [prefixWord, tailWord_1016340, baseEnd_1016340] using wordTrace_append hprefix tailTrace_1016340
  have hstable : (prefixWord ++ tailWord_1016340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016340).length < 2 ^ (prefixWord ++ tailWord_1016340).sum := by decide
  have hdescent : baseEnd_1016340 < baseStart_1016340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016441 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1016441 : Nat := 118140960795 + 1016441 * 2 ^ 59
def prefixEnd_1016441 : Nat := 4983230072969 + 3 ^ 40 * 1016441 * 2
def baseEnd_1016441 : Nat := 231965684416339068272435

theorem tailTrace_1016441 : CollatzResearch.WordTrace tailWord_1016441 prefixEnd_1016441 231965684416339068272435 := by
  unfold tailWord_1016441
  simp only [CollatzResearch.WordTrace]
  refine ⟨37072648910615326147361177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24715099273743550764907451 37072648910615326147361177)
  ·
    refine ⟨27804486682961494610520883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37072648910615326147361177 27804486682961494610520883)
    ·
      refine ⟨41706730024442241915781325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27804486682961494610520883 41706730024442241915781325)
      ·
        refine ⟨15640023759165840718417997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41706730024442241915781325 15640023759165840718417997)
        ·
          refine ⟨5865008909687190269406749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15640023759165840718417997 5865008909687190269406749)
          ·
            refine ⟨2199378341132696351027531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5865008909687190269406749 2199378341132696351027531)
            ·
              refine ⟨3299067511699044526541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199378341132696351027531 3299067511699044526541297)
              ·
                refine ⟨2474300633774283394905973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299067511699044526541297 2474300633774283394905973)
                ·
                  refine ⟨231965684416339068272435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474300633774283394905973 231965684416339068272435)
                  ·
                    rfl

theorem cell21_1016441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1016441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016441 prefixEnd_1016441 := by exact prefixLift 1016441
  have htrace : WordTrace (prefixWord ++ tailWord_1016441) baseStart_1016441 baseEnd_1016441 := by
    simpa [prefixWord, tailWord_1016441, baseEnd_1016441] using wordTrace_append hprefix tailTrace_1016441
  have hstable : (prefixWord ++ tailWord_1016441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016441).length < 2 ^ (prefixWord ++ tailWord_1016441).sum := by decide
  have hdescent : baseEnd_1016441 < baseStart_1016441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016450 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1016450 : Nat := 118140960795 + 1016450 * 2 ^ 59
def prefixEnd_1016450 : Nat := 4983230072969 + 3 ^ 40 * 1016450 * 2
def baseEnd_1016450 : Nat := 231967738338957052622417

theorem tailTrace_1016450 : CollatzResearch.WordTrace tailWord_1016450 prefixEnd_1016450 231967738338957052622417 := by
  unfold tailWord_1016450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268244291895680171109701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24715318111721813789625869 9268244291895680171109701)
  ·
    refine ⟨1737795804730440032083069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9268244291895680171109701 1737795804730440032083069)
    ·
      refine ⟨651673426773915012031151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1737795804730440032083069 651673426773915012031151)
      ·
        refine ⟨977510140160872518046727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651673426773915012031151 977510140160872518046727)
        ·
          refine ⟨1466265210241308777070091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977510140160872518046727 1466265210241308777070091)
          ·
            refine ⟨2199397815361963165605137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466265210241308777070091 2199397815361963165605137)
            ·
              refine ⟨1649548361521472374203853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199397815361963165605137 1649548361521472374203853)
              ·
                refine ⟨618580635570552140326445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1649548361521472374203853 618580635570552140326445)
                ·
                  refine ⟨231967738338957052622417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618580635570552140326445 231967738338957052622417)
                  ·
                    rfl

theorem cell21_1016450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1016450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016450 prefixEnd_1016450 := by exact prefixLift 1016450
  have htrace : WordTrace (prefixWord ++ tailWord_1016450) baseStart_1016450 baseEnd_1016450 := by
    simpa [prefixWord, tailWord_1016450, baseEnd_1016450] using wordTrace_append hprefix tailTrace_1016450
  have hstable : (prefixWord ++ tailWord_1016450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016450).length < 2 ^ (prefixWord ++ tailWord_1016450).sum := by decide
  have hdescent : baseEnd_1016450 < baseStart_1016450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016455 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_1016455 : Nat := 118140960795 + 1016455 * 2 ^ 59
def prefixEnd_1016455 : Nat := 4983230072969 + 3 ^ 40 * 1016455 * 2
def baseEnd_1016455 : Nat := 231968879407078155039073

theorem tailTrace_1016455 : CollatzResearch.WordTrace tailWord_1016455 prefixEnd_1016455 231968879407078155039073 := by
  unfold tailWord_1016455
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073159532564606538370819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24715439688376404358913879 37073159532564606538370819)
  ·
    refine ⟨55609739298846909807556229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37073159532564606538370819 55609739298846909807556229)
    ·
      refine ⟨10426826118533795588916793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55609739298846909807556229 10426826118533795588916793)
      ·
        refine ⟨7820119588900346691687595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10426826118533795588916793 7820119588900346691687595)
        ·
          refine ⟨11730179383350520037531393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820119588900346691687595 11730179383350520037531393)
          ·
            refine ⟨8797634537512890028148545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11730179383350520037531393 8797634537512890028148545)
            ·
              refine ⟨6598225903134667521111409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797634537512890028148545 6598225903134667521111409)
              ·
                refine ⟨4948669427351000640833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598225903134667521111409 4948669427351000640833557)
                ·
                  refine ⟨231968879407078155039073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4948669427351000640833557 231968879407078155039073)
                  ·
                    rfl

theorem cell21_1016455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_1016455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016455 prefixEnd_1016455 := by exact prefixLift 1016455
  have htrace : WordTrace (prefixWord ++ tailWord_1016455) baseStart_1016455 baseEnd_1016455 := by
    simpa [prefixWord, tailWord_1016455, baseEnd_1016455] using wordTrace_append hprefix tailTrace_1016455
  have hstable : (prefixWord ++ tailWord_1016455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016455).length < 2 ^ (prefixWord ++ tailWord_1016455).sum := by decide
  have hdescent : baseEnd_1016455 < baseStart_1016455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016548 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1016548 : Nat := 118140960795 + 1016548 * 2 ^ 59
def prefixEnd_1016548 : Nat := 4983230072969 + 3 ^ 40 * 1016548 * 2
def baseEnd_1016548 : Nat := 231990103274130659988883

theorem tailTrace_1016548 : CollatzResearch.WordTrace tailWord_1016548 prefixEnd_1016548 231990103274130659988883 := by
  unfold tailWord_1016548
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538275760613841710753149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24717701014151788947670865 18538275760613841710753149)
  ·
    refine ⟨6951853410230190641532431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18538275760613841710753149 6951853410230190641532431)
    ·
      refine ⟨10427780115345285962298647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6951853410230190641532431 10427780115345285962298647)
      ·
        refine ⟨15641670173017928943447971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427780115345285962298647 15641670173017928943447971)
        ·
          refine ⟨23462505259526893415171957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641670173017928943447971 23462505259526893415171957)
          ·
            refine ⟨2199609868080646257672371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23462505259526893415171957 2199609868080646257672371)
            ·
              refine ⟨3299414802120969386508557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199609868080646257672371 3299414802120969386508557)
              ·
                refine ⟨1237280550795363519940709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3299414802120969386508557 1237280550795363519940709)
                ·
                  refine ⟨231990103274130659988883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237280550795363519940709 231990103274130659988883)
                  ·
                    rfl

theorem cell21_1016548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1016548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016548 prefixEnd_1016548 := by exact prefixLift 1016548
  have htrace : WordTrace (prefixWord ++ tailWord_1016548) baseStart_1016548 baseEnd_1016548 := by
    simpa [prefixWord, tailWord_1016548, baseEnd_1016548] using wordTrace_append hprefix tailTrace_1016548
  have hstable : (prefixWord ++ tailWord_1016548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016548).length < 2 ^ (prefixWord ++ tailWord_1016548).sum := by decide
  have hdescent : baseEnd_1016548 < baseStart_1016548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016562 : List Nat := [3, 2, 1, 3, 1, 2, 2, 7]
def baseStart_1016562 : Nat := 118140960795 + 1016562 * 2 ^ 59
def prefixEnd_1016562 : Nat := 4983230072969 + 3 ^ 40 * 1016562 * 2
def baseEnd_1016562 : Nat := 77331099421623248918507

theorem tailTrace_1016562 : CollatzResearch.WordTrace tailWord_1016562 prefixEnd_1016562 77331099421623248918507 := by
  unfold tailWord_1016562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269265535794240953128985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24718041428784642541677293 9269265535794240953128985)
  ·
    refine ⟨6951949151845680714846739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9269265535794240953128985 6951949151845680714846739)
    ·
      refine ⟨10427923727768521072270109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6951949151845680714846739 10427923727768521072270109)
      ·
        refine ⟨3910471397913195402101291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10427923727768521072270109 3910471397913195402101291)
        ·
          refine ⟨5865707096869793103151937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910471397913195402101291 5865707096869793103151937)
          ·
            refine ⟨4399280322652344827363953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865707096869793103151937 4399280322652344827363953)
            ·
              refine ⟨3299460241989258620522965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399280322652344827363953 3299460241989258620522965)
              ·
                refine ⟨77331099421623248918507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3299460241989258620522965 77331099421623248918507)
                ·
                  rfl

theorem cell21_1016562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_1016562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016562 prefixEnd_1016562 := by exact prefixLift 1016562
  have htrace : WordTrace (prefixWord ++ tailWord_1016562) baseStart_1016562 baseEnd_1016562 := by
    simpa [prefixWord, tailWord_1016562, baseEnd_1016562] using wordTrace_append hprefix tailTrace_1016562
  have hstable : (prefixWord ++ tailWord_1016562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016562).length < 2 ^ (prefixWord ++ tailWord_1016562).sum := by decide
  have hdescent : baseEnd_1016562 < baseStart_1016562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016641 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_1016641 : Nat := 118140960795 + 1016641 * 2 ^ 59
def prefixEnd_1016641 : Nat := 4983230072969 + 3 ^ 40 * 1016641 * 2
def baseEnd_1016641 : Nat := 232011327141183164938693

theorem tailTrace_1016641 : CollatzResearch.WordTrace tailWord_1016641 prefixEnd_1016641 232011327141183164938693 := by
  unfold tailWord_1016641
  simp only [CollatzResearch.WordTrace]
  refine ⟨37079943509890760304641777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24719962339927173536427851 37079943509890760304641777)
  ·
    refine ⟨27809957632418070228481333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37079943509890760304641777 27809957632418070228481333)
    ·
      refine ⟨2607183528039194083920125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27809957632418070228481333 2607183528039194083920125)
      ·
        refine ⟨977693823014697781470047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2607183528039194083920125 977693823014697781470047)
        ·
          refine ⟨1466540734522046672205071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977693823014697781470047 1466540734522046672205071)
          ·
            refine ⟨2199811101783070008307607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466540734522046672205071 2199811101783070008307607)
            ·
              refine ⟨3299716652674605012461411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199811101783070008307607 3299716652674605012461411)
              ·
                refine ⟨4949574979011907518692117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299716652674605012461411 4949574979011907518692117)
                ·
                  refine ⟨232011327141183164938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4949574979011907518692117 232011327141183164938693)
                  ·
                    rfl

theorem cell21_1016641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_1016641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016641 prefixEnd_1016641 := by exact prefixLift 1016641
  have htrace : WordTrace (prefixWord ++ tailWord_1016641) baseStart_1016641 baseEnd_1016641 := by
    simpa [prefixWord, tailWord_1016641, baseEnd_1016641] using wordTrace_append hprefix tailTrace_1016641
  have hstable : (prefixWord ++ tailWord_1016641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016641).length < 2 ^ (prefixWord ++ tailWord_1016641).sum := by decide
  have hdescent : baseEnd_1016641 < baseStart_1016641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016697 : List Nat := [1, 2, 1, 3, 2, 3, 9]
def baseStart_1016697 : Nat := 118140960795 + 1016697 * 2 ^ 59
def prefixEnd_1016697 : Nat := 4983230072969 + 3 ^ 40 * 1016697 * 2
def baseEnd_1016697 : Nat := 25780456344904390222805

theorem tailTrace_1016697 : CollatzResearch.WordTrace tailWord_1016697 prefixEnd_1016697 25780456344904390222805 := by
  unfold tailWord_1016697
  simp only [CollatzResearch.WordTrace]
  refine ⟨37081985997687881868680345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24721323998458587912453563 37081985997687881868680345)
  ·
    refine ⟨27811489498265911401510259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37081985997687881868680345 27811489498265911401510259)
    ·
      refine ⟨41717234247398867102265389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27811489498265911401510259 41717234247398867102265389)
      ·
        refine ⟨15643962842774575163349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41717234247398867102265389 15643962842774575163349521)
        ·
          refine ⟨11732972132080931372512141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15643962842774575163349521 11732972132080931372512141)
          ·
            refine ⟨4399864549530349264692053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11732972132080931372512141 4399864549530349264692053)
            ·
              refine ⟨25780456344904390222805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4399864549530349264692053 25780456344904390222805)
              ·
                rfl

theorem cell21_1016697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 9].length) (baseStart_1016697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016697 prefixEnd_1016697 := by exact prefixLift 1016697
  have htrace : WordTrace (prefixWord ++ tailWord_1016697) baseStart_1016697 baseEnd_1016697 := by
    simpa [prefixWord, tailWord_1016697, baseEnd_1016697] using wordTrace_append hprefix tailTrace_1016697
  have hstable : (prefixWord ++ tailWord_1016697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016697).length < 2 ^ (prefixWord ++ tailWord_1016697).sum := by decide
  have hdescent : baseEnd_1016697 < baseStart_1016697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016714 : List Nat := [3, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1016714 : Nat := 118140960795 + 1016714 * 2 ^ 59
def prefixEnd_1016714 : Nat := 4983230072969 + 3 ^ 40 * 1016714 * 2
def baseEnd_1016714 : Nat := 77342662245250420073959

theorem tailTrace_1016714 : CollatzResearch.WordTrace tailWord_1016714 prefixEnd_1016714 77342662245250420073959 := by
  unfold tailWord_1016714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270651509656573443012299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24721737359084195848032797 9270651509656573443012299)
  ·
    refine ⟨13905977264484860164518449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270651509656573443012299 13905977264484860164518449)
    ·
      refine ⟨10429482948363645123388837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13905977264484860164518449 10429482948363645123388837)
      ·
        refine ⟨1955528052818183460635407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10429482948363645123388837 1955528052818183460635407)
        ·
          refine ⟨2933292079227275190953111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955528052818183460635407 2933292079227275190953111)
          ·
            refine ⟨4399938118840912786429667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933292079227275190953111 4399938118840912786429667)
            ·
              refine ⟨6599907178261369179644501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399938118840912786429667 6599907178261369179644501)
              ·
                refine ⟨77342662245250420073959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6599907178261369179644501 77342662245250420073959)
                ·
                  rfl

theorem cell21_1016714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1016714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016714 prefixEnd_1016714 := by exact prefixLift 1016714
  have htrace : WordTrace (prefixWord ++ tailWord_1016714) baseStart_1016714 baseEnd_1016714 := by
    simpa [prefixWord, tailWord_1016714, baseEnd_1016714] using wordTrace_append hprefix tailTrace_1016714
  have hstable : (prefixWord ++ tailWord_1016714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016714).length < 2 ^ (prefixWord ++ tailWord_1016714).sum := by decide
  have hdescent : baseEnd_1016714 < baseStart_1016714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016745 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 3]
def baseStart_1016745 : Nat := 118140960795 + 1016745 * 2 ^ 59
def prefixEnd_1016745 : Nat := 4983230072969 + 3 ^ 40 * 1016745 * 2
def baseEnd_1016745 : Nat := 232035061358102095205147

theorem tailTrace_1016745 : CollatzResearch.WordTrace tailWord_1016745 prefixEnd_1016745 232035061358102095205147 := by
  unfold tailWord_1016745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083736701513986066427689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24722491134342657377618459 37083736701513986066427689)
  ·
    refine ⟨27812802526135489549820767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37083736701513986066427689 27812802526135489549820767)
    ·
      refine ⟨41719203789203234324731151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27812802526135489549820767 41719203789203234324731151)
      ·
        refine ⟨62578805683804851487096727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41719203789203234324731151 62578805683804851487096727)
        ·
          refine ⟨93868208525707277230645091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62578805683804851487096727 93868208525707277230645091)
          ·
            refine ⟨140802312788560915845967637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93868208525707277230645091 140802312788560915845967637)
            ·
              refine ⟨6600108411963792930279733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140802312788560915845967637 6600108411963792930279733)
              ·
                refine ⟨618760163621605587213725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6600108411963792930279733 618760163621605587213725)
                ·
                  refine ⟨232035061358102095205147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618760163621605587213725 232035061358102095205147)
                  ·
                    rfl

theorem cell21_1016745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_1016745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016745 prefixEnd_1016745 := by exact prefixLift 1016745
  have htrace : WordTrace (prefixWord ++ tailWord_1016745) baseStart_1016745 baseEnd_1016745 := by
    simpa [prefixWord, tailWord_1016745, baseEnd_1016745] using wordTrace_append hprefix tailTrace_1016745
  have hstable : (prefixWord ++ tailWord_1016745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016745).length < 2 ^ (prefixWord ++ tailWord_1016745).sum := by decide
  have hdescent : baseEnd_1016745 < baseStart_1016745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016759 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_1016759 : Nat := 118140960795 + 1016759 * 2 ^ 59
def prefixEnd_1016759 : Nat := 4983230072969 + 3 ^ 40 * 1016759 * 2
def baseEnd_1016759 : Nat := 232038256348841181971785

theorem tailTrace_1016759 : CollatzResearch.WordTrace tailWord_1016759 prefixEnd_1016759 232038256348841181971785 := by
  unfold tailWord_1016759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37084247323463266457437331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24722831548975510971624887 37084247323463266457437331)
  ·
    refine ⟨55626370985194899686155997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37084247323463266457437331 55626370985194899686155997)
    ·
      refine ⟨20859889119448087382308499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55626370985194899686155997 20859889119448087382308499)
      ·
        refine ⟨31289833679172131073462749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20859889119448087382308499 31289833679172131073462749)
        ·
          refine ⟨11733687629689549152548531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31289833679172131073462749 11733687629689549152548531)
          ·
            refine ⟨17600531444534323728822797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11733687629689549152548531 17600531444534323728822797)
            ·
              refine ⟨6600199291700371398308549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17600531444534323728822797 6600199291700371398308549)
              ·
                refine ⟨1237537367193819637182853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6600199291700371398308549 1237537367193819637182853)
                ·
                  refine ⟨232038256348841181971785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237537367193819637182853 232038256348841181971785)
                  ·
                    rfl

theorem cell21_1016759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_1016759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016759 prefixEnd_1016759 := by exact prefixLift 1016759
  have htrace : WordTrace (prefixWord ++ tailWord_1016759) baseStart_1016759 baseEnd_1016759 := by
    simpa [prefixWord, tailWord_1016759, baseEnd_1016759] using wordTrace_append hprefix tailTrace_1016759
  have hstable : (prefixWord ++ tailWord_1016759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016759).length < 2 ^ (prefixWord ++ tailWord_1016759).sum := by decide
  have hdescent : baseEnd_1016759 < baseStart_1016759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016855 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 3]
def baseStart_1016855 : Nat := 118140960795 + 1016855 * 2 ^ 59
def prefixEnd_1016855 : Nat := 4983230072969 + 3 ^ 40 * 1016855 * 2
def baseEnd_1016855 : Nat := 232060164856766348371589

theorem tailTrace_1016855 : CollatzResearch.WordTrace tailWord_1016855 prefixEnd_1016855 232060164856766348371589 := by
  unfold tailWord_1016855
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087748731115474852932019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24725165820743649901954679 37087748731115474852932019)
  ·
    refine ⟨55631623096673212279398029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37087748731115474852932019 55631623096673212279398029)
    ·
      refine ⟨20861858661252454604774261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55631623096673212279398029 20861858661252454604774261)
      ·
        refine ⟨1955799249492417619197587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20861858661252454604774261 1955799249492417619197587)
        ·
          refine ⟨2933698874238626428796381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955799249492417619197587 2933698874238626428796381)
          ·
            refine ⟨1100137077839484910798643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2933698874238626428796381 1100137077839484910798643)
            ·
              refine ⟨1650205616759227366197965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100137077839484910798643 1650205616759227366197965)
              ·
                refine ⟨618827106284710262324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650205616759227366197965 618827106284710262324237)
                ·
                  refine ⟨232060164856766348371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618827106284710262324237 232060164856766348371589)
                  ·
                    rfl

theorem cell21_1016855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].length) (baseStart_1016855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016855 prefixEnd_1016855 := by exact prefixLift 1016855
  have htrace : WordTrace (prefixWord ++ tailWord_1016855) baseStart_1016855 baseEnd_1016855 := by
    simpa [prefixWord, tailWord_1016855, baseEnd_1016855] using wordTrace_append hprefix tailTrace_1016855
  have hstable : (prefixWord ++ tailWord_1016855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016855).length < 2 ^ (prefixWord ++ tailWord_1016855).sum := by decide
  have hdescent : baseEnd_1016855 < baseStart_1016855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016866 : List Nat := [3, 3, 1, 1, 1, 5, 7]
def baseStart_1016866 : Nat := 118140960795 + 1016866 * 2 ^ 59
def prefixEnd_1016866 : Nat := 4983230072969 + 3 ^ 40 * 1016866 * 2
def baseEnd_1016866 : Nat := 25784741689625863743137

theorem tailTrace_1016866 : CollatzResearch.WordTrace tailWord_1016866 prefixEnd_1016866 25784741689625863743137 := by
  unfold tailWord_1016866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272037483518905932895613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24725433289383749154388301 9272037483518905932895613)
  ·
    refine ⟨3477014056319589724835855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9272037483518905932895613 3477014056319589724835855)
    ·
      refine ⟨5215521084479384587253783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477014056319589724835855 5215521084479384587253783)
      ·
        refine ⟨7823281626719076880880675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215521084479384587253783 7823281626719076880880675)
        ·
          refine ⟨11734922440078615321321013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823281626719076880880675 11734922440078615321321013)
          ·
            refine ⟨1100148978757370186373845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11734922440078615321321013 1100148978757370186373845)
            ·
              refine ⟨25784741689625863743137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1100148978757370186373845 25784741689625863743137)
              ·
                rfl

theorem cell21_1016866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 7].length) (baseStart_1016866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016866 prefixEnd_1016866 := by exact prefixLift 1016866
  have htrace : WordTrace (prefixWord ++ tailWord_1016866) baseStart_1016866 baseEnd_1016866 := by
    simpa [prefixWord, tailWord_1016866, baseEnd_1016866] using wordTrace_append hprefix tailTrace_1016866
  have hstable : (prefixWord ++ tailWord_1016866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016866).length < 2 ^ (prefixWord ++ tailWord_1016866).sum := by decide
  have hdescent : baseEnd_1016866 < baseStart_1016866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016886 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1016886 : Nat := 118140960795 + 1016886 * 2 ^ 59
def prefixEnd_1016886 : Nat := 4983230072969 + 3 ^ 40 * 1016886 * 2
def baseEnd_1016886 : Nat := 232067239479117183354859

theorem tailTrace_1016886 : CollatzResearch.WordTrace tailWord_1016886 prefixEnd_1016886 232067239479117183354859 := by
  unfold tailWord_1016886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318054962125197946706907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24725919596002111431540341 2318054962125197946706907)
  ·
    refine ⟨3477082443187796920060361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318054962125197946706907 3477082443187796920060361)
    ·
      refine ⟨2607811832390847690045271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3477082443187796920060361 2607811832390847690045271)
      ·
        refine ⟨3911717748586271535067907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607811832390847690045271 3911717748586271535067907)
        ·
          refine ⟨5867576622879407302601861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911717748586271535067907 5867576622879407302601861)
          ·
            refine ⟨1100170616789888869237849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5867576622879407302601861 1100170616789888869237849)
            ·
              refine ⟨825127962592416651928387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100170616789888869237849 825127962592416651928387)
              ·
                refine ⟨1237691943888624977892581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825127962592416651928387 1237691943888624977892581)
                ·
                  refine ⟨232067239479117183354859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237691943888624977892581 232067239479117183354859)
                  ·
                    rfl

theorem cell21_1016886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1016886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016886 prefixEnd_1016886 := by exact prefixLift 1016886
  have htrace : WordTrace (prefixWord ++ tailWord_1016886) baseStart_1016886 baseEnd_1016886 := by
    simpa [prefixWord, tailWord_1016886, baseEnd_1016886] using wordTrace_append hprefix tailTrace_1016886
  have hstable : (prefixWord ++ tailWord_1016886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016886).length < 2 ^ (prefixWord ++ tailWord_1016886).sum := by decide
  have hdescent : baseEnd_1016886 < baseStart_1016886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016939 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_1016939 : Nat := 118140960795 + 1016939 * 2 ^ 59
def prefixEnd_1016939 : Nat := 4983230072969 + 3 ^ 40 * 1016939 * 2
def baseEnd_1016939 : Nat := 232079334801200868971417

theorem tailTrace_1016939 : CollatzResearch.WordTrace tailWord_1016939 prefixEnd_1016939 232079334801200868971417 := by
  unfold tailWord_1016939
  simp only [CollatzResearch.WordTrace]
  refine ⟨37090812462811157198989871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24727208308540771465993247 37090812462811157198989871)
  ·
    refine ⟨55636218694216735798484807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37090812462811157198989871 55636218694216735798484807)
    ·
      refine ⟨83454328041325103697727211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55636218694216735798484807 83454328041325103697727211)
      ·
        refine ⟨125181492061987655546590817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83454328041325103697727211 125181492061987655546590817)
        ·
          refine ⟨93886119046490741659943113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125181492061987655546590817 93886119046490741659943113)
          ·
            refine ⟨70414589284868056244957335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93886119046490741659943113 70414589284868056244957335)
            ·
              refine ⟨105621883927302084367436003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70414589284868056244957335 105621883927302084367436003)
              ·
                refine ⟨158432825890953126551154005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105621883927302084367436003 158432825890953126551154005)
                ·
                  refine ⟨232079334801200868971417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 158432825890953126551154005 232079334801200868971417)
                  ·
                    rfl

theorem cell21_1016939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_1016939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016939 prefixEnd_1016939 := by exact prefixLift 1016939
  have htrace : WordTrace (prefixWord ++ tailWord_1016939) baseStart_1016939 baseEnd_1016939 := by
    simpa [prefixWord, tailWord_1016939, baseEnd_1016939] using wordTrace_append hprefix tailTrace_1016939
  have hstable : (prefixWord ++ tailWord_1016939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016939).length < 2 ^ (prefixWord ++ tailWord_1016939).sum := by decide
  have hdescent : baseEnd_1016939 < baseStart_1016939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016942 : List Nat := [4, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1016942 : Nat := 118140960795 + 1016942 * 2 ^ 59
def prefixEnd_1016942 : Nat := 4983230072969 + 3 ^ 40 * 1016942 * 2
def baseEnd_1016942 : Nat := 77360006480691176807137

theorem tailTrace_1016942 : CollatzResearch.WordTrace tailWord_1016942 prefixEnd_1016942 77360006480691176807137 := by
  unfold tailWord_1016942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636365235225036088918635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24727281254533525807566053 4636365235225036088918635)
  ·
    refine ⟨6954547852837554133377953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4636365235225036088918635 6954547852837554133377953)
    ·
      refine ⟨5215910889628165600033465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6954547852837554133377953 5215910889628165600033465)
      ·
        refine ⟨3911933167221124200025099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5215910889628165600033465 3911933167221124200025099)
        ·
          refine ⟨5867899750831686300037649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911933167221124200025099 5867899750831686300037649)
          ·
            refine ⟨4400924813123764725028237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5867899750831686300037649 4400924813123764725028237)
            ·
              refine ⟨1650346804921411771885589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400924813123764725028237 1650346804921411771885589)
              ·
                refine ⟨77360006480691176807137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1650346804921411771885589 77360006480691176807137)
                ·
                  rfl

theorem cell21_1016942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1016942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016942 prefixEnd_1016942 := by exact prefixLift 1016942
  have htrace : WordTrace (prefixWord ++ tailWord_1016942) baseStart_1016942 baseEnd_1016942 := by
    simpa [prefixWord, tailWord_1016942, baseEnd_1016942] using wordTrace_append hprefix tailTrace_1016942
  have hstable : (prefixWord ++ tailWord_1016942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016942).length < 2 ^ (prefixWord ++ tailWord_1016942).sum := by decide
  have hdescent : baseEnd_1016942 < baseStart_1016942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016956 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1016956 : Nat := 118140960795 + 1016956 * 2 ^ 59
def prefixEnd_1016956 : Nat := 4983230072969 + 3 ^ 40 * 1016956 * 2
def baseEnd_1016956 : Nat := 232083214432812617188049

theorem tailTrace_1016956 : CollatzResearch.WordTrace tailWord_1016956 prefixEnd_1016956 232083214432812617188049 := by
  unfold tailWord_1016956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545716251874784551179361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24727621669166379401572481 18545716251874784551179361)
  ·
    refine ⟨13909287188906088413384521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18545716251874784551179361 13909287188906088413384521)
    ·
      refine ⟨10431965391679566310038391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13909287188906088413384521 10431965391679566310038391)
      ·
        refine ⟨15647948087519349465057587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431965391679566310038391 15647948087519349465057587)
        ·
          refine ⟨23471922131279024197586381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15647948087519349465057587 23471922131279024197586381)
          ·
            refine ⟨8801970799229634074094893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23471922131279024197586381 8801970799229634074094893)
            ·
              refine ⟨3300739049711112777785585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8801970799229634074094893 3300739049711112777785585)
              ·
                refine ⟨2475554287283334583339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300739049711112777785585 2475554287283334583339189)
                ·
                  refine ⟨232083214432812617188049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475554287283334583339189 232083214432812617188049)
                  ·
                    rfl

theorem cell21_1016956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1016956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016956 prefixEnd_1016956 := by exact prefixLift 1016956
  have htrace : WordTrace (prefixWord ++ tailWord_1016956) baseStart_1016956 baseEnd_1016956 := by
    simpa [prefixWord, tailWord_1016956, baseEnd_1016956] using wordTrace_append hprefix tailTrace_1016956
  have hstable : (prefixWord ++ tailWord_1016956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016956).length < 2 ^ (prefixWord ++ tailWord_1016956).sum := by decide
  have hdescent : baseEnd_1016956 < baseStart_1016956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016990 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1016990 : Nat := 118140960795 + 1016990 * 2 ^ 59
def prefixEnd_1016990 : Nat := 4983230072969 + 3 ^ 40 * 1016990 * 2
def baseEnd_1016990 : Nat := 232090973696036113621313

theorem tailTrace_1016990 : CollatzResearch.WordTrace tailWord_1016990 prefixEnd_1016990 232090973696036113621313 := by
  unfold tailWord_1016990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636584073203299113637053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24728448390417595272730949 4636584073203299113637053)
  ·
    refine ⟨1738719027451237167613895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4636584073203299113637053 1738719027451237167613895)
    ·
      refine ⟨2608078541176855751420843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738719027451237167613895 2608078541176855751420843)
      ·
        refine ⟨3912117811765283627131265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608078541176855751420843 3912117811765283627131265)
        ·
          refine ⟨2934088358823962720348449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3912117811765283627131265 2934088358823962720348449)
          ·
            refine ⟨2200566269117972040261337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934088358823962720348449 2200566269117972040261337)
            ·
              refine ⟨1650424701838479030196003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200566269117972040261337 1650424701838479030196003)
              ·
                refine ⟨2475637052757718545294005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650424701838479030196003 2475637052757718545294005)
                ·
                  refine ⟨232090973696036113621313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475637052757718545294005 232090973696036113621313)
                  ·
                    rfl

theorem cell21_1016990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1016990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1016990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1016990 prefixEnd_1016990 := by exact prefixLift 1016990
  have htrace : WordTrace (prefixWord ++ tailWord_1016990) baseStart_1016990 baseEnd_1016990 := by
    simpa [prefixWord, tailWord_1016990, baseEnd_1016990] using wordTrace_append hprefix tailTrace_1016990
  have hstable : (prefixWord ++ tailWord_1016990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016990).length < 2 ^ (prefixWord ++ tailWord_1016990).sum := by decide
  have hdescent : baseEnd_1016990 < baseStart_1016990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017094 : List Nat := [6, 2, 13]
def baseStart_1017094 : Nat := 118140960795 + 1017094 * 2 ^ 59
def prefixEnd_1017094 : Nat := 4983230072969 + 3 ^ 40 * 1017094 * 2
def baseEnd_1017094 : Nat := 318401519770857399023

theorem tailTrace_1017094 : CollatzResearch.WordTrace tailWord_1017094 prefixEnd_1017094 318401519770857399023 := by
  unfold tailWord_1017094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159264555539050583465073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24730977184833079113921557 1159264555539050583465073)
  ·
    refine ⟨869448416654287937598805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1159264555539050583465073 869448416654287937598805)
    ·
      refine ⟨318401519770857399023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 869448416654287937598805 318401519770857399023)
      ·
        rfl

theorem cell21_1017094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 13].length) (baseStart_1017094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017094 prefixEnd_1017094 := by exact prefixLift 1017094
  have htrace : WordTrace (prefixWord ++ tailWord_1017094) baseStart_1017094 baseEnd_1017094 := by
    simpa [prefixWord, tailWord_1017094, baseEnd_1017094] using wordTrace_append hprefix tailTrace_1017094
  have hstable : (prefixWord ++ tailWord_1017094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017094).length < 2 ^ (prefixWord ++ tailWord_1017094).sum := by decide
  have hdescent : baseEnd_1017094 < baseStart_1017094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017156 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1017156 : Nat := 118140960795 + 1017156 * 2 ^ 59
def prefixEnd_1017156 : Nat := 4983230072969 + 3 ^ 40 * 1017156 * 2
def baseEnd_1017156 : Nat := 232128857157656713854307

theorem tailTrace_1017156 : CollatzResearch.WordTrace tailWord_1017156 prefixEnd_1017156 232128857157656713854307 := by
  unfold tailWord_1017156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549363551512501629819661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24732484735350002173092881 18549363551512501629819661)
  ·
    refine ⟨6956011331817188111182373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18549363551512501629819661 6956011331817188111182373)
    ·
      refine ⟨1304252124715722770846695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6956011331817188111182373 1304252124715722770846695)
      ·
        refine ⟨1956378187073584156270043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304252124715722770846695 1956378187073584156270043)
        ·
          refine ⟨2934567280610376234405065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956378187073584156270043 2934567280610376234405065)
          ·
            refine ⟨2200925460457782175803799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934567280610376234405065 2200925460457782175803799)
            ·
              refine ⟨3301388190686673263705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200925460457782175803799 3301388190686673263705699)
              ·
                refine ⟨4952082286030009895558549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301388190686673263705699 4952082286030009895558549)
                ·
                  refine ⟨232128857157656713854307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4952082286030009895558549 232128857157656713854307)
                  ·
                    rfl

theorem cell21_1017156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1017156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017156 prefixEnd_1017156 := by exact prefixLift 1017156
  have htrace : WordTrace (prefixWord ++ tailWord_1017156) baseStart_1017156 baseEnd_1017156 := by
    simpa [prefixWord, tailWord_1017156, baseEnd_1017156] using wordTrace_append hprefix tailTrace_1017156
  have hstable : (prefixWord ++ tailWord_1017156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017156).length < 2 ^ (prefixWord ++ tailWord_1017156).sum := by decide
  have hdescent : baseEnd_1017156 < baseStart_1017156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017184 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1017184 : Nat := 118140960795 + 1017184 * 2 ^ 59
def prefixEnd_1017184 : Nat := 4983230072969 + 3 ^ 40 * 1017184 * 2
def baseEnd_1017184 : Nat := 232135247139134887387583

theorem tailTrace_1017184 : CollatzResearch.WordTrace tailWord_1017184 prefixEnd_1017184 232135247139134887387583 := by
  unfold tailWord_1017184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549874173461782020829303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24733165564615709361105737 18549874173461782020829303)
  ·
    refine ⟨27824811260192673031243955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18549874173461782020829303 27824811260192673031243955)
    ·
      refine ⟨41737216890289009546865933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27824811260192673031243955 41737216890289009546865933)
      ·
        refine ⟨15651456333858378580074725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41737216890289009546865933 15651456333858378580074725)
        ·
          refine ⟨2934648062598445983764011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15651456333858378580074725 2934648062598445983764011)
          ·
            refine ⟨4401972093897668975646017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934648062598445983764011 4401972093897668975646017)
            ·
              refine ⟨3301479070423251731734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401972093897668975646017 3301479070423251731734513)
              ·
                refine ⟨2476109302817438798800885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301479070423251731734513 2476109302817438798800885)
                ·
                  refine ⟨232135247139134887387583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476109302817438798800885 232135247139134887387583)
                  ·
                    rfl

theorem cell21_1017184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1017184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017184 prefixEnd_1017184 := by exact prefixLift 1017184
  have htrace : WordTrace (prefixWord ++ tailWord_1017184) baseStart_1017184 baseEnd_1017184 := by
    simpa [prefixWord, tailWord_1017184, baseEnd_1017184] using wordTrace_append hprefix tailTrace_1017184
  have hstable : (prefixWord ++ tailWord_1017184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017184).length < 2 ^ (prefixWord ++ tailWord_1017184).sum := by decide
  have hdescent : baseEnd_1017184 < baseStart_1017184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017201 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 3]
def baseStart_1017201 : Nat := 118140960795 + 1017201 * 2 ^ 59
def prefixEnd_1017201 : Nat := 4983230072969 + 3 ^ 40 * 1017201 * 2
def baseEnd_1017201 : Nat := 232139126770746635604215

theorem tailTrace_1017201 : CollatzResearch.WordTrace tailWord_1017201 prefixEnd_1017201 232139126770746635604215 := by
  unfold tailWord_1017201
  simp only [CollatzResearch.WordTrace]
  refine ⟨37100368387861975945027457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24733578925241317296684971 37100368387861975945027457)
  ·
    refine ⟨27825276290896481958770593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37100368387861975945027457 27825276290896481958770593)
    ·
      refine ⟨20868957218172361469077945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27825276290896481958770593 20868957218172361469077945)
      ·
        refine ⟨15651717913629271101808459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20868957218172361469077945 15651717913629271101808459)
        ·
          refine ⟨23477576870443906652712689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651717913629271101808459 23477576870443906652712689)
          ·
            refine ⟨17608182652832929989534517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477576870443906652712689 17608182652832929989534517)
            ·
              refine ⟨1650767123703087186518861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17608182652832929989534517 1650767123703087186518861)
              ·
                refine ⟨619037671388657694944573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650767123703087186518861 619037671388657694944573)
                ·
                  refine ⟨232139126770746635604215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619037671388657694944573 232139126770746635604215)
                  ·
                    rfl

theorem cell21_1017201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_1017201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017201 prefixEnd_1017201 := by exact prefixLift 1017201
  have htrace : WordTrace (prefixWord ++ tailWord_1017201) baseStart_1017201 baseEnd_1017201 := by
    simpa [prefixWord, tailWord_1017201, baseEnd_1017201] using wordTrace_append hprefix tailTrace_1017201
  have hstable : (prefixWord ++ tailWord_1017201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017201).length < 2 ^ (prefixWord ++ tailWord_1017201).sum := by decide
  have hdescent : baseEnd_1017201 < baseStart_1017201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017218 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1017218 : Nat := 118140960795 + 1017218 * 2 ^ 59
def prefixEnd_1017218 : Nat := 4983230072969 + 3 ^ 40 * 1017218 * 2
def baseEnd_1017218 : Nat := 232143006402358383820847

theorem tailTrace_1017218 : CollatzResearch.WordTrace tailWord_1017218 prefixEnd_1017218 232143006402358383820847 := by
  unfold tailWord_1017218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275247107200096962099077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24733992285866925232264205 9275247107200096962099077)
  ·
    refine ⟨1739108832600018180393577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9275247107200096962099077 1739108832600018180393577)
    ·
      refine ⟨1304331624450013635295183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1739108832600018180393577 1304331624450013635295183)
      ·
        refine ⟨1956497436675020452942775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304331624450013635295183 1956497436675020452942775)
        ·
          refine ⟨2934746155012530679414163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956497436675020452942775 2934746155012530679414163)
          ·
            refine ⟨4402119232518796019121245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934746155012530679414163 4402119232518796019121245)
            ·
              refine ⟨1650794712194548507170467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402119232518796019121245 1650794712194548507170467)
              ·
                refine ⟨2476192068291822760755701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650794712194548507170467 2476192068291822760755701)
                ·
                  refine ⟨232143006402358383820847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476192068291822760755701 232143006402358383820847)
                  ·
                    rfl

theorem cell21_1017218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1017218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017218 prefixEnd_1017218 := by exact prefixLift 1017218
  have htrace : WordTrace (prefixWord ++ tailWord_1017218) baseStart_1017218 baseEnd_1017218 := by
    simpa [prefixWord, tailWord_1017218, baseEnd_1017218] using wordTrace_append hprefix tailTrace_1017218
  have hstable : (prefixWord ++ tailWord_1017218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017218).length < 2 ^ (prefixWord ++ tailWord_1017218).sum := by decide
  have hdescent : baseEnd_1017218 < baseStart_1017218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017277 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1017277 : Nat := 118140960795 + 1017277 * 2 ^ 59
def prefixEnd_1017277 : Nat := 4983230072969 + 3 ^ 40 * 1017277 * 2
def baseEnd_1017277 : Nat := 232156471006187392337393

theorem tailTrace_1017277 : CollatzResearch.WordTrace tailWord_1017277 prefixEnd_1017277 232156471006187392337393 := by
  unfold tailWord_1017277
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103140335586640924794085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24735426890391093949862723 37103140335586640924794085)
  ·
    refine ⟨6956838812922495173398891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37103140335586640924794085 6956838812922495173398891)
    ·
      refine ⟨10435258219383742760098337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956838812922495173398891 10435258219383742760098337)
      ·
        refine ⟨7826443664537807070073753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435258219383742760098337 7826443664537807070073753)
        ·
          refine ⟨5869832748403355302555315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826443664537807070073753 5869832748403355302555315)
          ·
            refine ⟨8804749122605032953832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869832748403355302555315 8804749122605032953832973)
            ·
              refine ⟨3301780920976887357687365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8804749122605032953832973 3301780920976887357687365)
              ·
                refine ⟨619083922683166379566381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3301780920976887357687365 619083922683166379566381)
                ·
                  refine ⟨232156471006187392337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619083922683166379566381 232156471006187392337393)
                  ·
                    rfl

theorem cell21_1017277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1017277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017277 prefixEnd_1017277 := by exact prefixLift 1017277
  have htrace : WordTrace (prefixWord ++ tailWord_1017277) baseStart_1017277 baseEnd_1017277 := by
    simpa [prefixWord, tailWord_1017277, baseEnd_1017277] using wordTrace_append hprefix tailTrace_1017277
  have hstable : (prefixWord ++ tailWord_1017277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017277).length < 2 ^ (prefixWord ++ tailWord_1017277).sum := by decide
  have hdescent : baseEnd_1017277 < baseStart_1017277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017325 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1017325 : Nat := 118140960795 + 1017325 * 2 ^ 59
def prefixEnd_1017325 : Nat := 4983230072969 + 3 ^ 40 * 1017325 * 2
def baseEnd_1017325 : Nat := 232167425260149975537295

theorem tailTrace_1017325 : CollatzResearch.WordTrace tailWord_1017325 prefixEnd_1017325 232167425260149975537295 := by
  unfold tailWord_1017325
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104891039412745122541429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736594026275163415027619 37104891039412745122541429)
  ·
    refine ⟨3478583534944944855238259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37104891039412745122541429 3478583534944944855238259)
    ·
      refine ⟨5217875302417417282857389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478583534944944855238259 5217875302417417282857389)
      ·
        refine ⟨1956703238406531481071521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5217875302417417282857389 1956703238406531481071521)
        ·
          refine ⟨1467527428804898610803641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1956703238406531481071521 1467527428804898610803641)
          ·
            refine ⟨1100645571603673958102731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467527428804898610803641 1100645571603673958102731)
            ·
              refine ⟨1650968357405510937154097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100645571603673958102731 1650968357405510937154097)
              ·
                refine ⟨1238226268054133202865573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650968357405510937154097 1238226268054133202865573)
                ·
                  refine ⟨232167425260149975537295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238226268054133202865573 232167425260149975537295)
                  ·
                    rfl

theorem cell21_1017325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1017325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017325 prefixEnd_1017325 := by exact prefixLift 1017325
  have htrace : WordTrace (prefixWord ++ tailWord_1017325) baseStart_1017325 baseEnd_1017325 := by
    simpa [prefixWord, tailWord_1017325, baseEnd_1017325] using wordTrace_append hprefix tailTrace_1017325
  have hstable : (prefixWord ++ tailWord_1017325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017325).length < 2 ^ (prefixWord ++ tailWord_1017325).sum := by decide
  have hdescent : baseEnd_1017325 < baseStart_1017325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017336 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_1017336 : Nat := 118140960795 + 1017336 * 2 ^ 59
def prefixEnd_1017336 : Nat := 4983230072969 + 3 ^ 40 * 1017336 * 2
def baseEnd_1017336 : Nat := 232169935610016400853939

theorem tailTrace_1017336 : CollatzResearch.WordTrace tailWord_1017336 prefixEnd_1017336 232169935610016400853939 := by
  unfold tailWord_1017336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552646121186447000595931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24736861494915262667461241 18552646121186447000595931)
  ·
    refine ⟨27828969181779670500893897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552646121186447000595931 27828969181779670500893897)
    ·
      refine ⟨20871726886334752875670423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27828969181779670500893897 20871726886334752875670423)
      ·
        refine ⟨31307590329502129313505635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20871726886334752875670423 31307590329502129313505635)
        ·
          refine ⟨46961385494253193970258453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31307590329502129313505635 46961385494253193970258453)
          ·
            refine ⟨2201314945043118467355865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46961385494253193970258453 2201314945043118467355865)
            ·
              refine ⟨1650986208782338850516899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201314945043118467355865 1650986208782338850516899)
              ·
                refine ⟨2476479313173508275775349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650986208782338850516899 2476479313173508275775349)
                ·
                  refine ⟨232169935610016400853939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476479313173508275775349 232169935610016400853939)
                  ·
                    rfl

theorem cell21_1017336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_1017336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017336 prefixEnd_1017336 := by exact prefixLift 1017336
  have htrace : WordTrace (prefixWord ++ tailWord_1017336) baseStart_1017336 baseEnd_1017336 := by
    simpa [prefixWord, tailWord_1017336, baseEnd_1017336] using wordTrace_append hprefix tailTrace_1017336
  have hstable : (prefixWord ++ tailWord_1017336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017336).length < 2 ^ (prefixWord ++ tailWord_1017336).sum := by decide
  have hdescent : baseEnd_1017336 < baseStart_1017336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017342 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1017342 : Nat := 118140960795 + 1017342 * 2 ^ 59
def prefixEnd_1017342 : Nat := 4983230072969 + 3 ^ 40 * 1017342 * 2
def baseEnd_1017342 : Nat := 232171304891761723753927

theorem tailTrace_1017342 : CollatzResearch.WordTrace tailWord_1017342 prefixEnd_1017342 232171304891761723753927 := by
  unfold tailWord_1017342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638188885043894628238785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24737007386900771350606853 4638188885043894628238785)
  ·
    refine ⟨3478641663782920971179089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4638188885043894628238785 3478641663782920971179089)
    ·
      refine ⟨2608981247837190728384317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3478641663782920971179089 2608981247837190728384317)
      ·
        refine ⟨978367967938946523144119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608981247837190728384317 978367967938946523144119)
        ·
          refine ⟨1467551951908419784716179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978367967938946523144119 1467551951908419784716179)
          ·
            refine ⟨2201327927862629677074269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467551951908419784716179 2201327927862629677074269)
            ·
              refine ⟨825497972948486128902851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2201327927862629677074269 825497972948486128902851)
              ·
                refine ⟨1238246959422729193354277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825497972948486128902851 1238246959422729193354277)
                ·
                  refine ⟨232171304891761723753927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238246959422729193354277 232171304891761723753927)
                  ·
                    rfl

theorem cell21_1017342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1017342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017342 prefixEnd_1017342 := by exact prefixLift 1017342
  have htrace : WordTrace (prefixWord ++ tailWord_1017342) baseStart_1017342 baseEnd_1017342 := by
    simpa [prefixWord, tailWord_1017342, baseEnd_1017342] using wordTrace_append hprefix tailTrace_1017342
  have hstable : (prefixWord ++ tailWord_1017342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017342).length < 2 ^ (prefixWord ++ tailWord_1017342).sum := by decide
  have hdescent : baseEnd_1017342 < baseStart_1017342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017443 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_1017443 : Nat := 118140960795 + 1017443 * 2 ^ 59
def prefixEnd_1017443 : Nat := 4983230072969 + 3 ^ 40 * 1017443 * 2
def baseEnd_1017443 : Nat := 232194354467807992570387

theorem tailTrace_1017443 : CollatzResearch.WordTrace tailWord_1017443 prefixEnd_1017443 232194354467807992570387 := by
  unfold tailWord_1017443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109194852985251275336983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24739463235323500850224655 37109194852985251275336983)
  ·
    refine ⟨55663792279477876913005475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37109194852985251275336983 55663792279477876913005475)
    ·
      refine ⟨83495688419216815369508213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55663792279477876913005475 83495688419216815369508213)
      ·
        refine ⟨7827720789301576440891395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83495688419216815369508213 7827720789301576440891395)
        ·
          refine ⟨11741581183952364661337093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827720789301576440891395 11741581183952364661337093)
          ·
            refine ⟨2201546471991068374000705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11741581183952364661337093 2201546471991068374000705)
            ·
              refine ⟨1651159853993301280500529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201546471991068374000705 1651159853993301280500529)
              ·
                refine ⟨1238369890494975960375397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651159853993301280500529 1238369890494975960375397)
                ·
                  refine ⟨232194354467807992570387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238369890494975960375397 232194354467807992570387)
                  ·
                    rfl

theorem cell21_1017443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_1017443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017443 prefixEnd_1017443 := by exact prefixLift 1017443
  have htrace : WordTrace (prefixWord ++ tailWord_1017443) baseStart_1017443 baseEnd_1017443 := by
    simpa [prefixWord, tailWord_1017443, baseEnd_1017443] using wordTrace_append hprefix tailTrace_1017443
  have hstable : (prefixWord ++ tailWord_1017443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017443).length < 2 ^ (prefixWord ++ tailWord_1017443).sum := by decide
  have hdescent : baseEnd_1017443 < baseStart_1017443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017505 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 3]
def baseStart_1017505 : Nat := 118140960795 + 1017505 * 2 ^ 59
def prefixEnd_1017505 : Nat := 4983230072969 + 3 ^ 40 * 1017505 * 2
def baseEnd_1017505 : Nat := 232208503712509662536927

theorem tailTrace_1017505 : CollatzResearch.WordTrace tailWord_1017505 prefixEnd_1017505 232208503712509662536927 := by
  unfold tailWord_1017505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111456178760635864093969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24740970785840423909395979 37111456178760635864093969)
  ·
    refine ⟨27833592134070476898070477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37111456178760635864093969 27833592134070476898070477)
    ·
      refine ⟨10437597050276428836776429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27833592134070476898070477 10437597050276428836776429)
      ·
        refine ⟨3914098893853660813791161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10437597050276428836776429 3914098893853660813791161)
        ·
          refine ⟨2935574170390245610343371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914098893853660813791161 2935574170390245610343371)
          ·
            refine ⟨4403361255585368415515057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935574170390245610343371 4403361255585368415515057)
            ·
              refine ⟨3302520941689026311636293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403361255585368415515057 3302520941689026311636293)
              ·
                refine ⟨619222676566692433431805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3302520941689026311636293 619222676566692433431805)
                ·
                  refine ⟨232208503712509662536927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619222676566692433431805 232208503712509662536927)
                  ·
                    rfl

theorem cell21_1017505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_1017505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017505 prefixEnd_1017505 := by exact prefixLift 1017505
  have htrace : WordTrace (prefixWord ++ tailWord_1017505) baseStart_1017505 baseEnd_1017505 := by
    simpa [prefixWord, tailWord_1017505, baseEnd_1017505] using wordTrace_append hprefix tailTrace_1017505
  have hstable : (prefixWord ++ tailWord_1017505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017505).length < 2 ^ (prefixWord ++ tailWord_1017505).sum := by decide
  have hdescent : baseEnd_1017505 < baseStart_1017505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017519 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 4]
def baseStart_1017519 : Nat := 118140960795 + 1017519 * 2 ^ 59
def prefixEnd_1017519 : Nat := 4983230072969 + 3 ^ 40 * 1017519 * 2
def baseEnd_1017519 : Nat := 232211698703248749303565

theorem tailTrace_1017519 : CollatzResearch.WordTrace tailWord_1017519 prefixEnd_1017519 232211698703248749303565 := by
  unfold tailWord_1017519
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111966800709916255103611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741311200473277503402407 37111966800709916255103611)
  ·
    refine ⟨55667950201064874382655417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37111966800709916255103611 55667950201064874382655417)
    ·
      refine ⟨41750962650798655786991563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55667950201064874382655417 41750962650798655786991563)
      ·
        refine ⟨62626443976197983680487345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41750962650798655786991563 62626443976197983680487345)
        ·
          refine ⟨46969832982148487760365509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62626443976197983680487345 46969832982148487760365509)
          ·
            refine ⟨8806843684152841455068533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46969832982148487760365509 8806843684152841455068533)
            ·
              refine ⟨825641595389328886412675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8806843684152841455068533 825641595389328886412675)
              ·
                refine ⟨1238462393083993329619013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825641595389328886412675 1238462393083993329619013)
                ·
                  refine ⟨232211698703248749303565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238462393083993329619013 232211698703248749303565)
                  ·
                    rfl

theorem cell21_1017519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_1017519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017519 prefixEnd_1017519 := by exact prefixLift 1017519
  have htrace : WordTrace (prefixWord ++ tailWord_1017519) baseStart_1017519 baseEnd_1017519 := by
    simpa [prefixWord, tailWord_1017519, baseEnd_1017519] using wordTrace_append hprefix tailTrace_1017519
  have hstable : (prefixWord ++ tailWord_1017519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017519).length < 2 ^ (prefixWord ++ tailWord_1017519).sum := by decide
  have hdescent : baseEnd_1017519 < baseStart_1017519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017640 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1017640 : Nat := 118140960795 + 1017640 * 2 ^ 59
def prefixEnd_1017640 : Nat := 4983230072969 + 3 ^ 40 * 1017640 * 2
def baseEnd_1017640 : Nat := 232239312551779427786651

theorem tailTrace_1017640 : CollatzResearch.WordTrace tailWord_1017640 prefixEnd_1017640 232239312551779427786651 := by
  unfold tailWord_1017640
  simp only [CollatzResearch.WordTrace]
  refine ⟨18558190016635776960129187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24744253355514369280172249 18558190016635776960129187)
  ·
    refine ⟨27837285024953665440193781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18558190016635776960129187 27837285024953665440193781)
    ·
      refine ⟨2609745471089406135018167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27837285024953665440193781 2609745471089406135018167)
      ·
        refine ⟨3914618206634109202527251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609745471089406135018167 3914618206634109202527251)
        ·
          refine ⟨5871927309951163803790877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914618206634109202527251 5871927309951163803790877)
          ·
            refine ⟨2201972741231686426421579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5871927309951163803790877 2201972741231686426421579)
            ·
              refine ⟨3302959111847529639632369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201972741231686426421579 3302959111847529639632369)
              ·
                refine ⟨2477219333885647229724277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302959111847529639632369 2477219333885647229724277)
                ·
                  refine ⟨232239312551779427786651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477219333885647229724277 232239312551779427786651)
                  ·
                    rfl

theorem cell21_1017640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1017640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017640 prefixEnd_1017640 := by exact prefixLift 1017640
  have htrace : WordTrace (prefixWord ++ tailWord_1017640) baseStart_1017640 baseEnd_1017640 := by
    simpa [prefixWord, tailWord_1017640, baseEnd_1017640] using wordTrace_append hprefix tailTrace_1017640
  have hstable : (prefixWord ++ tailWord_1017640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017640).length < 2 ^ (prefixWord ++ tailWord_1017640).sum := by decide
  have hdescent : baseEnd_1017640 < baseStart_1017640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017713 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1017713 : Nat := 118140960795 + 1017713 * 2 ^ 59
def prefixEnd_1017713 : Nat := 4983230072969 + 3 ^ 40 * 1017713 * 2
def baseEnd_1017713 : Nat := 232255972146347523069835

theorem tailTrace_1017713 : CollatzResearch.WordTrace tailWord_1017713 prefixEnd_1017713 232255972146347523069835 := by
  unfold tailWord_1017713
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119042562007087387665793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24746028374671391591777195 37119042562007087387665793)
  ·
    refine ⟨27839281921505315540749345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37119042562007087387665793 27839281921505315540749345)
    ·
      refine ⟨20879461441128986655562009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27839281921505315540749345 20879461441128986655562009)
      ·
        refine ⟨15659596080846739991671507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879461441128986655562009 15659596080846739991671507)
        ·
          refine ⟨23489394121270109987507261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659596080846739991671507 23489394121270109987507261)
          ·
            refine ⟨8808522795476291245315223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23489394121270109987507261 8808522795476291245315223)
            ·
              refine ⟨13212784193214436867972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808522795476291245315223 13212784193214436867972835)
              ·
                refine ⟨19819176289821655301959253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13212784193214436867972835 19819176289821655301959253)
                ·
                  refine ⟨232255972146347523069835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19819176289821655301959253 232255972146347523069835)
                  ·
                    rfl

theorem cell21_1017713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1017713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017713 prefixEnd_1017713 := by exact prefixLift 1017713
  have htrace : WordTrace (prefixWord ++ tailWord_1017713) baseStart_1017713 baseEnd_1017713 := by
    simpa [prefixWord, tailWord_1017713, baseEnd_1017713] using wordTrace_append hprefix tailTrace_1017713
  have hstable : (prefixWord ++ tailWord_1017713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017713).length < 2 ^ (prefixWord ++ tailWord_1017713).sum := by decide
  have hdescent : baseEnd_1017713 < baseStart_1017713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017733 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1017733 : Nat := 118140960795 + 1017733 * 2 ^ 59
def prefixEnd_1017733 : Nat := 4983230072969 + 3 ^ 40 * 1017733 * 2
def baseEnd_1017733 : Nat := 232260536418831932736461

theorem tailTrace_1017733 : CollatzResearch.WordTrace tailWord_1017733 prefixEnd_1017733 232260536418831932736461 := by
  unfold tailWord_1017733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119772021934630803393853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24746514681289753868929235 37119772021934630803393853)
  ·
    refine ⟨13919914508225486551272695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37119772021934630803393853 13919914508225486551272695)
    ·
      refine ⟨20879871762338229826909043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919914508225486551272695 20879871762338229826909043)
      ·
        refine ⟨31319807643507344740363565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879871762338229826909043 31319807643507344740363565)
        ·
          refine ⟨11744927866315254277636337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31319807643507344740363565 11744927866315254277636337)
          ·
            refine ⟨8808695899736440708227253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11744927866315254277636337 8808695899736440708227253)
            ·
              refine ⟨825815240600291316396305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8808695899736440708227253 825815240600291316396305)
              ·
                refine ⟨619361430450218487297229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825815240600291316396305 619361430450218487297229)
                ·
                  refine ⟨232260536418831932736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619361430450218487297229 232260536418831932736461)
                  ·
                    rfl

theorem cell21_1017733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1017733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017733 prefixEnd_1017733 := by exact prefixLift 1017733
  have htrace : WordTrace (prefixWord ++ tailWord_1017733) baseStart_1017733 baseEnd_1017733 := by
    simpa [prefixWord, tailWord_1017733, baseEnd_1017733] using wordTrace_append hprefix tailTrace_1017733
  have hstable : (prefixWord ++ tailWord_1017733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017733).length < 2 ^ (prefixWord ++ tailWord_1017733).sum := by decide
  have hdescent : baseEnd_1017733 < baseStart_1017733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017792 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_1017792 : Nat := 118140960795 + 1017792 * 2 ^ 59
def prefixEnd_1017792 : Nat := 4983230072969 + 3 ^ 40 * 1017792 * 2
def baseEnd_1017792 : Nat := 232274001022660941253007

theorem tailTrace_1017792 : CollatzResearch.WordTrace tailWord_1017792 prefixEnd_1017792 232274001022660941253007 := by
  unfold tailWord_1017792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560961964360441939895815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24747949285813922586527753 18560961964360441939895815)
  ·
    refine ⟨27841442946540662909843723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560961964360441939895815 27841442946540662909843723)
    ·
      refine ⟨41762164419810994364765585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27841442946540662909843723 41762164419810994364765585)
      ·
        refine ⟨31321623314858245773574189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41762164419810994364765585 31321623314858245773574189)
        ·
          refine ⟨11745608743071842165090321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31321623314858245773574189 11745608743071842165090321)
          ·
            refine ⟨8809206557303881623817741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11745608743071842165090321 8809206557303881623817741)
            ·
              refine ⟨3303452458988955608931653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8809206557303881623817741 3303452458988955608931653)
              ·
                refine ⟨619397336060429176674685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3303452458988955608931653 619397336060429176674685)
                ·
                  refine ⟨232274001022660941253007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619397336060429176674685 232274001022660941253007)
                  ·
                    rfl

theorem cell21_1017792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_1017792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017792 prefixEnd_1017792 := by exact prefixLift 1017792
  have htrace : WordTrace (prefixWord ++ tailWord_1017792) baseStart_1017792 baseEnd_1017792 := by
    simpa [prefixWord, tailWord_1017792, baseEnd_1017792] using wordTrace_append hprefix tailTrace_1017792
  have hstable : (prefixWord ++ tailWord_1017792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017792).length < 2 ^ (prefixWord ++ tailWord_1017792).sum := by decide
  have hdescent : baseEnd_1017792 < baseStart_1017792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017806 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1017806 : Nat := 118140960795 + 1017806 * 2 ^ 59
def prefixEnd_1017806 : Nat := 4983230072969 + 3 ^ 40 * 1017806 * 2
def baseEnd_1017806 : Nat := 232277196013400028019645

theorem tailTrace_1017806 : CollatzResearch.WordTrace tailWord_1017806 prefixEnd_1017806 232277196013400028019645 := by
  unfold tailWord_1017806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640304318833770533850159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24748289700446776180534181 4640304318833770533850159)
  ·
    refine ⟨6960456478250655800775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640304318833770533850159 6960456478250655800775239)
    ·
      refine ⟨10440684717375983701162859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960456478250655800775239 10440684717375983701162859)
      ·
        refine ⟨15661027076063975551744289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440684717375983701162859 15661027076063975551744289)
        ·
          refine ⟨11745770307047981663808217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661027076063975551744289 11745770307047981663808217)
          ·
            refine ⟨8809327730285986247856163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11745770307047981663808217 8809327730285986247856163)
            ·
              refine ⟨13213991595428979371784245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809327730285986247856163 13213991595428979371784245)
              ·
                refine ⟨1238811712071466816104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13213991595428979371784245 1238811712071466816104773)
                ·
                  refine ⟨232277196013400028019645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238811712071466816104773 232277196013400028019645)
                  ·
                    rfl

theorem cell21_1017806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1017806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017806 prefixEnd_1017806 := by exact prefixLift 1017806
  have htrace : WordTrace (prefixWord ++ tailWord_1017806) baseStart_1017806 baseEnd_1017806 := by
    simpa [prefixWord, tailWord_1017806, baseEnd_1017806] using wordTrace_append hprefix tailTrace_1017806
  have hstable : (prefixWord ++ tailWord_1017806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017806).length < 2 ^ (prefixWord ++ tailWord_1017806).sum := by decide
  have hdescent : baseEnd_1017806 < baseStart_1017806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017885 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1017885 : Nat := 118140960795 + 1017885 * 2 ^ 59
def prefixEnd_1017885 : Nat := 4983230072969 + 3 ^ 40 * 1017885 * 2
def baseEnd_1017885 : Nat := 232295224889713446202817

theorem tailTrace_1017885 : CollatzResearch.WordTrace tailWord_1017885 prefixEnd_1017885 232295224889713446202817 := by
  unfold tailWord_1017885
  simp only [CollatzResearch.WordTrace]
  refine ⟨37125315917383960762927109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24750210611589307175284739 37125315917383960762927109)
  ·
    refine ⟨6960996734509492643048833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37125315917383960762927109 6960996734509492643048833)
    ·
      refine ⟨5220747550882119482286625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6960996734509492643048833 5220747550882119482286625)
      ·
        refine ⟨3915560663161589611714969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220747550882119482286625 3915560663161589611714969)
        ·
          refine ⟨2936670497371192208786227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915560663161589611714969 2936670497371192208786227)
          ·
            refine ⟨4405005746056788313179341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936670497371192208786227 4405005746056788313179341)
            ·
              refine ⟨1651877154771295617442253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4405005746056788313179341 1651877154771295617442253)
              ·
                refine ⟨619453933039235856540845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1651877154771295617442253 619453933039235856540845)
                ·
                  refine ⟨232295224889713446202817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619453933039235856540845 232295224889713446202817)
                  ·
                    rfl

theorem cell21_1017885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1017885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017885 prefixEnd_1017885 := by exact prefixLift 1017885
  have htrace : WordTrace (prefixWord ++ tailWord_1017885) baseStart_1017885 baseEnd_1017885 := by
    simpa [prefixWord, tailWord_1017885, baseEnd_1017885] using wordTrace_append hprefix tailTrace_1017885
  have hstable : (prefixWord ++ tailWord_1017885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017885).length < 2 ^ (prefixWord ++ tailWord_1017885).sum := by decide
  have hdescent : baseEnd_1017885 < baseStart_1017885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017902 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_1017902 : Nat := 118140960795 + 1017902 * 2 ^ 59
def prefixEnd_1017902 : Nat := 4983230072969 + 3 ^ 40 * 1017902 * 2
def baseEnd_1017902 : Nat := 232299104521325194419449

theorem tailTrace_1017902 : CollatzResearch.WordTrace tailWord_1017902 prefixEnd_1017902 232299104521325194419449 := by
  unfold tailWord_1017902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640741994790296583286995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24750623972214915110863973 4640741994790296583286995)
  ·
    refine ⟨6961112992185444874930493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640741994790296583286995 6961112992185444874930493)
    ·
      refine ⟨2610417372069541828098935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6961112992185444874930493 2610417372069541828098935)
      ·
        refine ⟨3915626058104312742148403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610417372069541828098935 3915626058104312742148403)
        ·
          refine ⟨5873439087156469113222605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915626058104312742148403 5873439087156469113222605)
          ·
            refine ⟨2202539657683675917458477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5873439087156469113222605 2202539657683675917458477)
            ·
              refine ⟨825952371631378469046929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202539657683675917458477 825952371631378469046929)
              ·
                refine ⟨619464278723533851785197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825952371631378469046929 619464278723533851785197)
                ·
                  refine ⟨232299104521325194419449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619464278723533851785197 232299104521325194419449)
                  ·
                    rfl

theorem cell21_1017902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_1017902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017902 prefixEnd_1017902 := by exact prefixLift 1017902
  have htrace : WordTrace (prefixWord ++ tailWord_1017902) baseStart_1017902 baseEnd_1017902 := by
    simpa [prefixWord, tailWord_1017902, baseEnd_1017902] using wordTrace_append hprefix tailTrace_1017902
  have hstable : (prefixWord ++ tailWord_1017902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017902).length < 2 ^ (prefixWord ++ tailWord_1017902).sum := by decide
  have hdescent : baseEnd_1017902 < baseStart_1017902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017913 : List Nat := [1, 2, 1, 5, 3, 1, 2, 6]
def baseStart_1017913 : Nat := 118140960795 + 1017913 * 2 ^ 59
def prefixEnd_1017913 : Nat := 4983230072969 + 3 ^ 40 * 1017913 * 2
def baseEnd_1017913 : Nat := 77433871623730539912031

theorem tailTrace_1017913 : CollatzResearch.WordTrace tailWord_1017913 prefixEnd_1017913 77433871623730539912031 := by
  unfold tailWord_1017913
  simp only [CollatzResearch.WordTrace]
  refine ⟨37126337161282521544946393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24750891440855014363297595 37126337161282521544946393)
  ·
    refine ⟨27844752870961891158709795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37126337161282521544946393 27844752870961891158709795)
    ·
      refine ⟨41767129306442836738064693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27844752870961891158709795 41767129306442836738064693)
      ·
        refine ⟨3915668372479015944193565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41767129306442836738064693 3915668372479015944193565)
        ·
          refine ⟨1468375639679630979072587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3915668372479015944193565 1468375639679630979072587)
          ·
            refine ⟨2202563459519446468608881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468375639679630979072587 2202563459519446468608881)
            ·
              refine ⟨1651922594639584851456661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202563459519446468608881 1651922594639584851456661)
              ·
                refine ⟨77433871623730539912031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1651922594639584851456661 77433871623730539912031)
                ·
                  rfl

theorem cell21_1017913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_1017913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017913 prefixEnd_1017913 := by exact prefixLift 1017913
  have htrace : WordTrace (prefixWord ++ tailWord_1017913) baseStart_1017913 baseEnd_1017913 := by
    simpa [prefixWord, tailWord_1017913, baseEnd_1017913] using wordTrace_append hprefix tailTrace_1017913
  have hstable : (prefixWord ++ tailWord_1017913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017913).length < 2 ^ (prefixWord ++ tailWord_1017913).sum := by decide
  have hdescent : baseEnd_1017913 < baseStart_1017913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017989 : List Nat := [1, 3, 1, 1, 5, 2, 3, 5]
def baseStart_1017989 : Nat := 118140960795 + 1017989 * 2 ^ 59
def prefixEnd_1017989 : Nat := 4983230072969 + 3 ^ 40 * 1017989 * 2
def baseEnd_1017989 : Nat := 77439653035544125489757

theorem tailTrace_1017989 : CollatzResearch.WordTrace tailWord_1017989 prefixEnd_1017989 77439653035544125489757 := by
  unfold tailWord_1017989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129109109007186524713021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24752739406004791016475347 37129109109007186524713021)
  ·
    refine ⟨13923415915877694946767383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37129109109007186524713021 13923415915877694946767383)
    ·
      refine ⟨20885123873816542420151075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923415915877694946767383 20885123873816542420151075)
      ·
        refine ⟨31327685810724813630226613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20885123873816542420151075 31327685810724813630226613)
        ·
          refine ⟨2936970544755451277833745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31327685810724813630226613 2936970544755451277833745)
          ·
            refine ⟨2202727908566588458375309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936970544755451277833745 2202727908566588458375309)
            ·
              refine ⟨826022965712470671890741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202727908566588458375309 826022965712470671890741)
              ·
                refine ⟨77439653035544125489757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 826022965712470671890741 77439653035544125489757)
                ·
                  rfl

theorem cell21_1017989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].length) (baseStart_1017989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1017989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1017989 prefixEnd_1017989 := by exact prefixLift 1017989
  have htrace : WordTrace (prefixWord ++ tailWord_1017989) baseStart_1017989 baseEnd_1017989 := by
    simpa [prefixWord, tailWord_1017989, baseEnd_1017989] using wordTrace_append hprefix tailTrace_1017989
  have hstable : (prefixWord ++ tailWord_1017989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017989).length < 2 ^ (prefixWord ++ tailWord_1017989).sum := by decide
  have hdescent : baseEnd_1017989 < baseStart_1017989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018020 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1018020 : Nat := 118140960795 + 1018020 * 2 ^ 59
def prefixEnd_1018020 : Nat := 4983230072969 + 3 ^ 40 * 1018020 * 2
def baseEnd_1018020 : Nat := 232326033728983211452541

theorem tailTrace_1018020 : CollatzResearch.WordTrace tailWord_1018020 prefixEnd_1018020 232326033728983211452541 := by
  unfold tailWord_1018020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565119885947439409545757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24753493181263252546061009 18565119885947439409545757)
  ·
    refine ⟨6961919957230289778579659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18565119885947439409545757 6961919957230289778579659)
    ·
      refine ⟨10442879935845434667869489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961919957230289778579659 10442879935845434667869489)
      ·
        refine ⟨7832159951884076000902117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10442879935845434667869489 7832159951884076000902117)
        ·
          refine ⟨1468529990978264250169147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7832159951884076000902117 1468529990978264250169147)
          ·
            refine ⟨2202794986467396375253721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468529990978264250169147 2202794986467396375253721)
            ·
              refine ⟨1652096239850547281440291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202794986467396375253721 1652096239850547281440291)
              ·
                refine ⟨2478144359775820922160437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652096239850547281440291 2478144359775820922160437)
                ·
                  refine ⟨232326033728983211452541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2478144359775820922160437 232326033728983211452541)
                  ·
                    rfl

theorem cell21_1018020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1018020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018020 prefixEnd_1018020 := by exact prefixLift 1018020
  have htrace : WordTrace (prefixWord ++ tailWord_1018020) baseStart_1018020 baseEnd_1018020 := by
    simpa [prefixWord, tailWord_1018020, baseEnd_1018020] using wordTrace_append hprefix tailTrace_1018020
  have hstable : (prefixWord ++ tailWord_1018020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018020).length < 2 ^ (prefixWord ++ tailWord_1018020).sum := by decide
  have hdescent : baseEnd_1018020 < baseStart_1018020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018031 : List Nat := [1, 1, 2, 1, 2, 3, 1, 10]
def baseStart_1018031 : Nat := 118140960795 + 1018031 * 2 ^ 59
def prefixEnd_1018031 : Nat := 4983230072969 + 3 ^ 40 * 1018031 * 2
def baseEnd_1018031 : Nat := 77442848026283212256395

theorem tailTrace_1018031 : CollatzResearch.WordTrace tailWord_1018031 prefixEnd_1018031 77442848026283212256395 := by
  unfold tailWord_1018031
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130640974855027697741947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24753760649903351798494631 37130640974855027697741947)
  ·
    refine ⟨55695961462282541546612921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37130640974855027697741947 55695961462282541546612921)
    ·
      refine ⟨41771971096711906159959691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55695961462282541546612921 41771971096711906159959691)
      ·
        refine ⟨62657956645067859239939537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41771971096711906159959691 62657956645067859239939537)
        ·
          refine ⟨46993467483800894429954653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62657956645067859239939537 46993467483800894429954653)
          ·
            refine ⟨17622550306425335411232995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46993467483800894429954653 17622550306425335411232995)
            ·
              refine ⟨26433825459638003116849493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17622550306425335411232995 26433825459638003116849493)
              ·
                refine ⟨77442848026283212256395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26433825459638003116849493 77442848026283212256395)
                ·
                  rfl

theorem cell21_1018031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_1018031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018031 prefixEnd_1018031 := by exact prefixLift 1018031
  have htrace : WordTrace (prefixWord ++ tailWord_1018031) baseStart_1018031 baseEnd_1018031 := by
    simpa [prefixWord, tailWord_1018031, baseEnd_1018031] using wordTrace_append hprefix tailTrace_1018031
  have hstable : (prefixWord ++ tailWord_1018031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018031).length < 2 ^ (prefixWord ++ tailWord_1018031).sum := by decide
  have hdescent : baseEnd_1018031 < baseStart_1018031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018048 : List Nat := [2, 1, 1, 2, 5, 2, 1, 7]
def baseStart_1018048 : Nat := 118140960795 + 1018048 * 2 ^ 59
def prefixEnd_1018048 : Nat := 4983230072969 + 3 ^ 40 * 1018048 * 2
def baseEnd_1018048 : Nat := 77444141236820461661939

theorem tailTrace_1018048 : CollatzResearch.WordTrace tailWord_1018048 prefixEnd_1018048 77444141236820461661939 := by
  unfold tailWord_1018048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565630507896719800555399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24754174010528959734073865 18565630507896719800555399)
  ·
    refine ⟨27848445761845079700833099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18565630507896719800555399 27848445761845079700833099)
    ·
      refine ⟨41772668642767619551249649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27848445761845079700833099 41772668642767619551249649)
      ·
        refine ⟨31329501482075714663437237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41772668642767619551249649 31329501482075714663437237)
        ·
          refine ⟨2937140763944598249697241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31329501482075714663437237 2937140763944598249697241)
          ·
            refine ⟨2202855572958448687272931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937140763944598249697241 2202855572958448687272931)
            ·
              refine ⟨3304283359437673030909397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202855572958448687272931 3304283359437673030909397)
              ·
                refine ⟨77444141236820461661939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3304283359437673030909397 77444141236820461661939)
                ·
                  rfl

theorem cell21_1018048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_1018048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018048 prefixEnd_1018048 := by exact prefixLift 1018048
  have htrace : WordTrace (prefixWord ++ tailWord_1018048) baseStart_1018048 baseEnd_1018048 := by
    simpa [prefixWord, tailWord_1018048, baseEnd_1018048] using wordTrace_append hprefix tailTrace_1018048
  have hstable : (prefixWord ++ tailWord_1018048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018048).length < 2 ^ (prefixWord ++ tailWord_1018048).sum := by decide
  have hdescent : baseEnd_1018048 < baseStart_1018048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018172 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_1018172 : Nat := 118140960795 + 1018172 * 2 ^ 59
def prefixEnd_1018172 : Nat := 4983230072969 + 3 ^ 40 * 1018172 * 2
def baseEnd_1018172 : Nat := 232360722199864724918897

theorem tailTrace_1018172 : CollatzResearch.WordTrace tailWord_1018172 prefixEnd_1018172 232360722199864724918897 := by
  unfold tailWord_1018172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567891833672104389312385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24757189111562805852416513 18567891833672104389312385)
  ·
    refine ⟨13925918875254078291984289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18567891833672104389312385 13925918875254078291984289)
    ·
      refine ⟨10444439156440558718988217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13925918875254078291984289 10444439156440558718988217)
      ·
        refine ⟨7833329367330419039241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444439156440558718988217 7833329367330419039241163)
        ·
          refine ⟨11749994050995628558861745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833329367330419039241163 11749994050995628558861745)
          ·
            refine ⟨8812495538246721419146309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749994050995628558861745 8812495538246721419146309)
            ·
              refine ⟨1652342913421260266089933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8812495538246721419146309 1652342913421260266089933)
              ·
                refine ⟨619628592532972599783725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652342913421260266089933 619628592532972599783725)
                ·
                  refine ⟨232360722199864724918897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619628592532972599783725 232360722199864724918897)
                  ·
                    rfl

theorem cell21_1018172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_1018172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018172 prefixEnd_1018172 := by exact prefixLift 1018172
  have htrace : WordTrace (prefixWord ++ tailWord_1018172) baseStart_1018172 baseEnd_1018172 := by
    simpa [prefixWord, tailWord_1018172, baseEnd_1018172] using wordTrace_append hprefix tailTrace_1018172
  have hstable : (prefixWord ++ tailWord_1018172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018172).length < 2 ^ (prefixWord ++ tailWord_1018172).sum := by decide
  have hdescent : baseEnd_1018172 < baseStart_1018172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018183 : List Nat := [1, 1, 4, 1, 2, 2, 10]
def baseStart_1018183 : Nat := 118140960795 + 1018183 * 2 ^ 59
def prefixEnd_1018183 : Nat := 4983230072969 + 3 ^ 40 * 1018183 * 2
def baseEnd_1018183 : Nat := 25818136949970127803949

theorem tailTrace_1018183 : CollatzResearch.WordTrace tailWord_1018183 prefixEnd_1018183 25818136949970127803949 := by
  unfold tailWord_1018183
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136184870304357657275203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24757456580202905104850135 37136184870304357657275203)
  ·
    refine ⟨55704277305456536485912805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37136184870304357657275203 55704277305456536485912805)
    ·
      refine ⟨10444551994773100591108651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55704277305456536485912805 10444551994773100591108651)
      ·
        refine ⟨15666827992159650886662977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444551994773100591108651 15666827992159650886662977)
        ·
          refine ⟨11750120994119738164997233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15666827992159650886662977 11750120994119738164997233)
          ·
            refine ⟨8812590745589803623747925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11750120994119738164997233 8812590745589803623747925)
            ·
              refine ⟨25818136949970127803949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8812590745589803623747925 25818136949970127803949)
              ·
                rfl

theorem cell21_1018183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_1018183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018183 prefixEnd_1018183 := by exact prefixLift 1018183
  have htrace : WordTrace (prefixWord ++ tailWord_1018183) baseStart_1018183 baseEnd_1018183 := by
    simpa [prefixWord, tailWord_1018183, baseEnd_1018183] using wordTrace_append hprefix tailTrace_1018183
  have hstable : (prefixWord ++ tailWord_1018183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018183).length < 2 ^ (prefixWord ++ tailWord_1018183).sum := by decide
  have hdescent : baseEnd_1018183 < baseStart_1018183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018231 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 3]
def baseStart_1018231 : Nat := 118140960795 + 1018231 * 2 ^ 59
def prefixEnd_1018231 : Nat := 4983230072969 + 3 ^ 40 * 1018231 * 2
def baseEnd_1018231 : Nat := 232374186803693733435443

theorem tailTrace_1018231 : CollatzResearch.WordTrace tailWord_1018231 prefixEnd_1018231 232374186803693733435443 := by
  unfold tailWord_1018231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137935574130461855022547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24758623716086974570015031 37137935574130461855022547)
  ·
    refine ⟨55706903361195692782533821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37137935574130461855022547 55706903361195692782533821)
    ·
      refine ⟨20890088760448384793450183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55706903361195692782533821 20890088760448384793450183)
      ·
        refine ⟨31335133140672577190175275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20890088760448384793450183 31335133140672577190175275)
        ·
          refine ⟨47002699711008865785262913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31335133140672577190175275 47002699711008865785262913)
          ·
            refine ⟨35252024783256649338947185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47002699711008865785262913 35252024783256649338947185)
            ·
              refine ⟨26439018587442487004210389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35252024783256649338947185 26439018587442487004210389)
              ·
                refine ⟨619664498143183289161181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26439018587442487004210389 619664498143183289161181)
                ·
                  refine ⟨232374186803693733435443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619664498143183289161181 232374186803693733435443)
                  ·
                    rfl

theorem cell21_1018231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].length) (baseStart_1018231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018231 prefixEnd_1018231 := by exact prefixLift 1018231
  have htrace : WordTrace (prefixWord ++ tailWord_1018231) baseStart_1018231 baseEnd_1018231 := by
    simpa [prefixWord, tailWord_1018231, baseEnd_1018231] using wordTrace_append hprefix tailTrace_1018231
  have hstable : (prefixWord ++ tailWord_1018231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018231).length < 2 ^ (prefixWord ++ tailWord_1018231).sum := by decide
  have hdescent : baseEnd_1018231 < baseStart_1018231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018245 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1018245 : Nat := 118140960795 + 1018245 * 2 ^ 59
def prefixEnd_1018245 : Nat := 4983230072969 + 3 ^ 40 * 1018245 * 2
def baseEnd_1018245 : Nat := 232377381794432820202081

theorem tailTrace_1018245 : CollatzResearch.WordTrace tailWord_1018245 prefixEnd_1018245 232377381794432820202081 := by
  unfold tailWord_1018245
  simp only [CollatzResearch.WordTrace]
  refine ⟨37138446196079742246032189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24758964130719828164021459 37138446196079742246032189)
  ·
    refine ⟨13926917323529903342262071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37138446196079742246032189 13926917323529903342262071)
    ·
      refine ⟨20890375985294855013393107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926917323529903342262071 20890375985294855013393107)
      ·
        refine ⟨31335563977942282520089661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20890375985294855013393107 31335563977942282520089661)
        ·
          refine ⟨11750836491728355945033623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31335563977942282520089661 11750836491728355945033623)
          ·
            refine ⟨17626254737592533917550435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750836491728355945033623 17626254737592533917550435)
            ·
              refine ⟨26439382106388800876325653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626254737592533917550435 26439382106388800876325653)
              ·
                refine ⟨1239346036236975041077765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26439382106388800876325653 1239346036236975041077765)
                ·
                  refine ⟨232377381794432820202081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239346036236975041077765 232377381794432820202081)
                  ·
                    rfl

theorem cell21_1018245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1018245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018245 prefixEnd_1018245 := by exact prefixLift 1018245
  have htrace : WordTrace (prefixWord ++ tailWord_1018245) baseStart_1018245 baseEnd_1018245 := by
    simpa [prefixWord, tailWord_1018245, baseEnd_1018245] using wordTrace_append hprefix tailTrace_1018245
  have hstable : (prefixWord ++ tailWord_1018245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018245).length < 2 ^ (prefixWord ++ tailWord_1018245).sum := by decide
  have hdescent : baseEnd_1018245 < baseStart_1018245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018341 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1018341 : Nat := 118140960795 + 1018341 * 2 ^ 59
def prefixEnd_1018341 : Nat := 4983230072969 + 3 ^ 40 * 1018341 * 2
def baseEnd_1018341 : Nat := 232399290302357986601885

theorem tailTrace_1018341 : CollatzResearch.WordTrace tailWord_1018341 prefixEnd_1018341 232399290302357986601885 := by
  unfold tailWord_1018341
  simp only [CollatzResearch.WordTrace]
  refine ⟨37141947603731950641526877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24761298402487967094351251 37141947603731950641526877)
  ·
    refine ⟨13928230351399481490572579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37141947603731950641526877 13928230351399481490572579)
    ·
      refine ⟨20892345527099222235858869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13928230351399481490572579 20892345527099222235858869)
      ·
        refine ⟨1958657393165552084611769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20892345527099222235858869 1958657393165552084611769)
        ·
          refine ⟨1468993044874164063458827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958657393165552084611769 1468993044874164063458827)
          ·
            refine ⟨2203489567311246095188241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468993044874164063458827 2203489567311246095188241)
            ·
              refine ⟨1652617175483434571391181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203489567311246095188241 1652617175483434571391181)
              ·
                refine ⟨619731440806287964271693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652617175483434571391181 619731440806287964271693)
                ·
                  refine ⟨232399290302357986601885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619731440806287964271693 232399290302357986601885)
                  ·
                    rfl

theorem cell21_1018341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1018341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018341 prefixEnd_1018341 := by exact prefixLift 1018341
  have htrace : WordTrace (prefixWord ++ tailWord_1018341) baseStart_1018341 baseEnd_1018341 := by
    simpa [prefixWord, tailWord_1018341, baseEnd_1018341] using wordTrace_append hprefix tailTrace_1018341
  have hstable : (prefixWord ++ tailWord_1018341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018341).length < 2 ^ (prefixWord ++ tailWord_1018341).sum := by decide
  have hdescent : baseEnd_1018341 < baseStart_1018341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018397 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1018397 : Nat := 118140960795 + 1018397 * 2 ^ 59
def prefixEnd_1018397 : Nat := 4983230072969 + 3 ^ 40 * 1018397 * 2
def baseEnd_1018397 : Nat := 232412070265314333668437

theorem tailTrace_1018397 : CollatzResearch.WordTrace tailWord_1018397 prefixEnd_1018397 232412070265314333668437 := by
  unfold tailWord_1018397
  simp only [CollatzResearch.WordTrace]
  refine ⟨37143990091529072205565445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24762660061019381470376963 37143990091529072205565445)
  ·
    refine ⟨6964498142161701038543521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37143990091529072205565445 6964498142161701038543521)
    ·
      refine ⟨5223373606621275778907641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6964498142161701038543521 5223373606621275778907641)
      ·
        refine ⟨3917530204965956834180731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5223373606621275778907641 3917530204965956834180731)
        ·
          refine ⟨5876295307448935251271097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917530204965956834180731 5876295307448935251271097)
          ·
            refine ⟨4407221480586701438453323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876295307448935251271097 4407221480586701438453323)
            ·
              refine ⟨6610832220880052157679985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407221480586701438453323 6610832220880052157679985)
              ·
                refine ⟨4958124165660039118259989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610832220880052157679985 4958124165660039118259989)
                ·
                  refine ⟨232412070265314333668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4958124165660039118259989 232412070265314333668437)
                  ·
                    rfl

theorem cell21_1018397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1018397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018397 prefixEnd_1018397 := by exact prefixLift 1018397
  have htrace : WordTrace (prefixWord ++ tailWord_1018397) baseStart_1018397 baseEnd_1018397 := by
    simpa [prefixWord, tailWord_1018397, baseEnd_1018397] using wordTrace_append hprefix tailTrace_1018397
  have hstable : (prefixWord ++ tailWord_1018397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018397).length < 2 ^ (prefixWord ++ tailWord_1018397).sum := by decide
  have hdescent : baseEnd_1018397 < baseStart_1018397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018428 : List Nat := [2, 2, 2, 2, 3, 2, 2, 6]
def baseStart_1018428 : Nat := 118140960795 + 1018428 * 2 ^ 59
def prefixEnd_1018428 : Nat := 4983230072969 + 3 ^ 40 * 1018428 * 2
def baseEnd_1018428 : Nat := 77473048295888389550569

theorem tailTrace_1018428 : CollatzResearch.WordTrace tailWord_1018428 prefixEnd_1018428 77473048295888389550569 := by
  unfold tailWord_1018428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572560377208382249971969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24763413836277842999962625 18572560377208382249971969)
  ·
    refine ⟨13929420282906286687478977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18572560377208382249971969 13929420282906286687478977)
    ·
      refine ⟨10447065212179715015609233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13929420282906286687478977 10447065212179715015609233)
      ·
        refine ⟨7835298909134786261706925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10447065212179715015609233 7835298909134786261706925)
        ·
          refine ⟨2938237090925544848140097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7835298909134786261706925 2938237090925544848140097)
          ·
            refine ⟨2203677818194158636105073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938237090925544848140097 2203677818194158636105073)
            ·
              refine ⟨1652758363645618977078805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203677818194158636105073 1652758363645618977078805)
              ·
                refine ⟨77473048295888389550569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1652758363645618977078805 77473048295888389550569)
                ·
                  rfl

theorem cell21_1018428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_1018428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018428 prefixEnd_1018428 := by exact prefixLift 1018428
  have htrace : WordTrace (prefixWord ++ tailWord_1018428) baseStart_1018428 baseEnd_1018428 := by
    simpa [prefixWord, tailWord_1018428, baseEnd_1018428] using wordTrace_append hprefix tailTrace_1018428
  have hstable : (prefixWord ++ tailWord_1018428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018428).length < 2 ^ (prefixWord ++ tailWord_1018428).sum := by decide
  have hdescent : baseEnd_1018428 < baseStart_1018428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018456 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1018456 : Nat := 118140960795 + 1018456 * 2 ^ 59
def prefixEnd_1018456 : Nat := 4983230072969 + 3 ^ 40 * 1018456 * 2
def baseEnd_1018456 : Nat := 232425534869143342184983

theorem tailTrace_1018456 : CollatzResearch.WordTrace tailWord_1018456 prefixEnd_1018456 232425534869143342184983 := by
  unfold tailWord_1018456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573070999157662640981611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24764094665543550187975481 18573070999157662640981611)
  ·
    refine ⟨27859606498736493961472417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18573070999157662640981611 27859606498736493961472417)
    ·
      refine ⟨20894704874052370471104313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27859606498736493961472417 20894704874052370471104313)
      ·
        refine ⟨15671028655539277853328235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20894704874052370471104313 15671028655539277853328235)
        ·
          refine ⟨23506542983308916779992353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671028655539277853328235 23506542983308916779992353)
          ·
            refine ⟨17629907237481687584994265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23506542983308916779992353 17629907237481687584994265)
            ·
              refine ⟨13222430428111265688745699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17629907237481687584994265 13222430428111265688745699)
              ·
                refine ⟨19833645642166898533118549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222430428111265688745699 19833645642166898533118549)
                ·
                  refine ⟨232425534869143342184983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19833645642166898533118549 232425534869143342184983)
                  ·
                    rfl

theorem cell21_1018456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1018456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018456 prefixEnd_1018456 := by exact prefixLift 1018456
  have htrace : WordTrace (prefixWord ++ tailWord_1018456) baseStart_1018456 baseEnd_1018456 := by
    simpa [prefixWord, tailWord_1018456, baseEnd_1018456] using wordTrace_append hprefix tailTrace_1018456
  have hstable : (prefixWord ++ tailWord_1018456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018456).length < 2 ^ (prefixWord ++ tailWord_1018456).sum := by decide
  have hdescent : baseEnd_1018456 < baseStart_1018456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018462 : List Nat := [4, 4, 1, 2, 1, 9]
def baseStart_1018462 : Nat := 118140960795 + 1018462 * 2 ^ 59
def prefixEnd_1018462 : Nat := 4983230072969 + 3 ^ 40 * 1018462 * 2
def baseEnd_1018462 : Nat := 8608403857440320929073

theorem tailTrace_1018462 : CollatzResearch.WordTrace tailWord_1018462 prefixEnd_1018462 8608403857440320929073 := by
  unfold tailWord_1018462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643295104536698538335205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24764240557529058871121093 4643295104536698538335205)
  ·
    refine ⟨870617832100630975937851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4643295104536698538335205 870617832100630975937851)
    ·
      refine ⟨1305926748150946463906777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870617832100630975937851 1305926748150946463906777)
      ·
        refine ⟨979445061113209847930083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305926748150946463906777 979445061113209847930083)
        ·
          refine ⟨1469167591669814771895125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979445061113209847930083 1469167591669814771895125)
          ·
            refine ⟨8608403857440320929073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1469167591669814771895125 8608403857440320929073)
            ·
              rfl

theorem cell21_1018462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 9].length) (baseStart_1018462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018462 prefixEnd_1018462 := by exact prefixLift 1018462
  have htrace : WordTrace (prefixWord ++ tailWord_1018462) baseStart_1018462 baseEnd_1018462 := by
    simpa [prefixWord, tailWord_1018462, baseEnd_1018462] using wordTrace_append hprefix tailTrace_1018462
  have hstable : (prefixWord ++ tailWord_1018462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018462).length < 2 ^ (prefixWord ++ tailWord_1018462).sum := by decide
  have hdescent : baseEnd_1018462 < baseStart_1018462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018476 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1018476 : Nat := 118140960795 + 1018476 * 2 ^ 59
def prefixEnd_1018476 : Nat := 4983230072969 + 3 ^ 40 * 1018476 * 2
def baseEnd_1018476 : Nat := 232430099141627751851609

theorem tailTrace_1018476 : CollatzResearch.WordTrace tailWord_1018476 prefixEnd_1018476 232430099141627751851609 := by
  unfold tailWord_1018476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573435729121434348845641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24764580972161912465127521 18573435729121434348845641)
  ·
    refine ⟨13930076796841075761634231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18573435729121434348845641 13930076796841075761634231)
    ·
      refine ⟨20895115195261613642451347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13930076796841075761634231 20895115195261613642451347)
      ·
        refine ⟨31342672792892420463677021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20895115195261613642451347 31342672792892420463677021)
        ·
          refine ⟨11753502297334657673878883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31342672792892420463677021 11753502297334657673878883)
          ·
            refine ⟨17630253446001986510818325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753502297334657673878883 17630253446001986510818325)
            ·
              refine ⟨826418130281343117694609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17630253446001986510818325 826418130281343117694609)
              ·
                refine ⟨619813597711007338270957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826418130281343117694609 619813597711007338270957)
                ·
                  refine ⟨232430099141627751851609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619813597711007338270957 232430099141627751851609)
                  ·
                    rfl

theorem cell21_1018476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1018476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018476 prefixEnd_1018476 := by exact prefixLift 1018476
  have htrace : WordTrace (prefixWord ++ tailWord_1018476) baseStart_1018476 baseEnd_1018476 := by
    simpa [prefixWord, tailWord_1018476, baseEnd_1018476] using wordTrace_append hprefix tailTrace_1018476
  have hstable : (prefixWord ++ tailWord_1018476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018476).length < 2 ^ (prefixWord ++ tailWord_1018476).sum := by decide
  have hdescent : baseEnd_1018476 < baseStart_1018476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018487 : List Nat := [1, 1, 3, 1, 1, 3, 5, 6]
def baseStart_1018487 : Nat := 118140960795 + 1018487 * 2 ^ 59
def prefixEnd_1018487 : Nat := 4983230072969 + 3 ^ 40 * 1018487 * 2
def baseEnd_1018487 : Nat := 77477536497164725722751

theorem tailTrace_1018487 : CollatzResearch.WordTrace tailWord_1018487 prefixEnd_1018487 77477536497164725722751 := by
  unfold tailWord_1018487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37147272661203017576341715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24764848440802011717561143 37147272661203017576341715)
  ·
    refine ⟨55720908991804526364512573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37147272661203017576341715 55720908991804526364512573)
    ·
      refine ⟨20895340871926697386692215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55720908991804526364512573 20895340871926697386692215)
      ·
        refine ⟨31343011307890046080038323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20895340871926697386692215 31343011307890046080038323)
        ·
          refine ⟨47014516961835069120057485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31343011307890046080038323 47014516961835069120057485)
          ·
            refine ⟨17630443860688150920021557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47014516961835069120057485 17630443860688150920021557)
            ·
              refine ⟨1652854111939514148752021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17630443860688150920021557 1652854111939514148752021)
              ·
                refine ⟨77477536497164725722751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1652854111939514148752021 77477536497164725722751)
                ·
                  rfl

theorem cell21_1018487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_1018487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018487 prefixEnd_1018487 := by exact prefixLift 1018487
  have htrace : WordTrace (prefixWord ++ tailWord_1018487) baseStart_1018487 baseEnd_1018487 := by
    simpa [prefixWord, tailWord_1018487, baseEnd_1018487] using wordTrace_append hprefix tailTrace_1018487
  have hstable : (prefixWord ++ tailWord_1018487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018487).length < 2 ^ (prefixWord ++ tailWord_1018487).sum := by decide
  have hdescent : baseEnd_1018487 < baseStart_1018487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018600 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_1018600 : Nat := 118140960795 + 1018600 * 2 ^ 59
def prefixEnd_1018600 : Nat := 4983230072969 + 3 ^ 40 * 1018600 * 2
def baseEnd_1018600 : Nat := 232458397631031091784689

theorem tailTrace_1018600 : CollatzResearch.WordTrace tailWord_1018600 prefixEnd_1018600 232458397631031091784689 := by
  unfold tailWord_1018600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18575697054896818937602627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24767596073195758583470169 18575697054896818937602627)
  ·
    refine ⟨27863545582345228406403941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18575697054896818937602627 27863545582345228406403941)
    ·
      refine ⟨5224414796689730326200739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27863545582345228406403941 5224414796689730326200739)
      ·
        refine ⟨7836622195034595489301109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5224414796689730326200739 7836622195034595489301109)
        ·
          refine ⟨734683330784493327121979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7836622195034595489301109 734683330784493327121979)
          ·
            refine ⟨1102024996176739990682969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734683330784493327121979 1102024996176739990682969)
            ·
              refine ⟨826518747132554993012227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102024996176739990682969 826518747132554993012227)
              ·
                refine ⟨1239778120698832489518341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826518747132554993012227 1239778120698832489518341)
                ·
                  refine ⟨232458397631031091784689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239778120698832489518341 232458397631031091784689)
                  ·
                    rfl

theorem cell21_1018600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_1018600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018600 prefixEnd_1018600 := by exact prefixLift 1018600
  have htrace : WordTrace (prefixWord ++ tailWord_1018600) baseStart_1018600 baseEnd_1018600 := by
    simpa [prefixWord, tailWord_1018600, baseEnd_1018600] using wordTrace_append hprefix tailTrace_1018600
  have hstable : (prefixWord ++ tailWord_1018600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018600).length < 2 ^ (prefixWord ++ tailWord_1018600).sum := by decide
  have hdescent : baseEnd_1018600 < baseStart_1018600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018656 : List Nat := [2, 1, 1, 5, 1, 4, 1, 6]
def baseStart_1018656 : Nat := 118140960795 + 1018656 * 2 ^ 59
def prefixEnd_1018656 : Nat := 4983230072969 + 3 ^ 40 * 1018656 * 2
def baseEnd_1018656 : Nat := 77490392531329146283747

theorem tailTrace_1018656 : CollatzResearch.WordTrace tailWord_1018656 prefixEnd_1018656 77490392531329146283747 := by
  unfold tailWord_1018656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576718298795379719621911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24768957731727172959495881 18576718298795379719621911)
  ·
    refine ⟨27865077448193069579432867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18576718298795379719621911 27865077448193069579432867)
    ·
      refine ⟨41797616172289604369149301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865077448193069579432867 41797616172289604369149301)
      ·
        refine ⟨3918526516152150409607747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41797616172289604369149301 3918526516152150409607747)
        ·
          refine ⟨5877789774228225614411621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918526516152150409607747 5877789774228225614411621)
          ·
            refine ⟨1102085582667792302702179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5877789774228225614411621 1102085582667792302702179)
            ·
              refine ⟨1653128374001688454053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102085582667792302702179 1653128374001688454053269)
              ·
                refine ⟨77490392531329146283747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1653128374001688454053269 77490392531329146283747)
                ·
                  rfl

theorem cell21_1018656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_1018656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018656 prefixEnd_1018656 := by exact prefixLift 1018656
  have htrace : WordTrace (prefixWord ++ tailWord_1018656) baseStart_1018656 baseEnd_1018656 := by
    simpa [prefixWord, tailWord_1018656, baseEnd_1018656] using wordTrace_append hprefix tailTrace_1018656
  have hstable : (prefixWord ++ tailWord_1018656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018656).length < 2 ^ (prefixWord ++ tailWord_1018656).sum := by decide
  have hdescent : baseEnd_1018656 < baseStart_1018656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018684 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1018684 : Nat := 118140960795 + 1018684 * 2 ^ 59
def prefixEnd_1018684 : Nat := 4983230072969 + 3 ^ 40 * 1018684 * 2
def baseEnd_1018684 : Nat := 232477567575465612384517

theorem tailTrace_1018684 : CollatzResearch.WordTrace tailWord_1018684 prefixEnd_1018684 232477567575465612384517 := by
  unfold tailWord_1018684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577228920744660110631553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24769638560992880147508737 18577228920744660110631553)
  ·
    refine ⟨13932921690558495082973665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18577228920744660110631553 13932921690558495082973665)
    ·
      refine ⟨10449691267918871312230249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13932921690558495082973665 10449691267918871312230249)
      ·
        refine ⟨7837268450939153484172687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10449691267918871312230249 7837268450939153484172687)
        ·
          refine ⟨11755902676408730226259031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837268450939153484172687 11755902676408730226259031)
          ·
            refine ⟨17633854014613095339388547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11755902676408730226259031 17633854014613095339388547)
            ·
              refine ⟨26450781021919643009082821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633854014613095339388547 26450781021919643009082821)
              ·
                refine ⟨4959521441609933064203029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26450781021919643009082821 4959521441609933064203029)
                ·
                  refine ⟨232477567575465612384517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4959521441609933064203029 232477567575465612384517)
                  ·
                    rfl

theorem cell21_1018684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1018684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018684 prefixEnd_1018684 := by exact prefixLift 1018684
  have htrace : WordTrace (prefixWord ++ tailWord_1018684) baseStart_1018684 baseEnd_1018684 := by
    simpa [prefixWord, tailWord_1018684, baseEnd_1018684] using wordTrace_append hprefix tailTrace_1018684
  have hstable : (prefixWord ++ tailWord_1018684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018684).length < 2 ^ (prefixWord ++ tailWord_1018684).sum := by decide
  have hdescent : baseEnd_1018684 < baseStart_1018684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018687 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 3]
def baseStart_1018687 : Nat := 118140960795 + 1018687 * 2 ^ 59
def prefixEnd_1018687 : Nat := 4983230072969 + 3 ^ 40 * 1018687 * 2
def baseEnd_1018687 : Nat := 232478252216338273834511

theorem tailTrace_1018687 : CollatzResearch.WordTrace tailWord_1018687 prefixEnd_1018687 232478252216338273834511 := by
  unfold tailWord_1018687
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154567260478451733622315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24769711506985634489081543 37154567260478451733622315)
  ·
    refine ⟨55731850890717677600433473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37154567260478451733622315 55731850890717677600433473)
    ·
      refine ⟨41798888168038258200325105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55731850890717677600433473 41798888168038258200325105)
      ·
        refine ⟨31349166126028693650243829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41798888168038258200325105 31349166126028693650243829)
        ·
          refine ⟨2938984324315190029710359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31349166126028693650243829 2938984324315190029710359)
          ·
            refine ⟨4408476486472785044565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938984324315190029710359 4408476486472785044565539)
            ·
              refine ⟨6612714729709177566848309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408476486472785044565539 6612714729709177566848309)
              ·
                refine ⟨619942005910235396892029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6612714729709177566848309 619942005910235396892029)
                ·
                  refine ⟨232478252216338273834511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619942005910235396892029 232478252216338273834511)
                  ·
                    rfl

theorem cell21_1018687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 3].length) (baseStart_1018687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018687 prefixEnd_1018687 := by exact prefixLift 1018687
  have htrace : WordTrace (prefixWord ++ tailWord_1018687) baseStart_1018687 baseEnd_1018687 := by
    simpa [prefixWord, tailWord_1018687, baseEnd_1018687] using wordTrace_append hprefix tailTrace_1018687
  have hstable : (prefixWord ++ tailWord_1018687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018687).length < 2 ^ (prefixWord ++ tailWord_1018687).sum := by decide
  have hdescent : baseEnd_1018687 < baseStart_1018687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018870 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1018870 : Nat := 118140960795 + 1018870 * 2 ^ 59
def prefixEnd_1018870 : Nat := 4983230072969 + 3 ^ 40 * 1018870 * 2
def baseEnd_1018870 : Nat := 232520015309570622284137

theorem tailTrace_1018870 : CollatzResearch.WordTrace tailWord_1018870 prefixEnd_1018870 232520015309570622284137 := by
  unfold tailWord_1018870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322577613675967124220879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24774161212543649325022709 2322577613675967124220879)
  ·
    refine ⟨3483866420513950686331319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322577613675967124220879 3483866420513950686331319)
    ·
      refine ⟨5225799630770926029496979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483866420513950686331319 5225799630770926029496979)
      ·
        refine ⟨7838699446156389044245469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225799630770926029496979 7838699446156389044245469)
        ·
          refine ⟨2939512292308645891592051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7838699446156389044245469 2939512292308645891592051)
          ·
            refine ⟨4409268438462968837388077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939512292308645891592051 4409268438462968837388077)
            ·
              refine ⟨1653475664423613314020529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409268438462968837388077 1653475664423613314020529)
              ·
                refine ⟨1240106748317709985515397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653475664423613314020529 1240106748317709985515397)
                ·
                  refine ⟨232520015309570622284137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240106748317709985515397 232520015309570622284137)
                  ·
                    rfl

theorem cell21_1018870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1018870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018870 prefixEnd_1018870 := by exact prefixLift 1018870
  have htrace : WordTrace (prefixWord ++ tailWord_1018870) baseStart_1018870 baseEnd_1018870 := by
    simpa [prefixWord, tailWord_1018870, baseEnd_1018870] using wordTrace_append hprefix tailTrace_1018870
  have hstable : (prefixWord ++ tailWord_1018870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018870).length < 2 ^ (prefixWord ++ tailWord_1018870).sum := by decide
  have hdescent : baseEnd_1018870 < baseStart_1018870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018915 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 3]
def baseStart_1018915 : Nat := 118140960795 + 1018915 * 2 ^ 59
def prefixEnd_1018915 : Nat := 4983230072969 + 3 ^ 40 * 1018915 * 2
def baseEnd_1018915 : Nat := 232530284922660544034045

theorem tailTrace_1018915 : CollatzResearch.WordTrace tailWord_1018915 prefixEnd_1018915 232530284922660544034045 := by
  unfold tailWord_1018915
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162883103652446672922199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24775255402434964448614799 37162883103652446672922199)
  ·
    refine ⟨55744324655478670009383299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37162883103652446672922199 55744324655478670009383299)
    ·
      refine ⟨83616486983218005014074949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55744324655478670009383299 83616486983218005014074949)
      ·
        refine ⟨15678091309353375940139053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83616486983218005014074949 15678091309353375940139053)
        ·
          refine ⟨5879284241007515977552145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15678091309353375940139053 5879284241007515977552145)
          ·
            refine ⟨4409463180755636983164109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879284241007515977552145 4409463180755636983164109)
            ·
              refine ⟨1653548692783363868686541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409463180755636983164109 1653548692783363868686541)
              ·
                refine ⟨620080759793761450757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1653548692783363868686541 620080759793761450757453)
                ·
                  refine ⟨232530284922660544034045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620080759793761450757453 232530284922660544034045)
                  ·
                    rfl

theorem cell21_1018915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].length) (baseStart_1018915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018915 prefixEnd_1018915 := by exact prefixLift 1018915
  have htrace : WordTrace (prefixWord ++ tailWord_1018915) baseStart_1018915 baseEnd_1018915 := by
    simpa [prefixWord, tailWord_1018915, baseEnd_1018915] using wordTrace_append hprefix tailTrace_1018915
  have hstable : (prefixWord ++ tailWord_1018915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018915).length < 2 ^ (prefixWord ++ tailWord_1018915).sum := by decide
  have hdescent : baseEnd_1018915 < baseStart_1018915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018932 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1018932 : Nat := 118140960795 + 1018932 * 2 ^ 59
def prefixEnd_1018932 : Nat := 4983230072969 + 3 ^ 40 * 1018932 * 2
def baseEnd_1018932 : Nat := 232534164554272292250677

theorem tailTrace_1018932 : CollatzResearch.WordTrace tailWord_1018932 prefixEnd_1018932 232534164554272292250677 := by
  unfold tailWord_1018932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581751572295429288145525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24775668763060572384194033 18581751572295429288145525)
  ·
    refine ⟨1742039209902696495763643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18581751572295429288145525 1742039209902696495763643)
    ·
      refine ⟨2613058814854044743645465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742039209902696495763643 2613058814854044743645465)
      ·
        refine ⟨1959794111140533557734099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613058814854044743645465 1959794111140533557734099)
        ·
          refine ⟨2939691166710800336601149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959794111140533557734099 2939691166710800336601149)
          ·
            refine ⟨1102384187516550126225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2939691166710800336601149 1102384187516550126225431)
            ·
              refine ⟨1653576281274825189338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102384187516550126225431 1653576281274825189338147)
              ·
                refine ⟨2480364421912237784007221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653576281274825189338147 2480364421912237784007221)
                ·
                  refine ⟨232534164554272292250677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2480364421912237784007221 232534164554272292250677)
                  ·
                    rfl

theorem cell21_1018932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1018932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1018932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1018932 prefixEnd_1018932 := by exact prefixLift 1018932
  have htrace : WordTrace (prefixWord ++ tailWord_1018932) baseStart_1018932 baseEnd_1018932 := by
    simpa [prefixWord, tailWord_1018932, baseEnd_1018932] using wordTrace_append hprefix tailTrace_1018932
  have hstable : (prefixWord ++ tailWord_1018932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018932).length < 2 ^ (prefixWord ++ tailWord_1018932).sum := by decide
  have hdescent : baseEnd_1018932 < baseStart_1018932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019039 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 4]
def baseStart_1019039 : Nat := 118140960795 + 1019039 * 2 ^ 59
def prefixEnd_1019039 : Nat := 4983230072969 + 3 ^ 40 * 1019039 * 2
def baseEnd_1019039 : Nat := 232558583412063883967125

theorem tailTrace_1019039 : CollatzResearch.WordTrace tailWord_1019039 prefixEnd_1019039 232558583412063883967125 := by
  unfold tailWord_1019039
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167405755203215850436171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24778270503468810566957447 37167405755203215850436171)
  ·
    refine ⟨55751108632804823775654257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37167405755203215850436171 55751108632804823775654257)
    ·
      refine ⟨41813331474603617831740693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55751108632804823775654257 41813331474603617831740693)
      ·
        refine ⟨1959999912872044585862845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41813331474603617831740693 1959999912872044585862845)
        ·
          refine ⟨734999967327016719698567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1959999912872044585862845 734999967327016719698567)
          ·
            refine ⟨1102499950990525079547851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734999967327016719698567 1102499950990525079547851)
            ·
              refine ⟨1653749926485787619321777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102499950990525079547851 1653749926485787619321777)
              ·
                refine ⟨1240312444864340714491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653749926485787619321777 1240312444864340714491333)
                ·
                  refine ⟨232558583412063883967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240312444864340714491333 232558583412063883967125)
                  ·
                    rfl

theorem cell21_1019039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].length) (baseStart_1019039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019039 prefixEnd_1019039 := by exact prefixLift 1019039
  have htrace : WordTrace (prefixWord ++ tailWord_1019039) baseStart_1019039 baseEnd_1019039 := by
    simpa [prefixWord, tailWord_1019039, baseEnd_1019039] using wordTrace_append hprefix tailTrace_1019039
  have hstable : (prefixWord ++ tailWord_1019039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019039).length < 2 ^ (prefixWord ++ tailWord_1019039).sum := by decide
  have hdescent : baseEnd_1019039 < baseStart_1019039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019101 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1019101 : Nat := 118140960795 + 1019101 * 2 ^ 59
def prefixEnd_1019101 : Nat := 4983230072969 + 3 ^ 40 * 1019101 * 2
def baseEnd_1019101 : Nat := 232572732656765553933665

theorem tailTrace_1019101 : CollatzResearch.WordTrace tailWord_1019101 prefixEnd_1019101 232572732656765553933665 := by
  unfold tailWord_1019101
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169667080978600439193157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24779778053985733626128771 37169667080978600439193157)
  ·
    refine ⟨6969312577683487582348717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37169667080978600439193157 6969312577683487582348717)
    ·
      refine ⟨2613492216631307843380769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6969312577683487582348717 2613492216631307843380769)
      ·
        refine ⟨1960119162473480882535577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613492216631307843380769 1960119162473480882535577)
        ·
          refine ⟨1470089371855110661901683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960119162473480882535577 1470089371855110661901683)
          ·
            refine ⟨2205134057782665992852525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470089371855110661901683 2205134057782665992852525)
            ·
              refine ⟨826925271668499747319697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2205134057782665992852525 826925271668499747319697)
              ·
                refine ⟨620193953751374810489773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826925271668499747319697 620193953751374810489773)
                ·
                  refine ⟨232572732656765553933665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620193953751374810489773 232572732656765553933665)
                  ·
                    rfl

theorem cell21_1019101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1019101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019101 prefixEnd_1019101 := by exact prefixLift 1019101
  have htrace : WordTrace (prefixWord ++ tailWord_1019101) baseStart_1019101 baseEnd_1019101 := by
    simpa [prefixWord, tailWord_1019101, baseEnd_1019101] using wordTrace_append hprefix tailTrace_1019101
  have hstable : (prefixWord ++ tailWord_1019101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019101).length < 2 ^ (prefixWord ++ tailWord_1019101).sum := by decide
  have hdescent : baseEnd_1019101 < baseStart_1019101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019160 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_1019160 : Nat := 118140960795 + 1019160 * 2 ^ 59
def prefixEnd_1019160 : Nat := 4983230072969 + 3 ^ 40 * 1019160 * 2
def baseEnd_1019160 : Nat := 232586197260594562450211

theorem tailTrace_1019160 : CollatzResearch.WordTrace tailWord_1019160 prefixEnd_1019160 232586197260594562450211 := by
  unfold tailWord_1019160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585909493882426757795467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24781212658509902343727289 18585909493882426757795467)
  ·
    refine ⟨27878864240823640136693201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18585909493882426757795467 27878864240823640136693201)
    ·
      refine ⟨20909148180617730102519901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27878864240823640136693201 20909148180617730102519901)
      ·
        refine ⟨7840930567731648788444963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20909148180617730102519901 7840930567731648788444963)
        ·
          refine ⟨11761395851597473182667445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840930567731648788444963 11761395851597473182667445)
          ·
            refine ⟨1102630861087263110875073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11761395851597473182667445 1102630861087263110875073)
            ·
              refine ⟨826973145815447333156305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102630861087263110875073 826973145815447333156305)
              ·
                refine ⟨620229859361585499867229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826973145815447333156305 620229859361585499867229)
                ·
                  refine ⟨232586197260594562450211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620229859361585499867229 232586197260594562450211)
                  ·
                    rfl

theorem cell21_1019160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_1019160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019160 prefixEnd_1019160 := by exact prefixLift 1019160
  have htrace : WordTrace (prefixWord ++ tailWord_1019160) baseStart_1019160 baseEnd_1019160 := by
    simpa [prefixWord, tailWord_1019160, baseEnd_1019160] using wordTrace_append hprefix tailTrace_1019160
  have hstable : (prefixWord ++ tailWord_1019160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019160).length < 2 ^ (prefixWord ++ tailWord_1019160).sum := by decide
  have hdescent : baseEnd_1019160 < baseStart_1019160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019171 : List Nat := [1, 1, 1, 4, 2, 5, 1, 6]
def baseStart_1019171 : Nat := 118140960795 + 1019171 * 2 ^ 59
def prefixEnd_1019171 : Nat := 4983230072969 + 3 ^ 40 * 1019171 * 2
def baseEnd_1019171 : Nat := 77529569203486995922285

theorem tailTrace_1019171 : CollatzResearch.WordTrace tailWord_1019171 prefixEnd_1019171 77529569203486995922285 := by
  unfold tailWord_1019171
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172220190725002394241367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24781480127150001596160911 37172220190725002394241367)
  ·
    refine ⟨55758330286087503591362051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37172220190725002394241367 55758330286087503591362051)
    ·
      refine ⟨83637495429131255387043077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55758330286087503591362051 83637495429131255387043077)
      ·
        refine ⟨15682030392962110385070577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83637495429131255387043077 15682030392962110385070577)
        ·
          refine ⟨11761522794721582788802933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682030392962110385070577 11761522794721582788802933)
          ·
            refine ⟨1102642762005148386450275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11761522794721582788802933 1102642762005148386450275)
            ·
              refine ⟨1653964143007722579675413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102642762005148386450275 1653964143007722579675413)
              ·
                refine ⟨77529569203486995922285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1653964143007722579675413 77529569203486995922285)
                ·
                  rfl

theorem cell21_1019171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_1019171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019171 prefixEnd_1019171 := by exact prefixLift 1019171
  have htrace : WordTrace (prefixWord ++ tailWord_1019171) baseStart_1019171 baseEnd_1019171 := by
    simpa [prefixWord, tailWord_1019171, baseEnd_1019171] using wordTrace_append hprefix tailTrace_1019171
  have hstable : (prefixWord ++ tailWord_1019171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019171).length < 2 ^ (prefixWord ++ tailWord_1019171).sum := by decide
  have hdescent : baseEnd_1019171 < baseStart_1019171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019185 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1019185 : Nat := 118140960795 + 1019185 * 2 ^ 59
def prefixEnd_1019185 : Nat := 4983230072969 + 3 ^ 40 * 1019185 * 2
def baseEnd_1019185 : Nat := 232591902601200074533493

theorem tailTrace_1019185 : CollatzResearch.WordTrace tailWord_1019185 prefixEnd_1019185 232591902601200074533493 := by
  unfold tailWord_1019185
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172730812674282785251009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24781820541782855190167339 37172730812674282785251009)
  ·
    refine ⟨27879548109505712088938257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37172730812674282785251009 27879548109505712088938257)
    ·
      refine ⟨20909661082129284066703693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27879548109505712088938257 20909661082129284066703693)
      ·
        refine ⟨7841122905798481525013885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20909661082129284066703693 7841122905798481525013885)
        ·
          refine ⟨2940421089674430571880207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841122905798481525013885 2940421089674430571880207)
          ·
            refine ⟨4410631634511645857820311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940421089674430571880207 4410631634511645857820311)
            ·
              refine ⟨6615947451767468786730467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410631634511645857820311 6615947451767468786730467)
              ·
                refine ⟨9923921177651203180095701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615947451767468786730467 9923921177651203180095701)
                ·
                  refine ⟨232591902601200074533493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9923921177651203180095701 232591902601200074533493)
                  ·
                    rfl

theorem cell21_1019185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1019185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019185 prefixEnd_1019185 := by exact prefixLift 1019185
  have htrace : WordTrace (prefixWord ++ tailWord_1019185) baseStart_1019185 baseEnd_1019185 := by
    simpa [prefixWord, tailWord_1019185, baseEnd_1019185] using wordTrace_append hprefix tailTrace_1019185
  have hstable : (prefixWord ++ tailWord_1019185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019185).length < 2 ^ (prefixWord ++ tailWord_1019185).sum := by decide
  have hdescent : baseEnd_1019185 < baseStart_1019185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019188 : List Nat := [2, 5, 1, 1, 1, 1, 5, 5]
def baseStart_1019188 : Nat := 118140960795 + 1019188 * 2 ^ 59
def prefixEnd_1019188 : Nat := 4983230072969 + 3 ^ 40 * 1019188 * 2
def baseEnd_1019188 : Nat := 77530862414024245327829

theorem tailTrace_1019188 : CollatzResearch.WordTrace tailWord_1019188 prefixEnd_1019188 77530862414024245327829 := by
  unfold tailWord_1019188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586420115831707148805109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24781893487775609531740145 18586420115831707148805109)
  ·
    refine ⟨1742476885859222545200479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18586420115831707148805109 1742476885859222545200479)
    ·
      refine ⟨2613715328788833817800719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742476885859222545200479 2613715328788833817800719)
      ·
        refine ⟨3920572993183250726701079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613715328788833817800719 3920572993183250726701079)
        ·
          refine ⟨5880859489774876090051619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920572993183250726701079 5880859489774876090051619)
          ·
            refine ⟨8821289234662314135077429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880859489774876090051619 8821289234662314135077429)
            ·
              refine ⟨826995865749591950163509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8821289234662314135077429 826995865749591950163509)
              ·
                refine ⟨77530862414024245327829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 826995865749591950163509 77530862414024245327829)
                ·
                  rfl

theorem cell21_1019188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_1019188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019188 prefixEnd_1019188 := by exact prefixLift 1019188
  have htrace : WordTrace (prefixWord ++ tailWord_1019188) baseStart_1019188 baseEnd_1019188 := by
    simpa [prefixWord, tailWord_1019188, baseEnd_1019188] using wordTrace_append hprefix tailTrace_1019188
  have hstable : (prefixWord ++ tailWord_1019188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019188).length < 2 ^ (prefixWord ++ tailWord_1019188).sum := by decide
  have hdescent : baseEnd_1019188 < baseStart_1019188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019253 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1019253 : Nat := 118140960795 + 1019253 * 2 ^ 59
def prefixEnd_1019253 : Nat := 4983230072969 + 3 ^ 40 * 1019253 * 2
def baseEnd_1019253 : Nat := 232607421127647067400021

theorem tailTrace_1019253 : CollatzResearch.WordTrace tailWord_1019253 prefixEnd_1019253 232607421127647067400021 := by
  unfold tailWord_1019253
  simp only [CollatzResearch.WordTrace]
  refine ⟨37175210976427930398726413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24783473984285286932484275 37175210976427930398726413)
  ·
    refine ⟨13940704116160473899522405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37175210976427930398726413 13940704116160473899522405)
    ·
      refine ⟨2613882021780088856160451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13940704116160473899522405 2613882021780088856160451)
      ·
        refine ⟨3920823032670133284240677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613882021780088856160451 3920823032670133284240677)
        ·
          refine ⟨735154318625649990795127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3920823032670133284240677 735154318625649990795127)
          ·
            refine ⟨1102731477938474986192691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735154318625649990795127 1102731477938474986192691)
            ·
              refine ⟨1654097216907712479289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102731477938474986192691 1654097216907712479289037)
              ·
                refine ⟨620286456340392179733389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654097216907712479289037 620286456340392179733389)
                ·
                  refine ⟨232607421127647067400021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620286456340392179733389 232607421127647067400021)
                  ·
                    rfl

theorem cell21_1019253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1019253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019253 prefixEnd_1019253 := by exact prefixLift 1019253
  have htrace : WordTrace (prefixWord ++ tailWord_1019253) baseStart_1019253 baseEnd_1019253 := by
    simpa [prefixWord, tailWord_1019253, baseEnd_1019253] using wordTrace_append hprefix tailTrace_1019253
  have hstable : (prefixWord ++ tailWord_1019253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019253).length < 2 ^ (prefixWord ++ tailWord_1019253).sum := by decide
  have hdescent : baseEnd_1019253 < baseStart_1019253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019275 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_1019275 : Nat := 118140960795 + 1019275 * 2 ^ 59
def prefixEnd_1019275 : Nat := 4983230072969 + 3 ^ 40 * 1019275 * 2
def baseEnd_1019275 : Nat := 232612441827379918033309

theorem tailTrace_1019275 : CollatzResearch.WordTrace tailWord_1019275 prefixEnd_1019275 232612441827379918033309 := by
  unfold tailWord_1019275
  simp only [CollatzResearch.WordTrace]
  refine ⟨37176013382348228156027279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24784008921565485437351519 37176013382348228156027279)
  ·
    refine ⟨55764020073522342234040919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37176013382348228156027279 55764020073522342234040919)
    ·
      refine ⟨83646030110283513351061379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55764020073522342234040919 83646030110283513351061379)
      ·
        refine ⟨125469045165425270026592069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83646030110283513351061379 125469045165425270026592069)
        ·
          refine ⟨23525445968517238129986013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125469045165425270026592069 23525445968517238129986013)
          ·
            refine ⟨8822042238193964298744755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23525445968517238129986013 8822042238193964298744755)
            ·
              refine ⟨13233063357290946448117133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822042238193964298744755 13233063357290946448117133)
              ·
                refine ⟨4962398758984104918043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13233063357290946448117133 4962398758984104918043925)
                ·
                  refine ⟨232612441827379918033309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4962398758984104918043925 232612441827379918033309)
                  ·
                    rfl

theorem cell21_1019275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_1019275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019275 prefixEnd_1019275 := by exact prefixLift 1019275
  have htrace : WordTrace (prefixWord ++ tailWord_1019275) baseStart_1019275 baseEnd_1019275 := by
    simpa [prefixWord, tailWord_1019275, baseEnd_1019275] using wordTrace_append hprefix tailTrace_1019275
  have hstable : (prefixWord ++ tailWord_1019275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019275).length < 2 ^ (prefixWord ++ tailWord_1019275).sum := by decide
  have hdescent : baseEnd_1019275 < baseStart_1019275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019413 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1019413 : Nat := 118140960795 + 1019413 * 2 ^ 59
def prefixEnd_1019413 : Nat := 4983230072969 + 3 ^ 40 * 1019413 * 2
def baseEnd_1019413 : Nat := 232643935307522344733027

theorem tailTrace_1019413 : CollatzResearch.WordTrace tailWord_1019413 prefixEnd_1019413 232643935307522344733027 := by
  unfold tailWord_1019413
  simp only [CollatzResearch.WordTrace]
  refine ⟨37181046655848277724550893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24787364437232185149700595 37181046655848277724550893)
  ·
    refine ⟨13942892495943104146706585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37181046655848277724550893 13942892495943104146706585)
    ·
      refine ⟨10457169371957328110029939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13942892495943104146706585 10457169371957328110029939)
      ·
        refine ⟨15685754057935992165044909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457169371957328110029939 15685754057935992165044909)
        ·
          refine ⟨5882157771725997061891841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15685754057935992165044909 5882157771725997061891841)
          ·
            refine ⟨4411618328794497796418881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882157771725997061891841 4411618328794497796418881)
            ·
              refine ⟨3308713746595873347314161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411618328794497796418881 3308713746595873347314161)
              ·
                refine ⟨2481535309946905010485621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308713746595873347314161 2481535309946905010485621)
                ·
                  refine ⟨232643935307522344733027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2481535309946905010485621 232643935307522344733027)
                  ·
                    rfl

theorem cell21_1019413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1019413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019413 prefixEnd_1019413 := by exact prefixLift 1019413
  have htrace : WordTrace (prefixWord ++ tailWord_1019413) baseStart_1019413 baseEnd_1019413 := by
    simpa [prefixWord, tailWord_1019413, baseEnd_1019413] using wordTrace_append hprefix tailTrace_1019413
  have hstable : (prefixWord ++ tailWord_1019413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019413).length < 2 ^ (prefixWord ++ tailWord_1019413).sum := by decide
  have hdescent : baseEnd_1019413 < baseStart_1019413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019416 : List Nat := [2, 1, 2, 3, 4, 2, 2, 5]
def baseStart_1019416 : Nat := 118140960795 + 1019416 * 2 ^ 59
def prefixEnd_1019416 : Nat := 4983230072969 + 3 ^ 40 * 1019416 * 2
def baseEnd_1019416 : Nat := 77548206649465002061007

theorem tailTrace_1019416 : CollatzResearch.WordTrace tailWord_1019416 prefixEnd_1019416 77548206649465002061007 := by
  unfold tailWord_1019416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590578037418704618455051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24787437383224939491273401 18590578037418704618455051)
  ·
    refine ⟨27885867056128056927682577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590578037418704618455051 27885867056128056927682577)
    ·
      refine ⟨20914400292096042695761933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27885867056128056927682577 20914400292096042695761933)
      ·
        refine ⟨7842900109536016010910725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20914400292096042695761933 7842900109536016010910725)
        ·
          refine ⟨1470543770538003002045761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7842900109536016010910725 1470543770538003002045761)
          ·
            refine ⟨1102907827903502251534321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470543770538003002045761 1102907827903502251534321)
            ·
              refine ⟨827180870927626688650741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102907827903502251534321 827180870927626688650741)
              ·
                refine ⟨77548206649465002061007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827180870927626688650741 77548206649465002061007)
                ·
                  rfl

theorem cell21_1019416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_1019416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019416 prefixEnd_1019416 := by exact prefixLift 1019416
  have htrace : WordTrace (prefixWord ++ tailWord_1019416) baseStart_1019416 baseEnd_1019416 := by
    simpa [prefixWord, tailWord_1019416, baseEnd_1019416] using wordTrace_append hprefix tailTrace_1019416
  have hstable : (prefixWord ++ tailWord_1019416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019416).length < 2 ^ (prefixWord ++ tailWord_1019416).sum := by decide
  have hdescent : baseEnd_1019416 < baseStart_1019416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019447 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 3]
def baseStart_1019447 : Nat := 118140960795 + 1019447 * 2 ^ 59
def prefixEnd_1019447 : Nat := 4983230072969 + 3 ^ 40 * 1019447 * 2
def baseEnd_1019447 : Nat := 232651694570745841166291

theorem tailTrace_1019447 : CollatzResearch.WordTrace tailWord_1019447 prefixEnd_1019447 232651694570745841166291 := by
  unfold tailWord_1019447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37182286737725101531288595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24788191158483401020859063 37182286737725101531288595)
  ·
    refine ⟨55773430106587652296932893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37182286737725101531288595 55773430106587652296932893)
    ·
      refine ⟨20915036289970369611349835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55773430106587652296932893 20915036289970369611349835)
      ·
        refine ⟨31372554434955554417024753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20915036289970369611349835 31372554434955554417024753)
        ·
          refine ⟨23529415826216665812768565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31372554434955554417024753 23529415826216665812768565)
          ·
            refine ⟨2205882733707812419947053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23529415826216665812768565 2205882733707812419947053)
            ·
              refine ⟨827206025140429657480145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2205882733707812419947053 827206025140429657480145)
              ·
                refine ⟨620404518855322243110109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827206025140429657480145 620404518855322243110109)
                ·
                  refine ⟨232651694570745841166291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620404518855322243110109 232651694570745841166291)
                  ·
                    rfl

theorem cell21_1019447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].length) (baseStart_1019447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019447 prefixEnd_1019447 := by exact prefixLift 1019447
  have htrace : WordTrace (prefixWord ++ tailWord_1019447) baseStart_1019447 baseEnd_1019447 := by
    simpa [prefixWord, tailWord_1019447, baseEnd_1019447] using wordTrace_append hprefix tailTrace_1019447
  have hstable : (prefixWord ++ tailWord_1019447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019447).length < 2 ^ (prefixWord ++ tailWord_1019447).sum := by decide
  have hdescent : baseEnd_1019447 < baseStart_1019447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019472 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1019472 : Nat := 118140960795 + 1019472 * 2 ^ 59
def prefixEnd_1019472 : Nat := 4983230072969 + 3 ^ 40 * 1019472 * 2
def baseEnd_1019472 : Nat := 232657399911351353249573

theorem tailTrace_1019472 : CollatzResearch.WordTrace tailWord_1019472 prefixEnd_1019472 232657399911351353249573 := by
  unfold tailWord_1019472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591599281317265400474335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24788799041756353867299113 18591599281317265400474335)
  ·
    refine ⟨27887398921975898100711503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18591599281317265400474335 27887398921975898100711503)
    ·
      refine ⟨41831098382963847151067255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27887398921975898100711503 41831098382963847151067255)
      ·
        refine ⟨62746647574445770726600883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41831098382963847151067255 62746647574445770726600883)
        ·
          refine ⟨94119971361668656089901325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62746647574445770726600883 94119971361668656089901325)
          ·
            refine ⟨35294989260625746033712997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94119971361668656089901325 35294989260625746033712997)
            ·
              refine ⟨6617810486367327381321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35294989260625746033712997 6617810486367327381321187)
              ·
                refine ⟨9926715729550991071981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617810486367327381321187 9926715729550991071981781)
                ·
                  refine ⟨232657399911351353249573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9926715729550991071981781 232657399911351353249573)
                  ·
                    rfl

theorem cell21_1019472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1019472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019472 prefixEnd_1019472 := by exact prefixLift 1019472
  have htrace : WordTrace (prefixWord ++ tailWord_1019472) baseStart_1019472 baseEnd_1019472 := by
    simpa [prefixWord, tailWord_1019472, baseEnd_1019472] using wordTrace_append hprefix tailTrace_1019472
  have hstable : (prefixWord ++ tailWord_1019472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019472).length < 2 ^ (prefixWord ++ tailWord_1019472).sum := by decide
  have hdescent : baseEnd_1019472 < baseStart_1019472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019540 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1019540 : Nat := 118140960795 + 1019540 * 2 ^ 59
def prefixEnd_1019540 : Nat := 4983230072969 + 3 ^ 40 * 1019540 * 2
def baseEnd_1019540 : Nat := 232672918437798346116101

theorem tailTrace_1019540 : CollatzResearch.WordTrace tailWord_1019540 prefixEnd_1019540 232672918437798346116101 := by
  unfold tailWord_1019540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592839363194089207212037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24790452484258785609616049 18592839363194089207212037)
  ·
    refine ⟨3486157380598891726352257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18592839363194089207212037 3486157380598891726352257)
    ·
      refine ⟨2614618035449168794764193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3486157380598891726352257 2614618035449168794764193)
      ·
        refine ⟨1960963526586876596073145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2614618035449168794764193 1960963526586876596073145)
        ·
          refine ⟨1470722644940157447054859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960963526586876596073145 1470722644940157447054859)
          ·
            refine ⟨2206083967410236170582289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470722644940157447054859 2206083967410236170582289)
            ·
              refine ⟨1654562975557677127936717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206083967410236170582289 1654562975557677127936717)
              ·
                refine ⟨620461115834128922976269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654562975557677127936717 620461115834128922976269)
                ·
                  refine ⟨232672918437798346116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620461115834128922976269 232672918437798346116101)
                  ·
                    rfl

theorem cell21_1019540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1019540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019540 prefixEnd_1019540 := by exact prefixLift 1019540
  have htrace : WordTrace (prefixWord ++ tailWord_1019540) baseStart_1019540 baseEnd_1019540 := by
    simpa [prefixWord, tailWord_1019540, baseEnd_1019540] using wordTrace_append hprefix tailTrace_1019540
  have hstable : (prefixWord ++ tailWord_1019540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019540).length < 2 ^ (prefixWord ++ tailWord_1019540).sum := by decide
  have hdescent : baseEnd_1019540 < baseStart_1019540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019551 : List Nat := [1, 1, 2, 7, 1, 1, 8]
def baseStart_1019551 : Nat := 118140960795 + 1019551 * 2 ^ 59
def prefixEnd_1019551 : Nat := 4983230072969 + 3 ^ 40 * 1019551 * 2
def baseEnd_1019551 : Nat := 25852825420851641270305

theorem tailTrace_1019551 : CollatzResearch.WordTrace tailWord_1019551 prefixEnd_1019551 25852825420851641270305 := by
  unfold tailWord_1019551
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186079929348327293074507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790719952898884862049671 37186079929348327293074507)
  ·
    refine ⟨55779119894022490939611761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37186079929348327293074507 55779119894022490939611761)
    ·
      refine ⟨41834339920516868204708821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55779119894022490939611761 41834339920516868204708821)
      ·
        refine ⟨980492341887114098547863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41834339920516868204708821 980492341887114098547863)
        ·
          refine ⟨1470738512830671147821795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980492341887114098547863 1470738512830671147821795)
          ·
            refine ⟨2206107769246006721732693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470738512830671147821795 2206107769246006721732693)
            ·
              refine ⟨25852825420851641270305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2206107769246006721732693 25852825420851641270305)
              ·
                rfl

theorem cell21_1019551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 8].length) (baseStart_1019551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019551 prefixEnd_1019551 := by exact prefixLift 1019551
  have htrace : WordTrace (prefixWord ++ tailWord_1019551) baseStart_1019551 baseEnd_1019551 := by
    simpa [prefixWord, tailWord_1019551, baseEnd_1019551] using wordTrace_append hprefix tailTrace_1019551
  have hstable : (prefixWord ++ tailWord_1019551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019551).length < 2 ^ (prefixWord ++ tailWord_1019551).sum := by decide
  have hdescent : baseEnd_1019551 < baseStart_1019551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019579 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_1019579 : Nat := 118140960795 + 1019579 * 2 ^ 59
def prefixEnd_1019579 : Nat := 4983230072969 + 3 ^ 40 * 1019579 * 2
def baseEnd_1019579 : Nat := 232681818769142944966021

theorem tailTrace_1019579 : CollatzResearch.WordTrace tailWord_1019579 prefixEnd_1019579 232681818769142944966021 := by
  unfold tailWord_1019579
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187101173246888075093791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24791400782164592050062527 37187101173246888075093791)
  ·
    refine ⟨55780651759870332112640687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37187101173246888075093791 55780651759870332112640687)
    ·
      refine ⟨83670977639805498168961031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55780651759870332112640687 83670977639805498168961031)
      ·
        refine ⟨125506466459708247253441547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83670977639805498168961031 125506466459708247253441547)
        ·
          refine ⟨188259699689562370880162321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125506466459708247253441547 188259699689562370880162321)
          ·
            refine ⟨141194774767171778160121741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188259699689562370880162321 141194774767171778160121741)
            ·
              refine ⟨52948040537689416810045653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141194774767171778160121741 52948040537689416810045653)
              ·
                refine ⟨1240969700102095706485445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52948040537689416810045653 1240969700102095706485445)
                ·
                  refine ⟨232681818769142944966021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240969700102095706485445 232681818769142944966021)
                  ·
                    rfl

theorem cell21_1019579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_1019579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019579 prefixEnd_1019579 := by exact prefixLift 1019579
  have htrace : WordTrace (prefixWord ++ tailWord_1019579) baseStart_1019579 baseEnd_1019579 := by
    simpa [prefixWord, tailWord_1019579, baseEnd_1019579] using wordTrace_append hprefix tailTrace_1019579
  have hstable : (prefixWord ++ tailWord_1019579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019579).length < 2 ^ (prefixWord ++ tailWord_1019579).sum := by decide
  have hdescent : baseEnd_1019579 < baseStart_1019579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019610 : List Nat := [3, 1, 1, 2, 2, 5, 7]
def baseStart_1019610 : Nat := 118140960795 + 1019610 * 2 ^ 59
def prefixEnd_1019610 : Nat := 4983230072969 + 3 ^ 40 * 1019610 * 2
def baseEnd_1019610 : Nat := 25854321487943753327699

theorem tailTrace_1019610 : CollatzResearch.WordTrace tailWord_1019610 prefixEnd_1019610 25854321487943753327699 := by
  unfold tailWord_1019610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297057959033645092368071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24792154557423053579648189 9297057959033645092368071)
  ·
    refine ⟨13945586938550467638552107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9297057959033645092368071 13945586938550467638552107)
    ·
      refine ⟨20918380407825701457828161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13945586938550467638552107 20918380407825701457828161)
      ·
        refine ⟨15688785305869276093371121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20918380407825701457828161 15688785305869276093371121)
        ·
          refine ⟨11766588979401957070028341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15688785305869276093371121 11766588979401957070028341)
          ·
            refine ⟨1103117716818933475315157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11766588979401957070028341 1103117716818933475315157)
            ·
              refine ⟨25854321487943753327699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1103117716818933475315157 25854321487943753327699)
              ·
                rfl

theorem cell21_1019610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 7].length) (baseStart_1019610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019610 prefixEnd_1019610 := by exact prefixLift 1019610
  have htrace : WordTrace (prefixWord ++ tailWord_1019610) baseStart_1019610 baseEnd_1019610 := by
    simpa [prefixWord, tailWord_1019610, baseEnd_1019610] using wordTrace_append hprefix tailTrace_1019610
  have hstable : (prefixWord ++ tailWord_1019610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019610).length < 2 ^ (prefixWord ++ tailWord_1019610).sum := by decide
  have hdescent : baseEnd_1019610 < baseStart_1019610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019661 : List Nat := [1, 7, 2, 1, 1, 9]
def baseStart_1019661 : Nat := 118140960795 + 1019661 * 2 ^ 59
def prefixEnd_1019661 : Nat := 4983230072969 + 3 ^ 40 * 1019661 * 2
def baseEnd_1019661 : Nat := 8618538232827000911081

theorem tailTrace_1019661 : CollatzResearch.WordTrace tailWord_1019661 prefixEnd_1019661 8618538232827000911081 := by
  unfold tailWord_1019661
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190091958949816079578837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24793394639299877386385891 37190091958949816079578837)
  ·
    refine ⟨871642780287886314365129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37190091958949816079578837 871642780287886314365129)
    ·
      refine ⟨653732085215914735773847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 871642780287886314365129 653732085215914735773847)
      ·
        refine ⟨980598127823872103660771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653732085215914735773847 980598127823872103660771)
        ·
          refine ⟨1470897191735808155491157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980598127823872103660771 1470897191735808155491157)
          ·
            refine ⟨8618538232827000911081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1470897191735808155491157 8618538232827000911081)
            ·
              rfl

theorem cell21_1019661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 9].length) (baseStart_1019661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019661 prefixEnd_1019661 := by exact prefixLift 1019661
  have htrace : WordTrace (prefixWord ++ tailWord_1019661) baseStart_1019661 baseEnd_1019661 := by
    simpa [prefixWord, tailWord_1019661, baseEnd_1019661] using wordTrace_append hprefix tailTrace_1019661
  have hstable : (prefixWord ++ tailWord_1019661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019661).length < 2 ^ (prefixWord ++ tailWord_1019661).sum := by decide
  have hdescent : baseEnd_1019661 < baseStart_1019661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019669 : List Nat := [1, 3, 2, 1, 2, 12]
def baseStart_1019669 : Nat := 118140960795 + 1019669 * 2 ^ 59
def prefixEnd_1019669 : Nat := 4983230072969 + 3 ^ 40 * 1019669 * 2
def baseEnd_1019669 : Nat := 8618605851678621795031

theorem tailTrace_1019669 : CollatzResearch.WordTrace tailWord_1019669 prefixEnd_1019669 8618605851678621795031 := by
  unfold tailWord_1019669
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190383742920833445870061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24793589161947222297246707 37190383742920833445870061)
  ·
    refine ⟨13946393903595312542201273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37190383742920833445870061 13946393903595312542201273)
    ·
      refine ⟨10459795427696484406650955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13946393903595312542201273 10459795427696484406650955)
      ·
        refine ⟨15689693141544726609976433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459795427696484406650955 15689693141544726609976433)
        ·
          refine ⟨11767269856158544957482325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15689693141544726609976433 11767269856158544957482325)
          ·
            refine ⟨8618605851678621795031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11767269856158544957482325 8618605851678621795031)
            ·
              rfl

theorem cell21_1019669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 12].length) (baseStart_1019669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019669 prefixEnd_1019669 := by exact prefixLift 1019669
  have htrace : WordTrace (prefixWord ++ tailWord_1019669) baseStart_1019669 baseEnd_1019669 := by
    simpa [prefixWord, tailWord_1019669, baseEnd_1019669] using wordTrace_append hprefix tailTrace_1019669
  have hstable : (prefixWord ++ tailWord_1019669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019669).length < 2 ^ (prefixWord ++ tailWord_1019669).sum := by decide
  have hdescent : baseEnd_1019669 < baseStart_1019669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019678 : List Nat := [4, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1019678 : Nat := 118140960795 + 1019678 * 2 ^ 59
def prefixEnd_1019678 : Nat := 4983230072969 + 3 ^ 40 * 1019678 * 2
def baseEnd_1019678 : Nat := 77568137305980257605273

theorem tailTrace_1019678 : CollatzResearch.WordTrace tailWord_1019678 prefixEnd_1019678 77568137305980257605273 := by
  unfold tailWord_1019678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648838999986028497868461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24793807999925485321965125 4648838999986028497868461)
  ·
    refine ⟨1743314624994760686700673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4648838999986028497868461 1743314624994760686700673)
    ·
      refine ⟨1307485968746070515025505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743314624994760686700673 1307485968746070515025505)
      ·
        refine ⟨980614476559552886269129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307485968746070515025505 980614476559552886269129)
        ·
          refine ⟨735460857419664664701847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980614476559552886269129 735460857419664664701847)
          ·
            refine ⟨1103191286129496997052771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735460857419664664701847 1103191286129496997052771)
            ·
              refine ⟨1654786929194245495579157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103191286129496997052771 1654786929194245495579157)
              ·
                refine ⟨77568137305980257605273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1654786929194245495579157 77568137305980257605273)
                ·
                  rfl

theorem cell21_1019678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1019678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1019678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1019678 prefixEnd_1019678 := by exact prefixLift 1019678
  have htrace : WordTrace (prefixWord ++ tailWord_1019678) baseStart_1019678 baseEnd_1019678 := by
    simpa [prefixWord, tailWord_1019678, baseEnd_1019678] using wordTrace_append hprefix tailTrace_1019678
  have hstable : (prefixWord ++ tailWord_1019678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019678).length < 2 ^ (prefixWord ++ tailWord_1019678).sum := by decide
  have hdescent : baseEnd_1019678 < baseStart_1019678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
