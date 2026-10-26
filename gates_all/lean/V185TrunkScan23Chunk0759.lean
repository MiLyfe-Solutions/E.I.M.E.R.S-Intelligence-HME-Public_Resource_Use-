import V185TrunkScan23Chunk0758

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4488392 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_4488392 : Nat := 118140960795 + 4488392 * 2 ^ 59
def prefixEnd_4488392 : Nat := 4983230072969 + 3 ^ 40 * 4488392 * 2
def baseEnd_4488392 : Nat := 2304702461795108379358267

theorem tailTrace_4488392 : CollatzResearch.WordTrace tailWord_4488392 prefixEnd_4488392 2304702461795108379358267 := by
  unfold tailWord_4488392
  simp only [CollatzResearch.WordTrace]
  refine ⟨81852552577664907585021715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109136736770219876780028953 81852552577664907585021715)
  ·
    refine ⟨122778828866497361377532573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81852552577664907585021715 122778828866497361377532573)
    ·
      refine ⟨46042060824936510516574715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122778828866497361377532573 46042060824936510516574715)
      ·
        refine ⟨69063091237404765774862073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46042060824936510516574715 69063091237404765774862073)
        ·
          refine ⟨51797318428053574331146555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69063091237404765774862073 51797318428053574331146555)
          ·
            refine ⟨77695977642080361496719833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51797318428053574331146555 77695977642080361496719833)
            ·
              refine ⟨58271983231560271122539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77695977642080361496719833 58271983231560271122539875)
              ·
                refine ⟨87407974847340406683809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58271983231560271122539875 87407974847340406683809813)
                ·
                  refine ⟨4097248820969081563303585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87407974847340406683809813 4097248820969081563303585)
                  ·
                    refine ⟨3072936615726811172477689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4097248820969081563303585 3072936615726811172477689)
                    ·
                      refine ⟨2304702461795108379358267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3072936615726811172477689 2304702461795108379358267)
                      ·
                        rfl

theorem cell23_4488392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_4488392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488392 prefixEnd_4488392 := by exact prefixLift 4488392
  have htrace : WordTrace (prefixWord ++ tailWord_4488392) baseStart_4488392 baseEnd_4488392 := by
    simpa [prefixWord, tailWord_4488392, baseEnd_4488392] using wordTrace_append hprefix tailTrace_4488392
  have hstable : (prefixWord ++ tailWord_4488392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488392).length < 2 ^ (prefixWord ++ tailWord_4488392).sum := by decide
  have hdescent : baseEnd_4488392 < baseStart_4488392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488465 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_4488465 : Nat := 118140960795 + 4488465 * 2 ^ 59
def prefixEnd_4488465 : Nat := 4983230072969 + 3 ^ 40 * 4488465 * 2
def baseEnd_4488465 : Nat := 2304739945882886593745431

theorem tailTrace_4488465 : CollatzResearch.WordTrace tailWord_4488465 prefixEnd_4488465 2304739945882886593745431 := by
  unfold tailWord_4488465
  simp only [CollatzResearch.WordTrace]
  refine ⟨163707767684065348637450849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109138511789376899091633899 163707767684065348637450849)
  ·
    refine ⟨122780825763049011478088137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163707767684065348637450849 122780825763049011478088137)
    ·
      refine ⟨92085619322286758608566103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122780825763049011478088137 92085619322286758608566103)
      ·
        refine ⟨138128428983430137912849155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92085619322286758608566103 138128428983430137912849155)
        ·
          refine ⟨207192643475145206869273733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138128428983430137912849155 207192643475145206869273733)
          ·
            refine ⟨38848620651589726287988825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207192643475145206869273733 38848620651589726287988825)
            ·
              refine ⟨29136465488692294715991619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38848620651589726287988825 29136465488692294715991619)
              ·
                refine ⟨43704698233038442073987429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29136465488692294715991619 43704698233038442073987429)
                ·
                  refine ⟨8194630918694707888872643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43704698233038442073987429 8194630918694707888872643)
                  ·
                    refine ⟨12291946378042061833308965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8194630918694707888872643 12291946378042061833308965)
                    ·
                      refine ⟨2304739945882886593745431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12291946378042061833308965 2304739945882886593745431)
                      ·
                        rfl

theorem cell23_4488465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_4488465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488465 prefixEnd_4488465 := by exact prefixLift 4488465
  have htrace : WordTrace (prefixWord ++ tailWord_4488465) baseStart_4488465 baseEnd_4488465 := by
    simpa [prefixWord, tailWord_4488465, baseEnd_4488465] using wordTrace_append hprefix tailTrace_4488465
  have hstable : (prefixWord ++ tailWord_4488465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488465).length < 2 ^ (prefixWord ++ tailWord_4488465).sum := by decide
  have hdescent : baseEnd_4488465 < baseStart_4488465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488526 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_4488526 : Nat := 118140960795 + 4488526 * 2 ^ 59
def prefixEnd_4488526 : Nat := 4983230072969 + 3 ^ 40 * 4488526 * 2
def baseEnd_4488526 : Nat := 768257089400936951694217

theorem tailTrace_4488526 : CollatzResearch.WordTrace tailWord_4488526 prefixEnd_4488526 768257089400936951694217 := by
  unfold tailWord_4488526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20463749067105544506927679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109139995024562904036947621 20463749067105544506927679)
  ·
    refine ⟨30695623600658316760391519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20463749067105544506927679 30695623600658316760391519)
    ·
      refine ⟨46043435400987475140587279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30695623600658316760391519 46043435400987475140587279)
      ·
        refine ⟨69065153101481212710880919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46043435400987475140587279 69065153101481212710880919)
        ·
          refine ⟨103597729652221819066321379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69065153101481212710880919 103597729652221819066321379)
          ·
            refine ⟨155396594478332728599482069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103597729652221819066321379 155396594478332728599482069)
            ·
              refine ⟨3642107683085923326550361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 155396594478332728599482069 3642107683085923326550361)
              ·
                refine ⟨2731580762314442494912771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642107683085923326550361 2731580762314442494912771)
                ·
                  refine ⟨4097371143471663742369157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731580762314442494912771 4097371143471663742369157)
                  ·
                    refine ⟨768257089400936951694217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097371143471663742369157 768257089400936951694217)
                    ·
                      rfl

theorem cell23_4488526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_4488526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488526 prefixEnd_4488526 := by exact prefixLift 4488526
  have htrace : WordTrace (prefixWord ++ tailWord_4488526) baseStart_4488526 baseEnd_4488526 := by
    simpa [prefixWord, tailWord_4488526, baseEnd_4488526] using wordTrace_append hprefix tailTrace_4488526
  have hstable : (prefixWord ++ tailWord_4488526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488526).length < 2 ^ (prefixWord ++ tailWord_4488526).sum := by decide
  have hdescent : baseEnd_4488526 < baseStart_4488526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488559 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 2, 3, 2]
def baseStart_4488559 : Nat := 118140960795 + 4488559 * 2 ^ 59
def prefixEnd_4488559 : Nat := 4983230072969 + 3 ^ 40 * 4488559 * 2
def baseEnd_4488559 : Nat := 2304788213064409225969999

theorem tailTrace_4488559 : CollatzResearch.WordTrace tailWord_4488559 prefixEnd_4488559 2304788213064409225969999 := by
  unfold tailWord_4488559
  simp only [CollatzResearch.WordTrace]
  refine ⟨163711196145724802691372731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109140797430483201794248487 163711196145724802691372731)
  ·
    refine ⟨245566794218587204037059097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163711196145724802691372731 245566794218587204037059097)
    ·
      refine ⟨184175095663940403027794323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245566794218587204037059097 184175095663940403027794323)
      ·
        refine ⟨276262643495910604541691485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184175095663940403027794323 276262643495910604541691485)
        ·
          refine ⟨103598491310966476703134307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276262643495910604541691485 103598491310966476703134307)
          ·
            refine ⟨155397736966449715054701461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103598491310966476703134307 155397736966449715054701461)
            ·
              refine ⟨7284268920302330393189131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155397736966449715054701461 7284268920302330393189131)
              ·
                refine ⟨10926403380453495589783697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284268920302330393189131 10926403380453495589783697)
                ·
                  refine ⟨8194802535340121692337773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10926403380453495589783697 8194802535340121692337773)
                  ·
                    refine ⟨3073050950752545634626665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8194802535340121692337773 3073050950752545634626665)
                    ·
                      refine ⟨2304788213064409225969999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073050950752545634626665 2304788213064409225969999)
                      ·
                        rfl

theorem cell23_4488559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3, 2].length) (baseStart_4488559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488559 prefixEnd_4488559 := by exact prefixLift 4488559
  have htrace : WordTrace (prefixWord ++ tailWord_4488559) baseStart_4488559 baseEnd_4488559 := by
    simpa [prefixWord, tailWord_4488559, baseEnd_4488559] using wordTrace_append hprefix tailTrace_4488559
  have hstable : (prefixWord ++ tailWord_4488559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488559).length < 2 ^ (prefixWord ++ tailWord_4488559).sum := by decide
  have hdescent : baseEnd_4488559 < baseStart_4488559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488583 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_4488583 : Nat := 118140960795 + 4488583 * 2 ^ 59
def prefixEnd_4488583 : Nat := 4983230072969 + 3 ^ 40 * 4488583 * 2
def baseEnd_4488583 : Nat := 2304800536600117132069889

theorem tailTrace_4488583 : CollatzResearch.WordTrace tailWord_4488583 prefixEnd_4488583 2304800536600117132069889 := by
  unfold tailWord_4488583
  simp only [CollatzResearch.WordTrace]
  refine ⟨163712071497637854790246403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109141380998425236526830935 163712071497637854790246403)
  ·
    refine ⟨245568107246456782185369605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163712071497637854790246403 245568107246456782185369605)
    ·
      refine ⟨46044020108710646659756801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245568107246456782185369605 46044020108710646659756801)
      ·
        refine ⟨34533015081532984994817601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46044020108710646659756801 34533015081532984994817601)
        ·
          refine ⟨25899761311149738746113201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34533015081532984994817601 25899761311149738746113201)
          ·
            refine ⟨19424820983362304059584901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25899761311149738746113201 19424820983362304059584901)
            ·
              refine ⟨3642153934380432011172169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19424820983362304059584901 3642153934380432011172169)
              ·
                refine ⟨2731615450785324008379127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642153934380432011172169 2731615450785324008379127)
                ·
                  refine ⟨4097423176177986012568691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731615450785324008379127 4097423176177986012568691)
                  ·
                    refine ⟨6146134764266979018853037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097423176177986012568691 6146134764266979018853037)
                    ·
                      refine ⟨2304800536600117132069889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146134764266979018853037 2304800536600117132069889)
                      ·
                        rfl

theorem cell23_4488583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_4488583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488583 prefixEnd_4488583 := by exact prefixLift 4488583
  have htrace : WordTrace (prefixWord ++ tailWord_4488583) baseStart_4488583 baseEnd_4488583 := by
    simpa [prefixWord, tailWord_4488583, baseEnd_4488583] using wordTrace_append hprefix tailTrace_4488583
  have hstable : (prefixWord ++ tailWord_4488583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488583).length < 2 ^ (prefixWord ++ tailWord_4488583).sum := by decide
  have hdescent : baseEnd_4488583 < baseStart_4488583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488633 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_4488633 : Nat := 118140960795 + 4488633 * 2 ^ 59
def prefixEnd_4488633 : Nat := 4983230072969 + 3 ^ 40 * 4488633 * 2
def baseEnd_4488633 : Nat := 768275403544280645481553

theorem tailTrace_4488633 : CollatzResearch.WordTrace tailWord_4488633 prefixEnd_4488633 768275403544280645481553 := by
  unfold tailWord_4488633
  simp only [CollatzResearch.WordTrace]
  refine ⟨163713895147456713329566553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109142596764971142219711035 163713895147456713329566553)
  ·
    refine ⟨122785421360592534997174915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163713895147456713329566553 122785421360592534997174915)
    ·
      refine ⟨184178132040888802495762373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122785421360592534997174915 184178132040888802495762373)
      ·
        refine ⟨34533399757666650467955445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184178132040888802495762373 34533399757666650467955445)
        ·
          refine ⟨3237506227281248481370823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34533399757666650467955445 3237506227281248481370823)
          ·
            refine ⟨4856259340921872722056235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237506227281248481370823 4856259340921872722056235)
            ·
              refine ⟨7284389011382809083084353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856259340921872722056235 7284389011382809083084353)
              ·
                refine ⟨5463291758537106812313265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7284389011382809083084353 5463291758537106812313265)
                ·
                  refine ⟨4097468818902830109234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5463291758537106812313265 4097468818902830109234949)
                  ·
                    refine ⟨768275403544280645481553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097468818902830109234949 768275403544280645481553)
                    ·
                      rfl

theorem cell23_4488633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_4488633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488633 prefixEnd_4488633 := by exact prefixLift 4488633
  have htrace : WordTrace (prefixWord ++ tailWord_4488633) baseStart_4488633 baseEnd_4488633 := by
    simpa [prefixWord, tailWord_4488633, baseEnd_4488633] using wordTrace_append hprefix tailTrace_4488633
  have hstable : (prefixWord ++ tailWord_4488633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488633).length < 2 ^ (prefixWord ++ tailWord_4488633).sum := by decide
  have hdescent : baseEnd_4488633 < baseStart_4488633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488666 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_4488666 : Nat := 118140960795 + 4488666 * 2 ^ 59
def prefixEnd_4488666 : Nat := 4983230072969 + 3 ^ 40 * 4488666 * 2
def baseEnd_4488666 : Nat := 2304843155494440307332007

theorem tailTrace_4488666 : CollatzResearch.WordTrace tailWord_4488666 prefixEnd_4488666 2304843155494440307332007 := by
  unfold tailWord_4488666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40928774689084289991379463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109143399170891439977011901 40928774689084289991379463)
  ·
    refine ⟨61393162033626434987069195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40928774689084289991379463 61393162033626434987069195)
    ·
      refine ⟨92089743050439652480603793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61393162033626434987069195 92089743050439652480603793)
      ·
        refine ⟨69067307287829739360452845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92089743050439652480603793 69067307287829739360452845)
        ·
          refine ⟨25900240232936152260169817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69067307287829739360452845 25900240232936152260169817)
          ·
            refine ⟨19425180174702114195127363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25900240232936152260169817 19425180174702114195127363)
            ·
              refine ⟨29137770262053171292691045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19425180174702114195127363 29137770262053171292691045)
              ·
                refine ⟨5463331924134969617379571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29137770262053171292691045 5463331924134969617379571)
                ·
                  refine ⟨8194997886202454426069357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463331924134969617379571 8194997886202454426069357)
                  ·
                    refine ⟨3073124207325920409776009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8194997886202454426069357 3073124207325920409776009)
                    ·
                      refine ⟨2304843155494440307332007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073124207325920409776009 2304843155494440307332007)
                      ·
                        rfl

theorem cell23_4488666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_4488666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488666 prefixEnd_4488666 := by exact prefixLift 4488666
  have htrace : WordTrace (prefixWord ++ tailWord_4488666) baseStart_4488666 baseEnd_4488666 := by
    simpa [prefixWord, tailWord_4488666, baseEnd_4488666] using wordTrace_append hprefix tailTrace_4488666
  have hstable : (prefixWord ++ tailWord_4488666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488666).length < 2 ^ (prefixWord ++ tailWord_4488666).sum := by decide
  have hdescent : baseEnd_4488666 < baseStart_4488666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488696 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_4488696 : Nat := 118140960795 + 4488696 * 2 ^ 59
def prefixEnd_4488696 : Nat := 4983230072969 + 3 ^ 40 * 4488696 * 2
def baseEnd_4488696 : Nat := 2304858559914075189956869

theorem tailTrace_4488696 : CollatzResearch.WordTrace tailWord_4488696 prefixEnd_4488696 2304858559914075189956869 := by
  unfold tailWord_4488696
  simp only [CollatzResearch.WordTrace]
  refine ⟨81858096473114237544554971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109144128630818983392739961 81858096473114237544554971)
  ·
    refine ⟨122787144709671356316832457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81858096473114237544554971 122787144709671356316832457)
    ·
      refine ⟨92090358532253517237624343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122787144709671356316832457 92090358532253517237624343)
      ·
        refine ⟨138135537798380275856436515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92090358532253517237624343 138135537798380275856436515)
        ·
          refine ⟨207203306697570413784654773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138135537798380275856436515 207203306697570413784654773)
          ·
            refine ⟨19425310002897226292311385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207203306697570413784654773 19425310002897226292311385)
            ·
              refine ⟨14568982502172919719233539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19425310002897226292311385 14568982502172919719233539)
              ·
                refine ⟨21853473753259379578850309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14568982502172919719233539 21853473753259379578850309)
                ·
                  refine ⟨4097526328736133671034433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21853473753259379578850309 4097526328736133671034433)
                  ·
                    refine ⟨3073144746552100253275825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4097526328736133671034433 3073144746552100253275825)
                    ·
                      refine ⟨2304858559914075189956869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073144746552100253275825 2304858559914075189956869)
                      ·
                        rfl

theorem cell23_4488696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_4488696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488696 prefixEnd_4488696 := by exact prefixLift 4488696
  have htrace : WordTrace (prefixWord ++ tailWord_4488696) baseStart_4488696 baseEnd_4488696 := by
    simpa [prefixWord, tailWord_4488696, baseEnd_4488696] using wordTrace_append hprefix tailTrace_4488696
  have hstable : (prefixWord ++ tailWord_4488696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488696).length < 2 ^ (prefixWord ++ tailWord_4488696).sum := by decide
  have hdescent : baseEnd_4488696 < baseStart_4488696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488752 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_4488752 : Nat := 118140960795 + 4488752 * 2 ^ 59
def prefixEnd_4488752 : Nat := 4983230072969 + 3 ^ 40 * 4488752 * 2
def baseEnd_4488752 : Nat := 2304887314830726970856611

theorem tailTrace_4488752 : CollatzResearch.WordTrace tailWord_4488752 prefixEnd_4488752 2304887314830726970856611 := by
  unfold tailWord_4488752
  simp only [CollatzResearch.WordTrace]
  refine ⟨81859117717012798326574255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109145490289350397768765673 81859117717012798326574255)
  ·
    refine ⟨122788676575519197489861383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81859117717012798326574255 122788676575519197489861383)
    ·
      refine ⟨184183014863278796234792075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122788676575519197489861383 184183014863278796234792075)
      ·
        refine ⟨276274522294918194352188113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184183014863278796234792075 276274522294918194352188113)
        ·
          refine ⟨207205891721188645764141085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276274522294918194352188113 207205891721188645764141085)
          ·
            refine ⟨77702209395445742161552907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207205891721188645764141085 77702209395445742161552907)
            ·
              refine ⟨116553314093168613242329361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77702209395445742161552907 116553314093168613242329361)
              ·
                refine ⟨87414985569876459931747021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116553314093168613242329361 87414985569876459931747021)
                ·
                  refine ⟨32780619588703672474405133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87414985569876459931747021 32780619588703672474405133)
                  ·
                    refine ⟨12292732345763877177901925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32780619588703672474405133 12292732345763877177901925)
                    ·
                      refine ⟨2304887314830726970856611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12292732345763877177901925 2304887314830726970856611)
                      ·
                        rfl

theorem cell23_4488752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_4488752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488752 prefixEnd_4488752 := by exact prefixLift 4488752
  have htrace : WordTrace (prefixWord ++ tailWord_4488752) baseStart_4488752 baseEnd_4488752 := by
    simpa [prefixWord, tailWord_4488752, baseEnd_4488752] using wordTrace_append hprefix tailTrace_4488752
  have hstable : (prefixWord ++ tailWord_4488752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488752).length < 2 ^ (prefixWord ++ tailWord_4488752).sum := by decide
  have hdescent : baseEnd_4488752 < baseStart_4488752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488769 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4488769 : Nat := 118140960795 + 4488769 * 2 ^ 59
def prefixEnd_4488769 : Nat := 4983230072969 + 3 ^ 40 * 4488769 * 2
def baseEnd_4488769 : Nat := 2304896044001853404344033

theorem tailTrace_4488769 : CollatzResearch.WordTrace tailWord_4488769 prefixEnd_4488769 2304896044001853404344033 := by
  unfold tailWord_4488769
  simp only [CollatzResearch.WordTrace]
  refine ⟨163718855474964008556517361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109145903649976005704344907 163718855474964008556517361)
  ·
    refine ⟨122789141606223006417388021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163718855474964008556517361 122789141606223006417388021)
    ·
      refine ⟨11511482025583406851630127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122789141606223006417388021 11511482025583406851630127)
      ·
        refine ⟨17267223038375110277445191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11511482025583406851630127 17267223038375110277445191)
        ·
          refine ⟨25900834557562665416167787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267223038375110277445191 25900834557562665416167787)
          ·
            refine ⟨38851251836343998124251681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25900834557562665416167787 38851251836343998124251681)
            ·
              refine ⟨29138438877257998593188761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38851251836343998124251681 29138438877257998593188761)
              ·
                refine ⟨21853829157943498944891571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29138438877257998593188761 21853829157943498944891571)
                ·
                  refine ⟨32780743736915248417337357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21853829157943498944891571 32780743736915248417337357)
                  ·
                    refine ⟨12292778901343218156501509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32780743736915248417337357 12292778901343218156501509)
                    ·
                      refine ⟨2304896044001853404344033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12292778901343218156501509 2304896044001853404344033)
                      ·
                        rfl

theorem cell23_4488769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4488769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488769 prefixEnd_4488769 := by exact prefixLift 4488769
  have htrace : WordTrace (prefixWord ++ tailWord_4488769) baseStart_4488769 baseEnd_4488769 := by
    simpa [prefixWord, tailWord_4488769, baseEnd_4488769] using wordTrace_append hprefix tailTrace_4488769
  have hstable : (prefixWord ++ tailWord_4488769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488769).length < 2 ^ (prefixWord ++ tailWord_4488769).sum := by decide
  have hdescent : baseEnd_4488769 < baseStart_4488769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488786 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_4488786 : Nat := 118140960795 + 4488786 * 2 ^ 59
def prefixEnd_4488786 : Nat := 4983230072969 + 3 ^ 40 * 4488786 * 2
def baseEnd_4488786 : Nat := 2304904773172979837831455

theorem tailTrace_4488786 : CollatzResearch.WordTrace tailWord_4488786 prefixEnd_4488786 2304904773172979837831455 := by
  unfold tailWord_4488786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40929868878975605114971553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109146317010601613639924141 40929868878975605114971553)
  ·
    refine ⟨30697401659231703836228665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40929868878975605114971553 30697401659231703836228665)
    ·
      refine ⟨23023051244423777877171499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30697401659231703836228665 23023051244423777877171499)
      ·
        refine ⟨34534576866635666815757249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23023051244423777877171499 34534576866635666815757249)
        ·
          refine ⟨25900932649976750111817937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34534576866635666815757249 25900932649976750111817937)
          ·
            refine ⟨19425699487482562583863453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25900932649976750111817937 19425699487482562583863453)
            ·
              refine ⟨7284637307805960968948795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19425699487482562583863453 7284637307805960968948795)
              ·
                refine ⟨10926955961708941453423193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284637307805960968948795 10926955961708941453423193)
                ·
                  refine ⟨8195216971281706090067395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10926955961708941453423193 8195216971281706090067395)
                  ·
                    refine ⟨12292825456922559135101093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8195216971281706090067395 12292825456922559135101093)
                    ·
                      refine ⟨2304904773172979837831455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12292825456922559135101093 2304904773172979837831455)
                      ·
                        rfl

theorem cell23_4488786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_4488786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488786 prefixEnd_4488786 := by exact prefixLift 4488786
  have htrace : WordTrace (prefixWord ++ tailWord_4488786) baseStart_4488786 baseEnd_4488786 := by
    simpa [prefixWord, tailWord_4488786, baseEnd_4488786] using wordTrace_append hprefix tailTrace_4488786
  have hstable : (prefixWord ++ tailWord_4488786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488786).length < 2 ^ (prefixWord ++ tailWord_4488786).sum := by decide
  have hdescent : baseEnd_4488786 < baseStart_4488786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488792 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 8]
def baseStart_4488792 : Nat := 118140960795 + 4488792 * 2 ^ 59
def prefixEnd_4488792 : Nat := 4983230072969 + 3 ^ 40 * 4488792 * 2
def baseEnd_4488792 : Nat := 256100872672989646039603

theorem tailTrace_4488792 : CollatzResearch.WordTrace tailWord_4488792 prefixEnd_4488792 256100872672989646039603 := by
  unfold tailWord_4488792
  simp only [CollatzResearch.WordTrace]
  refine ⟨81859847176940341742302315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109146462902587122323069753 81859847176940341742302315)
  ·
    refine ⟨122789770765410512613453473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81859847176940341742302315 122789770765410512613453473)
    ·
      refine ⟨92092328074057884460090105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122789770765410512613453473 92092328074057884460090105)
      ·
        refine ⟨69069246055543413345067579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92092328074057884460090105 69069246055543413345067579)
        ·
          refine ⟨103603869083315120017601369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69069246055543413345067579 103603869083315120017601369)
          ·
            refine ⟨77702901812486340013201027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103603869083315120017601369 77702901812486340013201027)
            ·
              refine ⟨116554352718729510019801541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77702901812486340013201027 116554352718729510019801541)
              ·
                refine ⟨21853941134761783128712789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116554352718729510019801541 21853941134761783128712789)
                ·
                  refine ⟨256100872672989646039603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21853941134761783128712789 256100872672989646039603)
                  ·
                    rfl

theorem cell23_4488792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_4488792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488792 prefixEnd_4488792 := by exact prefixLift 4488792
  have htrace : WordTrace (prefixWord ++ tailWord_4488792) baseStart_4488792 baseEnd_4488792 := by
    simpa [prefixWord, tailWord_4488792, baseEnd_4488792] using wordTrace_append hprefix tailTrace_4488792
  have hstable : (prefixWord ++ tailWord_4488792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488792).length < 2 ^ (prefixWord ++ tailWord_4488792).sum := by decide
  have hdescent : baseEnd_4488792 < baseStart_4488792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488809 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 6]
def baseStart_4488809 : Nat := 118140960795 + 4488809 * 2 ^ 59
def prefixEnd_4488809 : Nat := 4983230072969 + 3 ^ 40 * 4488809 * 2
def baseEnd_4488809 : Nat := 256101842580892583093761

theorem tailTrace_4488809 : CollatzResearch.WordTrace tailWord_4488809 prefixEnd_4488809 256101842580892583093761 := by
  unfold tailWord_4488809
  simp only [CollatzResearch.WordTrace]
  refine ⟨163720314394819095387973481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109146876263212730258648987 163720314394819095387973481)
  ·
    refine ⟨122790235796114321540980111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163720314394819095387973481 122790235796114321540980111)
    ·
      refine ⟨184185353694171482311470167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122790235796114321540980111 184185353694171482311470167)
      ·
        refine ⟨276278030541257223467205251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184185353694171482311470167 276278030541257223467205251)
        ·
          refine ⟨414417045811885835200807877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276278030541257223467205251 414417045811885835200807877)
          ·
            refine ⟨77703196089728594100151477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414417045811885835200807877 77703196089728594100151477)
            ·
              refine ⟨7284674633412055696889201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77703196089728594100151477 7284674633412055696889201)
              ·
                refine ⟨5463505975059041772666901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7284674633412055696889201 5463505975059041772666901)
                ·
                  refine ⟨256101842580892583093761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5463505975059041772666901 256101842580892583093761)
                  ·
                    rfl

theorem cell23_4488809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_4488809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488809 prefixEnd_4488809 := by exact prefixLift 4488809
  have htrace : WordTrace (prefixWord ++ tailWord_4488809) baseStart_4488809 baseEnd_4488809 := by
    simpa [prefixWord, tailWord_4488809, baseEnd_4488809] using wordTrace_append hprefix tailTrace_4488809
  have hstable : (prefixWord ++ tailWord_4488809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488809).length < 2 ^ (prefixWord ++ tailWord_4488809).sum := by decide
  have hdescent : baseEnd_4488809 < baseStart_4488809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488813 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_4488813 : Nat := 118140960795 + 4488813 * 2 ^ 59
def prefixEnd_4488813 : Nat := 4983230072969 + 3 ^ 40 * 4488813 * 2
def baseEnd_4488813 : Nat := 768306212383550410731277

theorem tailTrace_4488813 : CollatzResearch.WordTrace tailWord_4488813 prefixEnd_4488813 768306212383550410731277 := by
  unfold tailWord_4488813
  simp only [CollatzResearch.WordTrace]
  refine ⟨163720460286804604071119093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109146973524536402714079395 163720460286804604071119093)
  ·
    refine ⟨15348793151887931631667415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163720460286804604071119093 15348793151887931631667415)
    ·
      refine ⟨23023189727831897447501123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15348793151887931631667415 23023189727831897447501123)
      ·
        refine ⟨34534784591747846171251685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23023189727831897447501123 34534784591747846171251685)
        ·
          refine ⟨6475272110952721157109691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34534784591747846171251685 6475272110952721157109691)
          ·
            refine ⟨9712908166429081735664537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475272110952721157109691 9712908166429081735664537)
            ·
              refine ⟨7284681124821811301748403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9712908166429081735664537 7284681124821811301748403)
              ·
                refine ⟨10927021687232716952622605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284681124821811301748403 10927021687232716952622605)
                ·
                  refine ⟨4097633132712268857233477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10927021687232716952622605 4097633132712268857233477)
                  ·
                    refine ⟨768306212383550410731277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4097633132712268857233477 768306212383550410731277)
                    ·
                      rfl

theorem cell23_4488813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_4488813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488813 prefixEnd_4488813 := by exact prefixLift 4488813
  have htrace : WordTrace (prefixWord ++ tailWord_4488813) baseStart_4488813 baseEnd_4488813 := by
    simpa [prefixWord, tailWord_4488813, baseEnd_4488813] using wordTrace_append hprefix tailTrace_4488813
  have hstable : (prefixWord ++ tailWord_4488813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488813).length < 2 ^ (prefixWord ++ tailWord_4488813).sum := by decide
  have hdescent : baseEnd_4488813 < baseStart_4488813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488856 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_4488856 : Nat := 118140960795 + 4488856 * 2 ^ 59
def prefixEnd_4488856 : Nat := 4983230072969 + 3 ^ 40 * 4488856 * 2
def baseEnd_4488856 : Nat := 768313572272931521318711

theorem tailTrace_4488856 : CollatzResearch.WordTrace tailWord_4488856 prefixEnd_4488856 768313572272931521318711 := by
  unfold tailWord_4488856
  simp only [CollatzResearch.WordTrace]
  refine ⟨81861014312824411207467211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109148019083765881609956281 81861014312824411207467211)
  ·
    refine ⟨122791521469236616811200817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81861014312824411207467211 122791521469236616811200817)
    ·
      refine ⟨92093641101927462608400613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122791521469236616811200817 92093641101927462608400613)
      ·
        refine ⟨17267557706611399239075115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92093641101927462608400613 17267557706611399239075115)
        ·
          refine ⟨25901336559917098858612673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267557706611399239075115 25901336559917098858612673)
          ·
            refine ⟨19426002419937824143959505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25901336559917098858612673 19426002419937824143959505)
            ·
              refine ⟨14569501814953368107969629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19426002419937824143959505 14569501814953368107969629)
              ·
                refine ⟨5463563180607513040488611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14569501814953368107969629 5463563180607513040488611)
                ·
                  refine ⟨8195344770911269560732917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463563180607513040488611 8195344770911269560732917)
                  ·
                    refine ⟨768313572272931521318711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8195344770911269560732917 768313572272931521318711)
                    ·
                      rfl

theorem cell23_4488856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_4488856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488856 prefixEnd_4488856 := by exact prefixLift 4488856
  have htrace : WordTrace (prefixWord ++ tailWord_4488856) baseStart_4488856 baseEnd_4488856 := by
    simpa [prefixWord, tailWord_4488856, baseEnd_4488856] using wordTrace_append hprefix tailTrace_4488856
  have hstable : (prefixWord ++ tailWord_4488856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488856).length < 2 ^ (prefixWord ++ tailWord_4488856).sum := by decide
  have hdescent : baseEnd_4488856 < baseStart_4488856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488879 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_4488879 : Nat := 118140960795 + 4488879 * 2 ^ 59
def prefixEnd_4488879 : Nat := 4983230072969 + 3 ^ 40 * 4488879 * 2
def baseEnd_4488879 : Nat := 2304952526873847973968527

theorem tailTrace_4488879 : CollatzResearch.WordTrace tailWord_4488879 prefixEnd_4488879 2304952526873847973968527 := by
  unfold tailWord_4488879
  simp only [CollatzResearch.WordTrace]
  refine ⟨163722867504565497343021691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109148578336376998228681127 163722867504565497343021691)
  ·
    refine ⟨245584301256848246014532537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163722867504565497343021691 245584301256848246014532537)
    ·
      refine ⟨184188225942636184510899403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245584301256848246014532537 184188225942636184510899403)
      ·
        refine ⟨276282338913954276766349105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184188225942636184510899403 276282338913954276766349105)
        ·
          refine ⟨207211754185465707574761829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276282338913954276766349105 207211754185465707574761829)
          ·
            refine ⟨38852203909774820170267843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207211754185465707574761829 38852203909774820170267843)
            ·
              refine ⟨58278305864662230255401765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38852203909774820170267843 58278305864662230255401765)
              ·
                refine ⟨10927182349624168172887831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58278305864662230255401765 10927182349624168172887831)
                ·
                  refine ⟨16390773524436252259331747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10927182349624168172887831 16390773524436252259331747)
                  ·
                    refine ⟨24586160286654378388997621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16390773524436252259331747 24586160286654378388997621)
                    ·
                      refine ⟨2304952526873847973968527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24586160286654378388997621 2304952526873847973968527)
                      ·
                        rfl

theorem cell23_4488879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_4488879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488879 prefixEnd_4488879 := by exact prefixLift 4488879
  have htrace : WordTrace (prefixWord ++ tailWord_4488879) baseStart_4488879 baseEnd_4488879 := by
    simpa [prefixWord, tailWord_4488879, baseEnd_4488879] using wordTrace_append hprefix tailTrace_4488879
  have hstable : (prefixWord ++ tailWord_4488879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488879).length < 2 ^ (prefixWord ++ tailWord_4488879).sum := by decide
  have hdescent : baseEnd_4488879 < baseStart_4488879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488889 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4488889 : Nat := 118140960795 + 4488889 * 2 ^ 59
def prefixEnd_4488889 : Nat := 4983230072969 + 3 ^ 40 * 4488889 * 2
def baseEnd_4488889 : Nat := 2304957661680392934843481

theorem tailTrace_4488889 : CollatzResearch.WordTrace tailWord_4488889 prefixEnd_4488889 2304957661680392934843481 := by
  unfold tailWord_4488889
  simp only [CollatzResearch.WordTrace]
  refine ⟨163723232234529269050885721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109148821489686179367257147 163723232234529269050885721)
  ·
    refine ⟨122792424175896951788164291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163723232234529269050885721 122792424175896951788164291)
    ·
      refine ⟨184188636263845427682246437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122792424175896951788164291 184188636263845427682246437)
      ·
        refine ⟨34535369299471017690421207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184188636263845427682246437 34535369299471017690421207)
        ·
          refine ⟨51803053949206526535631811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34535369299471017690421207 51803053949206526535631811)
          ·
            refine ⟨77704580923809789803447717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51803053949206526535631811 77704580923809789803447717)
            ·
              refine ⟨14569608923214335588146447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77704580923809789803447717 14569608923214335588146447)
              ·
                refine ⟨21854413384821503382219671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14569608923214335588146447 21854413384821503382219671)
                ·
                  refine ⟨32781620077232255073329507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21854413384821503382219671 32781620077232255073329507)
                  ·
                    refine ⟨49172430115848382609994261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32781620077232255073329507 49172430115848382609994261)
                    ·
                      refine ⟨2304957661680392934843481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49172430115848382609994261 2304957661680392934843481)
                      ·
                        rfl

theorem cell23_4488889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4488889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488889 prefixEnd_4488889 := by exact prefixLift 4488889
  have htrace : WordTrace (prefixWord ++ tailWord_4488889) baseStart_4488889 baseEnd_4488889 := by
    simpa [prefixWord, tailWord_4488889, baseEnd_4488889] using wordTrace_append hprefix tailTrace_4488889
  have hstable : (prefixWord ++ tailWord_4488889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488889).length < 2 ^ (prefixWord ++ tailWord_4488889).sum := by decide
  have hdescent : baseEnd_4488889 < baseStart_4488889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488893 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4488893 : Nat := 118140960795 + 4488893 * 2 ^ 59
def prefixEnd_4488893 : Nat := 4983230072969 + 3 ^ 40 * 4488893 * 2
def baseEnd_4488893 : Nat := 2304959715603010919193463

theorem tailTrace_4488893 : CollatzResearch.WordTrace tailWord_4488893 prefixEnd_4488893 2304959715603010919193463 := by
  unfold tailWord_4488893
  simp only [CollatzResearch.WordTrace]
  refine ⟨163723378126514777734031333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109148918751009851822687555 163723378126514777734031333)
  ·
    refine ⟨30698133398721520825130875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163723378126514777734031333 30698133398721520825130875)
    ·
      refine ⟨46047200098082281237696313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30698133398721520825130875 46047200098082281237696313)
      ·
        refine ⟨34535400073561710928272235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46047200098082281237696313 34535400073561710928272235)
        ·
          refine ⟨51803100110342566392408353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34535400073561710928272235 51803100110342566392408353)
          ·
            refine ⟨38852325082756924794306265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51803100110342566392408353 38852325082756924794306265)
            ·
              refine ⟨29139243812067693595729699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38852325082756924794306265 29139243812067693595729699)
              ·
                refine ⟨43708865718101540393594549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29139243812067693595729699 43708865718101540393594549)
                ·
                  refine ⟨4097706161072019411899489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43708865718101540393594549 4097706161072019411899489)
                  ·
                    refine ⟨3073279620804014558924617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4097706161072019411899489 3073279620804014558924617)
                    ·
                      refine ⟨2304959715603010919193463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073279620804014558924617 2304959715603010919193463)
                      ·
                        rfl

theorem cell23_4488893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4488893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488893 prefixEnd_4488893 := by exact prefixLift 4488893
  have htrace : WordTrace (prefixWord ++ tailWord_4488893) baseStart_4488893 baseEnd_4488893 := by
    simpa [prefixWord, tailWord_4488893, baseEnd_4488893] using wordTrace_append hprefix tailTrace_4488893
  have hstable : (prefixWord ++ tailWord_4488893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488893).length < 2 ^ (prefixWord ++ tailWord_4488893).sum := by decide
  have hdescent : baseEnd_4488893 < baseStart_4488893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488896 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_4488896 : Nat := 118140960795 + 4488896 * 2 ^ 59
def prefixEnd_4488896 : Nat := 4983230072969 + 3 ^ 40 * 4488896 * 2
def baseEnd_4488896 : Nat := 2304961256044974407455949

theorem tailTrace_4488896 : CollatzResearch.WordTrace tailWord_4488896 prefixEnd_4488896 2304961256044974407455949 := by
  unfold tailWord_4488896
  simp only [CollatzResearch.WordTrace]
  refine ⟨81861743772751954623195271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109148991697002606164260361 81861743772751954623195271)
  ·
    refine ⟨122792615659127931934792907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81861743772751954623195271 122792615659127931934792907)
    ·
      refine ⟨184188923488691897902189361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122792615659127931934792907 184188923488691897902189361)
      ·
        refine ⟨138141692616518923426642021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184188923488691897902189361 138141692616518923426642021)
        ·
          refine ⟨25901567365597298142495379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138141692616518923426642021 25901567365597298142495379)
          ·
            refine ⟨38852351048395947213743069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25901567365597298142495379 38852351048395947213743069)
            ·
              refine ⟨14569631643148480205153651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38852351048395947213743069 14569631643148480205153651)
              ·
                refine ⟨21854447464722720307730477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14569631643148480205153651 21854447464722720307730477)
                ·
                  refine ⟨8195417799271020115398929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21854447464722720307730477 8195417799271020115398929)
                  ·
                    refine ⟨6146563349453265086549197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8195417799271020115398929 6146563349453265086549197)
                    ·
                      refine ⟨2304961256044974407455949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146563349453265086549197 2304961256044974407455949)
                      ·
                        rfl

theorem cell23_4488896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_4488896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488896 prefixEnd_4488896 := by exact prefixLift 4488896
  have htrace : WordTrace (prefixWord ++ tailWord_4488896) baseStart_4488896 baseEnd_4488896 := by
    simpa [prefixWord, tailWord_4488896, baseEnd_4488896] using wordTrace_append hprefix tailTrace_4488896
  have hstable : (prefixWord ++ tailWord_4488896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488896).length < 2 ^ (prefixWord ++ tailWord_4488896).sum := by decide
  have hdescent : baseEnd_4488896 < baseStart_4488896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488943 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_4488943 : Nat := 118140960795 + 4488943 * 2 ^ 59
def prefixEnd_4488943 : Nat := 4983230072969 + 3 ^ 40 * 4488943 * 2
def baseEnd_4488943 : Nat := 2304985389635735723568233

theorem tailTrace_4488943 : CollatzResearch.WordTrace tailWord_4488943 prefixEnd_4488943 2304985389635735723568233 := by
  unfold tailWord_4488943
  simp only [CollatzResearch.WordTrace]
  refine ⟨163725201776333636273351483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109150134517555757515567655 163725201776333636273351483)
  ·
    refine ⟨245587802664500454410027225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163725201776333636273351483 245587802664500454410027225)
    ·
      refine ⟨184190851998375340807520419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245587802664500454410027225 184190851998375340807520419)
      ·
        refine ⟨276286277997563011211280629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184190851998375340807520419 276286277997563011211280629)
        ·
          refine ⟨25901838562271532301057559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276286277997563011211280629 25901838562271532301057559)
          ·
            refine ⟨38852757843407298451586339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25901838562271532301057559 38852757843407298451586339)
            ·
              refine ⟨58279136765110947677379509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38852757843407298451586339 58279136765110947677379509)
              ·
                refine ⟨5463669071729151344754329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58279136765110947677379509 5463669071729151344754329)
                ·
                  refine ⟨4097751803796863508565747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5463669071729151344754329 4097751803796863508565747)
                  ·
                    refine ⟨6146627705695295262848621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097751803796863508565747 6146627705695295262848621)
                    ·
                      refine ⟨2304985389635735723568233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146627705695295262848621 2304985389635735723568233)
                      ·
                        rfl

theorem cell23_4488943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_4488943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488943 prefixEnd_4488943 := by exact prefixLift 4488943
  have htrace : WordTrace (prefixWord ++ tailWord_4488943) baseStart_4488943 baseEnd_4488943 := by
    simpa [prefixWord, tailWord_4488943, baseEnd_4488943] using wordTrace_append hprefix tailTrace_4488943
  have hstable : (prefixWord ++ tailWord_4488943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488943).length < 2 ^ (prefixWord ++ tailWord_4488943).sum := by decide
  have hdescent : baseEnd_4488943 < baseStart_4488943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488969 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_4488969 : Nat := 118140960795 + 4488969 * 2 ^ 59
def prefixEnd_4488969 : Nat := 4983230072969 + 3 ^ 40 * 4488969 * 2
def baseEnd_4488969 : Nat := 2304998740132752621843113

theorem tailTrace_4488969 : CollatzResearch.WordTrace tailWord_4488969 prefixEnd_4488969 2304998740132752621843113 := by
  unfold tailWord_4488969
  simp only [CollatzResearch.WordTrace]
  refine ⟨163726150074239442713797961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109150766716159628475865307 163726150074239442713797961)
  ·
    refine ⟨122794612555679582035348471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163726150074239442713797961 122794612555679582035348471)
    ·
      refine ⟨184191918833519373053022707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122794612555679582035348471 184191918833519373053022707)
      ·
        refine ⟨276287878250279059579534061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184191918833519373053022707 276287878250279059579534061)
        ·
          refine ⟨103607954343854647342325273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276287878250279059579534061 103607954343854647342325273)
          ·
            refine ⟨77705965757890985506743955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103607954343854647342325273 77705965757890985506743955)
            ·
              refine ⟨116558948636836478260115933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77705965757890985506743955 116558948636836478260115933)
              ·
                refine ⟨43709605738813679347543475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116558948636836478260115933 43709605738813679347543475)
                ·
                  refine ⟨65564408608220519021315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43709605738813679347543475 65564408608220519021315213)
                  ·
                    refine ⟨24586653228082694632993205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65564408608220519021315213 24586653228082694632993205)
                    ·
                      refine ⟨2304998740132752621843113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24586653228082694632993205 2304998740132752621843113)
                      ·
                        rfl

theorem cell23_4488969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_4488969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488969 prefixEnd_4488969 := by exact prefixLift 4488969
  have htrace : WordTrace (prefixWord ++ tailWord_4488969) baseStart_4488969 baseEnd_4488969 := by
    simpa [prefixWord, tailWord_4488969, baseEnd_4488969] using wordTrace_append hprefix tailTrace_4488969
  have hstable : (prefixWord ++ tailWord_4488969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488969).length < 2 ^ (prefixWord ++ tailWord_4488969).sum := by decide
  have hdescent : baseEnd_4488969 < baseStart_4488969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4488970 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_4488970 : Nat := 118140960795 + 4488970 * 2 ^ 59
def prefixEnd_4488970 : Nat := 4983230072969 + 3 ^ 40 * 4488970 * 2
def baseEnd_4488970 : Nat := 2304999253613407117930609

theorem tailTrace_4488970 : CollatzResearch.WordTrace tailWord_4488970 prefixEnd_4488970 2304999253613407117930609 := by
  unfold tailWord_4488970
  simp only [CollatzResearch.WordTrace]
  refine ⟨40931546636808954971146091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109150791031490546589722909 40931546636808954971146091)
  ·
    refine ⟨61397319955213432456719137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40931546636808954971146091 61397319955213432456719137)
    ·
      refine ⟨46047989966410074342539353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61397319955213432456719137 46047989966410074342539353)
      ·
        refine ⟨34535992474807555756904515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46047989966410074342539353 34535992474807555756904515)
        ·
          refine ⟨51803988712211333635356773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34535992474807555756904515 51803988712211333635356773)
          ·
            refine ⟨9713247883539625056629395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51803988712211333635356773 9713247883539625056629395)
            ·
              refine ⟨14569871825309437584944093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9713247883539625056629395 14569871825309437584944093)
              ·
                refine ⟨5463701934491039094354035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14569871825309437584944093 5463701934491039094354035)
                ·
                  refine ⟨8195552901736558641531053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463701934491039094354035 8195552901736558641531053)
                  ·
                    refine ⟨3073332338151209490574145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8195552901736558641531053 3073332338151209490574145)
                    ·
                      refine ⟨2304999253613407117930609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073332338151209490574145 2304999253613407117930609)
                      ·
                        rfl

theorem cell23_4488970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_4488970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4488970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4488970 prefixEnd_4488970 := by exact prefixLift 4488970
  have htrace : WordTrace (prefixWord ++ tailWord_4488970) baseStart_4488970 baseEnd_4488970 := by
    simpa [prefixWord, tailWord_4488970, baseEnd_4488970] using wordTrace_append hprefix tailTrace_4488970
  have hstable : (prefixWord ++ tailWord_4488970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4488970).length < 2 ^ (prefixWord ++ tailWord_4488970).sum := by decide
  have hdescent : baseEnd_4488970 < baseStart_4488970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4488970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489000 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4489000 : Nat := 118140960795 + 4489000 * 2 ^ 59
def prefixEnd_4489000 : Nat := 4983230072969 + 3 ^ 40 * 4489000 * 2
def baseEnd_4489000 : Nat := 2305014658033042000555471

theorem tailTrace_4489000 : CollatzResearch.WordTrace tailWord_4489000 prefixEnd_4489000 2305014658033042000555471 := by
  unfold tailWord_4489000
  simp only [CollatzResearch.WordTrace]
  refine ⟨81863640368563567504088227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109151520491418090005450969 81863640368563567504088227)
  ·
    refine ⟨122795460552845351256132341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81863640368563567504088227 122795460552845351256132341)
    ·
      refine ⟨11512074426829251680262407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122795460552845351256132341 11512074426829251680262407)
      ·
        refine ⟨17268111640243877520393611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11512074426829251680262407 17268111640243877520393611)
        ·
          refine ⟨25902167460365816280590417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17268111640243877520393611 25902167460365816280590417)
          ·
            refine ⟨19426625595274362210442813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25902167460365816280590417 19426625595274362210442813)
            ·
              refine ⟨7284984598227885828916055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19426625595274362210442813 7284984598227885828916055)
              ·
                refine ⟨10927476897341828743374083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284984598227885828916055 10927476897341828743374083)
                ·
                  refine ⟨16391215346012743115061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10927476897341828743374083 16391215346012743115061125)
                  ·
                    refine ⟨3073352877377389334073961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16391215346012743115061125 3073352877377389334073961)
                    ·
                      refine ⟨2305014658033042000555471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073352877377389334073961 2305014658033042000555471)
                      ·
                        rfl

theorem cell23_4489000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4489000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489000 prefixEnd_4489000 := by exact prefixLift 4489000
  have htrace : WordTrace (prefixWord ++ tailWord_4489000) baseStart_4489000 baseEnd_4489000 := by
    simpa [prefixWord, tailWord_4489000, baseEnd_4489000] using wordTrace_append hprefix tailTrace_4489000
  have hstable : (prefixWord ++ tailWord_4489000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489000).length < 2 ^ (prefixWord ++ tailWord_4489000).sum := by decide
  have hdescent : baseEnd_4489000 < baseStart_4489000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489039 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_4489039 : Nat := 118140960795 + 4489039 * 2 ^ 59
def prefixEnd_4489039 : Nat := 4983230072969 + 3 ^ 40 * 4489039 * 2
def baseEnd_4489039 : Nat := 2305034683778567347967791

theorem tailTrace_4489039 : CollatzResearch.WordTrace tailWord_4489039 prefixEnd_4489039 2305034683778567347967791 := by
  unfold tailWord_4489039
  simp only [CollatzResearch.WordTrace]
  refine ⟨163728703183985844668846171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109152468789323896445897447 163728703183985844668846171)
  ·
    refine ⟨245593054775978767003269257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163728703183985844668846171 245593054775978767003269257)
    ·
      refine ⟨184194791081984075252451943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245593054775978767003269257 184194791081984075252451943)
      ·
        refine ⟨276292186622976112878677915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184194791081984075252451943 276292186622976112878677915)
        ·
          refine ⟨414438279934464169318016873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276292186622976112878677915 414438279934464169318016873)
          ·
            refine ⟨310828709950848126988512655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414438279934464169318016873 310828709950848126988512655)
            ·
              refine ⟨466243064926272190482768983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310828709950848126988512655 466243064926272190482768983)
              ·
                refine ⟨699364597389408285724153475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466243064926272190482768983 699364597389408285724153475)
                ·
                  refine ⟨1049046896084112428586230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699364597389408285724153475 1049046896084112428586230213)
                  ·
                    refine ⟨196696293015771080359918165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049046896084112428586230213 196696293015771080359918165)
                    ·
                      refine ⟨2305034683778567347967791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 196696293015771080359918165 2305034683778567347967791)
                      ·
                        rfl

theorem cell23_4489039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_4489039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489039 prefixEnd_4489039 := by exact prefixLift 4489039
  have htrace : WordTrace (prefixWord ++ tailWord_4489039) baseStart_4489039 baseEnd_4489039 := by
    simpa [prefixWord, tailWord_4489039, baseEnd_4489039] using wordTrace_append hprefix tailTrace_4489039
  have hstable : (prefixWord ++ tailWord_4489039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489039).length < 2 ^ (prefixWord ++ tailWord_4489039).sum := by decide
  have hdescent : baseEnd_4489039 < baseStart_4489039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489070 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4489070 : Nat := 118140960795 + 4489070 * 2 ^ 59
def prefixEnd_4489070 : Nat := 4983230072969 + 3 ^ 40 * 4489070 * 2
def baseEnd_4489070 : Nat := 768350200559618908893383

theorem tailTrace_4489070 : CollatzResearch.WordTrace tailWord_4489070 prefixEnd_4489070 768350200559618908893383 := by
  unfold tailWord_4489070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466229230859192120403083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109153222564582357975483109 20466229230859192120403083)
  ·
    refine ⟨30699343846288788180604625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20466229230859192120403083 30699343846288788180604625)
    ·
      refine ⟨23024507884716591135453469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30699343846288788180604625 23024507884716591135453469)
      ·
        refine ⟨8634190456768721675795051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23024507884716591135453469 8634190456768721675795051)
        ·
          refine ⟨12951285685153082513692577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634190456768721675795051 12951285685153082513692577)
          ·
            refine ⟨9713464263864811885269433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12951285685153082513692577 9713464263864811885269433)
            ·
              refine ⟨7285098197898608913952075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9713464263864811885269433 7285098197898608913952075)
              ·
                refine ⟨10927647296847913370928113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285098197898608913952075 10927647296847913370928113)
                ·
                  refine ⟨8195735472635935028196085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10927647296847913370928113 8195735472635935028196085)
                  ·
                    refine ⟨768350200559618908893383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8195735472635935028196085 768350200559618908893383)
                    ·
                      rfl

theorem cell23_4489070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4489070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489070 prefixEnd_4489070 := by exact prefixLift 4489070
  have htrace : WordTrace (prefixWord ++ tailWord_4489070) baseStart_4489070 baseEnd_4489070 := by
    simpa [prefixWord, tailWord_4489070, baseEnd_4489070] using wordTrace_append hprefix tailTrace_4489070
  have hstable : (prefixWord ++ tailWord_4489070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489070).length < 2 ^ (prefixWord ++ tailWord_4489070).sum := by decide
  have hdescent : baseEnd_4489070 < baseStart_4489070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489073 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_4489073 : Nat := 118140960795 + 4489073 * 2 ^ 59
def prefixEnd_4489073 : Nat := 4983230072969 + 3 ^ 40 * 4489073 * 2
def baseEnd_4489073 : Nat := 2305052142120820214942635

theorem tailTrace_4489073 : CollatzResearch.WordTrace tailWord_4489073 prefixEnd_4489073 2305052142120820214942635 := by
  unfold tailWord_4489073
  simp only [CollatzResearch.WordTrace]
  refine ⟨163729943265862668475583873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109153295510575112317055915 163729943265862668475583873)
  ·
    refine ⟨122797457449397001356687905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163729943265862668475583873 122797457449397001356687905)
    ·
      refine ⟨92098093087047751017515929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122797457449397001356687905 92098093087047751017515929)
      ·
        refine ⟨69073569815285813263136947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92098093087047751017515929 69073569815285813263136947)
        ·
          refine ⟨103610354722928719894705421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69073569815285813263136947 103610354722928719894705421)
          ·
            refine ⟨38853883021098269960514533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103610354722928719894705421 38853883021098269960514533)
            ·
              refine ⟨7285103066455925617596475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38853883021098269960514533 7285103066455925617596475)
              ·
                refine ⟨10927654599683888426394713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285103066455925617596475 10927654599683888426394713)
                ·
                  refine ⟨8195740949762916319796035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10927654599683888426394713 8195740949762916319796035)
                  ·
                    refine ⟨12293611424644374479694053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8195740949762916319796035 12293611424644374479694053)
                    ·
                      refine ⟨2305052142120820214942635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12293611424644374479694053 2305052142120820214942635)
                      ·
                        rfl

theorem cell23_4489073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_4489073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489073 prefixEnd_4489073 := by exact prefixLift 4489073
  have htrace : WordTrace (prefixWord ++ tailWord_4489073) baseStart_4489073 baseEnd_4489073 := by
    simpa [prefixWord, tailWord_4489073, baseEnd_4489073] using wordTrace_append hprefix tailTrace_4489073
  have hstable : (prefixWord ++ tailWord_4489073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489073).length < 2 ^ (prefixWord ++ tailWord_4489073).sum := by decide
  have hdescent : baseEnd_4489073 < baseStart_4489073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489093 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_4489093 : Nat := 118140960795 + 4489093 * 2 ^ 59
def prefixEnd_4489093 : Nat := 4983230072969 + 3 ^ 40 * 4489093 * 2
def baseEnd_4489093 : Nat := 2305062411733910136692543

theorem tailTrace_4489093 : CollatzResearch.WordTrace tailWord_4489093 prefixEnd_4489093 2305062411733910136692543 := by
  unfold tailWord_4489093
  simp only [CollatzResearch.WordTrace]
  refine ⟨163730672725790211891311933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109153781817193474594207955 163730672725790211891311933)
  ·
    refine ⟨61399002272171329459241975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163730672725790211891311933 61399002272171329459241975)
    ·
      refine ⟨92098503408256994188862963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61399002272171329459241975 92098503408256994188862963)
      ·
        refine ⟨138147755112385491283294445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92098503408256994188862963 138147755112385491283294445)
        ·
          refine ⟨51805408167144559231235417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138147755112385491283294445 51805408167144559231235417)
          ·
            refine ⟨38854056125358419423426563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51805408167144559231235417 38854056125358419423426563)
            ·
              refine ⟨58281084188037629135139845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38854056125358419423426563 58281084188037629135139845)
              ·
                refine ⟨10927703285257055462838721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58281084188037629135139845 10927703285257055462838721)
                ·
                  refine ⟨8195777463942791597129041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10927703285257055462838721 8195777463942791597129041)
                  ·
                    refine ⟨6146833097957093697846781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8195777463942791597129041 6146833097957093697846781)
                    ·
                      refine ⟨2305062411733910136692543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146833097957093697846781 2305062411733910136692543)
                      ·
                        rfl

theorem cell23_4489093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_4489093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489093 prefixEnd_4489093 := by exact prefixLift 4489093
  have htrace : WordTrace (prefixWord ++ tailWord_4489093) baseStart_4489093 baseEnd_4489093 := by
    simpa [prefixWord, tailWord_4489093, baseEnd_4489093] using wordTrace_append hprefix tailTrace_4489093
  have hstable : (prefixWord ++ tailWord_4489093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489093).length < 2 ^ (prefixWord ++ tailWord_4489093).sum := by decide
  have hdescent : baseEnd_4489093 < baseStart_4489093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489127 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4489127 : Nat := 118140960795 + 4489127 * 2 ^ 59
def prefixEnd_4489127 : Nat := 4983230072969 + 3 ^ 40 * 4489127 * 2
def baseEnd_4489127 : Nat := 2305079870076163003667387

theorem tailTrace_4489127 : CollatzResearch.WordTrace tailWord_4489127 prefixEnd_4489127 2305079870076163003667387 := by
  unfold tailWord_4489127
  simp only [CollatzResearch.WordTrace]
  refine ⟨163731912807667035698049635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109154608538444690465366423 163731912807667035698049635)
  ·
    refine ⟨245597869211500553547074453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163731912807667035698049635 245597869211500553547074453)
    ·
      refine ⟨11512400119289088447519115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245597869211500553547074453 11512400119289088447519115)
      ·
        refine ⟨17268600178933632671278673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11512400119289088447519115 17268600178933632671278673)
        ·
          refine ⟨12951450134200224503459005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17268600178933632671278673 12951450134200224503459005)
          ·
            refine ⟨4856793800325084188797127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12951450134200224503459005 4856793800325084188797127)
            ·
              refine ⟨7285190700487626283195691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856793800325084188797127 7285190700487626283195691)
              ·
                refine ⟨10927786050731439424793537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285190700487626283195691 10927786050731439424793537)
                ·
                  refine ⟨8195839538048579568595153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10927786050731439424793537 8195839538048579568595153)
                  ·
                    refine ⟨6146879653536434676446365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8195839538048579568595153 6146879653536434676446365)
                    ·
                      refine ⟨2305079870076163003667387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146879653536434676446365 2305079870076163003667387)
                      ·
                        rfl

theorem cell23_4489127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4489127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489127 prefixEnd_4489127 := by exact prefixLift 4489127
  have htrace : WordTrace (prefixWord ++ tailWord_4489127) baseStart_4489127 baseEnd_4489127 := by
    simpa [prefixWord, tailWord_4489127, baseEnd_4489127] using wordTrace_append hprefix tailTrace_4489127
  have hstable : (prefixWord ++ tailWord_4489127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489127).length < 2 ^ (prefixWord ++ tailWord_4489127).sum := by decide
  have hdescent : baseEnd_4489127 < baseStart_4489127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489191 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4489191 : Nat := 118140960795 + 4489191 * 2 ^ 59
def prefixEnd_4489191 : Nat := 4983230072969 + 3 ^ 40 * 4489191 * 2
def baseEnd_4489191 : Nat := 2305112732838050753267093

theorem tailTrace_4489191 : CollatzResearch.WordTrace tailWord_4489191 prefixEnd_4489191 2305112732838050753267093 := by
  unfold tailWord_4489191
  simp only [CollatzResearch.WordTrace]
  refine ⟨163734247079435174628379427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109156164719623449752252951 163734247079435174628379427)
  ·
    refine ⟨245601370619152761942569141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163734247079435174628379427 245601370619152761942569141)
    ·
      refine ⟨23025128495545571432115857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245601370619152761942569141 23025128495545571432115857)
      ·
        refine ⟨17268846371659178574086893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23025128495545571432115857 17268846371659178574086893)
        ·
          refine ⟨6475817389372191965282585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17268846371659178574086893 6475817389372191965282585)
          ·
            refine ⟨4856863042029143973961939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475817389372191965282585 4856863042029143973961939)
            ·
              refine ⟨7285294563043715960942909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856863042029143973961939 7285294563043715960942909)
              ·
                refine ⟨2731985461141393485353591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7285294563043715960942909 2731985461141393485353591)
                ·
                  refine ⟨4097978191712090228030387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731985461141393485353591 4097978191712090228030387)
                  ·
                    refine ⟨6146967287568135342045581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4097978191712090228030387 6146967287568135342045581)
                    ·
                      refine ⟨2305112732838050753267093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146967287568135342045581 2305112732838050753267093)
                      ·
                        rfl

theorem cell23_4489191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4489191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489191 prefixEnd_4489191 := by exact prefixLift 4489191
  have htrace : WordTrace (prefixWord ++ tailWord_4489191) baseStart_4489191 baseEnd_4489191 := by
    simpa [prefixWord, tailWord_4489191, baseEnd_4489191] using wordTrace_append hprefix tailTrace_4489191
  have hstable : (prefixWord ++ tailWord_4489191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489191).length < 2 ^ (prefixWord ++ tailWord_4489191).sum := by decide
  have hdescent : baseEnd_4489191 < baseStart_4489191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489200 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_4489200 : Nat := 118140960795 + 4489200 * 2 ^ 59
def prefixEnd_4489200 : Nat := 4983230072969 + 3 ^ 40 * 4489200 * 2
def baseEnd_4489200 : Nat := 2305117354163941218054551

theorem tailTrace_4489200 : CollatzResearch.WordTrace tailWord_4489200 prefixEnd_4489200 2305117354163941218054551 := by
  unfold tailWord_4489200
  simp only [CollatzResearch.WordTrace]
  refine ⟨81867287668201284582728527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109156383557601712776971369 81867287668201284582728527)
  ·
    refine ⟨122800931502301926874092791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81867287668201284582728527 122800931502301926874092791)
    ·
      refine ⟨184201397253452890311139187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122800931502301926874092791 184201397253452890311139187)
      ·
        refine ⟨276302095880179335466708781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184201397253452890311139187 276302095880179335466708781)
        ·
          refine ⟨103613285955067250800015793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276302095880179335466708781 103613285955067250800015793)
          ·
            refine ⟨77709964466300438100011845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103613285955067250800015793 77709964466300438100011845)
            ·
              refine ⟨14570618337431332143752221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77709964466300438100011845 14570618337431332143752221)
              ·
                refine ⟨5463981876536749553907083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14570618337431332143752221 5463981876536749553907083)
                ·
                  refine ⟨8195972814805124330860625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5463981876536749553907083 8195972814805124330860625)
                  ·
                    refine ⟨6146979611103843248145469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8195972814805124330860625 6146979611103843248145469)
                    ·
                      refine ⟨2305117354163941218054551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6146979611103843248145469 2305117354163941218054551)
                      ·
                        rfl

theorem cell23_4489200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_4489200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489200 prefixEnd_4489200 := by exact prefixLift 4489200
  have htrace : WordTrace (prefixWord ++ tailWord_4489200) baseStart_4489200 baseEnd_4489200 := by
    simpa [prefixWord, tailWord_4489200, baseEnd_4489200] using wordTrace_append hprefix tailTrace_4489200
  have hstable : (prefixWord ++ tailWord_4489200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489200).length < 2 ^ (prefixWord ++ tailWord_4489200).sum := by decide
  have hdescent : baseEnd_4489200 < baseStart_4489200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489230 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4489230 : Nat := 118140960795 + 4489230 * 2 ^ 59
def prefixEnd_4489230 : Nat := 4983230072969 + 3 ^ 40 * 4489230 * 2
def baseEnd_4489230 : Nat := 2305132758583576100679413

theorem tailTrace_4489230 : CollatzResearch.WordTrace tailWord_4489230 prefixEnd_4489230 2305132758583576100679413 := by
  unfold tailWord_4489230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466958690786735536131143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109157113017529256192699429 20466958690786735536131143)
  ·
    refine ⟨30700438036180103304196715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20466958690786735536131143 30700438036180103304196715)
    ·
      refine ⟨46050657054270154956295073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30700438036180103304196715 46050657054270154956295073)
      ·
        refine ⟨34537992790702616217221305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46050657054270154956295073 34537992790702616217221305)
        ·
          refine ⟨25903494593026962162915979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34537992790702616217221305 25903494593026962162915979)
          ·
            refine ⟨38855241889540443244373969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25903494593026962162915979 38855241889540443244373969)
            ·
              refine ⟨29141431417155332433280477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38855241889540443244373969 29141431417155332433280477)
              ·
                refine ⟨10928036781433249662480179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29141431417155332433280477 10928036781433249662480179)
                ·
                  refine ⟨16392055172149874493720269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10928036781433249662480179 16392055172149874493720269)
                  ·
                    refine ⟨6147020689556202935145101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16392055172149874493720269 6147020689556202935145101)
                    ·
                      refine ⟨2305132758583576100679413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6147020689556202935145101 2305132758583576100679413)
                      ·
                        rfl

theorem cell23_4489230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4489230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489230 prefixEnd_4489230 := by exact prefixLift 4489230
  have htrace : WordTrace (prefixWord ++ tailWord_4489230) baseStart_4489230 baseEnd_4489230 := by
    simpa [prefixWord, tailWord_4489230, baseEnd_4489230] using wordTrace_append hprefix tailTrace_4489230
  have hstable : (prefixWord ++ tailWord_4489230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489230).length < 2 ^ (prefixWord ++ tailWord_4489230).sum := by decide
  have hdescent : baseEnd_4489230 < baseStart_4489230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489270 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4489270 : Nat := 118140960795 + 4489270 * 2 ^ 59
def prefixEnd_4489270 : Nat := 4983230072969 + 3 ^ 40 * 4489270 * 2
def baseEnd_4489270 : Nat := 2305153297809755944179229

theorem tailTrace_4489270 : CollatzResearch.WordTrace tailWord_4489270 prefixEnd_4489270 2305153297809755944179229 := by
  unfold tailWord_4489270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233570527884310695031579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109158085630765980747003509 10233570527884310695031579)
  ·
    refine ⟨15350355791826466042547369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233570527884310695031579 15350355791826466042547369)
    ·
      refine ⟨11512766843869849531910527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15350355791826466042547369 11512766843869849531910527)
      ·
        refine ⟨17269150265804774297865791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11512766843869849531910527 17269150265804774297865791)
        ·
          refine ⟨25903725398707161446798687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17269150265804774297865791 25903725398707161446798687)
          ·
            refine ⟨38855588098060742170198031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25903725398707161446798687 38855588098060742170198031)
            ·
              refine ⟨58283382147091113255297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38855588098060742170198031 58283382147091113255297047)
              ·
                refine ⟨87425073220636669882945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58283382147091113255297047 87425073220636669882945571)
                ·
                  refine ⟨131137609830955004824418357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87425073220636669882945571 131137609830955004824418357)
                  ·
                    refine ⟨12294150921652031702289221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131137609830955004824418357 12294150921652031702289221)
                    ·
                      refine ⟨2305153297809755944179229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12294150921652031702289221 2305153297809755944179229)
                      ·
                        rfl

theorem cell23_4489270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4489270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489270 prefixEnd_4489270 := by exact prefixLift 4489270
  have htrace : WordTrace (prefixWord ++ tailWord_4489270) baseStart_4489270 baseEnd_4489270 := by
    simpa [prefixWord, tailWord_4489270, baseEnd_4489270] using wordTrace_append hprefix tailTrace_4489270
  have hstable : (prefixWord ++ tailWord_4489270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489270).length < 2 ^ (prefixWord ++ tailWord_4489270).sum := by decide
  have hdescent : baseEnd_4489270 < baseStart_4489270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489287 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_4489287 : Nat := 118140960795 + 4489287 * 2 ^ 59
def prefixEnd_4489287 : Nat := 4983230072969 + 3 ^ 40 * 4489287 * 2
def baseEnd_4489287 : Nat := 2305162026980882377666651

theorem tailTrace_4489287 : CollatzResearch.WordTrace tailWord_4489287 prefixEnd_4489287 2305162026980882377666651 := by
  unfold tailWord_4489287
  simp only [CollatzResearch.WordTrace]
  refine ⟨163737748487087383023874115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109158498991391588682582743 163737748487087383023874115)
  ·
    refine ⟨245606622730631074535811173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163737748487087383023874115 245606622730631074535811173)
    ·
      refine ⟨46051241761993326475464595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245606622730631074535811173 46051241761993326475464595)
      ·
        refine ⟨69076862642989989713196893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46051241761993326475464595 69076862642989989713196893)
        ·
          refine ⟨25903823491121246142448835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69076862642989989713196893 25903823491121246142448835)
          ·
            refine ⟨38855735236681869213673253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25903823491121246142448835 38855735236681869213673253)
            ·
              refine ⟨7285450356877850477563735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38855735236681869213673253 7285450356877850477563735)
              ·
                refine ⟨10928175535316775716345603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285450356877850477563735 10928175535316775716345603)
                ·
                  refine ⟨16392263302975163574518405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10928175535316775716345603 16392263302975163574518405)
                  ·
                    refine ⟨3073549369307843170222201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16392263302975163574518405 3073549369307843170222201)
                    ·
                      refine ⟨2305162026980882377666651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073549369307843170222201 2305162026980882377666651)
                      ·
                        rfl

theorem cell23_4489287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_4489287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489287 prefixEnd_4489287 := by exact prefixLift 4489287
  have htrace : WordTrace (prefixWord ++ tailWord_4489287) baseStart_4489287 baseEnd_4489287 := by
    simpa [prefixWord, tailWord_4489287, baseEnd_4489287] using wordTrace_append hprefix tailTrace_4489287
  have hstable : (prefixWord ++ tailWord_4489287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489287).length < 2 ^ (prefixWord ++ tailWord_4489287).sum := by decide
  have hdescent : baseEnd_4489287 < baseStart_4489287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489353 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_4489353 : Nat := 118140960795 + 4489353 * 2 ^ 59
def prefixEnd_4489353 : Nat := 4983230072969 + 3 ^ 40 * 4489353 * 2
def baseEnd_4489353 : Nat := 768398638901359706480449

theorem tailTrace_4489353 : CollatzResearch.WordTrace tailWord_4489353 prefixEnd_4489353 768398638901359706480449 := by
  unfold tailWord_4489353
  simp only [CollatzResearch.WordTrace]
  refine ⟨163740155704848276295776713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109160103803232184197184475 163740155704848276295776713)
  ·
    refine ⟨122805116778636207221832535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163740155704848276295776713 122805116778636207221832535)
    ·
      refine ⟨184207675167954310832748803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122805116778636207221832535 184207675167954310832748803)
      ·
        refine ⟨276311512751931466249123205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184207675167954310832748803 276311512751931466249123205)
        ·
          refine ⟨51808408640987149921710601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276311512751931466249123205 51808408640987149921710601)
          ·
            refine ⟨38856306480740362441282951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51808408640987149921710601 38856306480740362441282951)
            ·
              refine ⟨58284459721110543661924427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38856306480740362441282951 58284459721110543661924427)
              ·
                refine ⟨87426689581665815492886641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58284459721110543661924427 87426689581665815492886641)
                ·
                  refine ⟨65570017186249361619664981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87426689581665815492886641 65570017186249361619664981)
                  ·
                    refine ⟨768398638901359706480449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65570017186249361619664981 768398638901359706480449)
                    ·
                      rfl

theorem cell23_4489353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_4489353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489353 prefixEnd_4489353 := by exact prefixLift 4489353
  have htrace : WordTrace (prefixWord ++ tailWord_4489353) baseStart_4489353 baseEnd_4489353 := by
    simpa [prefixWord, tailWord_4489353, baseEnd_4489353] using wordTrace_append hprefix tailTrace_4489353
  have hstable : (prefixWord ++ tailWord_4489353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489353).length < 2 ^ (prefixWord ++ tailWord_4489353).sum := by decide
  have hdescent : baseEnd_4489353 < baseStart_4489353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489360 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_4489360 : Nat := 118140960795 + 4489360 * 2 ^ 59
def prefixEnd_4489360 : Nat := 4983230072969 + 3 ^ 40 * 4489360 * 2
def baseEnd_4489360 : Nat := 2305199511068660592053815

theorem tailTrace_4489360 : CollatzResearch.WordTrace tailWord_4489360 prefixEnd_4489360 2305199511068660592053815 := by
  unfold tailWord_4489360
  simp only [CollatzResearch.WordTrace]
  refine ⟨81870205507911458245640767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109160274010548610994187689 81870205507911458245640767)
  ·
    refine ⟨122805308261867187368461151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81870205507911458245640767 122805308261867187368461151)
    ·
      refine ⟨184207962392800781052691727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122805308261867187368461151 184207962392800781052691727)
      ·
        refine ⟨276311943589201171579037591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184207962392800781052691727 276311943589201171579037591)
        ·
          refine ⟨414467915383801757368556387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276311943589201171579037591 414467915383801757368556387)
          ·
            refine ⟨621701873075702636052834581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414467915383801757368556387 621701873075702636052834581)
            ·
              refine ⟨29142275300423561064976621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 621701873075702636052834581 29142275300423561064976621)
              ·
                refine ⟨10928353237658835399366233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29142275300423561064976621 10928353237658835399366233)
                ·
                  refine ⟨8196264928244126549524675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10928353237658835399366233 8196264928244126549524675)
                  ·
                    refine ⟨12294397392366189824287013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8196264928244126549524675 12294397392366189824287013)
                    ·
                      refine ⟨2305199511068660592053815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12294397392366189824287013 2305199511068660592053815)
                      ·
                        rfl

theorem cell23_4489360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_4489360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489360 prefixEnd_4489360 := by exact prefixLift 4489360
  have htrace : WordTrace (prefixWord ++ tailWord_4489360) baseStart_4489360 baseEnd_4489360 := by
    simpa [prefixWord, tailWord_4489360, baseEnd_4489360] using wordTrace_append hprefix tailTrace_4489360
  have hstable : (prefixWord ++ tailWord_4489360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489360).length < 2 ^ (prefixWord ++ tailWord_4489360).sum := by decide
  have hdescent : baseEnd_4489360 < baseStart_4489360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489363 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_4489363 : Nat := 118140960795 + 4489363 * 2 ^ 59
def prefixEnd_4489363 : Nat := 4983230072969 + 3 ^ 40 * 4489363 * 2
def baseEnd_4489363 : Nat := 2305201051510624080316301

theorem tailTrace_4489363 : CollatzResearch.WordTrace tailWord_4489363 prefixEnd_4489363 2305201051510624080316301 := by
  unfold tailWord_4489363
  simp only [CollatzResearch.WordTrace]
  refine ⟨163740520434812048003640743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109160346956541365335760495 163740520434812048003640743)
  ·
    refine ⟨245610780652218072005461115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163740520434812048003640743 245610780652218072005461115)
    ·
      refine ⟨368416170978327108008191673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245610780652218072005461115 368416170978327108008191673)
      ·
        refine ⟨276312128233745331006143755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368416170978327108008191673 276312128233745331006143755)
        ·
          refine ⟨414468192350617996509215633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276312128233745331006143755 414468192350617996509215633)
          ·
            refine ⟨310851144262963497381911725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414468192350617996509215633 310851144262963497381911725)
            ·
              refine ⟨116569179098611311518216897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310851144262963497381911725 116569179098611311518216897)
              ·
                refine ⟨87426884323958483638662673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116569179098611311518216897 87426884323958483638662673)
                ·
                  refine ⟨65570163242968862728997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87426884323958483638662673 65570163242968862728997005)
                  ·
                    refine ⟨24588811216113323523373877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65570163242968862728997005 24588811216113323523373877)
                    ·
                      refine ⟨2305201051510624080316301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24588811216113323523373877 2305201051510624080316301)
                      ·
                        rfl

theorem cell23_4489363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_4489363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489363 prefixEnd_4489363 := by exact prefixLift 4489363
  have htrace : WordTrace (prefixWord ++ tailWord_4489363) baseStart_4489363 baseEnd_4489363 := by
    simpa [prefixWord, tailWord_4489363, baseEnd_4489363] using wordTrace_append hprefix tailTrace_4489363
  have hstable : (prefixWord ++ tailWord_4489363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489363).length < 2 ^ (prefixWord ++ tailWord_4489363).sum := by decide
  have hdescent : baseEnd_4489363 < baseStart_4489363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489374 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4489374 : Nat := 118140960795 + 4489374 * 2 ^ 59
def prefixEnd_4489374 : Nat := 4983230072969 + 3 ^ 40 * 4489374 * 2
def baseEnd_4489374 : Nat := 768402233265941179092917

theorem tailTrace_4489374 : CollatzResearch.WordTrace tailWord_4489374 prefixEnd_4489374 768402233265941179092917 := by
  unfold tailWord_4489374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20467615204721524610286397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109160614425181464588194117 20467615204721524610286397)
  ·
    refine ⟨7675355701770571728857399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20467615204721524610286397 7675355701770571728857399)
    ·
      refine ⟨11513033552655857593286099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7675355701770571728857399 11513033552655857593286099)
      ·
        refine ⟨17269550328983786389929149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513033552655857593286099 17269550328983786389929149)
        ·
          refine ⟨6476081373368919896223431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17269550328983786389929149 6476081373368919896223431)
          ·
            refine ⟨9714122060053379844335147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476081373368919896223431 9714122060053379844335147)
            ·
              refine ⟨14571183090080069766502721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714122060053379844335147 14571183090080069766502721)
              ·
                refine ⟨10928387317560052324877041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14571183090080069766502721 10928387317560052324877041)
                ·
                  refine ⟨8196290488170039243657781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10928387317560052324877041 8196290488170039243657781)
                  ·
                    refine ⟨768402233265941179092917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8196290488170039243657781 768402233265941179092917)
                    ·
                      rfl

theorem cell23_4489374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4489374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489374 prefixEnd_4489374 := by exact prefixLift 4489374
  have htrace : WordTrace (prefixWord ++ tailWord_4489374) baseStart_4489374 baseEnd_4489374 := by
    simpa [prefixWord, tailWord_4489374, baseEnd_4489374] using wordTrace_append hprefix tailTrace_4489374
  have hstable : (prefixWord ++ tailWord_4489374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489374).length < 2 ^ (prefixWord ++ tailWord_4489374).sum := by decide
  have hdescent : baseEnd_4489374 < baseStart_4489374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489377 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4489377 : Nat := 118140960795 + 4489377 * 2 ^ 59
def prefixEnd_4489377 : Nat := 4983230072969 + 3 ^ 40 * 4489377 * 2
def baseEnd_4489377 : Nat := 2305208240239787025541237

theorem tailTrace_4489377 : CollatzResearch.WordTrace tailWord_4489377 prefixEnd_4489377 2305208240239787025541237 := by
  unfold tailWord_4489377
  simp only [CollatzResearch.WordTrace]
  refine ⟨163741031056761328394650385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109160687371174218929766923 163741031056761328394650385)
  ·
    refine ⟨122805773292570996295987789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163741031056761328394650385 122805773292570996295987789)
    ·
      refine ⟨46052164984714123610995421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122805773292570996295987789 46052164984714123610995421)
      ·
        refine ⟨17269561869267796354123283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46052164984714123610995421 17269561869267796354123283)
        ·
          refine ⟨25904342803901694531184925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17269561869267796354123283 25904342803901694531184925)
          ·
            refine ⟨9714128551463135449194347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25904342803901694531184925 9714128551463135449194347)
            ·
              refine ⟨14571192827194703173791521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714128551463135449194347 14571192827194703173791521)
              ·
                refine ⟨10928394620396027380343641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14571192827194703173791521 10928394620396027380343641)
                ·
                  refine ⟨8196295965297020535257731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10928394620396027380343641 8196295965297020535257731)
                  ·
                    refine ⟨12294443947945530802886597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8196295965297020535257731 12294443947945530802886597)
                    ·
                      refine ⟨2305208240239787025541237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12294443947945530802886597 2305208240239787025541237)
                      ·
                        rfl

theorem cell23_4489377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4489377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489377 prefixEnd_4489377 := by exact prefixLift 4489377
  have htrace : WordTrace (prefixWord ++ tailWord_4489377) baseStart_4489377 baseEnd_4489377 := by
    simpa [prefixWord, tailWord_4489377, baseEnd_4489377] using wordTrace_append hprefix tailTrace_4489377
  have hstable : (prefixWord ++ tailWord_4489377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489377).length < 2 ^ (prefixWord ++ tailWord_4489377).sum := by decide
  have hdescent : baseEnd_4489377 < baseStart_4489377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489400 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 6]
def baseStart_4489400 : Nat := 118140960795 + 4489400 * 2 ^ 59
def prefixEnd_4489400 : Nat := 4983230072969 + 3 ^ 40 * 4489400 * 2
def baseEnd_4489400 : Nat := 256135561143871159505959

theorem tailTrace_4489400 : CollatzResearch.WordTrace tailWord_4489400 prefixEnd_4489400 256135561143871159505959 := by
  unfold tailWord_4489400
  simp only [CollatzResearch.WordTrace]
  refine ⟨81870934967839001661368827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109161246623785335548491769 81870934967839001661368827)
  ·
    refine ⟨122806402451758502492053241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81870934967839001661368827 122806402451758502492053241)
    ·
      refine ⟨92104801838818876869039931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122806402451758502492053241 92104801838818876869039931)
      ·
        refine ⟨138157202758228315303559897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92104801838818876869039931 138157202758228315303559897)
        ·
          refine ⟨103617902068671236477669923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138157202758228315303559897 103617902068671236477669923)
          ·
            refine ⟨155426853103006854716504885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103617902068671236477669923 155426853103006854716504885)
            ·
              refine ⟨14571267478406892629672333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155426853103006854716504885 14571267478406892629672333)
              ·
                refine ⟨5464225304402584736127125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14571267478406892629672333 5464225304402584736127125)
                ·
                  refine ⟨256135561143871159505959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5464225304402584736127125 256135561143871159505959)
                  ·
                    rfl

theorem cell23_4489400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_4489400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489400 prefixEnd_4489400 := by exact prefixLift 4489400
  have htrace : WordTrace (prefixWord ++ tailWord_4489400) baseStart_4489400 baseEnd_4489400 := by
    simpa [prefixWord, tailWord_4489400, baseEnd_4489400] using wordTrace_append hprefix tailTrace_4489400
  have hstable : (prefixWord ++ tailWord_4489400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489400).length < 2 ^ (prefixWord ++ tailWord_4489400).sum := by decide
  have hdescent : baseEnd_4489400 < baseStart_4489400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489447 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4489447 : Nat := 118140960795 + 4489447 * 2 ^ 59
def prefixEnd_4489447 : Nat := 4983230072969 + 3 ^ 40 * 4489447 * 2
def baseEnd_4489447 : Nat := 768414727961867250555305

theorem tailTrace_4489447 : CollatzResearch.WordTrace tailWord_4489447 prefixEnd_4489447 768414727961867250555305 := by
  unfold tailWord_4489447
  simp only [CollatzResearch.WordTrace]
  refine ⟨163743584166507730349698595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109162389444338486899799063 163743584166507730349698595)
  ·
    refine ⟨245615376249761595524547893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163743584166507730349698595 245615376249761595524547893)
    ·
      refine ⟨23026441523415149580426365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245615376249761595524547893 23026441523415149580426365)
      ·
        refine ⟨8634915571280681092659887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23026441523415149580426365 8634915571280681092659887)
        ·
          refine ⟨12952373356921021638989831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634915571280681092659887 12952373356921021638989831)
          ·
            refine ⟨19428560035381532458484747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952373356921021638989831 19428560035381532458484747)
            ·
              refine ⟨29142840053072298687727121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19428560035381532458484747 29142840053072298687727121)
              ·
                refine ⟨21857130039804224015795341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29142840053072298687727121 21857130039804224015795341)
                ·
                  refine ⟨8196423764926584005923253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21857130039804224015795341 8196423764926584005923253)
                  ·
                    refine ⟨768414727961867250555305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8196423764926584005923253 768414727961867250555305)
                    ·
                      rfl

theorem cell23_4489447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4489447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489447 prefixEnd_4489447 := by exact prefixLift 4489447
  have htrace : WordTrace (prefixWord ++ tailWord_4489447) baseStart_4489447 baseEnd_4489447 := by
    simpa [prefixWord, tailWord_4489447, baseEnd_4489447] using wordTrace_append hprefix tailTrace_4489447
  have hstable : (prefixWord ++ tailWord_4489447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489447).length < 2 ^ (prefixWord ++ tailWord_4489447).sum := by decide
  have hdescent : baseEnd_4489447 < baseStart_4489447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489484 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_4489484 : Nat := 118140960795 + 4489484 * 2 ^ 59
def prefixEnd_4489484 : Nat := 4983230072969 + 3 ^ 40 * 4489484 * 2
def baseEnd_4489484 : Nat := 2305263182669818106903245

theorem tailTrace_4489484 : CollatzResearch.WordTrace tailWord_4489484 prefixEnd_4489484 2305263182669818106903245 := by
  unfold tailWord_4489484
  simp only [CollatzResearch.WordTrace]
  refine ⟨81872466833686842834397753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109163289111582457112530337 81872466833686842834397753)
  ·
    refine ⟨61404350125265132125798315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81872466833686842834397753 61404350125265132125798315)
    ·
      refine ⟨92106525187897698188697473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61404350125265132125798315 92106525187897698188697473)
      ·
        refine ⟨69079893890923273641523105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92106525187897698188697473 69079893890923273641523105)
        ·
          refine ⟨51809920418192455231142329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69079893890923273641523105 51809920418192455231142329)
          ·
            refine ⟨38857440313644341423356747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51809920418192455231142329 38857440313644341423356747)
            ·
              refine ⟨58286160470466512135035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38857440313644341423356747 58286160470466512135035121)
              ·
                refine ⟨43714620352849884101276341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58286160470466512135035121 43714620352849884101276341)
                ·
                  refine ⟨4098245658079676634494657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43714620352849884101276341 4098245658079676634494657)
                  ·
                    refine ⟨3073684243559757475870993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4098245658079676634494657 3073684243559757475870993)
                    ·
                      refine ⟨2305263182669818106903245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073684243559757475870993 2305263182669818106903245)
                      ·
                        rfl

theorem cell23_4489484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_4489484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489484 prefixEnd_4489484 := by exact prefixLift 4489484
  have htrace : WordTrace (prefixWord ++ tailWord_4489484) baseStart_4489484 baseEnd_4489484 := by
    simpa [prefixWord, tailWord_4489484, baseEnd_4489484] using wordTrace_append hprefix tailTrace_4489484
  have hstable : (prefixWord ++ tailWord_4489484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489484).length < 2 ^ (prefixWord ++ tailWord_4489484).sum := by decide
  have hdescent : baseEnd_4489484 < baseStart_4489484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4489500 : Nat := 118140960795 + 4489500 * 2 ^ 59
def prefixEnd_4489500 : Nat := 4983230072969 + 3 ^ 40 * 4489500 * 2
def baseEnd_4489500 : Nat := 2305271398360290044303171

theorem tailTrace_4489500 : CollatzResearch.WordTrace tailWord_4489500 prefixEnd_4489500 2305271398360290044303171 := by
  unfold tailWord_4489500
  simp only [CollatzResearch.WordTrace]
  refine ⟨81872758617657860200688977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109163678156877146934251969 81872758617657860200688977)
  ·
    refine ⟨61404568963243395150516733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81872758617657860200688977 61404568963243395150516733)
    ·
      refine ⟨23026713361216273181443775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61404568963243395150516733 23026713361216273181443775)
      ·
        refine ⟨34540070041824409772165663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23026713361216273181443775 34540070041824409772165663)
        ·
          refine ⟨51810105062736614658248495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34540070041824409772165663 51810105062736614658248495)
          ·
            refine ⟨77715157594104921987372743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51810105062736614658248495 77715157594104921987372743)
            ·
              refine ⟨116572736391157382981059115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77715157594104921987372743 116572736391157382981059115)
              ·
                refine ⟨174859104586736074471588673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116572736391157382981059115 174859104586736074471588673)
                ·
                  refine ⟨131144328440052055853691505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174859104586736074471588673 131144328440052055853691505)
                  ·
                    refine ⟨98358246330039041890268629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131144328440052055853691505 98358246330039041890268629)
                    ·
                      refine ⟨2305271398360290044303171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98358246330039041890268629 2305271398360290044303171)
                      ·
                        rfl

theorem cell23_4489500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4489500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489500 prefixEnd_4489500 := by exact prefixLift 4489500
  have htrace : WordTrace (prefixWord ++ tailWord_4489500) baseStart_4489500 baseEnd_4489500 := by
    simpa [prefixWord, tailWord_4489500, baseEnd_4489500] using wordTrace_append hprefix tailTrace_4489500
  have hstable : (prefixWord ++ tailWord_4489500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489500).length < 2 ^ (prefixWord ++ tailWord_4489500).sum := by decide
  have hdescent : baseEnd_4489500 < baseStart_4489500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489514 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4489514 : Nat := 118140960795 + 4489514 * 2 ^ 59
def prefixEnd_4489514 : Nat := 4983230072969 + 3 ^ 40 * 4489514 * 2
def baseEnd_4489514 : Nat := 2305278587089452989528107

theorem tailTrace_4489514 : CollatzResearch.WordTrace tailWord_4489514 prefixEnd_4489514 2305278587089452989528107 := by
  unfold tailWord_4489514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40936506964316250198096899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109164018571510000528258397 40936506964316250198096899)
  ·
    refine ⟨61404760446474375297145349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40936506964316250198096899 61404760446474375297145349)
    ·
      refine ⟨11513392583713945368214753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61404760446474375297145349 11513392583713945368214753)
      ·
        refine ⟨8635044437785459026161065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11513392583713945368214753 8635044437785459026161065)
        ·
          refine ⟨6476283328339094269620799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8635044437785459026161065 6476283328339094269620799)
          ·
            refine ⟨9714424992508641404431199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476283328339094269620799 9714424992508641404431199)
            ·
              refine ⟨14571637488762962106646799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714424992508641404431199 14571637488762962106646799)
              ·
                refine ⟨21857456233144443159970199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14571637488762962106646799 21857456233144443159970199)
                ·
                  refine ⟨32786184349716664739955299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21857456233144443159970199 32786184349716664739955299)
                  ·
                    refine ⟨49179276524574997109932949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32786184349716664739955299 49179276524574997109932949)
                    ·
                      refine ⟨2305278587089452989528107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49179276524574997109932949 2305278587089452989528107)
                      ·
                        rfl

theorem cell23_4489514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4489514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489514 prefixEnd_4489514 := by exact prefixLift 4489514
  have htrace : WordTrace (prefixWord ++ tailWord_4489514) baseStart_4489514 baseEnd_4489514 := by
    simpa [prefixWord, tailWord_4489514, baseEnd_4489514] using wordTrace_append hprefix tailTrace_4489514
  have hstable : (prefixWord ++ tailWord_4489514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489514).length < 2 ^ (prefixWord ++ tailWord_4489514).sum := by decide
  have hdescent : baseEnd_4489514 < baseStart_4489514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489518 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4489518 : Nat := 118140960795 + 4489518 * 2 ^ 59
def prefixEnd_4489518 : Nat := 4983230072969 + 3 ^ 40 * 4489518 * 2
def baseEnd_4489518 : Nat := 2305280641012070973878089

theorem tailTrace_4489518 : CollatzResearch.WordTrace tailWord_4489518 prefixEnd_4489518 2305280641012070973878089 := by
  unfold tailWord_4489518
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468271718656313684441651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109164115832833672983688805 20468271718656313684441651)
  ·
    refine ⟨30702407577984470526662477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20468271718656313684441651 30702407577984470526662477)
    ·
      refine ⟨11513402841744176447498429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30702407577984470526662477 11513402841744176447498429)
      ·
        refine ⟨4317526065654066167811911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11513402841744176447498429 4317526065654066167811911)
        ·
          refine ⟨6476289098481099251717867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317526065654066167811911 6476289098481099251717867)
          ·
            refine ⟨9714433647721648877576801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476289098481099251717867 9714433647721648877576801)
            ·
              refine ⟨7285825235791236658182601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9714433647721648877576801 7285825235791236658182601)
              ·
                refine ⟨5464368926843427493636951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285825235791236658182601 5464368926843427493636951)
                ·
                  refine ⟨8196553390265141240455427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464368926843427493636951 8196553390265141240455427)
                  ·
                    refine ⟨12294830085397711860683141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8196553390265141240455427 12294830085397711860683141)
                    ·
                      refine ⟨2305280641012070973878089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12294830085397711860683141 2305280641012070973878089)
                      ·
                        rfl

theorem cell23_4489518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4489518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489518 prefixEnd_4489518 := by exact prefixLift 4489518
  have htrace : WordTrace (prefixWord ++ tailWord_4489518) baseStart_4489518 baseEnd_4489518 := by
    simpa [prefixWord, tailWord_4489518, baseEnd_4489518] using wordTrace_append hprefix tailTrace_4489518
  have hstable : (prefixWord ++ tailWord_4489518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489518).length < 2 ^ (prefixWord ++ tailWord_4489518).sum := by decide
  have hdescent : baseEnd_4489518 < baseStart_4489518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489521 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_4489521 : Nat := 118140960795 + 4489521 * 2 ^ 59
def prefixEnd_4489521 : Nat := 4983230072969 + 3 ^ 40 * 4489521 * 2
def baseEnd_4489521 : Nat := 2305282181454034462140575

theorem tailTrace_4489521 : CollatzResearch.WordTrace tailWord_4489521 prefixEnd_4489521 2305282181454034462140575 := by
  unfold tailWord_4489521
  simp only [CollatzResearch.WordTrace]
  refine ⟨163746283168239640987892417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109164188778826427325261611 163746283168239640987892417)
  ·
    refine ⟨122809712376179730740919313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163746283168239640987892417 122809712376179730740919313)
    ·
      refine ⟨92107284282134798055689485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122809712376179730740919313 92107284282134798055689485)
      ·
        refine ⟨34540231605800549270883557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92107284282134798055689485 34540231605800549270883557)
        ·
          refine ⟨6476293426087602988290667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34540231605800549270883557 6476293426087602988290667)
          ·
            refine ⟨9714440139131404482436001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476293426087602988290667 9714440139131404482436001)
            ·
              refine ⟨7285830104348553361827001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9714440139131404482436001 7285830104348553361827001)
              ·
                refine ⟨5464372578261415021370251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285830104348553361827001 5464372578261415021370251)
                ·
                  refine ⟨8196558867392122532055377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464372578261415021370251 8196558867392122532055377)
                  ·
                    refine ⟨6147419150544091899041533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8196558867392122532055377 6147419150544091899041533)
                    ·
                      refine ⟨2305282181454034462140575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6147419150544091899041533 2305282181454034462140575)
                      ·
                        rfl

theorem cell23_4489521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_4489521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489521 prefixEnd_4489521 := by exact prefixLift 4489521
  have htrace : WordTrace (prefixWord ++ tailWord_4489521) baseStart_4489521 baseEnd_4489521 := by
    simpa [prefixWord, tailWord_4489521, baseEnd_4489521] using wordTrace_append hprefix tailTrace_4489521
  have hstable : (prefixWord ++ tailWord_4489521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489521).length < 2 ^ (prefixWord ++ tailWord_4489521).sum := by decide
  have hdescent : baseEnd_4489521 < baseStart_4489521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489524 : List Nat := [2, 5, 1, 1, 1, 2, 4, 7]
def baseStart_4489524 : Nat := 118140960795 + 4489524 * 2 ^ 59
def prefixEnd_4489524 : Nat := 4983230072969 + 3 ^ 40 * 4489524 * 2
def baseEnd_4489524 : Nat := 85380878588740664829743

theorem tailTrace_4489524 : CollatzResearch.WordTrace tailWord_4489524 prefixEnd_4489524 85380878588740664829743 := by
  unfold tailWord_4489524
  simp only [CollatzResearch.WordTrace]
  refine ⟨81873196293614386250125813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109164261724819181666834417 81873196293614386250125813)
  ·
    refine ⟨7675612152526348710949295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81873196293614386250125813 7675612152526348710949295)
    ·
      refine ⟨11513418228789523066423943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7675612152526348710949295 11513418228789523066423943)
      ·
        refine ⟨17270127343184284599635915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513418228789523066423943 17270127343184284599635915)
        ·
          refine ⟨25905191014776426899453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270127343184284599635915 25905191014776426899453873)
          ·
            refine ⟨19428893261082320174590405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25905191014776426899453873 19428893261082320174590405)
            ·
              refine ⟨3642917486452935032735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19428893261082320174590405 3642917486452935032735701)
              ·
                refine ⟨85380878588740664829743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3642917486452935032735701 85380878588740664829743)
                ·
                  rfl

theorem cell23_4489524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 7].length) (baseStart_4489524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489524 prefixEnd_4489524 := by exact prefixLift 4489524
  have htrace : WordTrace (prefixWord ++ tailWord_4489524) baseStart_4489524 baseEnd_4489524 := by
    simpa [prefixWord, tailWord_4489524, baseEnd_4489524] using wordTrace_append hprefix tailTrace_4489524
  have hstable : (prefixWord ++ tailWord_4489524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489524).length < 2 ^ (prefixWord ++ tailWord_4489524).sum := by decide
  have hdescent : baseEnd_4489524 < baseStart_4489524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489527 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_4489527 : Nat := 118140960795 + 4489527 * 2 ^ 59
def prefixEnd_4489527 : Nat := 4983230072969 + 3 ^ 40 * 4489527 * 2
def baseEnd_4489527 : Nat := 2305285262337961438665547

theorem tailTrace_4489527 : CollatzResearch.WordTrace tailWord_4489527 prefixEnd_4489527 2305285262337961438665547 := by
  unfold tailWord_4489527
  simp only [CollatzResearch.WordTrace]
  refine ⟨163746502006217904012610835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109164334670811936008407223 163746502006217904012610835)
  ·
    refine ⟨245619753009326856018916253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163746502006217904012610835 245619753009326856018916253)
    ·
      refine ⟨92107407378497571007093595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245619753009326856018916253 92107407378497571007093595)
      ·
        refine ⟨138161111067746356510640393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92107407378497571007093595 138161111067746356510640393)
        ·
          refine ⟨103620833300809767382980295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138161111067746356510640393 103620833300809767382980295)
          ·
            refine ⟨155431249951214651074470443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103620833300809767382980295 155431249951214651074470443)
            ·
              refine ⟨233146874926821976611705665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155431249951214651074470443 233146874926821976611705665)
              ·
                refine ⟨174860156195116482458779249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233146874926821976611705665 174860156195116482458779249)
                ·
                  refine ⟨131145117146337361844084437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174860156195116482458779249 131145117146337361844084437)
                  ·
                    refine ⟨3073713683117281918220729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131145117146337361844084437 3073713683117281918220729)
                    ·
                      refine ⟨2305285262337961438665547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073713683117281918220729 2305285262337961438665547)
                      ·
                        rfl

theorem cell23_4489527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_4489527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489527 prefixEnd_4489527 := by exact prefixLift 4489527
  have htrace : WordTrace (prefixWord ++ tailWord_4489527) baseStart_4489527 baseEnd_4489527 := by
    simpa [prefixWord, tailWord_4489527, baseEnd_4489527] using wordTrace_append hprefix tailTrace_4489527
  have hstable : (prefixWord ++ tailWord_4489527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489527).length < 2 ^ (prefixWord ++ tailWord_4489527).sum := by decide
  have hdescent : baseEnd_4489527 < baseStart_4489527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489578 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4489578 : Nat := 118140960795 + 4489578 * 2 ^ 59
def prefixEnd_4489578 : Nat := 4983230072969 + 3 ^ 40 * 4489578 * 2
def baseEnd_4489578 : Nat := 2305311449851340739127813

theorem tailTrace_4489578 : CollatzResearch.WordTrace tailWord_4489578 prefixEnd_4489578 2305311449851340739127813 := by
  unfold tailWord_4489578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40937090532258284930679347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109165574752688759815144925 40937090532258284930679347)
  ·
    refine ⟨61405635798387427396019021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40937090532258284930679347 61405635798387427396019021)
    ·
      refine ⟨23027113424395285273507133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61405635798387427396019021 23027113424395285273507133)
      ·
        refine ⟨8635167534148231977565175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23027113424395285273507133 8635167534148231977565175)
        ·
          refine ⟨12952751301222347966347763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635167534148231977565175 12952751301222347966347763)
          ·
            refine ⟨19429126951833521949521645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952751301222347966347763 19429126951833521949521645)
            ·
              refine ⟨7285922606937570731070617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19429126951833521949521645 7285922606937570731070617)
              ·
                refine ⟨5464441955203178048302963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285922606937570731070617 5464441955203178048302963)
                ·
                  refine ⟨8196662932804767072454445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464441955203178048302963 8196662932804767072454445)
                  ·
                    refine ⟨3073748599801787652170417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8196662932804767072454445 3073748599801787652170417)
                    ·
                      refine ⟨2305311449851340739127813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073748599801787652170417 2305311449851340739127813)
                      ·
                        rfl

theorem cell23_4489578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4489578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489578 prefixEnd_4489578 := by exact prefixLift 4489578
  have htrace : WordTrace (prefixWord ++ tailWord_4489578) baseStart_4489578 baseEnd_4489578 := by
    simpa [prefixWord, tailWord_4489578, baseEnd_4489578] using wordTrace_append hprefix tailTrace_4489578
  have hstable : (prefixWord ++ tailWord_4489578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489578).length < 2 ^ (prefixWord ++ tailWord_4489578).sum := by decide
  have hdescent : baseEnd_4489578 < baseStart_4489578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489608 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4489608 : Nat := 118140960795 + 4489608 * 2 ^ 59
def prefixEnd_4489608 : Nat := 4983230072969 + 3 ^ 40 * 4489608 * 2
def baseEnd_4489608 : Nat := 2305326854270975621752675

theorem tailTrace_4489608 : CollatzResearch.WordTrace tailWord_4489608 prefixEnd_4489608 2305326854270975621752675 := by
  unfold tailWord_4489608
  simp only [CollatzResearch.WordTrace]
  refine ⟨81874728159462227423154739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109166304212616303230872985 81874728159462227423154739)
  ·
    refine ⟨122812092239193341134732109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81874728159462227423154739 122812092239193341134732109)
    ·
      refine ⟨46054534589697502925524541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122812092239193341134732109 46054534589697502925524541)
      ·
        refine ⟨17270450471136563597071703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46054534589697502925524541 17270450471136563597071703)
        ·
          refine ⟨25905675706704845395607555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270450471136563597071703 25905675706704845395607555)
          ·
            refine ⟨38858513560057268093411333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25905675706704845395607555 38858513560057268093411333)
            ·
              refine ⟨7285971292510737767514625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38858513560057268093411333 7285971292510737767514625)
              ·
                refine ⟨5464478469383053325635969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285971292510737767514625 5464478469383053325635969)
                ·
                  refine ⟨4098358852037289994226977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464478469383053325635969 4098358852037289994226977)
                  ·
                    refine ⟨3073769139027967495670233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4098358852037289994226977 3073769139027967495670233)
                    ·
                      refine ⟨2305326854270975621752675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073769139027967495670233 2305326854270975621752675)
                      ·
                        rfl

theorem cell23_4489608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4489608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489608 prefixEnd_4489608 := by exact prefixLift 4489608
  have htrace : WordTrace (prefixWord ++ tailWord_4489608) baseStart_4489608 baseEnd_4489608 := by
    simpa [prefixWord, tailWord_4489608, baseEnd_4489608] using wordTrace_append hprefix tailTrace_4489608
  have hstable : (prefixWord ++ tailWord_4489608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489608).length < 2 ^ (prefixWord ++ tailWord_4489608).sum := by decide
  have hdescent : baseEnd_4489608 < baseStart_4489608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489624 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4489624 : Nat := 118140960795 + 4489624 * 2 ^ 59
def prefixEnd_4489624 : Nat := 4983230072969 + 3 ^ 40 * 4489624 * 2
def baseEnd_4489624 : Nat := 2305335069961447559152601

theorem tailTrace_4489624 : CollatzResearch.WordTrace tailWord_4489624 prefixEnd_4489624 2305335069961447559152601 := by
  unfold tailWord_4489624
  simp only [CollatzResearch.WordTrace]
  refine ⟨81875019943433244789445963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109166693257910993052594617 81875019943433244789445963)
  ·
    refine ⟨122812529915149867184168945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81875019943433244789445963 122812529915149867184168945)
    ·
      refine ⟨92109397436362400388126709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122812529915149867184168945 92109397436362400388126709)
      ·
        refine ⟨8635256009658975036386879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92109397436362400388126709 8635256009658975036386879)
        ·
          refine ⟨12952884014488462554580319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635256009658975036386879 12952884014488462554580319)
          ·
            refine ⟨19429326021732693831870479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952884014488462554580319 19429326021732693831870479)
            ·
              refine ⟨29143989032599040747805719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19429326021732693831870479 29143989032599040747805719)
              ·
                refine ⟨43715983548898561121708579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29143989032599040747805719 43715983548898561121708579)
                ·
                  refine ⟨65573975323347841682562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43715983548898561121708579 65573975323347841682562869)
                  ·
                    refine ⟨6147560186563860157740269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65573975323347841682562869 6147560186563860157740269)
                    ·
                      refine ⟨2305335069961447559152601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6147560186563860157740269 2305335069961447559152601)
                      ·
                        rfl

theorem cell23_4489624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4489624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489624 prefixEnd_4489624 := by exact prefixLift 4489624
  have htrace : WordTrace (prefixWord ++ tailWord_4489624) baseStart_4489624 baseEnd_4489624 := by
    simpa [prefixWord, tailWord_4489624, baseEnd_4489624] using wordTrace_append hprefix tailTrace_4489624
  have hstable : (prefixWord ++ tailWord_4489624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489624).length < 2 ^ (prefixWord ++ tailWord_4489624).sum := by decide
  have hdescent : baseEnd_4489624 < baseStart_4489624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489782 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4489782 : Nat := 118140960795 + 4489782 * 2 ^ 59
def prefixEnd_4489782 : Nat := 4983230072969 + 3 ^ 40 * 4489782 * 2
def baseEnd_4489782 : Nat := 2305416199904857940976875

theorem tailTrace_4489782 : CollatzResearch.WordTrace tailWord_4489782 prefixEnd_4489782 2305416199904857940976875 := by
  unfold tailWord_4489782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234737663768380160196475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109170535080196055042095733 10234737663768380160196475)
  ·
    refine ⟨15352106495652570240294713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10234737663768380160196475 15352106495652570240294713)
    ·
      refine ⟨11514079871739427680221035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15352106495652570240294713 11514079871739427680221035)
      ·
        refine ⟨17271119807609141520331553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514079871739427680221035 17271119807609141520331553)
        ·
          refine ⟨12953339855706856140248665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17271119807609141520331553 12953339855706856140248665)
          ·
            refine ⟨9715004891780142105186499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12953339855706856140248665 9715004891780142105186499)
            ·
              refine ⟨14572507337670213157779749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9715004891780142105186499 14572507337670213157779749)
              ·
                refine ⟨2732345125813164967083703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14572507337670213157779749 2732345125813164967083703)
                ·
                  refine ⟨4098517688719747450625555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732345125813164967083703 4098517688719747450625555)
                  ·
                    refine ⟨6147776533079621175938333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4098517688719747450625555 6147776533079621175938333)
                    ·
                      refine ⟨2305416199904857940976875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6147776533079621175938333 2305416199904857940976875)
                      ·
                        rfl

theorem cell23_4489782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4489782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489782 prefixEnd_4489782 := by exact prefixLift 4489782
  have htrace : WordTrace (prefixWord ++ tailWord_4489782) baseStart_4489782 baseEnd_4489782 := by
    simpa [prefixWord, tailWord_4489782, baseEnd_4489782] using wordTrace_append hprefix tailTrace_4489782
  have hstable : (prefixWord ++ tailWord_4489782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489782).length < 2 ^ (prefixWord ++ tailWord_4489782).sum := by decide
  have hdescent : baseEnd_4489782 < baseStart_4489782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489784 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_4489784 : Nat := 118140960795 + 4489784 * 2 ^ 59
def prefixEnd_4489784 : Nat := 4983230072969 + 3 ^ 40 * 4489784 * 2
def baseEnd_4489784 : Nat := 2305417226866166933151865

theorem tailTrace_4489784 : CollatzResearch.WordTrace tailWord_4489784 prefixEnd_4489784 2305417226866166933151865 := by
  unfold tailWord_4489784
  simp only [CollatzResearch.WordTrace]
  refine ⟨81877937783143418452358203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109170583710857891269810937 81877937783143418452358203)
  ·
    refine ⟨122816906674715127678537305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81877937783143418452358203 122816906674715127678537305)
    ·
      refine ⟨92112680006036345758902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122816906674715127678537305 92112680006036345758902979)
      ·
        refine ⟨138169020009054518638354469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92112680006036345758902979 138169020009054518638354469)
        ·
          refine ⟨25906691251697722244691463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138169020009054518638354469 25906691251697722244691463)
          ·
            refine ⟨38860036877546583367037195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25906691251697722244691463 38860036877546583367037195)
            ·
              refine ⟨58290055316319875050555793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38860036877546583367037195 58290055316319875050555793)
              ·
                refine ⟨43717541487239906287916845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58290055316319875050555793 43717541487239906287916845)
                ·
                  refine ⟨16394078057714964857968817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43717541487239906287916845 16394078057714964857968817)
                  ·
                    refine ⟨12295558543286223643476613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16394078057714964857968817 12295558543286223643476613)
                    ·
                      refine ⟨2305417226866166933151865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12295558543286223643476613 2305417226866166933151865)
                      ·
                        rfl

theorem cell23_4489784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_4489784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489784 prefixEnd_4489784 := by exact prefixLift 4489784
  have htrace : WordTrace (prefixWord ++ tailWord_4489784) baseStart_4489784 baseEnd_4489784 := by
    simpa [prefixWord, tailWord_4489784, baseEnd_4489784] using wordTrace_append hprefix tailTrace_4489784
  have hstable : (prefixWord ++ tailWord_4489784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489784).length < 2 ^ (prefixWord ++ tailWord_4489784).sum := by decide
  have hdescent : baseEnd_4489784 < baseStart_4489784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489798 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4489798 : Nat := 118140960795 + 4489798 * 2 ^ 59
def prefixEnd_4489798 : Nat := 4983230072969 + 3 ^ 40 * 4489798 * 2
def baseEnd_4489798 : Nat := 768474805198443292792267

theorem tailTrace_4489798 : CollatzResearch.WordTrace tailWord_4489798 prefixEnd_4489798 768474805198443292792267 := by
  unfold tailWord_4489798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117387068382378665491439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109170924125490744863817365 5117387068382378665491439)
  ·
    refine ⟨7676080602573567998237159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5117387068382378665491439 7676080602573567998237159)
    ·
      refine ⟨11514120903860351997355739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676080602573567998237159 11514120903860351997355739)
      ·
        refine ⟨17271181355790527996033609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514120903860351997355739 17271181355790527996033609)
        ·
          refine ⟨12953386016842895997025207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17271181355790527996033609 12953386016842895997025207)
          ·
            refine ⟨19430079025264343995537811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12953386016842895997025207 19430079025264343995537811)
            ·
              refine ⟨29145118537896515993306717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19430079025264343995537811 29145118537896515993306717)
              ·
                refine ⟨10929419451711193497490019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29145118537896515993306717 10929419451711193497490019)
                ·
                  refine ⟨16394129177566790246235029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10929419451711193497490019 16394129177566790246235029)
                  ·
                    refine ⟨768474805198443292792267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16394129177566790246235029 768474805198443292792267)
                    ·
                      rfl

theorem cell23_4489798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4489798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489798 prefixEnd_4489798 := by exact prefixLift 4489798
  have htrace : WordTrace (prefixWord ++ tailWord_4489798) baseStart_4489798 baseEnd_4489798 := by
    simpa [prefixWord, tailWord_4489798, baseEnd_4489798] using wordTrace_append hprefix tailTrace_4489798
  have hstable : (prefixWord ++ tailWord_4489798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489798).length < 2 ^ (prefixWord ++ tailWord_4489798).sum := by decide
  have hdescent : baseEnd_4489798 < baseStart_4489798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489805 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4489805 : Nat := 118140960795 + 4489805 * 2 ^ 59
def prefixEnd_4489805 : Nat := 4983230072969 + 3 ^ 40 * 4489805 * 2
def baseEnd_4489805 : Nat := 2305428009959911350989269

theorem tailTrace_4489805 : CollatzResearch.WordTrace tailWord_4489805 prefixEnd_4489805 2305428009959911350989269 := by
  unfold tailWord_4489805
  simp only [CollatzResearch.WordTrace]
  refine ⟨163756641499210757491230869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109171094332807171660820579 163756641499210757491230869)
  ·
    refine ⟨7676092570275504257401447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163756641499210757491230869 7676092570275504257401447)
    ·
      refine ⟨11514138855413256386102171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676092570275504257401447 11514138855413256386102171)
      ·
        refine ⟨17271208283119884579153257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514138855413256386102171 17271208283119884579153257)
        ·
          refine ⟨12953406212339913434364943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17271208283119884579153257 12953406212339913434364943)
          ·
            refine ⟨19430109318509870151547415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12953406212339913434364943 19430109318509870151547415)
            ·
              refine ⟨29145163977764805227321123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19430109318509870151547415 29145163977764805227321123)
              ·
                refine ⟨43717745966647207840981685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29145163977764805227321123 43717745966647207840981685)
                ·
                  refine ⟨4098538684373175735092033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43717745966647207840981685 4098538684373175735092033)
                  ·
                    refine ⟨3073904013279881801319025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4098538684373175735092033 3073904013279881801319025)
                    ·
                      refine ⟨2305428009959911350989269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3073904013279881801319025 2305428009959911350989269)
                      ·
                        rfl

theorem cell23_4489805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4489805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489805 prefixEnd_4489805 := by exact prefixLift 4489805
  have htrace : WordTrace (prefixWord ++ tailWord_4489805) baseStart_4489805 baseEnd_4489805 := by
    simpa [prefixWord, tailWord_4489805, baseEnd_4489805] using wordTrace_append hprefix tailTrace_4489805
  have hstable : (prefixWord ++ tailWord_4489805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489805).length < 2 ^ (prefixWord ++ tailWord_4489805).sum := by decide
  have hdescent : baseEnd_4489805 < baseStart_4489805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489825 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_4489825 : Nat := 118140960795 + 4489825 * 2 ^ 59
def prefixEnd_4489825 : Nat := 4983230072969 + 3 ^ 40 * 4489825 * 2
def baseEnd_4489825 : Nat := 2305438279573001272739177

theorem tailTrace_4489825 : CollatzResearch.WordTrace tailWord_4489825 prefixEnd_4489825 2305438279573001272739177 := by
  unfold tailWord_4489825
  simp only [CollatzResearch.WordTrace]
  refine ⟨163757370959138300906958929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109171580639425533937972619 163757370959138300906958929)
  ·
    refine ⟨122818028219353725680219197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163757370959138300906958929 122818028219353725680219197)
    ·
      refine ⟨46056760582257647130082199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122818028219353725680219197 46056760582257647130082199)
      ·
        refine ⟨69085140873386470695123299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46056760582257647130082199 69085140873386470695123299)
        ·
          refine ⟨103627711310079706042684949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69085140873386470695123299 103627711310079706042684949)
          ·
            refine ⟨4857548967659986220750857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103627711310079706042684949 4857548967659986220750857)
            ·
              refine ⟨3643161725744989665563143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857548967659986220750857 3643161725744989665563143)
              ·
                refine ⟨5464742588617484498344715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643161725744989665563143 5464742588617484498344715)
                ·
                  refine ⟨8197113882926226747517073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464742588617484498344715 8197113882926226747517073)
                  ·
                    refine ⟨6147835412194670060637805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8197113882926226747517073 6147835412194670060637805)
                    ·
                      refine ⟨2305438279573001272739177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6147835412194670060637805 2305438279573001272739177)
                      ·
                        rfl

theorem cell23_4489825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_4489825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489825 prefixEnd_4489825 := by exact prefixLift 4489825
  have htrace : WordTrace (prefixWord ++ tailWord_4489825) baseStart_4489825 baseEnd_4489825 := by
    simpa [prefixWord, tailWord_4489825, baseEnd_4489825] using wordTrace_append hprefix tailTrace_4489825
  have hstable : (prefixWord ++ tailWord_4489825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489825).length < 2 ^ (prefixWord ++ tailWord_4489825).sum := by decide
  have hdescent : baseEnd_4489825 < baseStart_4489825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489832 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_4489832 : Nat := 118140960795 + 4489832 * 2 ^ 59
def prefixEnd_4489832 : Nat := 4983230072969 + 3 ^ 40 * 4489832 * 2
def baseEnd_4489832 : Nat := 768480624645860915117215

theorem tailTrace_4489832 : CollatzResearch.WordTrace tailWord_4489832 prefixEnd_4489832 768480624645860915117215 := by
  unfold tailWord_4489832
  simp only [CollatzResearch.WordTrace]
  refine ⟨81878813135056470551231875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109171750846741960734975833 81878813135056470551231875)
  ·
    refine ⟨122818219702584705826847813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81878813135056470551231875 122818219702584705826847813)
    ·
      refine ⟨23028416194234632342533965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122818219702584705826847813 23028416194234632342533965)
      ·
        refine ⟨8635656072837987128450237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23028416194234632342533965 8635656072837987128450237)
        ·
          refine ⟨3238371027314245173168839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8635656072837987128450237 3238371027314245173168839)
          ·
            refine ⟨4857556540971367759753259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238371027314245173168839 4857556540971367759753259)
            ·
              refine ⟨7286334811457051639629889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857556540971367759753259 7286334811457051639629889)
              ·
                refine ⟨5464751108592788729722417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7286334811457051639629889 5464751108592788729722417)
                ·
                  refine ⟨4098563331444591547291813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464751108592788729722417 4098563331444591547291813)
                  ·
                    refine ⟨768480624645860915117215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098563331444591547291813 768480624645860915117215)
                    ·
                      rfl

theorem cell23_4489832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_4489832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489832 prefixEnd_4489832 := by exact prefixLift 4489832
  have htrace : WordTrace (prefixWord ++ tailWord_4489832) baseStart_4489832 baseEnd_4489832 := by
    simpa [prefixWord, tailWord_4489832, baseEnd_4489832] using wordTrace_append hprefix tailTrace_4489832
  have hstable : (prefixWord ++ tailWord_4489832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489832).length < 2 ^ (prefixWord ++ tailWord_4489832).sum := by decide
  have hdescent : baseEnd_4489832 < baseStart_4489832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489968 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2]
def baseStart_4489968 : Nat := 118140960795 + 4489968 * 2 ^ 59
def prefixEnd_4489968 : Nat := 4983230072969 + 3 ^ 40 * 4489968 * 2
def baseEnd_4489968 : Nat := 2305511707306594213251019

theorem tailTrace_4489968 : CollatzResearch.WordTrace tailWord_4489968 prefixEnd_4489968 2305511707306594213251019 := by
  unfold tailWord_4489968
  simp only [CollatzResearch.WordTrace]
  refine ⟨81881293298810118164707279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109175057731746824219609705 81881293298810118164707279)
  ·
    refine ⟨122821939948215177247060919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81881293298810118164707279 122821939948215177247060919)
    ·
      refine ⟨184232909922322765870591379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122821939948215177247060919 184232909922322765870591379)
      ·
        refine ⟨276349364883484148805887069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184232909922322765870591379 276349364883484148805887069)
        ·
          refine ⟨103631011831306555802207651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276349364883484148805887069 103631011831306555802207651)
          ·
            refine ⟨155446517746959833703311477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103631011831306555802207651 155446517746959833703311477)
            ·
              refine ⟨14573111038777484409685451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155446517746959833703311477 14573111038777484409685451)
              ·
                refine ⟨21859666558166226614528177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14573111038777484409685451 21859666558166226614528177)
                ·
                  refine ⟨16394749918624669960896133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21859666558166226614528177 16394749918624669960896133)
                  ·
                    refine ⟨3074015609742125617668025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16394749918624669960896133 3074015609742125617668025)
                    ·
                      refine ⟨2305511707306594213251019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074015609742125617668025 2305511707306594213251019)
                      ·
                        rfl

theorem cell23_4489968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2].length) (baseStart_4489968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489968 prefixEnd_4489968 := by exact prefixLift 4489968
  have htrace : WordTrace (prefixWord ++ tailWord_4489968) baseStart_4489968 baseEnd_4489968 := by
    simpa [prefixWord, tailWord_4489968, baseEnd_4489968] using wordTrace_append hprefix tailTrace_4489968
  have hstable : (prefixWord ++ tailWord_4489968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489968).length < 2 ^ (prefixWord ++ tailWord_4489968).sum := by decide
  have hdescent : baseEnd_4489968 < baseStart_4489968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489971 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3]
def baseStart_4489971 : Nat := 118140960795 + 4489971 * 2 ^ 59
def prefixEnd_4489971 : Nat := 4983230072969 + 3 ^ 40 * 4489971 * 2
def baseEnd_4489971 : Nat := 2305513247748557701513505

theorem tailTrace_4489971 : CollatzResearch.WordTrace tailWord_4489971 prefixEnd_4489971 2305513247748557701513505 := by
  unfold tailWord_4489971
  simp only [CollatzResearch.WordTrace]
  refine ⟨163762696016609367841773767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109175130677739578561182511 163762696016609367841773767)
  ·
    refine ⟨245644044024914051762660651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163762696016609367841773767 245644044024914051762660651)
    ·
      refine ⟨368466066037371077643990977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245644044024914051762660651 368466066037371077643990977)
      ·
        refine ⟨276349549528028308232993233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368466066037371077643990977 276349549528028308232993233)
        ·
          refine ⟨207262162146021231174744925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276349549528028308232993233 207262162146021231174744925)
          ·
            refine ⟨77723310804757961690529347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207262162146021231174744925 77723310804757961690529347)
            ·
              refine ⟨116584966207136942535794021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77723310804757961690529347 116584966207136942535794021)
              ·
                refine ⟨21859681163838176725461379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116584966207136942535794021 21859681163838176725461379)
                ·
                  refine ⟨32789521745757265088192069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21859681163838176725461379 32789521745757265088192069)
                  ·
                    refine ⟨6148035327329487204036013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32789521745757265088192069 6148035327329487204036013)
                    ·
                      refine ⟨2305513247748557701513505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148035327329487204036013 2305513247748557701513505)
                      ·
                        rfl

theorem cell23_4489971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_4489971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489971 prefixEnd_4489971 := by exact prefixLift 4489971
  have htrace : WordTrace (prefixWord ++ tailWord_4489971) baseStart_4489971 baseEnd_4489971 := by
    simpa [prefixWord, tailWord_4489971, baseEnd_4489971] using wordTrace_append hprefix tailTrace_4489971
  have hstable : (prefixWord ++ tailWord_4489971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489971).length < 2 ^ (prefixWord ++ tailWord_4489971).sum := by decide
  have hdescent : baseEnd_4489971 < baseStart_4489971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4489988 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4489988 : Nat := 118140960795 + 4489988 * 2 ^ 59
def prefixEnd_4489988 : Nat := 4983230072969 + 3 ^ 40 * 4489988 * 2
def baseEnd_4489988 : Nat := 2305521976919684135000927

theorem tailTrace_4489988 : CollatzResearch.WordTrace tailWord_4489988 prefixEnd_4489988 2305521976919684135000927 := by
  unfold tailWord_4489988
  simp only [CollatzResearch.WordTrace]
  refine ⟨81881658028773889872571309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109175544038365186496761745 81881658028773889872571309)
  ·
    refine ⟨30705621760790208702214241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81881658028773889872571309 30705621760790208702214241)
    ·
      refine ⟨23029216320592656526660681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30705621760790208702214241 23029216320592656526660681)
      ·
        refine ⟨17271912240444492394995511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23029216320592656526660681 17271912240444492394995511)
        ·
          refine ⟨25907868360666738592493267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17271912240444492394995511 25907868360666738592493267)
          ·
            refine ⟨38861802541000107888739901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25907868360666738592493267 38861802541000107888739901)
            ·
              refine ⟨14573175952875040458277463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38861802541000107888739901 14573175952875040458277463)
              ·
                refine ⟨21859763929312560687416195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14573175952875040458277463 21859763929312560687416195)
                ·
                  refine ⟨32789645893968841031124293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21859763929312560687416195 32789645893968841031124293)
                  ·
                    refine ⟨6148058605119157693335805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32789645893968841031124293 6148058605119157693335805)
                    ·
                      refine ⟨2305521976919684135000927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148058605119157693335805 2305521976919684135000927)
                      ·
                        rfl

theorem cell23_4489988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4489988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4489988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4489988 prefixEnd_4489988 := by exact prefixLift 4489988
  have htrace : WordTrace (prefixWord ++ tailWord_4489988) baseStart_4489988 baseEnd_4489988 := by
    simpa [prefixWord, tailWord_4489988, baseEnd_4489988] using wordTrace_append hprefix tailTrace_4489988
  have hstable : (prefixWord ++ tailWord_4489988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4489988).length < 2 ^ (prefixWord ++ tailWord_4489988).sum := by decide
  have hdescent : baseEnd_4489988 < baseStart_4489988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4489988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490028 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_4490028 : Nat := 118140960795 + 4490028 * 2 ^ 59
def prefixEnd_4490028 : Nat := 4983230072969 + 3 ^ 40 * 4490028 * 2
def baseEnd_4490028 : Nat := 2305542516145863978500743

theorem tailTrace_4490028 : CollatzResearch.WordTrace tailWord_4490028 prefixEnd_4490028 2305542516145863978500743 := by
  unfold tailWord_4490028
  simp only [CollatzResearch.WordTrace]
  refine ⟨81882387488701433288299369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109176516651601911051065825 81882387488701433288299369)
  ·
    refine ⟨61411790616526074966224527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81882387488701433288299369 61411790616526074966224527)
    ·
      refine ⟨92117685924789112449336791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61411790616526074966224527 92117685924789112449336791)
      ·
        refine ⟨138176528887183668674005187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92117685924789112449336791 138176528887183668674005187)
        ·
          refine ⟨207264793330775503011007781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138176528887183668674005187 207264793330775503011007781)
          ·
            refine ⟨38862148749520406814563959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207264793330775503011007781 38862148749520406814563959)
            ·
              refine ⟨58293223124280610221845939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38862148749520406814563959 58293223124280610221845939)
              ·
                refine ⟨87439834686420915332768909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58293223124280610221845939 87439834686420915332768909)
                ·
                  refine ⟨32789938007407843249788341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87439834686420915332768909 32789938007407843249788341)
                  ·
                    refine ⟨3074056688194485304667657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32789938007407843249788341 3074056688194485304667657)
                    ·
                      refine ⟨2305542516145863978500743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074056688194485304667657 2305542516145863978500743)
                      ·
                        rfl

theorem cell23_4490028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_4490028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490028 prefixEnd_4490028 := by exact prefixLift 4490028
  have htrace : WordTrace (prefixWord ++ tailWord_4490028) baseStart_4490028 baseEnd_4490028 := by
    simpa [prefixWord, tailWord_4490028, baseEnd_4490028] using wordTrace_append hprefix tailTrace_4490028
  have hstable : (prefixWord ++ tailWord_4490028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490028).length < 2 ^ (prefixWord ++ tailWord_4490028).sum := by decide
  have hdescent : baseEnd_4490028 < baseStart_4490028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490035 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 3]
def baseStart_4490035 : Nat := 118140960795 + 4490035 * 2 ^ 59
def prefixEnd_4490035 : Nat := 4983230072969 + 3 ^ 40 * 4490035 * 2
def baseEnd_4490035 : Nat := 2305546110510445451113211

theorem tailTrace_4490035 : CollatzResearch.WordTrace tailWord_4490035 prefixEnd_4490035 2305546110510445451113211 := by
  unfold tailWord_4490035
  simp only [CollatzResearch.WordTrace]
  refine ⟨163765030288377506772103559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109176686858918337848069039 163765030288377506772103559)
  ·
    refine ⟨245647545432566260158155339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163765030288377506772103559 245647545432566260158155339)
    ·
      refine ⟨368471318148849390237233009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245647545432566260158155339 368471318148849390237233009)
      ·
        refine ⟨276353488611637042677924757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368471318148849390237233009 276353488611637042677924757)
        ·
          refine ⟨12954069778670486375527723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 276353488611637042677924757 12954069778670486375527723)
          ·
            refine ⟨19431104668005729563291585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12954069778670486375527723 19431104668005729563291585)
            ·
              refine ⟨14573328501004297172468689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19431104668005729563291585 14573328501004297172468689)
              ·
                refine ⟨10929996375753222879351517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14573328501004297172468689 10929996375753222879351517)
                ·
                  refine ⟨4098748640907458579756819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10929996375753222879351517 4098748640907458579756819)
                  ·
                    refine ⟨6148122961361187869635229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4098748640907458579756819 6148122961361187869635229)
                    ·
                      refine ⟨2305546110510445451113211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148122961361187869635229 2305546110510445451113211)
                      ·
                        rfl

theorem cell23_4490035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_4490035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490035 prefixEnd_4490035 := by exact prefixLift 4490035
  have htrace : WordTrace (prefixWord ++ tailWord_4490035) baseStart_4490035 baseEnd_4490035 := by
    simpa [prefixWord, tailWord_4490035, baseEnd_4490035] using wordTrace_append hprefix tailTrace_4490035
  have hstable : (prefixWord ++ tailWord_4490035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490035).length < 2 ^ (prefixWord ++ tailWord_4490035).sum := by decide
  have hdescent : baseEnd_4490035 < baseStart_4490035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490046 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4490046 : Nat := 118140960795 + 4490046 * 2 ^ 59
def prefixEnd_4490046 : Nat := 4983230072969 + 3 ^ 40 * 4490046 * 2
def baseEnd_4490046 : Nat := 768517252932548302691887

theorem tailTrace_4490046 : CollatzResearch.WordTrace tailWord_4490046 prefixEnd_4490046 768517252932548302691887 := by
  unfold tailWord_4490046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470678936417206956344249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109176954327558437100502661 20470678936417206956344249)
  ·
    refine ⟨15353009202312905217258187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20470678936417206956344249 15353009202312905217258187)
    ·
      refine ⟨23029513803469357825887281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15353009202312905217258187 23029513803469357825887281)
      ·
        refine ⟨17272135352602018369415461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23029513803469357825887281 17272135352602018369415461)
        ·
          refine ⟨3238525378612878444265399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17272135352602018369415461 3238525378612878444265399)
          ·
            refine ⟨4857788067919317666398099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238525378612878444265399 4857788067919317666398099)
            ·
              refine ⟨7286682101878976499597149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857788067919317666398099 7286682101878976499597149)
              ·
                refine ⟨2732505788204616187348931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7286682101878976499597149 2732505788204616187348931)
                ·
                  refine ⟨4098758682306924281023397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732505788204616187348931 4098758682306924281023397)
                  ·
                    refine ⟨768517252932548302691887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098758682306924281023397 768517252932548302691887)
                    ·
                      rfl

theorem cell23_4490046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4490046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490046 prefixEnd_4490046 := by exact prefixLift 4490046
  have htrace : WordTrace (prefixWord ++ tailWord_4490046) baseStart_4490046 baseEnd_4490046 := by
    simpa [prefixWord, tailWord_4490046, baseEnd_4490046] using wordTrace_append hprefix tailTrace_4490046
  have hstable : (prefixWord ++ tailWord_4490046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490046).length < 2 ^ (prefixWord ++ tailWord_4490046).sum := by decide
  have hdescent : baseEnd_4490046 < baseStart_4490046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490051 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 6]
def baseStart_4490051 : Nat := 118140960795 + 4490051 * 2 ^ 59
def prefixEnd_4490051 : Nat := 4983230072969 + 3 ^ 40 * 4490051 * 2
def baseEnd_4490051 : Nat := 768518108733639129504379

theorem tailTrace_4490051 : CollatzResearch.WordTrace tailWord_4490051 prefixEnd_4490051 768518108733639129504379 := by
  unfold tailWord_4490051
  simp only [CollatzResearch.WordTrace]
  refine ⟨163765613856319541504686007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109177075904213027669790671 163765613856319541504686007)
  ·
    refine ⟨245648420784479312257029011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163765613856319541504686007 245648420784479312257029011)
    ·
      refine ⟨368472631176718968385543517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245648420784479312257029011 368472631176718968385543517)
      ·
        refine ⟨138177236691269613144578819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368472631176718968385543517 138177236691269613144578819)
        ·
          refine ⟨207265855036904419716868229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138177236691269613144578819 207265855036904419716868229)
          ·
            refine ⟨38862347819419578696912793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207265855036904419716868229 38862347819419578696912793)
            ·
              refine ⟨29146760864564684022684595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38862347819419578696912793 29146760864564684022684595)
              ·
                refine ⟨43720141296847026034026893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29146760864564684022684595 43720141296847026034026893)
                ·
                  refine ⟨16395052986317634762760085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43720141296847026034026893 16395052986317634762760085)
                  ·
                    refine ⟨768518108733639129504379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16395052986317634762760085 768518108733639129504379)
                    ·
                      rfl

theorem cell23_4490051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_4490051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490051 prefixEnd_4490051 := by exact prefixLift 4490051
  have htrace : WordTrace (prefixWord ++ tailWord_4490051) baseStart_4490051 baseEnd_4490051 := by
    simpa [prefixWord, tailWord_4490051, baseEnd_4490051] using wordTrace_append hprefix tailTrace_4490051
  have hstable : (prefixWord ++ tailWord_4490051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490051).length < 2 ^ (prefixWord ++ tailWord_4490051).sum := by decide
  have hdescent : baseEnd_4490051 < baseStart_4490051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490069 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4490069 : Nat := 118140960795 + 4490069 * 2 ^ 59
def prefixEnd_4490069 : Nat := 4983230072969 + 3 ^ 40 * 4490069 * 2
def baseEnd_4490069 : Nat := 2305563568852698318088055

theorem tailTrace_4490069 : CollatzResearch.WordTrace tailWord_4490069 prefixEnd_4490069 2305563568852698318088055 := by
  unfold tailWord_4490069
  simp only [CollatzResearch.WordTrace]
  refine ⟨163766270370254330578841261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109177513580169553719227507 163766270370254330578841261)
  ·
    refine ⟨61412351388845373967065473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163766270370254330578841261 61412351388845373967065473)
    ·
      refine ⟨46059263541634030475299105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61412351388845373967065473 46059263541634030475299105)
      ·
        refine ⟨34544447656225522856474329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46059263541634030475299105 34544447656225522856474329)
        ·
          refine ⟨25908335742169142142355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34544447656225522856474329 25908335742169142142355747)
          ·
            refine ⟨38862503613253713213533621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25908335742169142142355747 38862503613253713213533621)
            ·
              refine ⟨3643359713742535613768777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38862503613253713213533621 3643359713742535613768777)
              ·
                refine ⟨2732519785306901710326583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643359713742535613768777 2732519785306901710326583)
                ·
                  refine ⟨4098779677960352565489875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732519785306901710326583 4098779677960352565489875)
                  ·
                    refine ⟨6148169516940528848234813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4098779677960352565489875 6148169516940528848234813)
                    ·
                      refine ⟨2305563568852698318088055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148169516940528848234813 2305563568852698318088055)
                      ·
                        rfl

theorem cell23_4490069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4490069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490069 prefixEnd_4490069 := by exact prefixLift 4490069
  have htrace : WordTrace (prefixWord ++ tailWord_4490069) baseStart_4490069 baseEnd_4490069 := by
    simpa [prefixWord, tailWord_4490069, baseEnd_4490069] using wordTrace_append hprefix tailTrace_4490069
  have hstable : (prefixWord ++ tailWord_4490069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490069).length < 2 ^ (prefixWord ++ tailWord_4490069).sum := by decide
  have hdescent : baseEnd_4490069 < baseStart_4490069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490088 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4490088 : Nat := 118140960795 + 4490088 * 2 ^ 59
def prefixEnd_4490088 : Nat := 4983230072969 + 3 ^ 40 * 4490088 * 2
def baseEnd_4490088 : Nat := 2305573324985133743750467

theorem tailTrace_4490088 : CollatzResearch.WordTrace tailWord_4490088 prefixEnd_4490088 2305573324985133743750467 := by
  unfold tailWord_4490088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81883481678592748411891459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109177975571456997882521945 81883481678592748411891459)
  ·
    refine ⟨122825222517889122617837189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81883481678592748411891459 122825222517889122617837189)
    ·
      refine ⟨23029729222104210490844473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122825222517889122617837189 23029729222104210490844473)
      ·
        refine ⟨17272296916578157868133355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23029729222104210490844473 17272296916578157868133355)
        ·
          refine ⟨25908445374867236802200033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17272296916578157868133355 25908445374867236802200033)
          ·
            refine ⟨19431334031150427601650025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25908445374867236802200033 19431334031150427601650025)
            ·
              refine ⟨14573500523362820701237519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19431334031150427601650025 14573500523362820701237519)
              ·
                refine ⟨21860250785044231051856279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14573500523362820701237519 21860250785044231051856279)
                ·
                  refine ⟨32790376177566346577784419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21860250785044231051856279 32790376177566346577784419)
                  ·
                    refine ⟨49185564266349519866676629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32790376177566346577784419 49185564266349519866676629)
                    ·
                      refine ⟨2305573324985133743750467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49185564266349519866676629 2305573324985133743750467)
                      ·
                        rfl

theorem cell23_4490088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4490088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490088 prefixEnd_4490088 := by exact prefixLift 4490088
  have htrace : WordTrace (prefixWord ++ tailWord_4490088) baseStart_4490088 baseEnd_4490088 := by
    simpa [prefixWord, tailWord_4490088, baseEnd_4490088] using wordTrace_append hprefix tailTrace_4490088
  have hstable : (prefixWord ++ tailWord_4490088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490088).length < 2 ^ (prefixWord ++ tailWord_4490088).sum := by decide
  have hdescent : baseEnd_4490088 < baseStart_4490088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490135 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_4490135 : Nat := 118140960795 + 4490135 * 2 ^ 59
def prefixEnd_4490135 : Nat := 4983230072969 + 3 ^ 40 * 4490135 * 2
def baseEnd_4490135 : Nat := 2305597458575895059862751

theorem tailTrace_4490135 : CollatzResearch.WordTrace tailWord_4490135 prefixEnd_4490135 2305597458575895059862751 := by
  unfold tailWord_4490135
  simp only [CollatzResearch.WordTrace]
  refine ⟨163768677588015223850743859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109179118392010149233829239 163768677588015223850743859)
  ·
    refine ⟨245653016382022835776115789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163768677588015223850743859 245653016382022835776115789)
    ·
      refine ⟨92119881143258563416043421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245653016382022835776115789 92119881143258563416043421)
      ·
        refine ⟨34544955428721961281016283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92119881143258563416043421 34544955428721961281016283)
        ·
          refine ⟨51817433143082941921524425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34544955428721961281016283 51817433143082941921524425)
          ·
            refine ⟨38863074857312206441143319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51817433143082941921524425 38863074857312206441143319)
            ·
              refine ⟨58294612285968309661714979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38863074857312206441143319 58294612285968309661714979)
              ·
                refine ⟨87441918428952464492572469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58294612285968309661714979 87441918428952464492572469)
                ·
                  refine ⟨8197679852714293546178669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87441918428952464492572469 8197679852714293546178669)
                  ·
                    refine ⟨3074129944767860079817001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8197679852714293546178669 3074129944767860079817001)
                    ·
                      refine ⟨2305597458575895059862751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074129944767860079817001 2305597458575895059862751)
                      ·
                        rfl

theorem cell23_4490135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_4490135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490135 prefixEnd_4490135 := by exact prefixLift 4490135
  have htrace : WordTrace (prefixWord ++ tailWord_4490135) baseStart_4490135 baseEnd_4490135 := by
    simpa [prefixWord, tailWord_4490135, baseEnd_4490135] using wordTrace_append hprefix tailTrace_4490135
  have hstable : (prefixWord ++ tailWord_4490135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490135).length < 2 ^ (prefixWord ++ tailWord_4490135).sum := by decide
  have hdescent : baseEnd_4490135 < baseStart_4490135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490148 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4490148 : Nat := 118140960795 + 4490148 * 2 ^ 59
def prefixEnd_4490148 : Nat := 4983230072969 + 3 ^ 40 * 4490148 * 2
def baseEnd_4490148 : Nat := 2305604133824403509000191

theorem tailTrace_4490148 : CollatzResearch.WordTrace tailWord_4490148 prefixEnd_4490148 2305604133824403509000191 := by
  unfold tailWord_4490148
  simp only [CollatzResearch.WordTrace]
  refine ⟨81884575868484063535483549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109179434491312084713978065 81884575868484063535483549)
  ·
    refine ⟨30706715950681523825806331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81884575868484063535483549 30706715950681523825806331)
    ·
      refine ⟨46060073926022285738709497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30706715950681523825806331 46060073926022285738709497)
      ·
        refine ⟨34545055444516714304032123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46060073926022285738709497 34545055444516714304032123)
        ·
          refine ⟨51817583166775071456048185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34545055444516714304032123 51817583166775071456048185)
          ·
            refine ⟨38863187375081303592036139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51817583166775071456048185 38863187375081303592036139)
            ·
              refine ⟨58294781062621955388054209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38863187375081303592036139 58294781062621955388054209)
              ·
                refine ⟨43721085796966466541040657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58294781062621955388054209 43721085796966466541040657)
                ·
                  refine ⟨32790814347724849905780493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43721085796966466541040657 32790814347724849905780493)
                  ·
                    refine ⟨12296555380396818714667685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32790814347724849905780493 12296555380396818714667685)
                    ·
                      refine ⟨2305604133824403509000191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12296555380396818714667685 2305604133824403509000191)
                      ·
                        rfl

theorem cell23_4490148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4490148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490148 prefixEnd_4490148 := by exact prefixLift 4490148
  have htrace : WordTrace (prefixWord ++ tailWord_4490148) baseStart_4490148 baseEnd_4490148 := by
    simpa [prefixWord, tailWord_4490148, baseEnd_4490148] using wordTrace_append hprefix tailTrace_4490148
  have hstable : (prefixWord ++ tailWord_4490148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490148).length < 2 ^ (prefixWord ++ tailWord_4490148).sum := by decide
  have hdescent : baseEnd_4490148 < baseStart_4490148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490169 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4490169 : Nat := 118140960795 + 4490169 * 2 ^ 59
def prefixEnd_4490169 : Nat := 4983230072969 + 3 ^ 40 * 4490169 * 2
def baseEnd_4490169 : Nat := 2305614916918147926837595

theorem tailTrace_4490169 : CollatzResearch.WordTrace tailWord_4490169 prefixEnd_4490169 2305614916918147926837595 := by
  unfold tailWord_4490169
  simp only [CollatzResearch.WordTrace]
  refine ⟨163769917669892047657481561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109179945113261365104987707 163769917669892047657481561)
  ·
    refine ⟨122827438252419035743111171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163769917669892047657481561 122827438252419035743111171)
    ·
      refine ⟨184241157378628553614666757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122827438252419035743111171 184241157378628553614666757)
      ·
        refine ⟨34545217008492853802750017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184241157378628553614666757 34545217008492853802750017)
        ·
          refine ⟨25908912756369640352062513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34545217008492853802750017 25908912756369640352062513)
          ·
            refine ⟨19431684567277230264046885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25908912756369640352062513 19431684567277230264046885)
            ·
              refine ⟨3643440856364480674508791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19431684567277230264046885 3643440856364480674508791)
              ·
                refine ⟨5465161284546721011763187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643440856364480674508791 5465161284546721011763187)
                ·
                  refine ⟨8197741926820081517644781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465161284546721011763187 8197741926820081517644781)
                  ·
                    refine ⟨3074153222557530569116793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8197741926820081517644781 3074153222557530569116793)
                    ·
                      refine ⟨2305614916918147926837595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074153222557530569116793 2305614916918147926837595)
                      ·
                        rfl

theorem cell23_4490169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4490169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490169 prefixEnd_4490169 := by exact prefixLift 4490169
  have htrace : WordTrace (prefixWord ++ tailWord_4490169) baseStart_4490169 baseEnd_4490169 := by
    simpa [prefixWord, tailWord_4490169, baseEnd_4490169] using wordTrace_append hprefix tailTrace_4490169
  have hstable : (prefixWord ++ tailWord_4490169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490169).length < 2 ^ (prefixWord ++ tailWord_4490169).sum := by decide
  have hdescent : baseEnd_4490169 < baseStart_4490169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490205 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 7]
def baseStart_4490205 : Nat := 118140960795 + 4490205 * 2 ^ 59
def prefixEnd_4490205 : Nat := 4983230072969 + 3 ^ 40 * 4490205 * 2
def baseEnd_4490205 : Nat := 256181489135745531776381

theorem tailTrace_4490205 : CollatzResearch.WordTrace tailWord_4490205 prefixEnd_4490205 256181489135745531776381 := by
  unfold tailWord_4490205
  simp only [CollatzResearch.WordTrace]
  refine ⟨163771230697761625805792069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109180820465174417203861379 163771230697761625805792069)
  ·
    refine ⟨30707105755830304838586013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163771230697761625805792069 30707105755830304838586013)
    ·
      refine ⟨11515164658436364314469755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30707105755830304838586013 11515164658436364314469755)
      ·
        refine ⟨17272746987654546471704633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11515164658436364314469755 17272746987654546471704633)
        ·
          refine ⟨12954560240740909853778475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17272746987654546471704633 12954560240740909853778475)
          ·
            refine ⟨19431840361111364780667713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12954560240740909853778475 19431840361111364780667713)
            ·
              refine ⟨14573880270833523585500785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19431840361111364780667713 14573880270833523585500785)
              ·
                refine ⟨10930410203125142689125589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14573880270833523585500785 10930410203125142689125589)
                ·
                  refine ⟨256181489135745531776381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10930410203125142689125589 256181489135745531776381)
                  ·
                    rfl

theorem cell23_4490205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_4490205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490205 prefixEnd_4490205 := by exact prefixLift 4490205
  have htrace : WordTrace (prefixWord ++ tailWord_4490205) baseStart_4490205 baseEnd_4490205 := by
    simpa [prefixWord, tailWord_4490205, baseEnd_4490205] using wordTrace_append hprefix tailTrace_4490205
  have hstable : (prefixWord ++ tailWord_4490205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490205).length < 2 ^ (prefixWord ++ tailWord_4490205).sum := by decide
  have hdescent : baseEnd_4490205 < baseStart_4490205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490265 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_4490265 : Nat := 118140960795 + 4490265 * 2 ^ 59
def prefixEnd_4490265 : Nat := 4983230072969 + 3 ^ 40 * 4490265 * 2
def baseEnd_4490265 : Nat := 768554737020326517079051

theorem tailTrace_4490265 : CollatzResearch.WordTrace tailWord_4490265 prefixEnd_4490265 768554737020326517079051 := by
  unfold tailWord_4490265
  simp only [CollatzResearch.WordTrace]
  refine ⟨163773419077544256052976249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109182279385029504035317499 163773419077544256052976249)
  ·
    refine ⟨122830064308158192039732187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163773419077544256052976249 122830064308158192039732187)
    ·
      refine ⟨184245096462237288059598281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122830064308158192039732187 184245096462237288059598281)
      ·
        refine ⟨138183822346677966044698711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184245096462237288059598281 138183822346677966044698711)
        ·
          refine ⟨207275733520016949067048067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138183822346677966044698711 207275733520016949067048067)
          ·
            refine ⟨310913600280025423600572101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207275733520016949067048067 310913600280025423600572101)
            ·
              refine ⟨58296300052504766925107269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 310913600280025423600572101 58296300052504766925107269)
              ·
                refine ⟨10930556259844643798457613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58296300052504766925107269 10930556259844643798457613)
                ·
                  refine ⟨4098958597441741424421605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10930556259844643798457613 4098958597441741424421605)
                  ·
                    refine ⟨768554737020326517079051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4098958597441741424421605 768554737020326517079051)
                    ·
                      rfl

theorem cell23_4490265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_4490265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490265 prefixEnd_4490265 := by exact prefixLift 4490265
  have htrace : WordTrace (prefixWord ++ tailWord_4490265) baseStart_4490265 baseEnd_4490265 := by
    simpa [prefixWord, tailWord_4490265, baseEnd_4490265] using wordTrace_append hprefix tailTrace_4490265
  have hstable : (prefixWord ++ tailWord_4490265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490265).length < 2 ^ (prefixWord ++ tailWord_4490265).sum := by decide
  have hdescent : baseEnd_4490265 < baseStart_4490265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490325 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_4490325 : Nat := 118140960795 + 4490325 * 2 ^ 59
def prefixEnd_4490325 : Nat := 4983230072969 + 3 ^ 40 * 4490325 * 2
def baseEnd_4490325 : Nat := 768565006633416438828959

theorem tailTrace_4490325 : CollatzResearch.WordTrace tailWord_4490325 prefixEnd_4490325 768565006633416438828959 := by
  unfold tailWord_4490325
  simp only [CollatzResearch.WordTrace]
  refine ⟨163775607457326886300160429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109183738304884590866773619 163775607457326886300160429)
  ·
    refine ⟨61415852796497582362560161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163775607457326886300160429 61415852796497582362560161)
    ·
      refine ⟨46061889597373186771920121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61415852796497582362560161 46061889597373186771920121)
      ·
        refine ⟨34546417198029890078940091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46061889597373186771920121 34546417198029890078940091)
        ·
          refine ⟨51819625797044835118410137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34546417198029890078940091 51819625797044835118410137)
          ·
            refine ⟨38864719347783626338807603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51819625797044835118410137 38864719347783626338807603)
            ·
              refine ⟨58297079021675439508211405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38864719347783626338807603 58297079021675439508211405)
              ·
                refine ⟨21861404633128289815579277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58297079021675439508211405 21861404633128289815579277)
                ·
                  refine ⟨8198026737423108680842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21861404633128289815579277 8198026737423108680842229)
                  ·
                    refine ⟨768565006633416438828959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8198026737423108680842229 768565006633416438828959)
                    ·
                      rfl

theorem cell23_4490325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_4490325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490325 prefixEnd_4490325 := by exact prefixLift 4490325
  have htrace : WordTrace (prefixWord ++ tailWord_4490325) baseStart_4490325 baseEnd_4490325 := by
    simpa [prefixWord, tailWord_4490325, baseEnd_4490325] using wordTrace_append hprefix tailTrace_4490325
  have hstable : (prefixWord ++ tailWord_4490325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490325).length < 2 ^ (prefixWord ++ tailWord_4490325).sum := by decide
  have hdescent : baseEnd_4490325 < baseStart_4490325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490326 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4490326 : Nat := 118140960795 + 4490326 * 2 ^ 59
def prefixEnd_4490326 : Nat := 4983230072969 + 3 ^ 40 * 4490326 * 2
def baseEnd_4490326 : Nat := 2305695533380903812574373

theorem tailTrace_4490326 : CollatzResearch.WordTrace tailWord_4490326 prefixEnd_4490326 2305695533380903812574373 := by
  unfold tailWord_4490326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235977745645203966934177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109183762620215508980631221 10235977745645203966934177)
  ·
    refine ⟨7676983309233902975200633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10235977745645203966934177 7676983309233902975200633)
    ·
      refine ⟨5757737481925427231400475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7676983309233902975200633 5757737481925427231400475)
      ·
        refine ⟨8636606222888140847100713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757737481925427231400475 8636606222888140847100713)
        ·
          refine ⟨6477454667166105635325535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636606222888140847100713 6477454667166105635325535)
          ·
            refine ⟨9716182000749158452988303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477454667166105635325535 9716182000749158452988303)
            ·
              refine ⟨14574273001123737679482455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9716182000749158452988303 14574273001123737679482455)
              ·
                refine ⟨21861409501685606519223683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14574273001123737679482455 21861409501685606519223683)
                ·
                  refine ⟨32792114252528409778835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21861409501685606519223683 32792114252528409778835525)
                  ·
                    refine ⟨6148521422349076833531661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32792114252528409778835525 6148521422349076833531661)
                    ·
                      refine ⟨2305695533380903812574373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148521422349076833531661 2305695533380903812574373)
                      ·
                        rfl

theorem cell23_4490326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4490326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490326 prefixEnd_4490326 := by exact prefixLift 4490326
  have htrace : WordTrace (prefixWord ++ tailWord_4490326) baseStart_4490326 baseEnd_4490326 := by
    simpa [prefixWord, tailWord_4490326, baseEnd_4490326] using wordTrace_append hprefix tailTrace_4490326
  have hstable : (prefixWord ++ tailWord_4490326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490326).length < 2 ^ (prefixWord ++ tailWord_4490326).sum := by decide
  have hdescent : baseEnd_4490326 < baseStart_4490326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490333 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4490333 : Nat := 118140960795 + 4490333 * 2 ^ 59
def prefixEnd_4490333 : Nat := 4983230072969 + 3 ^ 40 * 4490333 * 2
def baseEnd_4490333 : Nat := 768566375915161761728947

theorem tailTrace_4490333 : CollatzResearch.WordTrace tailWord_4490333 prefixEnd_4490333 768566375915161761728947 := by
  unfold tailWord_4490333
  simp only [CollatzResearch.WordTrace]
  refine ⟨163775899241297903666451653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109183932827531935777634435 163775899241297903666451653)
  ·
    refine ⟨30707981107743356937459685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163775899241297903666451653 30707981107743356937459685)
    ·
      refine ⟨5757746457701879425773691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30707981107743356937459685 5757746457701879425773691)
      ·
        refine ⟨8636619686552819138660537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757746457701879425773691 8636619686552819138660537)
        ·
          refine ⟨6477464764914614353995403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636619686552819138660537 6477464764914614353995403)
          ·
            refine ⟨9716197147371921530993105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477464764914614353995403 9716197147371921530993105)
            ·
              refine ⟨7287147860528941148244829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716197147371921530993105 7287147860528941148244829)
              ·
                refine ⟨2732680447698352930591811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7287147860528941148244829 2732680447698352930591811)
                ·
                  refine ⟨4099020671547529395887717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732680447698352930591811 4099020671547529395887717)
                  ·
                    refine ⟨768566375915161761728947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099020671547529395887717 768566375915161761728947)
                    ·
                      rfl

theorem cell23_4490333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4490333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490333 prefixEnd_4490333 := by exact prefixLift 4490333
  have htrace : WordTrace (prefixWord ++ tailWord_4490333) baseStart_4490333 baseEnd_4490333 := by
    simpa [prefixWord, tailWord_4490333, baseEnd_4490333] using wordTrace_append hprefix tailTrace_4490333
  have hstable : (prefixWord ++ tailWord_4490333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490333).length < 2 ^ (prefixWord ++ tailWord_4490333).sum := by decide
  have hdescent : baseEnd_4490333 < baseStart_4490333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490372 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_4490372 : Nat := 118140960795 + 4490372 * 2 ^ 59
def prefixEnd_4490372 : Nat := 4983230072969 + 3 ^ 40 * 4490372 * 2
def baseEnd_4490372 : Nat := 768573051163670210866387

theorem tailTrace_4490372 : CollatzResearch.WordTrace tailWord_4490372 prefixEnd_4490372 768573051163670210866387 := by
  unfold tailWord_4490372
  simp only [CollatzResearch.WordTrace]
  refine ⟨81888660844078306663560685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109184881125437742218080913 81888660844078306663560685)
  ·
    refine ⟨30708247816529364998835257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81888660844078306663560685 30708247816529364998835257)
    ·
      refine ⟨23031185862397023749126443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30708247816529364998835257 23031185862397023749126443)
      ·
        refine ⟨34546778793595535623689665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031185862397023749126443 34546778793595535623689665)
        ·
          refine ⟨25910084095196651717767249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34546778793595535623689665 25910084095196651717767249)
          ·
            refine ⟨19432563071397488788325437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25910084095196651717767249 19432563071397488788325437)
            ·
              refine ⟨7287211151774058295622039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19432563071397488788325437 7287211151774058295622039)
              ·
                refine ⟨10930816727661087443433059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287211151774058295622039 10930816727661087443433059)
                ·
                  refine ⟨16396225091491631165149589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10930816727661087443433059 16396225091491631165149589)
                  ·
                    refine ⟨768573051163670210866387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16396225091491631165149589 768573051163670210866387)
                    ·
                      rfl

theorem cell23_4490372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_4490372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490372 prefixEnd_4490372 := by exact prefixLift 4490372
  have htrace : WordTrace (prefixWord ++ tailWord_4490372) baseStart_4490372 baseEnd_4490372 := by
    simpa [prefixWord, tailWord_4490372, baseEnd_4490372] using wordTrace_append hprefix tailTrace_4490372
  have hstable : (prefixWord ++ tailWord_4490372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490372).length < 2 ^ (prefixWord ++ tailWord_4490372).sum := by decide
  have hdescent : baseEnd_4490372 < baseStart_4490372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490399 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4490399 : Nat := 118140960795 + 4490399 * 2 ^ 59
def prefixEnd_4490399 : Nat := 4983230072969 + 3 ^ 40 * 4490399 * 2
def baseEnd_4490399 : Nat := 2305733017468682026961537

theorem tailTrace_4490399 : CollatzResearch.WordTrace tailWord_4490399 prefixEnd_4490399 2305733017468682026961537 := by
  unfold tailWord_4490399
  simp only [CollatzResearch.WordTrace]
  refine ⟨163778306459058796938354251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109185537639372531292236167 163778306459058796938354251)
  ·
    refine ⟨245667459688588195407531377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163778306459058796938354251 245667459688588195407531377)
    ·
      refine ⟨184250594766441146555648533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245667459688588195407531377 184250594766441146555648533)
      ·
        refine ⟨8636746629676928744796025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184250594766441146555648533 8636746629676928744796025)
        ·
          refine ⟨6477559972257696558597019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636746629676928744796025 6477559972257696558597019)
          ·
            refine ⟨9716339958386544837895529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477559972257696558597019 9716339958386544837895529)
            ·
              refine ⟨7287254968789908628421647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716339958386544837895529 7287254968789908628421647)
              ·
                refine ⟨10930882453184862942632471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287254968789908628421647 10930882453184862942632471)
                ·
                  refine ⟨16396323679777294413948707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10930882453184862942632471 16396323679777294413948707)
                  ·
                    refine ⟨24594485519665941620923061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16396323679777294413948707 24594485519665941620923061)
                    ·
                      refine ⟨2305733017468682026961537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24594485519665941620923061 2305733017468682026961537)
                      ·
                        rfl

theorem cell23_4490399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4490399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490399 prefixEnd_4490399 := by exact prefixLift 4490399
  have htrace : WordTrace (prefixWord ++ tailWord_4490399) baseStart_4490399 baseEnd_4490399 := by
    simpa [prefixWord, tailWord_4490399, baseEnd_4490399] using wordTrace_append hprefix tailTrace_4490399
  have hstable : (prefixWord ++ tailWord_4490399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490399).length < 2 ^ (prefixWord ++ tailWord_4490399).sum := by decide
  have hdescent : baseEnd_4490399 < baseStart_4490399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490433 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4490433 : Nat := 118140960795 + 4490433 * 2 ^ 59
def prefixEnd_4490433 : Nat := 4983230072969 + 3 ^ 40 * 4490433 * 2
def baseEnd_4490433 : Nat := 2305750475810934893936381

theorem tailTrace_4490433 : CollatzResearch.WordTrace tailWord_4490433 prefixEnd_4490433 2305750475810934893936381 := by
  unfold tailWord_4490433
  simp only [CollatzResearch.WordTrace]
  refine ⟨163779546540935620745091953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109186364360623747163394635 163779546540935620745091953)
  ·
    refine ⟨122834659905701715558818965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163779546540935620745091953 122834659905701715558818965)
    ·
      refine ⟨5757874683079767916819639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122834659905701715558818965 5757874683079767916819639)
      ·
        refine ⟨8636812024619651875229459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757874683079767916819639 8636812024619651875229459)
        ·
          refine ⟨12955218036929477812844189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8636812024619651875229459 12955218036929477812844189)
          ·
            refine ⟨4858206763848554179816571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12955218036929477812844189 4858206763848554179816571)
            ·
              refine ⟨7287310145772831269724857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858206763848554179816571 7287310145772831269724857)
              ·
                refine ⟨5465482609329623452293643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7287310145772831269724857 5465482609329623452293643)
                ·
                  refine ⟨8198223913994435178440465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465482609329623452293643 8198223913994435178440465)
                  ·
                    refine ⟨6148667935495826383830349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8198223913994435178440465 6148667935495826383830349)
                    ·
                      refine ⟨2305750475810934893936381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148667935495826383830349 2305750475810934893936381)
                      ·
                        rfl

theorem cell23_4490433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4490433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490433 prefixEnd_4490433 := by exact prefixLift 4490433
  have htrace : WordTrace (prefixWord ++ tailWord_4490433) baseStart_4490433 baseEnd_4490433 := by
    simpa [prefixWord, tailWord_4490433, baseEnd_4490433] using wordTrace_append hprefix tailTrace_4490433
  have hstable : (prefixWord ++ tailWord_4490433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490433).length < 2 ^ (prefixWord ++ tailWord_4490433).sum := by decide
  have hdescent : baseEnd_4490433 < baseStart_4490433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490435 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_4490435 : Nat := 118140960795 + 4490435 * 2 ^ 59
def prefixEnd_4490435 : Nat := 4983230072969 + 3 ^ 40 * 4490435 * 2
def baseEnd_4490435 : Nat := 2305751502772243886111371

theorem tailTrace_4490435 : CollatzResearch.WordTrace tailWord_4490435 prefixEnd_4490435 2305751502772243886111371 := by
  unfold tailWord_4490435
  simp only [CollatzResearch.WordTrace]
  refine ⟨163779619486928375086664759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109186412991285583391109839 163779619486928375086664759)
  ·
    refine ⟨245669429230392562629997139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163779619486928375086664759 245669429230392562629997139)
    ·
      refine ⟨368504143845588843944995709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245669429230392562629997139 368504143845588843944995709)
      ·
        refine ⟨138189053942095816479373391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368504143845588843944995709 138189053942095816479373391)
        ·
          refine ⟨207283580913143724719060087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138189053942095816479373391 207283580913143724719060087)
          ·
            refine ⟨310925371369715587078590131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207283580913143724719060087 310925371369715587078590131)
            ·
              refine ⟨466388057054573380617885197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310925371369715587078590131 466388057054573380617885197)
              ·
                refine ⟨174895521395465017731706949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466388057054573380617885197 174895521395465017731706949)
                ·
                  refine ⟨32792910261649690824695053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174895521395465017731706949 32792910261649690824695053)
                  ·
                    refine ⟨12297341348118634059260645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32792910261649690824695053 12297341348118634059260645)
                    ·
                      refine ⟨2305751502772243886111371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12297341348118634059260645 2305751502772243886111371)
                      ·
                        rfl

theorem cell23_4490435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_4490435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490435 prefixEnd_4490435 := by exact prefixLift 4490435
  have htrace : WordTrace (prefixWord ++ tailWord_4490435) baseStart_4490435 baseEnd_4490435 := by
    simpa [prefixWord, tailWord_4490435, baseEnd_4490435] using wordTrace_append hprefix tailTrace_4490435
  have hstable : (prefixWord ++ tailWord_4490435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490435).length < 2 ^ (prefixWord ++ tailWord_4490435).sum := by decide
  have hdescent : baseEnd_4490435 < baseStart_4490435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490472 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4490472 : Nat := 118140960795 + 4490472 * 2 ^ 59
def prefixEnd_4490472 : Nat := 4983230072969 + 3 ^ 40 * 4490472 * 2
def baseEnd_4490472 : Nat := 2305770501556460241348701

theorem tailTrace_4490472 : CollatzResearch.WordTrace tailWord_4490472 prefixEnd_4490472 2305770501556460241348701 := by
  unfold tailWord_4490472
  simp only [CollatzResearch.WordTrace]
  refine ⟨81890484493897165202880835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109187312658529553603841113 81890484493897165202880835)
  ·
    refine ⟨122835726740845747804321253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81890484493897165202880835 122835726740845747804321253)
    ·
      refine ⟨23031698763908577713310235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122835726740845747804321253 23031698763908577713310235)
      ·
        refine ⟨34547548145862866569965353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031698763908577713310235 34547548145862866569965353)
        ·
          refine ⟨25910661109397149927474015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34547548145862866569965353 25910661109397149927474015)
          ·
            refine ⟨38865991664095724891211023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25910661109397149927474015 38865991664095724891211023)
            ·
              refine ⟨58298987496143587336816535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38865991664095724891211023 58298987496143587336816535)
              ·
                refine ⟨87448481244215381005224803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58298987496143587336816535 87448481244215381005224803)
                ·
                  refine ⟨131172721866323071507837205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87448481244215381005224803 131172721866323071507837205)
                  ·
                    refine ⟨6148721337483893976929869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131172721866323071507837205 6148721337483893976929869)
                    ·
                      refine ⟨2305770501556460241348701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148721337483893976929869 2305770501556460241348701)
                      ·
                        rfl

theorem cell23_4490472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4490472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490472 prefixEnd_4490472 := by exact prefixLift 4490472
  have htrace : WordTrace (prefixWord ++ tailWord_4490472) baseStart_4490472 baseEnd_4490472 := by
    simpa [prefixWord, tailWord_4490472, baseEnd_4490472] using wordTrace_append hprefix tailTrace_4490472
  have hstable : (prefixWord ++ tailWord_4490472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490472).length < 2 ^ (prefixWord ++ tailWord_4490472).sum := by decide
  have hdescent : baseEnd_4490472 < baseStart_4490472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490486 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4490486 : Nat := 118140960795 + 4490486 * 2 ^ 59
def prefixEnd_4490486 : Nat := 4983230072969 + 3 ^ 40 * 4490486 * 2
def baseEnd_4490486 : Nat := 2305777690285623186573637

theorem tailTrace_4490486 : CollatzResearch.WordTrace tailWord_4490486 prefixEnd_4490486 2305777690285623186573637 := by
  unfold tailWord_4490486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236342475608975674798207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109187653073162407197847541 10236342475608975674798207)
  ·
    refine ⟨15354513713413463512197311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10236342475608975674798207 15354513713413463512197311)
    ·
      refine ⟨23031770570120195268295967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15354513713413463512197311 23031770570120195268295967)
      ·
        refine ⟨34547655855180292902443951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031770570120195268295967 34547655855180292902443951)
        ·
          refine ⟨51821483782770439353665927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34547655855180292902443951 51821483782770439353665927)
          ·
            refine ⟨77732225674155659030498891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51821483782770439353665927 77732225674155659030498891)
            ·
              refine ⟨116598338511233488545748337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77732225674155659030498891 116598338511233488545748337)
              ·
                refine ⟨87448753883425116409311253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116598338511233488545748337 87448753883425116409311253)
                ·
                  refine ⟨4099160338285552331686465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87448753883425116409311253 4099160338285552331686465)
                  ·
                    refine ⟨3074370253714164248764849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099160338285552331686465 3074370253714164248764849)
                    ·
                      refine ⟨2305777690285623186573637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074370253714164248764849 2305777690285623186573637)
                      ·
                        rfl

theorem cell23_4490486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4490486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490486 prefixEnd_4490486 := by exact prefixLift 4490486
  have htrace : WordTrace (prefixWord ++ tailWord_4490486) baseStart_4490486 baseEnd_4490486 := by
    simpa [prefixWord, tailWord_4490486, baseEnd_4490486] using wordTrace_append hprefix tailTrace_4490486
  have hstable : (prefixWord ++ tailWord_4490486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490486).length < 2 ^ (prefixWord ++ tailWord_4490486).sum := by decide
  have hdescent : baseEnd_4490486 < baseStart_4490486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490532 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4490532 : Nat := 118140960795 + 4490532 * 2 ^ 59
def prefixEnd_4490532 : Nat := 4983230072969 + 3 ^ 40 * 4490532 * 2
def baseEnd_4490532 : Nat := 2305801310395730006598425

theorem tailTrace_4490532 : CollatzResearch.WordTrace tailWord_4490532 prefixEnd_4490532 2305801310395730006598425 := by
  unfold tailWord_4490532
  simp only [CollatzResearch.WordTrace]
  refine ⟨81891578683788480326472925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109188771578384640435297233 81891578683788480326472925)
  ·
    refine ⟨30709342006420680122427347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81891578683788480326472925 30709342006420680122427347)
    ·
      refine ⟨46064013009631020183641021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30709342006420680122427347 46064013009631020183641021)
      ·
        refine ⟨17274004878611632568865383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46064013009631020183641021 17274004878611632568865383)
        ·
          refine ⟨25911007317917448853298075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17274004878611632568865383 25911007317917448853298075)
          ·
            refine ⟨38866510976876173279947113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25911007317917448853298075 38866510976876173279947113)
            ·
              refine ⟨29149883232657129959960335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38866510976876173279947113 29149883232657129959960335)
              ·
                refine ⟨43724824848985694939940503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29149883232657129959960335 43724824848985694939940503)
                ·
                  refine ⟨65587237273478542409910755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43724824848985694939940503 65587237273478542409910755)
                  ·
                    refine ⟨98380855910217813614866133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65587237273478542409910755 98380855910217813614866133)
                    ·
                      refine ⟨2305801310395730006598425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98380855910217813614866133 2305801310395730006598425)
                      ·
                        rfl

theorem cell23_4490532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4490532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490532 prefixEnd_4490532 := by exact prefixLift 4490532
  have htrace : WordTrace (prefixWord ++ tailWord_4490532) baseStart_4490532 baseEnd_4490532 := by
    simpa [prefixWord, tailWord_4490532, baseEnd_4490532] using wordTrace_append hprefix tailTrace_4490532
  have hstable : (prefixWord ++ tailWord_4490532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490532).length < 2 ^ (prefixWord ++ tailWord_4490532).sum := by decide
  have hdescent : baseEnd_4490532 < baseStart_4490532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490573 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4490573 : Nat := 118140960795 + 4490573 * 2 ^ 59
def prefixEnd_4490573 : Nat := 4983230072969 + 3 ^ 40 * 4490573 * 2
def baseEnd_4490573 : Nat := 768607454367521448728579

theorem tailTrace_4490573 : CollatzResearch.WordTrace tailWord_4490573 prefixEnd_4490573 768607454367521448728579 := by
  unfold tailWord_4490573
  simp only [CollatzResearch.WordTrace]
  refine ⟨163784652760428424655188373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109189768506952283103458915 163784652760428424655188373)
  ·
    refine ⟨7677405598145082405711955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163784652760428424655188373 7677405598145082405711955)
    ·
      refine ⟨11516108397217623608567933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7677405598145082405711955 11516108397217623608567933)
      ·
        refine ⟨4318540648956608853212975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11516108397217623608567933 4318540648956608853212975)
        ·
          refine ⟨6477810973434913279819463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318540648956608853212975 6477810973434913279819463)
          ·
            refine ⟨9716716460152369919729195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477810973434913279819463 9716716460152369919729195)
            ·
              refine ⟨14575074690228554879593793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9716716460152369919729195 14575074690228554879593793)
              ·
                refine ⟨10931306017671416159695345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14575074690228554879593793 10931306017671416159695345)
                ·
                  refine ⟨8198479513253562119771509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10931306017671416159695345 8198479513253562119771509)
                  ·
                    refine ⟨768607454367521448728579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8198479513253562119771509 768607454367521448728579)
                    ·
                      rfl

theorem cell23_4490573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4490573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490573 prefixEnd_4490573 := by exact prefixLift 4490573
  have htrace : WordTrace (prefixWord ++ tailWord_4490573) baseStart_4490573 baseEnd_4490573 := by
    simpa [prefixWord, tailWord_4490573, baseEnd_4490573] using wordTrace_append hprefix tailTrace_4490573
  have hstable : (prefixWord ++ tailWord_4490573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490573).length < 2 ^ (prefixWord ++ tailWord_4490573).sum := by decide
  have hdescent : baseEnd_4490573 < baseStart_4490573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490579 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3]
def baseStart_4490579 : Nat := 118140960795 + 4490579 * 2 ^ 59
def prefixEnd_4490579 : Nat := 4983230072969 + 3 ^ 40 * 4490579 * 2
def baseEnd_4490579 : Nat := 2305825443986491322710709

theorem tailTrace_4490579 : CollatzResearch.WordTrace tailWord_4490579 prefixEnd_4490579 2305825443986491322710709 := by
  unfold tailWord_4490579
  simp only [CollatzResearch.WordTrace]
  refine ⟨163784871598406687679906791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109189914398937791786604527 163784871598406687679906791)
  ·
    refine ⟨245677307397610031519860187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163784871598406687679906791 245677307397610031519860187)
    ·
      refine ⟨368515961096415047279790281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245677307397610031519860187 368515961096415047279790281)
      ·
        refine ⟨276386970822311285459842711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368515961096415047279790281 276386970822311285459842711)
        ·
          refine ⟨414580456233466928189764067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276386970822311285459842711 414580456233466928189764067)
          ·
            refine ⟨621870684350200392284646101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414580456233466928189764067 621870684350200392284646101)
            ·
              refine ⟨14575094164457821694171393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 621870684350200392284646101 14575094164457821694171393)
              ·
                refine ⟨10931320623343366270628545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14575094164457821694171393 10931320623343366270628545)
                ·
                  refine ⟨8198490467507524702971409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10931320623343366270628545 8198490467507524702971409)
                  ·
                    refine ⟨6148867850630643527228557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8198490467507524702971409 6148867850630643527228557)
                    ·
                      refine ⟨2305825443986491322710709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148867850630643527228557 2305825443986491322710709)
                      ·
                        rfl

theorem cell23_4490579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_4490579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490579 prefixEnd_4490579 := by exact prefixLift 4490579
  have htrace : WordTrace (prefixWord ++ tailWord_4490579) baseStart_4490579 baseEnd_4490579 := by
    simpa [prefixWord, tailWord_4490579, baseEnd_4490579] using wordTrace_append hprefix tailTrace_4490579
  have hstable : (prefixWord ++ tailWord_4490579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490579).length < 2 ^ (prefixWord ++ tailWord_4490579).sum := by decide
  have hdescent : baseEnd_4490579 < baseStart_4490579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490586 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_4490586 : Nat := 118140960795 + 4490586 * 2 ^ 59
def prefixEnd_4490586 : Nat := 4983230072969 + 3 ^ 40 * 4490586 * 2
def baseEnd_4490586 : Nat := 768609679450357598441059

theorem tailTrace_4490586 : CollatzResearch.WordTrace tailWord_4490586 prefixEnd_4490586 768609679450357598441059 := by
  unfold tailWord_4490586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40946281727345331968852903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109190084606254218583607741 40946281727345331968852903)
  ·
    refine ⟨61419422591017997953279355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40946281727345331968852903 61419422591017997953279355)
    ·
      refine ⟨92129133886526996929919033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61419422591017997953279355 92129133886526996929919033)
      ·
        refine ⟨69096850414895247697439275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92129133886526996929919033 69096850414895247697439275)
        ·
          refine ⟨103645275622342871546158913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69096850414895247697439275 103645275622342871546158913)
          ·
            refine ⟨77733956716757153659619185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103645275622342871546158913 77733956716757153659619185)
            ·
              refine ⟨58300467537567865244714389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77733956716757153659619185 58300467537567865244714389)
              ·
                refine ⟨2732834415823493683345987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58300467537567865244714389 2732834415823493683345987)
                ·
                  refine ⟨4099251623735240525018981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732834415823493683345987 4099251623735240525018981)
                  ·
                    refine ⟨768609679450357598441059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099251623735240525018981 768609679450357598441059)
                    ·
                      rfl

theorem cell23_4490586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_4490586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490586 prefixEnd_4490586 := by exact prefixLift 4490586
  have htrace : WordTrace (prefixWord ++ tailWord_4490586) baseStart_4490586 baseEnd_4490586 := by
    simpa [prefixWord, tailWord_4490586, baseEnd_4490586] using wordTrace_append hprefix tailTrace_4490586
  have hstable : (prefixWord ++ tailWord_4490586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490586).length < 2 ^ (prefixWord ++ tailWord_4490586).sum := by decide
  have hdescent : baseEnd_4490586 < baseStart_4490586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490613 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4490613 : Nat := 118140960795 + 4490613 * 2 ^ 59
def prefixEnd_4490613 : Nat := 4983230072969 + 3 ^ 40 * 4490613 * 2
def baseEnd_4490613 : Nat := 2305842902328744189685553

theorem tailTrace_4490613 : CollatzResearch.WordTrace tailWord_4490613 prefixEnd_4490613 2305842902328744189685553 := by
  unfold tailWord_4490613
  simp only [CollatzResearch.WordTrace]
  refine ⟨163786111680283511486644493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109190741120189007657762995 163786111680283511486644493)
  ·
    refine ⟨61419791880106316807491685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163786111680283511486644493 61419791880106316807491685)
    ·
      refine ⟨11516210977519934401404691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61419791880106316807491685 11516210977519934401404691)
      ·
        refine ⟨17274316466279901602107037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11516210977519934401404691 17274316466279901602107037)
        ·
          refine ⟨6477868674854963100790139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17274316466279901602107037 6477868674854963100790139)
          ·
            refine ⟨9716803012282444651185209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477868674854963100790139 9716803012282444651185209)
            ·
              refine ⟨7287602259211833488388907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716803012282444651185209 7287602259211833488388907)
              ·
                refine ⟨10931403388817750232583361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287602259211833488388907 10931403388817750232583361)
                ·
                  refine ⟨8198552541613312674437521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10931403388817750232583361 8198552541613312674437521)
                  ·
                    refine ⟨6148914406209984505828141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8198552541613312674437521 6148914406209984505828141)
                    ·
                      refine ⟨2305842902328744189685553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6148914406209984505828141 2305842902328744189685553)
                      ·
                        rfl

theorem cell23_4490613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4490613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490613 prefixEnd_4490613 := by exact prefixLift 4490613
  have htrace : WordTrace (prefixWord ++ tailWord_4490613) baseStart_4490613 baseEnd_4490613 := by
    simpa [prefixWord, tailWord_4490613, baseEnd_4490613] using wordTrace_append hprefix tailTrace_4490613
  have hstable : (prefixWord ++ tailWord_4490613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490613).length < 2 ^ (prefixWord ++ tailWord_4490613).sum := by decide
  have hdescent : baseEnd_4490613 < baseStart_4490613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490629 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_4490629 : Nat := 118140960795 + 4490629 * 2 ^ 59
def prefixEnd_4490629 : Nat := 4983230072969 + 3 ^ 40 * 4490629 * 2
def baseEnd_4490629 : Nat := 768617039339738709028493

theorem tailTrace_4490629 : CollatzResearch.WordTrace tailWord_4490629 prefixEnd_4490629 768617039339738709028493 := by
  unfold tailWord_4490629
  simp only [CollatzResearch.WordTrace]
  refine ⟨163786695248225546219226941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109191130165483697479484627 163786695248225546219226941)
  ·
    refine ⟨61420010718084579832210103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163786695248225546219226941 61420010718084579832210103)
    ·
      refine ⟨92130016077126869748315155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61420010718084579832210103 92130016077126869748315155)
      ·
        refine ⟨138195024115690304622472733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92130016077126869748315155 138195024115690304622472733)
        ·
          refine ⟨51823134043383864233427275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138195024115690304622472733 51823134043383864233427275)
          ·
            refine ⟨77734701065075796350140913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51823134043383864233427275 77734701065075796350140913)
            ·
              refine ⟨58301025798806847262605685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77734701065075796350140913 58301025798806847262605685)
              ·
                refine ⟨5465721168638141930869283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58301025798806847262605685 5465721168638141930869283)
                ·
                  refine ⟨8198581752957212896303925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465721168638141930869283 8198581752957212896303925)
                  ·
                    refine ⟨768617039339738709028493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8198581752957212896303925 768617039339738709028493)
                    ·
                      rfl

theorem cell23_4490629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_4490629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490629 prefixEnd_4490629 := by exact prefixLift 4490629
  have htrace : WordTrace (prefixWord ++ tailWord_4490629) baseStart_4490629 baseEnd_4490629 := by
    simpa [prefixWord, tailWord_4490629, baseEnd_4490629] using wordTrace_append hprefix tailTrace_4490629
  have hstable : (prefixWord ++ tailWord_4490629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490629).length < 2 ^ (prefixWord ++ tailWord_4490629).sum := by decide
  have hdescent : baseEnd_4490629 < baseStart_4490629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490636 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_4490636 : Nat := 118140960795 + 4490636 * 2 ^ 59
def prefixEnd_4490636 : Nat := 4983230072969 + 3 ^ 40 * 4490636 * 2
def baseEnd_4490636 : Nat := 2305854712383797599697947

theorem tailTrace_4490636 : CollatzResearch.WordTrace tailWord_4490636 prefixEnd_4490636 2305854712383797599697947 := by
  unfold tailWord_4490636
  simp only [CollatzResearch.WordTrace]
  refine ⟨81893475279600093207365881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109191300372800124276487841 81893475279600093207365881)
  ·
    refine ⟨61420106459700069905524411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81893475279600093207365881 61420106459700069905524411)
    ·
      refine ⟨92130159689550104858286617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61420106459700069905524411 92130159689550104858286617)
      ·
        refine ⟨69097619767162578643714963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92130159689550104858286617 69097619767162578643714963)
        ·
          refine ⟨103646429650743867965572445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69097619767162578643714963 103646429650743867965572445)
          ·
            refine ⟨38867411119028950487089667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103646429650743867965572445 38867411119028950487089667)
            ·
              refine ⟨58301116678543425730634501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38867411119028950487089667 58301116678543425730634501)
              ·
                refine ⟨10931459377226892324493969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58301116678543425730634501 10931459377226892324493969)
                ·
                  refine ⟨8198594532920169243370477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10931459377226892324493969 8198594532920169243370477)
                  ·
                    refine ⟨3074472949845063466263929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8198594532920169243370477 3074472949845063466263929)
                    ·
                      refine ⟨2305854712383797599697947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074472949845063466263929 2305854712383797599697947)
                      ·
                        rfl

theorem cell23_4490636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_4490636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490636 prefixEnd_4490636 := by exact prefixLift 4490636
  have htrace : WordTrace (prefixWord ++ tailWord_4490636) baseStart_4490636 baseEnd_4490636 := by
    simpa [prefixWord, tailWord_4490636, baseEnd_4490636] using wordTrace_append hprefix tailTrace_4490636
  have hstable : (prefixWord ++ tailWord_4490636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490636).length < 2 ^ (prefixWord ++ tailWord_4490636).sum := by decide
  have hdescent : baseEnd_4490636 < baseStart_4490636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490649 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_4490649 : Nat := 118140960795 + 4490649 * 2 ^ 59
def prefixEnd_4490649 : Nat := 4983230072969 + 3 ^ 40 * 4490649 * 2
def baseEnd_4490649 : Nat := 2305861387632306048835387

theorem tailTrace_4490649 : CollatzResearch.WordTrace tailWord_4490649 prefixEnd_4490649 2305861387632306048835387 := by
  unfold tailWord_4490649
  simp only [CollatzResearch.WordTrace]
  refine ⟨163787424708153089634955001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109191616472102059756636667 163787424708153089634955001)
  ·
    refine ⟨122840568531114817226216251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163787424708153089634955001 122840568531114817226216251)
    ·
      refine ⟨184260852796672225839324377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122840568531114817226216251 184260852796672225839324377)
      ·
        refine ⟨138195639597504169379493283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184260852796672225839324377 138195639597504169379493283)
        ·
          refine ⟨207293459396256254069239925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138195639597504169379493283 207293459396256254069239925)
          ·
            refine ⟨19433761818399023818991243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207293459396256254069239925 19433761818399023818991243)
            ·
              refine ⟨29150642727598535728486865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19433761818399023818991243 29150642727598535728486865)
              ·
                refine ⟨21862982045698901796365149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29150642727598535728486865 21862982045698901796365149)
                ·
                  refine ⟨8198618267137088173636931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21862982045698901796365149 8198618267137088173636931)
                  ·
                    refine ⟨12297927400705632260455397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8198618267137088173636931 12297927400705632260455397)
                    ·
                      refine ⟨2305861387632306048835387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12297927400705632260455397 2305861387632306048835387)
                      ·
                        rfl

theorem cell23_4490649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_4490649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490649 prefixEnd_4490649 := by exact prefixLift 4490649
  have htrace : WordTrace (prefixWord ++ tailWord_4490649) baseStart_4490649 baseEnd_4490649 := by
    simpa [prefixWord, tailWord_4490649, baseEnd_4490649] using wordTrace_append hprefix tailTrace_4490649
  have hstable : (prefixWord ++ tailWord_4490649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490649).length < 2 ^ (prefixWord ++ tailWord_4490649).sum := by decide
  have hdescent : baseEnd_4490649 < baseStart_4490649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490659 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 6]
def baseStart_4490659 : Nat := 118140960795 + 4490659 * 2 ^ 59
def prefixEnd_4490659 : Nat := 4983230072969 + 3 ^ 40 * 4490659 * 2
def baseEnd_4490659 : Nat := 768622174146283669903447

theorem tailTrace_4490659 : CollatzResearch.WordTrace tailWord_4490659 prefixEnd_4490659 768622174146283669903447 := by
  unfold tailWord_4490659
  simp only [CollatzResearch.WordTrace]
  refine ⟨163787789438116861342819031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109191859625411240895212687 163787789438116861342819031)
  ·
    refine ⟨245681684157175292014228547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163787789438116861342819031 245681684157175292014228547)
    ·
      refine ⟨368522526235762938021342821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245681684157175292014228547 368522526235762938021342821)
      ·
        refine ⟨69097973669205550879001779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368522526235762938021342821 69097973669205550879001779)
        ·
          refine ⟨103646960503808326318502669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69097973669205550879001779 103646960503808326318502669)
          ·
            refine ⟨38867610188928122369438501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103646960503808326318502669 38867610188928122369438501)
            ·
              refine ⟨7287676910424022944269719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38867610188928122369438501 7287676910424022944269719)
              ·
                refine ⟨10931515365636034416404579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287676910424022944269719 10931515365636034416404579)
                ·
                  refine ⟨16397273048454051624606869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10931515365636034416404579 16397273048454051624606869)
                  ·
                    refine ⟨768622174146283669903447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16397273048454051624606869 768622174146283669903447)
                    ·
                      rfl

theorem cell23_4490659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].length) (baseStart_4490659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490659 prefixEnd_4490659 := by exact prefixLift 4490659
  have htrace : WordTrace (prefixWord ++ tailWord_4490659) baseStart_4490659 baseEnd_4490659 := by
    simpa [prefixWord, tailWord_4490659, baseEnd_4490659] using wordTrace_append hprefix tailTrace_4490659
  have hstable : (prefixWord ++ tailWord_4490659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490659).length < 2 ^ (prefixWord ++ tailWord_4490659).sum := by decide
  have hdescent : baseEnd_4490659 < baseStart_4490659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490679 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_4490679 : Nat := 118140960795 + 4490679 * 2 ^ 59
def prefixEnd_4490679 : Nat := 4983230072969 + 3 ^ 40 * 4490679 * 2
def baseEnd_4490679 : Nat := 2305876792051940931460249

theorem tailTrace_4490679 : CollatzResearch.WordTrace tailWord_4490679 prefixEnd_4490679 2305876792051940931460249 := by
  unfold tailWord_4490679
  simp only [CollatzResearch.WordTrace]
  refine ⟨163788518898044404758547091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109192345932029603172364727 163788518898044404758547091)
  ·
    refine ⟨245682778347066607137820637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163788518898044404758547091 245682778347066607137820637)
    ·
      refine ⟨92131041880149977676682739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245682778347066607137820637 92131041880149977676682739)
      ·
        refine ⟨138196562820224966515024109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92131041880149977676682739 138196562820224966515024109)
        ·
          refine ⟨51823711057584362443134041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138196562820224966515024109 51823711057584362443134041)
          ·
            refine ⟨38867783293188271832350531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51823711057584362443134041 38867783293188271832350531)
            ·
              refine ⟨58301674939782407748525797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38867783293188271832350531 58301674939782407748525797)
              ·
                refine ⟨10931564051209201452848587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58301674939782407748525797 10931564051209201452848587)
                ·
                  refine ⟨16397346076813802179272881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10931564051209201452848587 16397346076813802179272881)
                  ·
                    refine ⟨12298009557610351634454661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16397346076813802179272881 12298009557610351634454661)
                    ·
                      refine ⟨2305876792051940931460249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12298009557610351634454661 2305876792051940931460249)
                      ·
                        rfl

theorem cell23_4490679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_4490679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490679 prefixEnd_4490679 := by exact prefixLift 4490679
  have htrace : WordTrace (prefixWord ++ tailWord_4490679) baseStart_4490679 baseEnd_4490679 := by
    simpa [prefixWord, tailWord_4490679, baseEnd_4490679] using wordTrace_append hprefix tailTrace_4490679
  have hstable : (prefixWord ++ tailWord_4490679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490679).length < 2 ^ (prefixWord ++ tailWord_4490679).sum := by decide
  have hdescent : baseEnd_4490679 < baseStart_4490679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490699 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3]
def baseStart_4490699 : Nat := 118140960795 + 4490699 * 2 ^ 59
def prefixEnd_4490699 : Nat := 4983230072969 + 3 ^ 40 * 4490699 * 2
def baseEnd_4490699 : Nat := 2305887061665030853210157

theorem tailTrace_4490699 : CollatzResearch.WordTrace tailWord_4490699 prefixEnd_4490699 2305887061665030853210157 := by
  unfold tailWord_4490699
  simp only [CollatzResearch.WordTrace]
  refine ⟨163789248357971948174275151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109192832238647965449516767 163789248357971948174275151)
  ·
    refine ⟨245683872536957922261412727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163789248357971948174275151 245683872536957922261412727)
    ·
      refine ⟨368525808805436883392119091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245683872536957922261412727 368525808805436883392119091)
      ·
        refine ⟨552788713208155325088178637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368525808805436883392119091 552788713208155325088178637)
        ·
          refine ⟨207295767453058246908066989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552788713208155325088178637 207295767453058246908066989)
          ·
            refine ⟨77735912794896842590525121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207295767453058246908066989 77735912794896842590525121)
            ·
              refine ⟨58301934596172631942893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77735912794896842590525121 58301934596172631942893841)
              ·
                refine ⟨43726450947129473957170381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58301934596172631942893841 43726450947129473957170381)
                ·
                  refine ⟨16397419105173552733938893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43726450947129473957170381 16397419105173552733938893)
                  ·
                    refine ⟨6149032164440082275227085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16397419105173552733938893 6149032164440082275227085)
                    ·
                      refine ⟨2305887061665030853210157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149032164440082275227085 2305887061665030853210157)
                      ·
                        rfl

theorem cell23_4490699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].length) (baseStart_4490699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490699 prefixEnd_4490699 := by exact prefixLift 4490699
  have htrace : WordTrace (prefixWord ++ tailWord_4490699) baseStart_4490699 baseEnd_4490699 := by
    simpa [prefixWord, tailWord_4490699, baseEnd_4490699] using wordTrace_append hprefix tailTrace_4490699
  have hstable : (prefixWord ++ tailWord_4490699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490699).length < 2 ^ (prefixWord ++ tailWord_4490699).sum := by decide
  have hdescent : baseEnd_4490699 < baseStart_4490699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490700 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4490700 : Nat := 118140960795 + 4490700 * 2 ^ 59
def prefixEnd_4490700 : Nat := 4983230072969 + 3 ^ 40 * 4490700 * 2
def baseEnd_4490700 : Nat := 2305887575145685349297653

theorem tailTrace_4490700 : CollatzResearch.WordTrace tailWord_4490700 prefixEnd_4490700 2305887575145685349297653 := by
  unfold tailWord_4490700
  simp only [CollatzResearch.WordTrace]
  refine ⟨81894642415484162672530777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109192856553978883563374369 81894642415484162672530777)
  ·
    refine ⟨61420981811613122004398083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81894642415484162672530777 61420981811613122004398083)
    ·
      refine ⟨92131472717419683006597125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61420981811613122004398083 92131472717419683006597125)
      ·
        refine ⟨17274651134516190563736961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92131472717419683006597125 17274651134516190563736961)
        ·
          refine ⟨12955988350887142922802721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17274651134516190563736961 12955988350887142922802721)
          ·
            refine ⟨9716991263165357192102041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12955988350887142922802721 9716991263165357192102041)
            ·
              refine ⟨7287743447374017894076531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716991263165357192102041 7287743447374017894076531)
              ·
                refine ⟨10931615171061026841114797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287743447374017894076531 10931615171061026841114797)
                ·
                  refine ⟨4099355689147885065418049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10931615171061026841114797 4099355689147885065418049)
                  ·
                    refine ⟨3074516766860913799063537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099355689147885065418049 3074516766860913799063537)
                    ·
                      refine ⟨2305887575145685349297653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074516766860913799063537 2305887575145685349297653)
                      ·
                        rfl

theorem cell23_4490700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4490700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490700 prefixEnd_4490700 := by exact prefixLift 4490700
  have htrace : WordTrace (prefixWord ++ tailWord_4490700) baseStart_4490700 baseEnd_4490700 := by
    simpa [prefixWord, tailWord_4490700, baseEnd_4490700] using wordTrace_append hprefix tailTrace_4490700
  have hstable : (prefixWord ++ tailWord_4490700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490700).length < 2 ^ (prefixWord ++ tailWord_4490700).sum := by decide
  have hdescent : baseEnd_4490700 < baseStart_4490700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490769 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_4490769 : Nat := 118140960795 + 4490769 * 2 ^ 59
def prefixEnd_4490769 : Nat := 4983230072969 + 3 ^ 40 * 4490769 * 2
def baseEnd_4490769 : Nat := 2305923005310845579334835

theorem tailTrace_4490769 : CollatzResearch.WordTrace tailWord_4490769 prefixEnd_4490769 2305923005310845579334835 := by
  unfold tailWord_4490769
  simp only [CollatzResearch.WordTrace]
  refine ⟨163791801467718350129323361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109194534311812233419548907 163791801467718350129323361)
  ·
    refine ⟨122843851100788762596992521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163791801467718350129323361 122843851100788762596992521)
    ·
      refine ⟨92132888325591571947744391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122843851100788762596992521 92132888325591571947744391)
      ·
        refine ⟨138199332488387357921616587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92132888325591571947744391 138199332488387357921616587)
        ·
          refine ⟨207298998732581036882424881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138199332488387357921616587 207298998732581036882424881)
          ·
            refine ⟨155474249049435777661818661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207298998732581036882424881 155474249049435777661818661)
            ·
              refine ⟨29151421696769208311590999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155474249049435777661818661 29151421696769208311590999)
              ·
                refine ⟨43727132545153812467386499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29151421696769208311590999 43727132545153812467386499)
                ·
                  refine ⟨65590698817730718701079749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43727132545153812467386499 65590698817730718701079749)
                  ·
                    refine ⟨12298256028324509756452453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65590698817730718701079749 12298256028324509756452453)
                    ·
                      refine ⟨2305923005310845579334835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12298256028324509756452453 2305923005310845579334835)
                      ·
                        rfl

theorem cell23_4490769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_4490769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490769 prefixEnd_4490769 := by exact prefixLift 4490769
  have htrace : WordTrace (prefixWord ++ tailWord_4490769) baseStart_4490769 baseEnd_4490769 := by
    simpa [prefixWord, tailWord_4490769, baseEnd_4490769] using wordTrace_append hprefix tailTrace_4490769
  have hstable : (prefixWord ++ tailWord_4490769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490769).length < 2 ^ (prefixWord ++ tailWord_4490769).sum := by decide
  have hdescent : baseEnd_4490769 < baseStart_4490769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490823 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_4490823 : Nat := 118140960795 + 4490823 * 2 ^ 59
def prefixEnd_4490823 : Nat := 4983230072969 + 3 ^ 40 * 4490823 * 2
def baseEnd_4490823 : Nat := 2305950733266188368059587

theorem tailTrace_4490823 : CollatzResearch.WordTrace tailWord_4490823 prefixEnd_4490823 2305950733266188368059587 := by
  unfold tailWord_4490823
  simp only [CollatzResearch.WordTrace]
  refine ⟨163793771009522717351789123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109195847339681811567859415 163793771009522717351789123)
  ·
    refine ⟨245690656514284076027683685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163793771009522717351789123 245690656514284076027683685)
    ·
      refine ⟨46066998096428264255190691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245690656514284076027683685 46066998096428264255190691)
      ·
        refine ⟨69100497144642396382786037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46066998096428264255190691 69100497144642396382786037)
        ·
          refine ⟨6478171607310224660886191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69100497144642396382786037 6478171607310224660886191)
          ·
            refine ⟨9717257410965336991329287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478171607310224660886191 9717257410965336991329287)
            ·
              refine ⟨14575886116448005486993931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9717257410965336991329287 14575886116448005486993931)
              ·
                refine ⟨21863829174672008230490897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14575886116448005486993931 21863829174672008230490897)
                ·
                  refine ⟨16397871881004006172868173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21863829174672008230490897 16397871881004006172868173)
                  ·
                    refine ⟨6149201955376502314825565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16397871881004006172868173 6149201955376502314825565)
                    ·
                      refine ⟨2305950733266188368059587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149201955376502314825565 2305950733266188368059587)
                      ·
                        rfl

theorem cell23_4490823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_4490823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490823 prefixEnd_4490823 := by exact prefixLift 4490823
  have htrace : WordTrace (prefixWord ++ tailWord_4490823) baseStart_4490823 baseEnd_4490823 := by
    simpa [prefixWord, tailWord_4490823, baseEnd_4490823] using wordTrace_append hprefix tailTrace_4490823
  have hstable : (prefixWord ++ tailWord_4490823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490823).length < 2 ^ (prefixWord ++ tailWord_4490823).sum := by decide
  have hdescent : baseEnd_4490823 < baseStart_4490823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490873 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_4490873 : Nat := 118140960795 + 4490873 * 2 ^ 59
def prefixEnd_4490873 : Nat := 4983230072969 + 3 ^ 40 * 4490873 * 2
def baseEnd_4490873 : Nat := 768658802432971057478119

theorem tailTrace_4490873 : CollatzResearch.WordTrace tailWord_4490873 prefixEnd_4490873 768658802432971057478119 := by
  unfold tailWord_4490873
  simp only [CollatzResearch.WordTrace]
  refine ⟨163795594659341575891109273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109197063106227717260739515 163795594659341575891109273)
  ·
    refine ⟨122846695994506181918331955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163795594659341575891109273 122846695994506181918331955)
    ·
      refine ⟨184270043991759272877497933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122846695994506181918331955 184270043991759272877497933)
      ·
        refine ⟨69101266496909727329061725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184270043991759272877497933 69101266496909727329061725)
        ·
          refine ⟨25912974936341147748398147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69101266496909727329061725 25912974936341147748398147)
          ·
            refine ⟨38869462404511721622597221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25912974936341147748398147 38869462404511721622597221)
            ·
              refine ⟨7288024200845947804236979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38869462404511721622597221 7288024200845947804236979)
              ·
                refine ⟨10932036301268921706355469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288024200845947804236979 10932036301268921706355469)
                ·
                  refine ⟨4099513612975845639883301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10932036301268921706355469 4099513612975845639883301)
                  ·
                    refine ⟨768658802432971057478119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099513612975845639883301 768658802432971057478119)
                    ·
                      rfl

theorem cell23_4490873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_4490873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490873 prefixEnd_4490873 := by exact prefixLift 4490873
  have htrace : WordTrace (prefixWord ++ tailWord_4490873) baseStart_4490873 baseEnd_4490873 := by
    simpa [prefixWord, tailWord_4490873, baseEnd_4490873] using wordTrace_append hprefix tailTrace_4490873
  have hstable : (prefixWord ++ tailWord_4490873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490873).length < 2 ^ (prefixWord ++ tailWord_4490873).sum := by decide
  have hdescent : baseEnd_4490873 < baseStart_4490873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490879 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_4490879 : Nat := 118140960795 + 4490879 * 2 ^ 59
def prefixEnd_4490879 : Nat := 4983230072969 + 3 ^ 40 * 4490879 * 2
def baseEnd_4490879 : Nat := 2305979488182840148959329

theorem tailTrace_4490879 : CollatzResearch.WordTrace tailWord_4490879 prefixEnd_4490879 2305979488182840148959329 := by
  unfold tailWord_4490879
  simp only [CollatzResearch.WordTrace]
  refine ⟨163795813497319838915827691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109197208998213225943885127 163795813497319838915827691)
  ·
    refine ⟨245693720245979758373741537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163795813497319838915827691 245693720245979758373741537)
    ·
      refine ⟨184270290184484818780306153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245693720245979758373741537 184270290184484818780306153)
      ·
        refine ⟨138202717638363614085229615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184270290184484818780306153 138202717638363614085229615)
        ·
          refine ⟨207304076457545421127844423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138202717638363614085229615 207304076457545421127844423)
          ·
            refine ⟨310956114686318131691766635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207304076457545421127844423 310956114686318131691766635)
            ·
              refine ⟨466434172029477197537649953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310956114686318131691766635 466434172029477197537649953)
              ·
                refine ⟨349825629022107898153237465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466434172029477197537649953 349825629022107898153237465)
                ·
                  refine ⟨262369221766580923614928099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349825629022107898153237465 262369221766580923614928099)
                  ·
                    refine ⟨393553832649871385422392149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262369221766580923614928099 393553832649871385422392149)
                    ·
                      refine ⟨2305979488182840148959329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 393553832649871385422392149 2305979488182840148959329)
                      ·
                        rfl

theorem cell23_4490879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_4490879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490879 prefixEnd_4490879 := by exact prefixLift 4490879
  have htrace : WordTrace (prefixWord ++ tailWord_4490879) baseStart_4490879 baseEnd_4490879 := by
    simpa [prefixWord, tailWord_4490879, baseEnd_4490879] using wordTrace_append hprefix tailTrace_4490879
  have hstable : (prefixWord ++ tailWord_4490879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490879).length < 2 ^ (prefixWord ++ tailWord_4490879).sum := by decide
  have hdescent : baseEnd_4490879 < baseStart_4490879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490930 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_4490930 : Nat := 118140960795 + 4490930 * 2 ^ 59
def prefixEnd_4490930 : Nat := 4983230072969 + 3 ^ 40 * 4490930 * 2
def baseEnd_4490930 : Nat := 2306005675696219449421595

theorem tailTrace_4490930 : CollatzResearch.WordTrace tailWord_4490930 prefixEnd_4490930 2306005675696219449421595 := by
  unfold tailWord_4490930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40949418405033768656483561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109198449080090049750622829 40949418405033768656483561)
  ·
    refine ⟨30712063803775326492362671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40949418405033768656483561 30712063803775326492362671)
    ·
      refine ⟨46068095705662989738544007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30712063803775326492362671 46068095705662989738544007)
      ·
        refine ⟨69102143558494484607816011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46068095705662989738544007 69102143558494484607816011)
        ·
          refine ⟨103653215337741726911724017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69102143558494484607816011 103653215337741726911724017)
          ·
            refine ⟨77739911503306295183793013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103653215337741726911724017 77739911503306295183793013)
            ·
              refine ⟨7288116703434965173480595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77739911503306295183793013 7288116703434965173480595)
              ·
                refine ⟨10932175055152447760220893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288116703434965173480595 10932175055152447760220893)
                ·
                  refine ⟨4099565645682167910082835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10932175055152447760220893 4099565645682167910082835)
                  ·
                    refine ⟨6149348468523251865124253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4099565645682167910082835 6149348468523251865124253)
                    ·
                      refine ⟨2306005675696219449421595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149348468523251865124253 2306005675696219449421595)
                      ·
                        rfl

theorem cell23_4490930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_4490930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490930 prefixEnd_4490930 := by exact prefixLift 4490930
  have htrace : WordTrace (prefixWord ++ tailWord_4490930) baseStart_4490930 baseEnd_4490930 := by
    simpa [prefixWord, tailWord_4490930, baseEnd_4490930] using wordTrace_append hprefix tailTrace_4490930
  have hstable : (prefixWord ++ tailWord_4490930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490930).length < 2 ^ (prefixWord ++ tailWord_4490930).sum := by decide
  have hdescent : baseEnd_4490930 < baseStart_4490930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490980 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_4490980 : Nat := 118140960795 + 4490980 * 2 ^ 59
def prefixEnd_4490980 : Nat := 4983230072969 + 3 ^ 40 * 4490980 * 2
def baseEnd_4490980 : Nat := 768677116576314751265455

theorem tailTrace_4490980 : CollatzResearch.WordTrace tailWord_4490980 prefixEnd_4490980 768677116576314751265455 := by
  unfold tailWord_4490980
  simp only [CollatzResearch.WordTrace]
  refine ⟨81899748634976966582627197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109199664846635955443502929 81899748634976966582627197)
  ·
    refine ⟨30712405738116362468485199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81899748634976966582627197 30712405738116362468485199)
    ·
      refine ⟨46068608607174543702727799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30712405738116362468485199 46068608607174543702727799)
      ·
        refine ⟨69102912910761815554091699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46068608607174543702727799 69102912910761815554091699)
        ·
          refine ⟨103654369366142723331137549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69102912910761815554091699 103654369366142723331137549)
          ·
            refine ⟨38870388512303521249176581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103654369366142723331137549 38870388512303521249176581)
            ·
              refine ⟨7288197846056910234220609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38870388512303521249176581 7288197846056910234220609)
              ·
                refine ⟨5466148384542682675665457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7288197846056910234220609 5466148384542682675665457)
                ·
                  refine ⟨4099611288407012006749093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5466148384542682675665457 4099611288407012006749093)
                  ·
                    refine ⟨768677116576314751265455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099611288407012006749093 768677116576314751265455)
                    ·
                      rfl

theorem cell23_4490980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_4490980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490980 prefixEnd_4490980 := by exact prefixLift 4490980
  have htrace : WordTrace (prefixWord ++ tailWord_4490980) baseStart_4490980 baseEnd_4490980 := by
    simpa [prefixWord, tailWord_4490980, baseEnd_4490980] using wordTrace_append hprefix tailTrace_4490980
  have hstable : (prefixWord ++ tailWord_4490980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490980).length < 2 ^ (prefixWord ++ tailWord_4490980).sum := by decide
  have hdescent : baseEnd_4490980 < baseStart_4490980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4490993 : List Nat := [1, 2, 2, 2, 2, 5, 1, 8]
def baseStart_4490993 : Nat := 118140960795 + 4490993 * 2 ^ 59
def prefixEnd_4490993 : Nat := 4983230072969 + 3 ^ 40 * 4490993 * 2
def baseEnd_4490993 : Nat := 85408815739905655664215

theorem tailTrace_4490993 : CollatzResearch.WordTrace tailWord_4490993 prefixEnd_4490993 85408815739905655664215 := by
  unfold tailWord_4490993
  simp only [CollatzResearch.WordTrace]
  refine ⟨163799971418906836385477633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109199980945937890923651755 163799971418906836385477633)
  ·
    refine ⟨122849978564180127289108225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163799971418906836385477633 122849978564180127289108225)
    ·
      refine ⟨92137483923135095466831169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122849978564180127289108225 92137483923135095466831169)
      ·
        refine ⟨69103112942351321600123377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92137483923135095466831169 69103112942351321600123377)
        ·
          refine ⟨51827334706763491200092533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69103112942351321600123377 51827334706763491200092533)
          ·
            refine ⟨4858812628759077300008675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51827334706763491200092533 4858812628759077300008675)
            ·
              refine ⟨7288218943138615950013013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858812628759077300008675 7288218943138615950013013)
              ·
                refine ⟨85408815739905655664215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7288218943138615950013013 85408815739905655664215)
                ·
                  rfl

theorem cell23_4490993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 8].length) (baseStart_4490993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4490993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4490993 prefixEnd_4490993 := by exact prefixLift 4490993
  have htrace : WordTrace (prefixWord ++ tailWord_4490993) baseStart_4490993 baseEnd_4490993 := by
    simpa [prefixWord, tailWord_4490993, baseEnd_4490993] using wordTrace_append hprefix tailTrace_4490993
  have hstable : (prefixWord ++ tailWord_4490993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4490993).length < 2 ^ (prefixWord ++ tailWord_4490993).sum := by decide
  have hdescent : baseEnd_4490993 < baseStart_4490993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4490993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491010 : List Nat := [3, 4, 1, 1, 1, 1, 5, 7]
def baseStart_4491010 : Nat := 118140960795 + 4491010 * 2 ^ 59
def prefixEnd_4491010 : Nat := 4983230072969 + 3 ^ 40 * 4491010 * 2
def baseEnd_4491010 : Nat := 85409139042539968015601

theorem tailTrace_4491010 : CollatzResearch.WordTrace tailWord_4491010 prefixEnd_4491010 85409139042539968015601 := by
  unfold tailWord_4491010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40950147864961312072211621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109200394306563498859230989 40950147864961312072211621)
  ·
    refine ⟨7678152724680246013539679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40950147864961312072211621 7678152724680246013539679)
    ·
      refine ⟨11517229087020369020309519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7678152724680246013539679 11517229087020369020309519)
      ·
        refine ⟨17275843630530553530464279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11517229087020369020309519 17275843630530553530464279)
        ·
          refine ⟨25913765445795830295696419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17275843630530553530464279 25913765445795830295696419)
          ·
            refine ⟨38870648168693745443544629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25913765445795830295696419 38870648168693745443544629)
            ·
              refine ⟨3644123265815038635332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38870648168693745443544629 3644123265815038635332309)
              ·
                refine ⟨85409139042539968015601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3644123265815038635332309 85409139042539968015601)
                ·
                  rfl

theorem cell23_4491010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_4491010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491010 prefixEnd_4491010 := by exact prefixLift 4491010
  have htrace : WordTrace (prefixWord ++ tailWord_4491010) baseStart_4491010 baseEnd_4491010 := by
    simpa [prefixWord, tailWord_4491010, baseEnd_4491010] using wordTrace_append hprefix tailTrace_4491010
  have hstable : (prefixWord ++ tailWord_4491010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491010).length < 2 ^ (prefixWord ++ tailWord_4491010).sum := by decide
  have hdescent : baseEnd_4491010 < baseStart_4491010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491038 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4491038 : Nat := 118140960795 + 4491038 * 2 ^ 59
def prefixEnd_4491038 : Nat := 4983230072969 + 3 ^ 40 * 4491038 * 2
def baseEnd_4491038 : Nat := 2306061131606905026871099

theorem tailTrace_4491038 : CollatzResearch.WordTrace tailWord_4491038 prefixEnd_4491038 2306061131606905026871099 := by
  unfold tailWord_4491038
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475201587967976133858221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109201075135829206047243845 20475201587967976133858221)
  ·
    refine ⟨7678200595487991050196833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20475201587967976133858221 7678200595487991050196833)
    ·
      refine ⟨5758650446615993287647625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7678200595487991050196833 5758650446615993287647625)
      ·
        refine ⟨4318987834961994965735719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5758650446615993287647625 4318987834961994965735719)
        ·
          refine ⟨6478481752442992448603579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318987834961994965735719 6478481752442992448603579)
          ·
            refine ⟨9717722628664488672905369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478481752442992448603579 9717722628664488672905369)
            ·
              refine ⟨7288291971498366504679027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9717722628664488672905369 7288291971498366504679027)
              ·
                refine ⟨10932437957247549757018541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288291971498366504679027 10932437957247549757018541)
                ·
                  refine ⟨4099664233967831158881953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10932437957247549757018541 4099664233967831158881953)
                  ·
                    refine ⟨3074748175475873369161465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099664233967831158881953 3074748175475873369161465)
                    ·
                      refine ⟨2306061131606905026871099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074748175475873369161465 2306061131606905026871099)
                      ·
                        rfl

theorem cell23_4491038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4491038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491038 prefixEnd_4491038 := by exact prefixLift 4491038
  have htrace : WordTrace (prefixWord ++ tailWord_4491038) baseStart_4491038 baseEnd_4491038 := by
    simpa [prefixWord, tailWord_4491038, baseEnd_4491038] using wordTrace_append hprefix tailTrace_4491038
  have hstable : (prefixWord ++ tailWord_4491038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491038).length < 2 ^ (prefixWord ++ tailWord_4491038).sum := by decide
  have hdescent : baseEnd_4491038 < baseStart_4491038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491054 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4491054 : Nat := 118140960795 + 4491054 * 2 ^ 59
def prefixEnd_4491054 : Nat := 4983230072969 + 3 ^ 40 * 4491054 * 2
def baseEnd_4491054 : Nat := 2306069347297376964271025

theorem tailTrace_4491054 : CollatzResearch.WordTrace tailWord_4491054 prefixEnd_4491054 2306069347297376964271025 := by
  unfold tailWord_4491054
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475274533960730475431027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109201464181123895868965477 20475274533960730475431027)
  ·
    refine ⟨30712911800941095713146541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20475274533960730475431027 30712911800941095713146541)
    ·
      refine ⟨11517341925352910892429953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30712911800941095713146541 11517341925352910892429953)
      ·
        refine ⟨8638006444014683169322465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11517341925352910892429953 8638006444014683169322465)
        ·
          refine ⟨6478504833011012376991849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8638006444014683169322465 6478504833011012376991849)
          ·
            refine ⟨4858878624758259282743887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478504833011012376991849 4858878624758259282743887)
            ·
              refine ⟨7288317937137388924115831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858878624758259282743887 7288317937137388924115831)
              ·
                refine ⟨10932476905706083386173747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288317937137388924115831 10932476905706083386173747)
                ·
                  refine ⟨16398715358559125079260621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10932476905706083386173747 16398715358559125079260621)
                  ·
                    refine ⟨6149518259459671904722733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16398715358559125079260621 6149518259459671904722733)
                    ·
                      refine ⟨2306069347297376964271025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149518259459671904722733 2306069347297376964271025)
                      ·
                        rfl

theorem cell23_4491054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4491054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491054 prefixEnd_4491054 := by exact prefixLift 4491054
  have htrace : WordTrace (prefixWord ++ tailWord_4491054) baseStart_4491054 baseEnd_4491054 := by
    simpa [prefixWord, tailWord_4491054, baseEnd_4491054] using wordTrace_append hprefix tailTrace_4491054
  have hstable : (prefixWord ++ tailWord_4491054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491054).length < 2 ^ (prefixWord ++ tailWord_4491054).sum := by decide
  have hdescent : baseEnd_4491054 < baseStart_4491054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491245 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_4491245 : Nat := 118140960795 + 4491245 * 2 ^ 59
def prefixEnd_4491245 : Nat := 4983230072969 + 3 ^ 40 * 4491245 * 2
def baseEnd_4491245 : Nat := 768722474034128572327549

theorem tailTrace_4491245 : CollatzResearch.WordTrace tailWord_4491245 prefixEnd_4491245 768722474034128572327549 := by
  unfold tailWord_4491245
  simp only [CollatzResearch.WordTrace]
  refine ⟨163809162613993883423651189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109206108409329255615767459 163809162613993883423651189)
  ·
    refine ⟨15357108995061926570967299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163809162613993883423651189 15357108995061926570967299)
    ·
      refine ⟨23035663492592889856450949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15357108995061926570967299 23035663492592889856450949)
      ·
        refine ⟨4319186904861166848084553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23035663492592889856450949 4319186904861166848084553)
        ·
          refine ⟨3239390178645875136063415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4319186904861166848084553 3239390178645875136063415)
          ·
            refine ⟨4859085267968812704095123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239390178645875136063415 4859085267968812704095123)
            ·
              refine ⟨7288627901953219056142685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859085267968812704095123 7288627901953219056142685)
              ·
                refine ⟨2733235463232457146053507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7288627901953219056142685 2733235463232457146053507)
                ·
                  refine ⟨4099853194848685719080261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2733235463232457146053507 4099853194848685719080261)
                  ·
                    refine ⟨768722474034128572327549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4099853194848685719080261 768722474034128572327549)
                    ·
                      rfl

theorem cell23_4491245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_4491245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491245 prefixEnd_4491245 := by exact prefixLift 4491245
  have htrace : WordTrace (prefixWord ++ tailWord_4491245) baseStart_4491245 baseEnd_4491245 := by
    simpa [prefixWord, tailWord_4491245, baseEnd_4491245] using wordTrace_append hprefix tailTrace_4491245
  have hstable : (prefixWord ++ tailWord_4491245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491245).length < 2 ^ (prefixWord ++ tailWord_4491245).sum := by decide
  have hdescent : baseEnd_4491245 < baseStart_4491245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491257 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4491257 : Nat := 118140960795 + 4491257 * 2 ^ 59
def prefixEnd_4491257 : Nat := 4983230072969 + 3 ^ 40 * 4491257 * 2
def baseEnd_4491257 : Nat := 2306173583870239670032591

theorem tailTrace_4491257 : CollatzResearch.WordTrace tailWord_4491257 prefixEnd_4491257 2306173583870239670032591 := by
  unfold tailWord_4491257
  simp only [CollatzResearch.WordTrace]
  refine ⟨163809600289950409473088025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109206400193300272982058683 163809600289950409473088025)
  ·
    refine ⟨122857200217462807104816019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163809600289950409473088025 122857200217462807104816019)
    ·
      refine ⟨184285800326194210657224029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122857200217462807104816019 184285800326194210657224029)
      ·
        refine ⟨69107175122322828996459011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184285800326194210657224029 69107175122322828996459011)
        ·
          refine ⟨103660762683484243494688517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69107175122322828996459011 103660762683484243494688517)
          ·
            refine ⟨19436393003153295655254097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103660762683484243494688517 19436393003153295655254097)
            ·
              refine ⟨14577294752364971741440573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19436393003153295655254097 14577294752364971741440573)
              ·
                refine ⟨5466485532136864403040215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14577294752364971741440573 5466485532136864403040215)
                ·
                  refine ⟨8199728298205296604560323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5466485532136864403040215 8199728298205296604560323)
                  ·
                    refine ⟨12299592447307944906840485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8199728298205296604560323 12299592447307944906840485)
                    ·
                      refine ⟨2306173583870239670032591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12299592447307944906840485 2306173583870239670032591)
                      ·
                        rfl

theorem cell23_4491257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4491257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491257 prefixEnd_4491257 := by exact prefixLift 4491257
  have htrace : WordTrace (prefixWord ++ tailWord_4491257) baseStart_4491257 baseEnd_4491257 := by
    simpa [prefixWord, tailWord_4491257, baseEnd_4491257] using wordTrace_append hprefix tailTrace_4491257
  have hstable : (prefixWord ++ tailWord_4491257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491257).length < 2 ^ (prefixWord ++ tailWord_4491257).sum := by decide
  have hdescent : baseEnd_4491257 < baseStart_4491257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491268 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4491268 : Nat := 118140960795 + 4491268 * 2 ^ 59
def prefixEnd_4491268 : Nat := 4983230072969 + 3 ^ 40 * 4491268 * 2
def baseEnd_4491268 : Nat := 2306179232157439126995041

theorem tailTrace_4491268 : CollatzResearch.WordTrace tailWord_4491268 prefixEnd_4491268 2306179232157439126995041 := by
  unfold tailWord_4491268
  simp only [CollatzResearch.WordTrace]
  refine ⟨81905000746455279175869229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109206667661940372234492305 81905000746455279175869229)
  ·
    refine ⟨30714375279920729690950961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81905000746455279175869229 30714375279920729690950961)
    ·
      refine ⟨23035781459940547268213221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30714375279920729690950961 23035781459940547268213221)
      ·
        refine ⟨4319209023738852612789979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23035781459940547268213221 4319209023738852612789979)
        ·
          refine ⟨6478813535608278919184969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319209023738852612789979 6478813535608278919184969)
          ·
            refine ⟨4859110151706209189388727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478813535608278919184969 4859110151706209189388727)
            ·
              refine ⟨7288665227559313784083091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859110151706209189388727 7288665227559313784083091)
              ·
                refine ⟨10932997841338970676124637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288665227559313784083091 10932997841338970676124637)
                ·
                  refine ⟨4099874190502114003546739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10932997841338970676124637 4099874190502114003546739)
                  ·
                    refine ⟨6149811285753171005320109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4099874190502114003546739 6149811285753171005320109)
                    ·
                      refine ⟨2306179232157439126995041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149811285753171005320109 2306179232157439126995041)
                      ·
                        rfl

theorem cell23_4491268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4491268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491268 prefixEnd_4491268 := by exact prefixLift 4491268
  have htrace : WordTrace (prefixWord ++ tailWord_4491268) baseStart_4491268 baseEnd_4491268 := by
    simpa [prefixWord, tailWord_4491268, baseEnd_4491268] using wordTrace_append hprefix tailTrace_4491268
  have hstable : (prefixWord ++ tailWord_4491268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491268).length < 2 ^ (prefixWord ++ tailWord_4491268).sum := by decide
  have hdescent : baseEnd_4491268 < baseStart_4491268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491307 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 3]
def baseStart_4491307 : Nat := 118140960795 + 4491307 * 2 ^ 59
def prefixEnd_4491307 : Nat := 4983230072969 + 3 ^ 40 * 4491307 * 2
def baseEnd_4491307 : Nat := 2306199257902964474407361

theorem tailTrace_4491307 : CollatzResearch.WordTrace tailWord_4491307 prefixEnd_4491307 2306199257902964474407361 := by
  unfold tailWord_4491307
  simp only [CollatzResearch.WordTrace]
  refine ⟨163811423939769268012408175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109207615959846178674938783 163811423939769268012408175)
  ·
    refine ⟨245717135909653902018612263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163811423939769268012408175 245717135909653902018612263)
    ·
      refine ⟨368575703864480853027918395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245717135909653902018612263 368575703864480853027918395)
      ·
        refine ⟨552863555796721279541877593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368575703864480853027918395 552863555796721279541877593)
        ·
          refine ⟨414647666847540959656408195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552863555796721279541877593 414647666847540959656408195)
          ·
            refine ⟨621971500271311439484612293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414647666847540959656408195 621971500271311439484612293)
            ·
              refine ⟨116619656300870894903364805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 621971500271311439484612293 116619656300870894903364805)
              ·
                refine ⟨21866185556413292794380901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116619656300870894903364805 21866185556413292794380901)
                ·
                  refine ⟨4099909791827492398946419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21866185556413292794380901 4099909791827492398946419)
                  ·
                    refine ⟨6149864687741238598419629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4099909791827492398946419 6149864687741238598419629)
                    ·
                      refine ⟨2306199257902964474407361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149864687741238598419629 2306199257902964474407361)
                      ·
                        rfl

theorem cell23_4491307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 3].length) (baseStart_4491307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491307 prefixEnd_4491307 := by exact prefixLift 4491307
  have htrace : WordTrace (prefixWord ++ tailWord_4491307) baseStart_4491307 baseEnd_4491307 := by
    simpa [prefixWord, tailWord_4491307, baseEnd_4491307] using wordTrace_append hprefix tailTrace_4491307
  have hstable : (prefixWord ++ tailWord_4491307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491307).length < 2 ^ (prefixWord ++ tailWord_4491307).sum := by decide
  have hdescent : baseEnd_4491307 < baseStart_4491307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491340 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_4491340 : Nat := 118140960795 + 4491340 * 2 ^ 59
def prefixEnd_4491340 : Nat := 4983230072969 + 3 ^ 40 * 4491340 * 2
def baseEnd_4491340 : Nat := 768738734254854281764903

theorem tailTrace_4491340 : CollatzResearch.WordTrace tailWord_4491340 prefixEnd_4491340 768738734254854281764903 := by
  unfold tailWord_4491340
  simp only [CollatzResearch.WordTrace]
  refine ⟨81906313774324857324179737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109208418365766476432239649 81906313774324857324179737)
  ·
    refine ⟨61429735330743642993134803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81906313774324857324179737 61429735330743642993134803)
    ·
      refine ⟨92144602996115464489702205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61429735330743642993134803 92144602996115464489702205)
      ·
        refine ⟨34554226123543299183638327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92144602996115464489702205 34554226123543299183638327)
        ·
          refine ⟨51831339185314948775457491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34554226123543299183638327 51831339185314948775457491)
          ·
            refine ⟨77747008777972423163186237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51831339185314948775457491 77747008777972423163186237)
            ·
              refine ⟨29155128291739658686194839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77747008777972423163186237 29155128291739658686194839)
              ·
                refine ⟨43732692437609488029292259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29155128291739658686194839 43732692437609488029292259)
                ·
                  refine ⟨65599038656414232043938389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43732692437609488029292259 65599038656414232043938389)
                  ·
                    refine ⟨768738734254854281764903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65599038656414232043938389 768738734254854281764903)
                    ·
                      rfl

theorem cell23_4491340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_4491340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491340 prefixEnd_4491340 := by exact prefixLift 4491340
  have htrace : WordTrace (prefixWord ++ tailWord_4491340) baseStart_4491340 baseEnd_4491340 := by
    simpa [prefixWord, tailWord_4491340, baseEnd_4491340] using wordTrace_append hprefix tailTrace_4491340
  have hstable : (prefixWord ++ tailWord_4491340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491340).length < 2 ^ (prefixWord ++ tailWord_4491340).sum := by decide
  have hdescent : baseEnd_4491340 < baseStart_4491340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491341 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4491341 : Nat := 118140960795 + 4491341 * 2 ^ 59
def prefixEnd_4491341 : Nat := 4983230072969 + 3 ^ 40 * 4491341 * 2
def baseEnd_4491341 : Nat := 2306216716245217341382205

theorem tailTrace_4491341 : CollatzResearch.WordTrace tailWord_4491341 prefixEnd_4491341 2306216716245217341382205 := by
  unfold tailWord_4491341
  simp only [CollatzResearch.WordTrace]
  refine ⟨163812664021646091819145877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109208442681097394546097251 163812664021646091819145877)
  ·
    refine ⟨7678718626014660554022463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163812664021646091819145877 7678718626014660554022463)
    ·
      refine ⟨11518077939021990831033695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7678718626014660554022463 11518077939021990831033695)
      ·
        refine ⟨17277116908532986246550543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11518077939021990831033695 17277116908532986246550543)
        ·
          refine ⟨25915675362799479369825815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17277116908532986246550543 25915675362799479369825815)
          ·
            refine ⟨38873513044199219054738723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25915675362799479369825815 38873513044199219054738723)
            ·
              refine ⟨58310269566298828582108085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38873513044199219054738723 58310269566298828582108085)
              ·
                refine ⟨5466587771840515179572633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58310269566298828582108085 5466587771840515179572633)
                ·
                  refine ⟨4099940828880386384679475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5466587771840515179572633 4099940828880386384679475)
                  ·
                    refine ⟨6149911243320579577019213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4099940828880386384679475 6149911243320579577019213)
                    ·
                      refine ⟨2306216716245217341382205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6149911243320579577019213 2306216716245217341382205)
                      ·
                        rfl

theorem cell23_4491341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4491341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491341 prefixEnd_4491341 := by exact prefixLift 4491341
  have htrace : WordTrace (prefixWord ++ tailWord_4491341) baseStart_4491341 baseEnd_4491341 := by
    simpa [prefixWord, tailWord_4491341, baseEnd_4491341] using wordTrace_append hprefix tailTrace_4491341
  have hstable : (prefixWord ++ tailWord_4491341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491341).length < 2 ^ (prefixWord ++ tailWord_4491341).sum := by decide
  have hdescent : baseEnd_4491341 < baseStart_4491341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491364 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_4491364 : Nat := 118140960795 + 4491364 * 2 ^ 59
def prefixEnd_4491364 : Nat := 4983230072969 + 3 ^ 40 * 4491364 * 2
def baseEnd_4491364 : Nat := 2306228526300270751394599

theorem tailTrace_4491364 : CollatzResearch.WordTrace tailWord_4491364 prefixEnd_4491364 2306228526300270751394599 := by
  unfold tailWord_4491364
  simp only [CollatzResearch.WordTrace]
  refine ⟨81906751450281383373616573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109209001933708511164822097 81906751450281383373616573)
  ·
    refine ⟨30715031793855518765106215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81906751450281383373616573 30715031793855518765106215)
    ·
      refine ⟨46072547690783278147659323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30715031793855518765106215 46072547690783278147659323)
      ·
        refine ⟨69108821536174917221488985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46072547690783278147659323 69108821536174917221488985)
        ·
          refine ⟨51831616152131187916116739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69108821536174917221488985 51831616152131187916116739)
          ·
            refine ⟨77747424228196781874175109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51831616152131187916116739 77747424228196781874175109)
            ·
              refine ⟨14577642042786896601407833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77747424228196781874175109 14577642042786896601407833)
              ·
                refine ⟨10933231532090172451055875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14577642042786896601407833 10933231532090172451055875)
                ·
                  refine ⟨16399847298135258676583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10933231532090172451055875 16399847298135258676583813)
                  ·
                    refine ⟨3074971368400361001859465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16399847298135258676583813 3074971368400361001859465)
                    ·
                      refine ⟨2306228526300270751394599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3074971368400361001859465 2306228526300270751394599)
                      ·
                        rfl

theorem cell23_4491364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_4491364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491364 prefixEnd_4491364 := by exact prefixLift 4491364
  have htrace : WordTrace (prefixWord ++ tailWord_4491364) baseStart_4491364 baseEnd_4491364 := by
    simpa [prefixWord, tailWord_4491364, baseEnd_4491364] using wordTrace_append hprefix tailTrace_4491364
  have hstable : (prefixWord ++ tailWord_4491364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491364).length < 2 ^ (prefixWord ++ tailWord_4491364).sum := by decide
  have hdescent : baseEnd_4491364 < baseStart_4491364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491421 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 5]
def baseStart_4491421 : Nat := 118140960795 + 4491421 * 2 ^ 59
def prefixEnd_4491421 : Nat := 4983230072969 + 3 ^ 40 * 4491421 * 2
def baseEnd_4491421 : Nat := 256250866077508558709093

theorem tailTrace_4491421 : CollatzResearch.WordTrace tailWord_4491421 prefixEnd_4491421 256250866077508558709093 := by
  unfold tailWord_4491421
  simp only [CollatzResearch.WordTrace]
  refine ⟨163815581861356265482058117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109210387907570843654705411 163815581861356265482058117)
  ·
    refine ⟨30715421599004299777885897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163815581861356265482058117 30715421599004299777885897)
    ·
      refine ⟨23036566199253224833414423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30715421599004299777885897 23036566199253224833414423)
      ·
        refine ⟨34554849298879837250121635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23036566199253224833414423 34554849298879837250121635)
        ·
          refine ⟨51832273948319755875182453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34554849298879837250121635 51832273948319755875182453)
          ·
            refine ⟨4859275682654977113298355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51832273948319755875182453 4859275682654977113298355)
            ·
              refine ⟨7288913523982465669947533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859275682654977113298355 7288913523982465669947533)
              ·
                refine ⟨2733342571493424626230325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7288913523982465669947533 2733342571493424626230325)
                ·
                  refine ⟨256250866077508558709093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733342571493424626230325 256250866077508558709093)
                  ·
                    rfl

theorem cell23_4491421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_4491421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491421 prefixEnd_4491421 := by exact prefixLift 4491421
  have htrace : WordTrace (prefixWord ++ tailWord_4491421) baseStart_4491421 baseEnd_4491421 := by
    simpa [prefixWord, tailWord_4491421, baseEnd_4491421] using wordTrace_append hprefix tailTrace_4491421
  have hstable : (prefixWord ++ tailWord_4491421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491421).length < 2 ^ (prefixWord ++ tailWord_4491421).sum := by decide
  have hdescent : baseEnd_4491421 < baseStart_4491421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491438 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_4491438 : Nat := 118140960795 + 4491438 * 2 ^ 59
def prefixEnd_4491438 : Nat := 4983230072969 + 3 ^ 40 * 4491438 * 2
def baseEnd_4491438 : Nat := 256251835985411495763251

theorem tailTrace_4491438 : CollatzResearch.WordTrace tailWord_4491438 prefixEnd_4491438 256251835985411495763251 := by
  unfold tailWord_4491438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20477025237786834673178371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109210801268196451590284645 20477025237786834673178371)
  ·
    refine ⟨30715537856680252009767557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20477025237786834673178371 30715537856680252009767557)
    ·
      refine ⟨5759163348127547251831417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30715537856680252009767557 5759163348127547251831417)
      ·
        refine ⟨4319372511095660438873563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5759163348127547251831417 4319372511095660438873563)
        ·
          refine ⟨6479058766643490658310345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319372511095660438873563 6479058766643490658310345)
          ·
            refine ⟨4859294074982617993732759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6479058766643490658310345 4859294074982617993732759)
            ·
              refine ⟨7288941112473926990599139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859294074982617993732759 7288941112473926990599139)
              ·
                refine ⟨10933411668710890485898709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288941112473926990599139 10933411668710890485898709)
                ·
                  refine ⟨256251835985411495763251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10933411668710890485898709 256251835985411495763251)
                  ·
                    rfl

theorem cell23_4491438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_4491438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491438 prefixEnd_4491438 := by exact prefixLift 4491438
  have htrace : WordTrace (prefixWord ++ tailWord_4491438) baseStart_4491438 baseEnd_4491438 := by
    simpa [prefixWord, tailWord_4491438, baseEnd_4491438] using wordTrace_append hprefix tailTrace_4491438
  have hstable : (prefixWord ++ tailWord_4491438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491438).length < 2 ^ (prefixWord ++ tailWord_4491438).sum := by decide
  have hdescent : baseEnd_4491438 < baseStart_4491438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491504 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_4491504 : Nat := 118140960795 + 4491504 * 2 ^ 59
def prefixEnd_4491504 : Nat := 4983230072969 + 3 ^ 40 * 4491504 * 2
def baseEnd_4491504 : Nat := 2306300413591900203643955

theorem tailTrace_4491504 : CollatzResearch.WordTrace tailWord_4491504 prefixEnd_4491504 2306300413591900203643955 := by
  unfold tailWord_4491504
  simp only [CollatzResearch.WordTrace]
  refine ⟨81909304560027785328664783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109212406080037047104886377 81909304560027785328664783)
  ·
    refine ⟨122863956840041677992997175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81909304560027785328664783 122863956840041677992997175)
    ·
      refine ⟨184295935260062516989495763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122863956840041677992997175 184295935260062516989495763)
      ·
        refine ⟨276443902890093775484243645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184295935260062516989495763 276443902890093775484243645)
        ·
          refine ⟨103666463583785165806591367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276443902890093775484243645 103666463583785165806591367)
          ·
            refine ⟨155499695375677748709887051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103666463583785165806591367 155499695375677748709887051)
            ·
              refine ⟨233249543063516623064830577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155499695375677748709887051 233249543063516623064830577)
              ·
                refine ⟨174937157297637467298622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233249543063516623064830577 174937157297637467298622933)
                ·
                  refine ⟨4100089624163378139811475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174937157297637467298622933 4100089624163378139811475)
                  ·
                    refine ⟨6150134436245067209717213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100089624163378139811475 6150134436245067209717213)
                    ·
                      refine ⟨2306300413591900203643955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150134436245067209717213 2306300413591900203643955)
                      ·
                        rfl

theorem cell23_4491504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_4491504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491504 prefixEnd_4491504 := by exact prefixLift 4491504
  have htrace : WordTrace (prefixWord ++ tailWord_4491504) baseStart_4491504 baseEnd_4491504 := by
    simpa [prefixWord, tailWord_4491504, baseEnd_4491504] using wordTrace_append hprefix tailTrace_4491504
  have hstable : (prefixWord ++ tailWord_4491504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491504).length < 2 ^ (prefixWord ++ tailWord_4491504).sum := by decide
  have hdescent : baseEnd_4491504 < baseStart_4491504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491507 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 5, 5]
def baseStart_4491507 : Nat := 118140960795 + 4491507 * 2 ^ 59
def prefixEnd_4491507 : Nat := 4983230072969 + 3 ^ 40 * 4491507 * 2
def baseEnd_4491507 : Nat := 768767318011287897302147

theorem tailTrace_4491507 : CollatzResearch.WordTrace tailWord_4491507 prefixEnd_4491507 768767318011287897302147 := by
  unfold tailWord_4491507
  simp only [CollatzResearch.WordTrace]
  refine ⟨163818718539044702169688775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109212479026029801446459183 163818718539044702169688775)
  ·
    refine ⟨245728077808567053254533163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163818718539044702169688775 245728077808567053254533163)
    ·
      refine ⟨368592116712850579881799745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245728077808567053254533163 368592116712850579881799745)
      ·
        refine ⟨276444087534637934911349809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368592116712850579881799745 276444087534637934911349809)
        ·
          refine ⟨207333065650978451183512357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276444087534637934911349809 207333065650978451183512357)
          ·
            refine ⟨38874949809558459596908567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207333065650978451183512357 38874949809558459596908567)
            ·
              refine ⟨58312424714337689395362851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38874949809558459596908567 58312424714337689395362851)
              ·
                refine ⟨87468637071506534093044277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58312424714337689395362851 87468637071506534093044277)
                ·
                  refine ⟨8200184725453737571222901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87468637071506534093044277 8200184725453737571222901)
                  ·
                    refine ⟨768767318011287897302147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8200184725453737571222901 768767318011287897302147)
                    ·
                      rfl

theorem cell23_4491507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].length) (baseStart_4491507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491507 prefixEnd_4491507 := by exact prefixLift 4491507
  have htrace : WordTrace (prefixWord ++ tailWord_4491507) baseStart_4491507 baseEnd_4491507 := by
    simpa [prefixWord, tailWord_4491507, baseEnd_4491507] using wordTrace_append hprefix tailTrace_4491507
  have hstable : (prefixWord ++ tailWord_4491507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491507).length < 2 ^ (prefixWord ++ tailWord_4491507).sum := by decide
  have hdescent : baseEnd_4491507 < baseStart_4491507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491521 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_4491521 : Nat := 118140960795 + 4491521 * 2 ^ 59
def prefixEnd_4491521 : Nat := 4983230072969 + 3 ^ 40 * 4491521 * 2
def baseEnd_4491521 : Nat := 2306309142763026637131377

theorem tailTrace_4491521 : CollatzResearch.WordTrace tailWord_4491521 prefixEnd_4491521 2306309142763026637131377 := by
  unfold tailWord_4491521
  simp only [CollatzResearch.WordTrace]
  refine ⟨163819229160993982560698417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109212819440662655040465611 163819229160993982560698417)
  ·
    refine ⟨122864421870745486920523813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163819229160993982560698417 122864421870745486920523813)
    ·
      refine ⟨23037079100764778797598215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122864421870745486920523813 23037079100764778797598215)
      ·
        refine ⟨34555618651147168196397323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23037079100764778797598215 34555618651147168196397323)
        ·
          refine ⟨51833427976720752294595985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34555618651147168196397323 51833427976720752294595985)
          ·
            refine ⟨38875070982540564220946989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51833427976720752294595985 38875070982540564220946989)
            ·
              refine ⟨14578151618452711582855121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38875070982540564220946989 14578151618452711582855121)
              ·
                refine ⟨10933613713839533687141341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14578151618452711582855121 10933613713839533687141341)
                ·
                  refine ⟨4100105142689825132678003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10933613713839533687141341 4100105142689825132678003)
                  ·
                    refine ⟨6150157714034737699017005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100105142689825132678003 6150157714034737699017005)
                    ·
                      refine ⟨2306309142763026637131377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150157714034737699017005 2306309142763026637131377)
                      ·
                        rfl

theorem cell23_4491521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_4491521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491521 prefixEnd_4491521 := by exact prefixLift 4491521
  have htrace : WordTrace (prefixWord ++ tailWord_4491521) baseStart_4491521 baseEnd_4491521 := by
    simpa [prefixWord, tailWord_4491521, baseEnd_4491521] using wordTrace_append hprefix tailTrace_4491521
  have hstable : (prefixWord ++ tailWord_4491521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491521).length < 2 ^ (prefixWord ++ tailWord_4491521).sum := by decide
  have hdescent : baseEnd_4491521 < baseStart_4491521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491541 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_4491541 : Nat := 118140960795 + 4491541 * 2 ^ 59
def prefixEnd_4491541 : Nat := 4983230072969 + 3 ^ 40 * 4491541 * 2
def baseEnd_4491541 : Nat := 768773137458705519627095

theorem tailTrace_4491541 : CollatzResearch.WordTrace tailWord_4491541 prefixEnd_4491541 768773137458705519627095 := by
  unfold tailWord_4491541
  simp only [CollatzResearch.WordTrace]
  refine ⟨163819958620921525976426477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109213305747281017317617651 163819958620921525976426477)
  ·
    refine ⟨61432484482845572241159929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163819958620921525976426477 61432484482845572241159929)
    ·
      refine ⟨46074363362134179180869947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61432484482845572241159929 46074363362134179180869947)
      ·
        refine ⟨69111545043201268771304921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46074363362134179180869947 69111545043201268771304921)
        ·
          refine ⟨51833658782400951578478691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69111545043201268771304921 51833658782400951578478691)
          ·
            refine ⟨77750488173601427367718037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51833658782400951578478691 77750488173601427367718037)
            ·
              refine ⟨3644554133137566907861783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77750488173601427367718037 3644554133137566907861783)
              ·
                refine ⟨5466831199706350361792675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644554133137566907861783 5466831199706350361792675)
                ·
                  refine ⟨8200246799559525542689013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5466831199706350361792675 8200246799559525542689013)
                  ·
                    refine ⟨768773137458705519627095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8200246799559525542689013 768773137458705519627095)
                    ·
                      rfl

theorem cell23_4491541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_4491541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491541 prefixEnd_4491541 := by exact prefixLift 4491541
  have htrace : WordTrace (prefixWord ++ tailWord_4491541) baseStart_4491541 baseEnd_4491541 := by
    simpa [prefixWord, tailWord_4491541, baseEnd_4491541] using wordTrace_append hprefix tailTrace_4491541
  have hstable : (prefixWord ++ tailWord_4491541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491541).length < 2 ^ (prefixWord ++ tailWord_4491541).sum := by decide
  have hdescent : baseEnd_4491541 < baseStart_4491541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491564 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_4491564 : Nat := 118140960795 + 4491564 * 2 ^ 59
def prefixEnd_4491564 : Nat := 4983230072969 + 3 ^ 40 * 4491564 * 2
def baseEnd_4491564 : Nat := 2306331222431169968893679

theorem tailTrace_4491564 : CollatzResearch.WordTrace tailWord_4491564 prefixEnd_4491564 2306331222431169968893679 := by
  unfold tailWord_4491564
  simp only [CollatzResearch.WordTrace]
  refine ⟨81910398749919100452256873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109213864999892133936342497 81910398749919100452256873)
  ·
    refine ⟨61432799062439325339192655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81910398749919100452256873 61432799062439325339192655)
    ·
      refine ⟨92149198593658988008788983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61432799062439325339192655 92149198593658988008788983)
      ·
        refine ⟨138223797890488482013183475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92149198593658988008788983 138223797890488482013183475)
        ·
          refine ⟨207335696835732723019775213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138223797890488482013183475 207335696835732723019775213)
          ·
            refine ⟨77750886313399771132415705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207335696835732723019775213 77750886313399771132415705)
            ·
              refine ⟨58313164735049828349311779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77750886313399771132415705 58313164735049828349311779)
              ·
                refine ⟨87469747102574742523967669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58313164735049828349311779 87469747102574742523967669)
                ·
                  refine ⟨8200288790866382111621969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87469747102574742523967669 8200288790866382111621969)
                  ·
                    refine ⟨6150216593149786583716477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8200288790866382111621969 6150216593149786583716477)
                    ·
                      refine ⟨2306331222431169968893679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150216593149786583716477 2306331222431169968893679)
                      ·
                        rfl

theorem cell23_4491564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_4491564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491564 prefixEnd_4491564 := by exact prefixLift 4491564
  have htrace : WordTrace (prefixWord ++ tailWord_4491564) baseStart_4491564 baseEnd_4491564 := by
    simpa [prefixWord, tailWord_4491564, baseEnd_4491564] using wordTrace_append hprefix tailTrace_4491564
  have hstable : (prefixWord ++ tailWord_4491564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491564).length < 2 ^ (prefixWord ++ tailWord_4491564).sum := by decide
  have hdescent : baseEnd_4491564 < baseStart_4491564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491578 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_4491578 : Nat := 118140960795 + 4491578 * 2 ^ 59
def prefixEnd_4491578 : Nat := 4983230072969 + 3 ^ 40 * 4491578 * 2
def baseEnd_4491578 : Nat := 2306338411160332914118615

theorem tailTrace_4491578 : CollatzResearch.WordTrace tailWord_4491578 prefixEnd_4491578 2306338411160332914118615 := by
  unfold tailWord_4491578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40955327030446870323880847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109214205414524987530348925 40955327030446870323880847)
  ·
    refine ⟨61432990545670305485821271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40955327030446870323880847 61432990545670305485821271)
    ·
      refine ⟨92149485818505458228731907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61432990545670305485821271 92149485818505458228731907)
      ·
        refine ⟨138224228727758187343097861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92149485818505458228731907 138224228727758187343097861)
        ·
          refine ⟨25917042886454660126830849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138224228727758187343097861 25917042886454660126830849)
          ·
            refine ⟨19437782164840995095123137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25917042886454660126830849 19437782164840995095123137)
            ·
              refine ⟨14578336623630746321342353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19437782164840995095123137 14578336623630746321342353)
              ·
                refine ⟨10933752467723059741006765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14578336623630746321342353 10933752467723059741006765)
                ·
                  refine ⟨4100157175396147402877537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10933752467723059741006765 4100157175396147402877537)
                  ·
                    refine ⟨3075117881547110552158153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4100157175396147402877537 3075117881547110552158153)
                    ·
                      refine ⟨2306338411160332914118615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075117881547110552158153 2306338411160332914118615)
                      ·
                        rfl

theorem cell23_4491578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_4491578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491578 prefixEnd_4491578 := by exact prefixLift 4491578
  have htrace : WordTrace (prefixWord ++ tailWord_4491578) baseStart_4491578 baseEnd_4491578 := by
    simpa [prefixWord, tailWord_4491578, baseEnd_4491578] using wordTrace_append hprefix tailTrace_4491578
  have hstable : (prefixWord ++ tailWord_4491578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491578).length < 2 ^ (prefixWord ++ tailWord_4491578).sum := by decide
  have hdescent : baseEnd_4491578 < baseStart_4491578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491655 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_4491655 : Nat := 118140960795 + 4491655 * 2 ^ 59
def prefixEnd_4491655 : Nat := 4983230072969 + 3 ^ 40 * 4491655 * 2
def baseEnd_4491655 : Nat := 2306377949170729112855761

theorem tailTrace_4491655 : CollatzResearch.WordTrace tailWord_4491655 prefixEnd_4491655 2306377949170729112855761 := by
  unfold tailWord_4491655
  simp only [CollatzResearch.WordTrace]
  refine ⟨163824116542508523446076419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109216077695005682297384279 163824116542508523446076419)
  ·
    refine ⟨245736174813762785169114629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163824116542508523446076419 245736174813762785169114629)
    ·
      refine ⟨46075532777580522219208993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245736174813762785169114629 46075532777580522219208993)
      ·
        refine ⟨34556649583185391664406745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46075532777580522219208993 34556649583185391664406745)
        ·
          refine ⟨25917487187389043748305059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34556649583185391664406745 25917487187389043748305059)
          ·
            refine ⟨38876230781083565622457589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25917487187389043748305059 38876230781083565622457589)
            ·
              refine ⟨3644646635726584277105399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38876230781083565622457589 3644646635726584277105399)
              ·
                refine ⟨5466969953589876415658099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644646635726584277105399 5466969953589876415658099)
                ·
                  refine ⟨8200454930384814623487149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5466969953589876415658099 8200454930384814623487149)
                  ·
                    refine ⟨3075170598894305483807681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8200454930384814623487149 3075170598894305483807681)
                    ·
                      refine ⟨2306377949170729112855761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075170598894305483807681 2306377949170729112855761)
                      ·
                        rfl

theorem cell23_4491655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_4491655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491655 prefixEnd_4491655 := by exact prefixLift 4491655
  have htrace : WordTrace (prefixWord ++ tailWord_4491655) baseStart_4491655 baseEnd_4491655 := by
    simpa [prefixWord, tailWord_4491655, baseEnd_4491655] using wordTrace_append hprefix tailTrace_4491655
  have hstable : (prefixWord ++ tailWord_4491655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491655).length < 2 ^ (prefixWord ++ tailWord_4491655).sum := by decide
  have hdescent : baseEnd_4491655 < baseStart_4491655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491678 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4491678 : Nat := 118140960795 + 4491678 * 2 ^ 59
def prefixEnd_4491678 : Nat := 4983230072969 + 3 ^ 40 * 4491678 * 2
def baseEnd_4491678 : Nat := 768796586408594174289385

theorem tailTrace_4491678 : CollatzResearch.WordTrace tailWord_4491678 prefixEnd_4491678 768796586408594174289385 := by
  unfold tailWord_4491678
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478119427678149796770461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109216636947616798916109125 20478119427678149796770461)
  ·
    refine ⟨7679294785379306173788923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20478119427678149796770461 7679294785379306173788923)
    ·
      refine ⟨11518942178068959260683385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679294785379306173788923 11518942178068959260683385)
      ·
        refine ⟨8639206633551719445512539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11518942178068959260683385 8639206633551719445512539)
        ·
          refine ⟨12958809950327579168268809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8639206633551719445512539 12958809950327579168268809)
          ·
            refine ⟨9719107462745684376201607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12958809950327579168268809 9719107462745684376201607)
            ·
              refine ⟨14578661194118526564302411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719107462745684376201607 14578661194118526564302411)
              ·
                refine ⟨21867991791177789846453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14578661194118526564302411 21867991791177789846453617)
                ·
                  refine ⟨16400993843383342384840213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21867991791177789846453617 16400993843383342384840213)
                  ·
                    refine ⟨768796586408594174289385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16400993843383342384840213 768796586408594174289385)
                    ·
                      rfl

theorem cell23_4491678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4491678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491678 prefixEnd_4491678 := by exact prefixLift 4491678
  have htrace : WordTrace (prefixWord ++ tailWord_4491678) baseStart_4491678 baseEnd_4491678 := by
    simpa [prefixWord, tailWord_4491678, baseEnd_4491678] using wordTrace_append hprefix tailTrace_4491678
  have hstable : (prefixWord ++ tailWord_4491678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491678).length < 2 ^ (prefixWord ++ tailWord_4491678).sum := by decide
  have hdescent : baseEnd_4491678 < baseStart_4491678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491708 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 5]
def baseStart_4491708 : Nat := 118140960795 + 4491708 * 2 ^ 59
def prefixEnd_4491708 : Nat := 4983230072969 + 3 ^ 40 * 4491708 * 2
def baseEnd_4491708 : Nat := 256267240405046378388113

theorem tailTrace_4491708 : CollatzResearch.WordTrace tailWord_4491708 prefixEnd_4491708 256267240405046378388113 := by
  unfold tailWord_4491708
  simp only [CollatzResearch.WordTrace]
  refine ⟨81913024805658256748877889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109217366407544342331837185 81913024805658256748877889)
  ·
    refine ⟨61434768604243692561658417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81913024805658256748877889 61434768604243692561658417)
    ·
      refine ⟨46076076453182769421243813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61434768604243692561658417 46076076453182769421243813)
      ·
        refine ⟨8639264334971769266483215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46076076453182769421243813 8639264334971769266483215)
        ·
          refine ⟨12958896502457653899724823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8639264334971769266483215 12958896502457653899724823)
          ·
            refine ⟨19438344753686480849587235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12958896502457653899724823 19438344753686480849587235)
            ·
              refine ⟨29157517130529721274380853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19438344753686480849587235 29157517130529721274380853)
              ·
                refine ⟨2733517230987161369473205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29157517130529721274380853 2733517230987161369473205)
                ·
                  refine ⟨256267240405046378388113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733517230987161369473205 256267240405046378388113)
                  ·
                    rfl

theorem cell23_4491708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_4491708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491708 prefixEnd_4491708 := by exact prefixLift 4491708
  have htrace : WordTrace (prefixWord ++ tailWord_4491708) baseStart_4491708 baseEnd_4491708 := by
    simpa [prefixWord, tailWord_4491708, baseEnd_4491708] using wordTrace_append hprefix tailTrace_4491708
  have hstable : (prefixWord ++ tailWord_4491708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491708).length < 2 ^ (prefixWord ++ tailWord_4491708).sum := by decide
  have hdescent : baseEnd_4491708 < baseStart_4491708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491741 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4491741 : Nat := 118140960795 + 4491741 * 2 ^ 59
def prefixEnd_4491741 : Nat := 4983230072969 + 3 ^ 40 * 4491741 * 2
def baseEnd_4491741 : Nat := 2306422108507015776380365

theorem tailTrace_4491741 : CollatzResearch.WordTrace tailWord_4491741 prefixEnd_4491741 2306422108507015776380365 := by
  unfold tailWord_4491741
  simp only [CollatzResearch.WordTrace]
  refine ⟨163827253220196960133707077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109218168813464640089138051 163827253220196960133707077)
  ·
    refine ⟨30717609978786930025070077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163827253220196960133707077 30717609978786930025070077)
    ·
      refine ⟨11519103742045098759401279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30717609978786930025070077 11519103742045098759401279)
      ·
        refine ⟨17278655613067648139101919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519103742045098759401279 17278655613067648139101919)
        ·
          refine ⟨25917983419601472208652879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278655613067648139101919 25917983419601472208652879)
          ·
            refine ⟨38876975129402208312979319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25917983419601472208652879 38876975129402208312979319)
            ·
              refine ⟨58315462694103312469468979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38876975129402208312979319 58315462694103312469468979)
              ·
                refine ⟨87473194041154968704203469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58315462694103312469468979 87473194041154968704203469)
                ·
                  refine ⟨32802447765433113264076301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87473194041154968704203469 32802447765433113264076301)
                  ·
                    refine ⟨12300917912037417474028613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32802447765433113264076301 12300917912037417474028613)
                    ·
                      refine ⟨2306422108507015776380365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12300917912037417474028613 2306422108507015776380365)
                      ·
                        rfl

theorem cell23_4491741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4491741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491741 prefixEnd_4491741 := by exact prefixLift 4491741
  have htrace : WordTrace (prefixWord ++ tailWord_4491741) baseStart_4491741 baseEnd_4491741 := by
    simpa [prefixWord, tailWord_4491741, baseEnd_4491741] using wordTrace_append hprefix tailTrace_4491741
  have hstable : (prefixWord ++ tailWord_4491741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491741).length < 2 ^ (prefixWord ++ tailWord_4491741).sum := by decide
  have hdescent : baseEnd_4491741 < baseStart_4491741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491761 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_4491761 : Nat := 118140960795 + 4491761 * 2 ^ 59
def prefixEnd_4491761 : Nat := 4983230072969 + 3 ^ 40 * 4491761 * 2
def baseEnd_4491761 : Nat := 2306432378120105698130273

theorem tailTrace_4491761 : CollatzResearch.WordTrace tailWord_4491761 prefixEnd_4491761 2306432378120105698130273 := by
  unfold tailWord_4491761
  simp only [CollatzResearch.WordTrace]
  refine ⟨163827982680124503549435137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109218655120083002366290091 163827982680124503549435137)
  ·
    refine ⟨122870987010093377662076353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163827982680124503549435137 122870987010093377662076353)
    ·
      refine ⟨92153240257570033246557265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122870987010093377662076353 92153240257570033246557265)
      ·
        refine ⟨69114930193177524934917949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92153240257570033246557265 69114930193177524934917949)
        ·
          refine ⟨25918098822441571850594231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69114930193177524934917949 25918098822441571850594231)
          ·
            refine ⟨38877148233662357775891347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25918098822441571850594231 38877148233662357775891347)
            ·
              refine ⟨58315722350493536663837021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38877148233662357775891347 58315722350493536663837021)
              ·
                refine ⟨21868395881435076248938883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58315722350493536663837021 21868395881435076248938883)
                ·
                  refine ⟨32802593822152614373408325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21868395881435076248938883 32802593822152614373408325)
                  ·
                    refine ⟨6150486341653615195014061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32802593822152614373408325 6150486341653615195014061)
                    ·
                      refine ⟨2306432378120105698130273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150486341653615195014061 2306432378120105698130273)
                      ·
                        rfl

theorem cell23_4491761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_4491761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491761 prefixEnd_4491761 := by exact prefixLift 4491761
  have htrace : WordTrace (prefixWord ++ tailWord_4491761) baseStart_4491761 baseEnd_4491761 := by
    simpa [prefixWord, tailWord_4491761, baseEnd_4491761] using wordTrace_append hprefix tailTrace_4491761
  have hstable : (prefixWord ++ tailWord_4491761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491761).length < 2 ^ (prefixWord ++ tailWord_4491761).sum := by decide
  have hdescent : baseEnd_4491761 < baseStart_4491761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491782 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4491782 : Nat := 118140960795 + 4491782 * 2 ^ 59
def prefixEnd_4491782 : Nat := 4983230072969 + 3 ^ 40 * 4491782 * 2
def baseEnd_4491782 : Nat := 2306443161213850115967677

theorem tailTrace_4491782 : CollatzResearch.WordTrace tailWord_4491782 prefixEnd_4491782 2306443161213850115967677 := by
  unfold tailWord_4491782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119648394157763254248425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109219165742032282757299733 5119648394157763254248425)
  ·
    refine ⟨3839736295618322440686319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5119648394157763254248425 3839736295618322440686319)
    ·
      refine ⟨5759604443427483661029479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839736295618322440686319 5759604443427483661029479)
      ·
        refine ⟨8639406665141225491544219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759604443427483661029479 8639406665141225491544219)
        ·
          refine ⟨12959109997711838237316329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8639406665141225491544219 12959109997711838237316329)
          ·
            refine ⟨9719332498283878677987247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12959109997711838237316329 9719332498283878677987247)
            ·
              refine ⟨14578998747425818016980871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719332498283878677987247 14578998747425818016980871)
              ·
                refine ⟨21868498121138727025471307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14578998747425818016980871 21868498121138727025471307)
                ·
                  refine ⟨32802747181708090538206961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21868498121138727025471307 32802747181708090538206961)
                  ·
                    refine ⟨24602060386281067903655221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32802747181708090538206961 24602060386281067903655221)
                    ·
                      refine ⟨2306443161213850115967677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24602060386281067903655221 2306443161213850115967677)
                      ·
                        rfl

theorem cell23_4491782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4491782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491782 prefixEnd_4491782 := by exact prefixLift 4491782
  have htrace : WordTrace (prefixWord ++ tailWord_4491782) baseStart_4491782 baseEnd_4491782 := by
    simpa [prefixWord, tailWord_4491782, baseEnd_4491782] using wordTrace_append hprefix tailTrace_4491782
  have hstable : (prefixWord ++ tailWord_4491782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491782).length < 2 ^ (prefixWord ++ tailWord_4491782).sum := by decide
  have hdescent : baseEnd_4491782 < baseStart_4491782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491812 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4491812 : Nat := 118140960795 + 4491812 * 2 ^ 59
def prefixEnd_4491812 : Nat := 4983230072969 + 3 ^ 40 * 4491812 * 2
def baseEnd_4491812 : Nat := 2306458565633484998592539

theorem tailTrace_4491812 : CollatzResearch.WordTrace tailWord_4491812 prefixEnd_4491812 2306458565633484998592539 := by
  unfold tailWord_4491812
  simp only [CollatzResearch.WordTrace]
  refine ⟨81914921401469869629770845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109219895201959826173027793 81914921401469869629770845)
  ·
    refine ⟨30718095525551201111164067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81914921401469869629770845 30718095525551201111164067)
    ·
      refine ⟨46077143288326801666746101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30718095525551201111164067 46077143288326801666746101)
      ·
        refine ⟨4319732183280637656257447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46077143288326801666746101 4319732183280637656257447)
        ·
          refine ⟨6479598274920956484386171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319732183280637656257447 6479598274920956484386171)
          ·
            refine ⟨9719397412381434726579257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479598274920956484386171 9719397412381434726579257)
            ·
              refine ⟨7289548059286076044934443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9719397412381434726579257 7289548059286076044934443)
              ·
                refine ⟨10934322088929114067401665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7289548059286076044934443 10934322088929114067401665)
                ·
                  refine ⟨8200741566696835550551249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10934322088929114067401665 8200741566696835550551249)
                  ·
                    refine ⟨6150556175022626662913437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8200741566696835550551249 6150556175022626662913437)
                    ·
                      refine ⟨2306458565633484998592539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150556175022626662913437 2306458565633484998592539)
                      ·
                        rfl

theorem cell23_4491812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4491812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491812 prefixEnd_4491812 := by exact prefixLift 4491812
  have htrace : WordTrace (prefixWord ++ tailWord_4491812) baseStart_4491812 baseEnd_4491812 := by
    simpa [prefixWord, tailWord_4491812, baseEnd_4491812] using wordTrace_append hprefix tailTrace_4491812
  have hstable : (prefixWord ++ tailWord_4491812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491812).length < 2 ^ (prefixWord ++ tailWord_4491812).sum := by decide
  have hdescent : baseEnd_4491812 < baseStart_4491812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491851 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_4491851 : Nat := 118140960795 + 4491851 * 2 ^ 59
def prefixEnd_4491851 : Nat := 4983230072969 + 3 ^ 40 * 4491851 * 2
def baseEnd_4491851 : Nat := 2306478591379010346004859

theorem tailTrace_4491851 : CollatzResearch.WordTrace tailWord_4491851 prefixEnd_4491851 2306478591379010346004859 := by
  unfold tailWord_4491851
  simp only [CollatzResearch.WordTrace]
  refine ⟨163831265249798448920211407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109220843499865632613474271 163831265249798448920211407)
  ·
    refine ⟨245746897874697673380317111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163831265249798448920211407 245746897874697673380317111)
    ·
      refine ⟨368620346812046510070475667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245746897874697673380317111 368620346812046510070475667)
      ·
        refine ⟨552930520218069765105713501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368620346812046510070475667 552930520218069765105713501)
        ·
          refine ⟨207348945081776161914642563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552930520218069765105713501 207348945081776161914642563)
          ·
            refine ⟨311023417622664242871963845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207348945081776161914642563 311023417622664242871963845)
            ·
              refine ⟨58316890804249545538493221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 311023417622664242871963845 58316890804249545538493221)
              ·
                refine ⟨10934417025796789788467479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58316890804249545538493221 10934417025796789788467479)
                ·
                  refine ⟨16401625538695184682701219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10934417025796789788467479 16401625538695184682701219)
                  ·
                    refine ⟨24602438308042777024051829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16401625538695184682701219 24602438308042777024051829)
                    ·
                      refine ⟨2306478591379010346004859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24602438308042777024051829 2306478591379010346004859)
                      ·
                        rfl

theorem cell23_4491851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_4491851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491851 prefixEnd_4491851 := by exact prefixLift 4491851
  have htrace : WordTrace (prefixWord ++ tailWord_4491851) baseStart_4491851 baseEnd_4491851 := by
    simpa [prefixWord, tailWord_4491851, baseEnd_4491851] using wordTrace_append hprefix tailTrace_4491851
  have hstable : (prefixWord ++ tailWord_4491851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491851).length < 2 ^ (prefixWord ++ tailWord_4491851).sum := by decide
  have hdescent : baseEnd_4491851 < baseStart_4491851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491858 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4491858 : Nat := 118140960795 + 4491858 * 2 ^ 59
def prefixEnd_4491858 : Nat := 4983230072969 + 3 ^ 40 * 4491858 * 2
def baseEnd_4491858 : Nat := 768827395247863939539109

theorem tailTrace_4491858 : CollatzResearch.WordTrace tailWord_4491858 prefixEnd_4491858 768827395247863939539109 := by
  unfold tailWord_4491858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957880140193272278929057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109221013707182059410477485 40957880140193272278929057)
  ·
    refine ⟨30718410105144954209196793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40957880140193272278929057 30718410105144954209196793)
    ·
      refine ⟨23038807578858715656897595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30718410105144954209196793 23038807578858715656897595)
      ·
        refine ⟨34558211368288073485346393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23038807578858715656897595 34558211368288073485346393)
        ·
          refine ⟨25918658526216055114009795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34558211368288073485346393 25918658526216055114009795)
          ·
            refine ⟨38877987789324082671014693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25918658526216055114009795 38877987789324082671014693)
            ·
              refine ⟨7289622710498265500815255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38877987789324082671014693 7289622710498265500815255)
              ·
                refine ⟨10934434065747398251222883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7289622710498265500815255 10934434065747398251222883)
                ·
                  refine ⟨16401651098621097376834325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10934434065747398251222883 16401651098621097376834325)
                  ·
                    refine ⟨768827395247863939539109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16401651098621097376834325 768827395247863939539109)
                    ·
                      rfl

theorem cell23_4491858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4491858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491858 prefixEnd_4491858 := by exact prefixLift 4491858
  have htrace : WordTrace (prefixWord ++ tailWord_4491858) baseStart_4491858 baseEnd_4491858 := by
    simpa [prefixWord, tailWord_4491858, baseEnd_4491858] using wordTrace_append hprefix tailTrace_4491858
  have hstable : (prefixWord ++ tailWord_4491858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491858).length < 2 ^ (prefixWord ++ tailWord_4491858).sum := by decide
  have hdescent : baseEnd_4491858 < baseStart_4491858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491861 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4491861 : Nat := 118140960795 + 4491861 * 2 ^ 59
def prefixEnd_4491861 : Nat := 4983230072969 + 3 ^ 40 * 4491861 * 2
def baseEnd_4491861 : Nat := 2306483726185555306879813

theorem tailTrace_4491861 : CollatzResearch.WordTrace tailWord_4491861 prefixEnd_4491861 2306483726185555306879813 := by
  unfold tailWord_4491861
  simp only [CollatzResearch.WordTrace]
  refine ⟨163831629979762220628075437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109221086653174813752050291 163831629979762220628075437)
  ·
    refine ⟨61436861242410832735528289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163831629979762220628075437 61436861242410832735528289)
    ·
      refine ⟨46077645931808124551646217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61436861242410832735528289 46077645931808124551646217)
      ·
        refine ⟨34558234448856093413734663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46077645931808124551646217 34558234448856093413734663)
        ·
          refine ⟨51837351673284140120601995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34558234448856093413734663 51837351673284140120601995)
          ·
            refine ⟨77756027509926210180902993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51837351673284140120601995 77756027509926210180902993)
            ·
              refine ⟨58317020632444657635677245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77756027509926210180902993 58317020632444657635677245)
              ·
                refine ⟨21868882737166746613378967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58317020632444657635677245 21868882737166746613378967)
                ·
                  refine ⟨32803324105750119920068451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21868882737166746613378967 32803324105750119920068451)
                  ·
                    refine ⟨49204986158625179880102677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32803324105750119920068451 49204986158625179880102677)
                    ·
                      refine ⟨2306483726185555306879813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49204986158625179880102677 2306483726185555306879813)
                      ·
                        rfl

theorem cell23_4491861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4491861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491861 prefixEnd_4491861 := by exact prefixLift 4491861
  have htrace : WordTrace (prefixWord ++ tailWord_4491861) baseStart_4491861 baseEnd_4491861 := by
    simpa [prefixWord, tailWord_4491861, baseEnd_4491861] using wordTrace_append hprefix tailTrace_4491861
  have hstable : (prefixWord ++ tailWord_4491861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491861).length < 2 ^ (prefixWord ++ tailWord_4491861).sum := by decide
  have hdescent : baseEnd_4491861 < baseStart_4491861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491921 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_4491921 : Nat := 118140960795 + 4491921 * 2 ^ 59
def prefixEnd_4491921 : Nat := 4983230072969 + 3 ^ 40 * 4491921 * 2
def baseEnd_4491921 : Nat := 2306514535024825072129537

theorem tailTrace_4491921 : CollatzResearch.WordTrace tailWord_4491921 prefixEnd_4491921 2306514535024825072129537 := by
  unfold tailWord_4491921
  simp only [CollatzResearch.WordTrace]
  refine ⟨163833818359544850875259617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109222545573029900583506411 163833818359544850875259617)
  ·
    refine ⟨122875363769658638156444713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163833818359544850875259617 122875363769658638156444713)
    ·
      refine ⟨92156522827243978617333535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122875363769658638156444713 92156522827243978617333535)
      ·
        refine ⟨138234784240865967926000303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92156522827243978617333535 138234784240865967926000303)
        ·
          refine ⟨207352176361298951889000455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138234784240865967926000303 207352176361298951889000455)
          ·
            refine ⟨311028264541948427833500683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207352176361298951889000455 311028264541948427833500683)
            ·
              refine ⟨466542396812922641750251025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311028264541948427833500683 466542396812922641750251025)
              ·
                refine ⟨349906797609691981312688269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466542396812922641750251025 349906797609691981312688269)
                ·
                  refine ⟨131215049103634492992258101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349906797609691981312688269 131215049103634492992258101)
                  ·
                    refine ⟨12301410853465733718024197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131215049103634492992258101 12301410853465733718024197)
                    ·
                      refine ⟨2306514535024825072129537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12301410853465733718024197 2306514535024825072129537)
                      ·
                        rfl

theorem cell23_4491921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_4491921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491921 prefixEnd_4491921 := by exact prefixLift 4491921
  have htrace : WordTrace (prefixWord ++ tailWord_4491921) baseStart_4491921 baseEnd_4491921 := by
    simpa [prefixWord, tailWord_4491921, baseEnd_4491921] using wordTrace_append hprefix tailTrace_4491921
  have hstable : (prefixWord ++ tailWord_4491921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491921).length < 2 ^ (prefixWord ++ tailWord_4491921).sum := by decide
  have hdescent : baseEnd_4491921 < baseStart_4491921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4491989 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4491989 : Nat := 118140960795 + 4491989 * 2 ^ 59
def prefixEnd_4491989 : Nat := 4983230072969 + 3 ^ 40 * 4491989 * 2
def baseEnd_4491989 : Nat := 2306549451709330806079225

theorem tailTrace_4491989 : CollatzResearch.WordTrace tailWord_4491989 prefixEnd_4491989 2306549451709330806079225 := by
  unfold tailWord_4491989
  simp only [CollatzResearch.WordTrace]
  refine ⟨163836298523298498488735021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109224199015532332325823347 163836298523298498488735021)
  ·
    refine ⟨61438611946236936933275633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163836298523298498488735021 61438611946236936933275633)
    ·
      refine ⟨46078958959677702699956725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61438611946236936933275633 46078958959677702699956725)
      ·
        refine ⟨4319902402469784628120943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46078958959677702699956725 4319902402469784628120943)
        ·
          refine ⟨6479853603704676942181415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319902402469784628120943 6479853603704676942181415)
          ·
            refine ⟨9719780405557015413272123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479853603704676942181415 9719780405557015413272123)
            ·
              refine ⟨14579670608335523119908185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719780405557015413272123 14579670608335523119908185)
              ·
                refine ⟨10934752956251642339931139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14579670608335523119908185 10934752956251642339931139)
                ·
                  refine ⟨16402129434377463509896709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10934752956251642339931139 16402129434377463509896709)
                  ·
                    refine ⟨3075399268945774408105633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16402129434377463509896709 3075399268945774408105633)
                    ·
                      refine ⟨2306549451709330806079225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075399268945774408105633 2306549451709330806079225)
                      ·
                        rfl

theorem cell23_4491989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4491989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4491989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4491989 prefixEnd_4491989 := by exact prefixLift 4491989
  have htrace : WordTrace (prefixWord ++ tailWord_4491989) baseStart_4491989 baseEnd_4491989 := by
    simpa [prefixWord, tailWord_4491989, baseEnd_4491989] using wordTrace_append hprefix tailTrace_4491989
  have hstable : (prefixWord ++ tailWord_4491989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4491989).length < 2 ^ (prefixWord ++ tailWord_4491989).sum := by decide
  have hdescent : baseEnd_4491989 < baseStart_4491989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4491989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492015 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 5, 2]
def baseStart_4492015 : Nat := 118140960795 + 4492015 * 2 ^ 59
def prefixEnd_4492015 : Nat := 4983230072969 + 3 ^ 40 * 4492015 * 2
def baseEnd_4492015 : Nat := 2306562802206347704354105

theorem tailTrace_4492015 : CollatzResearch.WordTrace tailWord_4492015 prefixEnd_4492015 2306562802206347704354105 := by
  unfold tailWord_4492015
  simp only [CollatzResearch.WordTrace]
  refine ⟨163837246821204304929181499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109224831214136203286120999 163837246821204304929181499)
  ·
    refine ⟨245755870231806457393772249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163837246821204304929181499 245755870231806457393772249)
    ·
      refine ⟨184316902673854843045329187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245755870231806457393772249 184316902673854843045329187)
      ·
        refine ⟨276475354010782264567993781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184316902673854843045329187 276475354010782264567993781)
        ·
          refine ⟨25919564438510837303249417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276475354010782264567993781 25919564438510837303249417)
          ·
            refine ⟨19439673328883127977437063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25919564438510837303249417 19439673328883127977437063)
            ·
              refine ⟨29159509993324691966155595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19439673328883127977437063 29159509993324691966155595)
              ·
                refine ⟨43739264989987037949233393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29159509993324691966155595 43739264989987037949233393)
                ·
                  refine ⟨32804448742490278461925045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43739264989987037949233393 32804448742490278461925045)
                  ·
                    refine ⟨3075417069608463605805473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32804448742490278461925045 3075417069608463605805473)
                    ·
                      refine ⟨2306562802206347704354105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075417069608463605805473 2306562802206347704354105)
                      ·
                        rfl

theorem cell23_4492015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5, 2].length) (baseStart_4492015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492015 prefixEnd_4492015 := by exact prefixLift 4492015
  have htrace : WordTrace (prefixWord ++ tailWord_4492015) baseStart_4492015 baseEnd_4492015 := by
    simpa [prefixWord, tailWord_4492015, baseEnd_4492015] using wordTrace_append hprefix tailTrace_4492015
  have hstable : (prefixWord ++ tailWord_4492015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492015).length < 2 ^ (prefixWord ++ tailWord_4492015).sum := by decide
  have hdescent : baseEnd_4492015 < baseStart_4492015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492058 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4492058 : Nat := 118140960795 + 4492058 * 2 ^ 59
def prefixEnd_4492058 : Nat := 4983230072969 + 3 ^ 40 * 4492058 * 2
def baseEnd_4492058 : Nat := 2306584881874491036116407

theorem tailTrace_4492058 : CollatzResearch.WordTrace tailWord_4492058 prefixEnd_4492058 2306584881874491036116407 := by
  unfold tailWord_4492058
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959703790012130818249207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109225876773365682181997885 40959703790012130818249207)
  ·
    refine ⟨61439555685018196227373811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40959703790012130818249207 61439555685018196227373811)
    ·
      refine ⟨92159333527527294341060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61439555685018196227373811 92159333527527294341060717)
      ·
        refine ⟨34559750072822735377897769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92159333527527294341060717 34559750072822735377897769)
        ·
          refine ⟨25919812554617051533423327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34559750072822735377897769 25919812554617051533423327)
          ·
            refine ⟨38879718831925577300134991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25919812554617051533423327 38879718831925577300134991)
            ·
              refine ⟨58319578247888365950202487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38879718831925577300134991 58319578247888365950202487)
              ·
                refine ⟨87479367371832548925303731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58319578247888365950202487 87479367371832548925303731)
                ·
                  refine ⟨131219051057748823387955597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87479367371832548925303731 131219051057748823387955597)
                  ·
                    refine ⟨49207144146655808770483349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131219051057748823387955597 49207144146655808770483349)
                    ·
                      refine ⟨2306584881874491036116407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49207144146655808770483349 2306584881874491036116407)
                      ·
                        rfl

theorem cell23_4492058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4492058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492058 prefixEnd_4492058 := by exact prefixLift 4492058
  have htrace : WordTrace (prefixWord ++ tailWord_4492058) baseStart_4492058 baseEnd_4492058 := by
    simpa [prefixWord, tailWord_4492058, baseEnd_4492058] using wordTrace_append hprefix tailTrace_4492058
  have hstable : (prefixWord ++ tailWord_4492058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492058).length < 2 ^ (prefixWord ++ tailWord_4492058).sum := by decide
  have hdescent : baseEnd_4492058 < baseStart_4492058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492065 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4492065 : Nat := 118140960795 + 4492065 * 2 ^ 59
def prefixEnd_4492065 : Nat := 4983230072969 + 3 ^ 40 * 4492065 * 2
def baseEnd_4492065 : Nat := 2306588476239072508728875

theorem tailTrace_4492065 : CollatzResearch.WordTrace tailWord_4492065 prefixEnd_4492065 2306588476239072508728875 := by
  unfold tailWord_4492065
  simp only [CollatzResearch.WordTrace]
  refine ⟨163839070471023163468501649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109226046980682108979001099 163839070471023163468501649)
  ·
    refine ⟨122879302853267372601376237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163839070471023163468501649 122879302853267372601376237)
    ·
      refine ⟨46079738569975264725516089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122879302853267372601376237 46079738569975264725516089)
      ·
        refine ⟨34559803927481448544137067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46079738569975264725516089 34559803927481448544137067)
        ·
          refine ⟨51839705891222172816205601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34559803927481448544137067 51839705891222172816205601)
          ·
            refine ⟨38879779418416629612154201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51839705891222172816205601 38879779418416629612154201)
            ·
              refine ⟨29159834563812472209115651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38879779418416629612154201 29159834563812472209115651)
              ·
                refine ⟨43739751845718708313673477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29159834563812472209115651 43739751845718708313673477)
                ·
                  refine ⟨8201203471072257808813777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43739751845718708313673477 8201203471072257808813777)
                  ·
                    refine ⟨6150902603304193356610333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8201203471072257808813777 6150902603304193356610333)
                    ·
                      refine ⟨2306588476239072508728875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6150902603304193356610333 2306588476239072508728875)
                      ·
                        rfl

theorem cell23_4492065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4492065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492065 prefixEnd_4492065 := by exact prefixLift 4492065
  have htrace : WordTrace (prefixWord ++ tailWord_4492065) baseStart_4492065 baseEnd_4492065 := by
    simpa [prefixWord, tailWord_4492065, baseEnd_4492065] using wordTrace_append hprefix tailTrace_4492065
  have hstable : (prefixWord ++ tailWord_4492065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492065).length < 2 ^ (prefixWord ++ tailWord_4492065).sum := by decide
  have hdescent : baseEnd_4492065 < baseStart_4492065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492072 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4492072 : Nat := 118140960795 + 4492072 * 2 ^ 59
def prefixEnd_4492072 : Nat := 4983230072969 + 3 ^ 40 * 4492072 * 2
def baseEnd_4492072 : Nat := 768864023534551327113781

theorem tailTrace_4492072 : CollatzResearch.WordTrace tailWord_4492072 prefixEnd_4492072 768864023534551327113781 := by
  unfold tailWord_4492072
  simp only [CollatzResearch.WordTrace]
  refine ⟨81919662890998901832003235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109226217187998535776004313 81919662890998901832003235)
  ·
    refine ⟨122879494336498352748004853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81919662890998901832003235 122879494336498352748004853)
    ·
      refine ⟨11519952594046720570125455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122879494336498352748004853 11519952594046720570125455)
      ·
        refine ⟨17279928891070080855188183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519952594046720570125455 17279928891070080855188183)
        ·
          refine ⟨25919893336605121282782275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17279928891070080855188183 25919893336605121282782275)
          ·
            refine ⟨38879840004907681924173413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25919893336605121282782275 38879840004907681924173413)
            ·
              refine ⟨7289970000920190360782515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38879840004907681924173413 7289970000920190360782515)
              ·
                refine ⟨10934955001380285541173773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7289970000920190360782515 10934955001380285541173773)
                ·
                  refine ⟨4100608125517607077940165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10934955001380285541173773 4100608125517607077940165)
                  ·
                    refine ⟨768864023534551327113781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100608125517607077940165 768864023534551327113781)
                    ·
                      rfl

theorem cell23_4492072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4492072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492072 prefixEnd_4492072 := by exact prefixLift 4492072
  have htrace : WordTrace (prefixWord ++ tailWord_4492072) baseStart_4492072 baseEnd_4492072 := by
    simpa [prefixWord, tailWord_4492072, baseEnd_4492072] using wordTrace_append hprefix tailTrace_4492072
  have hstable : (prefixWord ++ tailWord_4492072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492072).length < 2 ^ (prefixWord ++ tailWord_4492072).sum := by decide
  have hdescent : baseEnd_4492072 < baseStart_4492072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492088 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_4492088 : Nat := 118140960795 + 4492088 * 2 ^ 59
def prefixEnd_4492088 : Nat := 4983230072969 + 3 ^ 40 * 4492088 * 2
def baseEnd_4492088 : Nat := 2306600286294125918741269

theorem tailTrace_4492088 : CollatzResearch.WordTrace tailWord_4492088 prefixEnd_4492088 2306600286294125918741269 := by
  unfold tailWord_4492088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81919954674969919198294459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109226606233293225597725945 81919954674969919198294459)
  ·
    refine ⟨122879932012454878797441689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81919954674969919198294459 122879932012454878797441689)
    ·
      refine ⟨92159949009341159098081267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122879932012454878797441689 92159949009341159098081267)
      ·
        refine ⟨138239923514011738647121901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92159949009341159098081267 138239923514011738647121901)
        ·
          refine ⟨51839971317754401992670713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138239923514011738647121901 51839971317754401992670713)
          ·
            refine ⟨38879978488315801494503035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51839971317754401992670713 38879978488315801494503035)
            ·
              refine ⟨58319967732473702241754553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38879978488315801494503035 58319967732473702241754553)
              ·
                refine ⟨43739975799355276681315915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58319967732473702241754553 43739975799355276681315915)
                ·
                  refine ⟨65609963699032915021973873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43739975799355276681315915 65609963699032915021973873)
                  ·
                    refine ⟨49207472774274686266480405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65609963699032915021973873 49207472774274686266480405)
                    ·
                      refine ⟨2306600286294125918741269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49207472774274686266480405 2306600286294125918741269)
                      ·
                        rfl

theorem cell23_4492088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_4492088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492088 prefixEnd_4492088 := by exact prefixLift 4492088
  have htrace : WordTrace (prefixWord ++ tailWord_4492088) baseStart_4492088 baseEnd_4492088 := by
    simpa [prefixWord, tailWord_4492088, baseEnd_4492088] using wordTrace_append hprefix tailTrace_4492088
  have hstable : (prefixWord ++ tailWord_4492088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492088).length < 2 ^ (prefixWord ++ tailWord_4492088).sum := by decide
  have hdescent : baseEnd_4492088 < baseStart_4492088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492122 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_4492122 : Nat := 118140960795 + 4492122 * 2 ^ 59
def prefixEnd_4492122 : Nat := 4983230072969 + 3 ^ 40 * 4492122 * 2
def baseEnd_4492122 : Nat := 2306617744636378785716113

theorem tailTrace_4492122 : CollatzResearch.WordTrace tailWord_4492122 prefixEnd_4492122 2306617744636378785716113 := by
  unfold tailWord_4492122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40960287357954165550831655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109227432954544441468884413 40960287357954165550831655)
  ·
    refine ⟨61440431036931248326247483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40960287357954165550831655 61440431036931248326247483)
    ·
      refine ⟨92160646555396872489371225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61440431036931248326247483 92160646555396872489371225)
      ·
        refine ⟨69120484916547654367028419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92160646555396872489371225 69120484916547654367028419)
        ·
          refine ⟨103680727374821481550542629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69120484916547654367028419 103680727374821481550542629)
          ·
            refine ⟨19440136382779027790726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103680727374821481550542629 19440136382779027790726743)
            ·
              refine ⟨29160204574168541686090115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19440136382779027790726743 29160204574168541686090115)
              ·
                refine ⟨43740306861252812529135173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29160204574168541686090115 43740306861252812529135173)
                ·
                  refine ⟨8201307536484902349212845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43740306861252812529135173 8201307536484902349212845)
                  ·
                    refine ⟨3075490326181838380954817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8201307536484902349212845 3075490326181838380954817)
                    ·
                      refine ⟨2306617744636378785716113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075490326181838380954817 2306617744636378785716113)
                      ·
                        rfl

theorem cell23_4492122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_4492122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492122 prefixEnd_4492122 := by exact prefixLift 4492122
  have htrace : WordTrace (prefixWord ++ tailWord_4492122) baseStart_4492122 baseEnd_4492122 := by
    simpa [prefixWord, tailWord_4492122, baseEnd_4492122] using wordTrace_append hprefix tailTrace_4492122
  have hstable : (prefixWord ++ tailWord_4492122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492122).length < 2 ^ (prefixWord ++ tailWord_4492122).sum := by decide
  have hdescent : baseEnd_4492122 < baseStart_4492122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492149 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4492149 : Nat := 118140960795 + 4492149 * 2 ^ 59
def prefixEnd_4492149 : Nat := 4983230072969 + 3 ^ 40 * 4492149 * 2
def baseEnd_4492149 : Nat := 768877202871350060026163

theorem tailTrace_4492149 : CollatzResearch.WordTrace tailWord_4492149 prefixEnd_4492149 768877202871350060026163 := by
  unfold tailWord_4492149
  simp only [CollatzResearch.WordTrace]
  refine ⟨163842134202718845814559501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109228089468479230543039667 163842134202718845814559501)
  ·
    refine ⟨61440800326019567180459813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163842134202718845814559501 61440800326019567180459813)
    ·
      refine ⟨11520150061128668846336215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61440800326019567180459813 11520150061128668846336215)
      ·
        refine ⟨17280225091693003269504323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11520150061128668846336215 17280225091693003269504323)
        ·
          refine ⟨25920337637539504904256485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17280225091693003269504323 25920337637539504904256485)
          ·
            refine ⟨4860063307038657169548091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25920337637539504904256485 4860063307038657169548091)
            ·
              refine ⟨7290094960557985754322137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860063307038657169548091 7290094960557985754322137)
              ·
                refine ⟨5467571220418489315741603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7290094960557985754322137 5467571220418489315741603)
                ·
                  refine ⟨8201356830627733973612405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5467571220418489315741603 8201356830627733973612405)
                  ·
                    refine ⟨768877202871350060026163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8201356830627733973612405 768877202871350060026163)
                    ·
                      rfl

theorem cell23_4492149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4492149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492149 prefixEnd_4492149 := by exact prefixLift 4492149
  have htrace : WordTrace (prefixWord ++ tailWord_4492149) baseStart_4492149 baseEnd_4492149 := by
    simpa [prefixWord, tailWord_4492149, baseEnd_4492149] using wordTrace_append hprefix tailTrace_4492149
  have hstable : (prefixWord ++ tailWord_4492149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492149).length < 2 ^ (prefixWord ++ tailWord_4492149).sum := by decide
  have hdescent : baseEnd_4492149 < baseStart_4492149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492165 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_4492165 : Nat := 118140960795 + 4492165 * 2 ^ 59
def prefixEnd_4492165 : Nat := 4983230072969 + 3 ^ 40 * 4492165 * 2
def baseEnd_4492165 : Nat := 2306639824304522117478415

theorem tailTrace_4492165 : CollatzResearch.WordTrace tailWord_4492165 prefixEnd_4492165 2306639824304522117478415 := by
  unfold tailWord_4492165
  simp only [CollatzResearch.WordTrace]
  refine ⟨163842717770660880547141949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109228478513773920364761299 163842717770660880547141949)
  ·
    refine ⟨61441019163997830205178231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163842717770660880547141949 61441019163997830205178231)
    ·
      refine ⟨92161528745996745307767347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61441019163997830205178231 92161528745996745307767347)
      ·
        refine ⟨138242293118995117961651021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92161528745996745307767347 138242293118995117961651021)
        ·
          refine ⟨51840859919623169235619133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138242293118995117961651021 51840859919623169235619133)
          ·
            refine ⟨19440322469858688463357175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51840859919623169235619133 19440322469858688463357175)
            ·
              refine ⟨29160483704788032695035763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19440322469858688463357175 29160483704788032695035763)
              ·
                refine ⟨43740725557182049042553645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29160483704788032695035763 43740725557182049042553645)
                ·
                  refine ⟨16402772083943268390957617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43740725557182049042553645 16402772083943268390957617)
                  ·
                    refine ⟨12302079062957451293218213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16402772083943268390957617 12302079062957451293218213)
                    ·
                      refine ⟨2306639824304522117478415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12302079062957451293218213 2306639824304522117478415)
                      ·
                        rfl

theorem cell23_4492165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_4492165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492165 prefixEnd_4492165 := by exact prefixLift 4492165
  have htrace : WordTrace (prefixWord ++ tailWord_4492165) baseStart_4492165 baseEnd_4492165 := by
    simpa [prefixWord, tailWord_4492165, baseEnd_4492165] using wordTrace_append hprefix tailTrace_4492165
  have hstable : (prefixWord ++ tailWord_4492165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492165).length < 2 ^ (prefixWord ++ tailWord_4492165).sum := by decide
  have hdescent : baseEnd_4492165 < baseStart_4492165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492169 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 1, 1, 4]
def baseStart_4492169 : Nat := 118140960795 + 4492169 * 2 ^ 59
def prefixEnd_4492169 : Nat := 4983230072969 + 3 ^ 40 * 4492169 * 2
def baseEnd_4492169 : Nat := 2306641878227140101828397

theorem tailTrace_4492169 : CollatzResearch.WordTrace tailWord_4492169 prefixEnd_4492169 2306641878227140101828397 := by
  unfold tailWord_4492169
  simp only [CollatzResearch.WordTrace]
  refine ⟨163842863662646389230287561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109228575775097592820191707 163842863662646389230287561)
  ·
    refine ⟨122882147746984791922715671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163842863662646389230287561 122882147746984791922715671)
    ·
      refine ⟨184323221620477187884073507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122882147746984791922715671 184323221620477187884073507)
      ·
        refine ⟨276484832430715781826110261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184323221620477187884073507 276484832430715781826110261)
        ·
          refine ⟨25920453040379604546197837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276484832430715781826110261 25920453040379604546197837)
          ·
            refine ⟨9720169890142351704824189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25920453040379604546197837 9720169890142351704824189)
            ·
              refine ⟨3645063708803381889309071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9720169890142351704824189 3645063708803381889309071)
              ·
                refine ⟨5467595563205072833963607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645063708803381889309071 5467595563205072833963607)
                ·
                  refine ⟨8201393344807609250945411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5467595563205072833963607 8201393344807609250945411)
                  ·
                    refine ⟨12302090017211413876418117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8201393344807609250945411 12302090017211413876418117)
                    ·
                      refine ⟨2306641878227140101828397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12302090017211413876418117 2306641878227140101828397)
                      ·
                        rfl

theorem cell23_4492169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 1, 4].length) (baseStart_4492169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492169 prefixEnd_4492169 := by exact prefixLift 4492169
  have htrace : WordTrace (prefixWord ++ tailWord_4492169) baseStart_4492169 baseEnd_4492169 := by
    simpa [prefixWord, tailWord_4492169, baseEnd_4492169] using wordTrace_append hprefix tailTrace_4492169
  have hstable : (prefixWord ++ tailWord_4492169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492169).length < 2 ^ (prefixWord ++ tailWord_4492169).sum := by decide
  have hdescent : baseEnd_4492169 < baseStart_4492169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492172 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4492172 : Nat := 118140960795 + 4492172 * 2 ^ 59
def prefixEnd_4492172 : Nat := 4983230072969 + 3 ^ 40 * 4492172 * 2
def baseEnd_4492172 : Nat := 2306643418669103590090883

theorem tailTrace_4492172 : CollatzResearch.WordTrace tailWord_4492172 prefixEnd_4492172 2306643418669103590090883 := by
  unfold tailWord_4492172
  simp only [CollatzResearch.WordTrace]
  refine ⟨81921486540817760371323385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109228648721090347161764513 81921486540817760371323385)
  ·
    refine ⟨61441114905613320278492539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81921486540817760371323385 61441114905613320278492539)
    ·
      refine ⟨92161672358419980417738809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61441114905613320278492539 92161672358419980417738809)
      ·
        refine ⟨69121254268814985313304107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92161672358419980417738809 69121254268814985313304107)
        ·
          refine ⟨103681881403222477969956161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69121254268814985313304107 103681881403222477969956161)
          ·
            refine ⟨77761411052416858477467121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103681881403222477969956161 77761411052416858477467121)
            ·
              refine ⟨58321058289312643858100341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77761411052416858477467121 58321058289312643858100341)
              ·
                refine ⟨5467599214623060361696907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58321058289312643858100341 5467599214623060361696907)
                ·
                  refine ⟨8201398821934590542545361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5467599214623060361696907 8201398821934590542545361)
                  ·
                    refine ⟨6151049116450942906909021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8201398821934590542545361 6151049116450942906909021)
                    ·
                      refine ⟨2306643418669103590090883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151049116450942906909021 2306643418669103590090883)
                      ·
                        rfl

theorem cell23_4492172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4492172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492172 prefixEnd_4492172 := by exact prefixLift 4492172
  have htrace : WordTrace (prefixWord ++ tailWord_4492172) baseStart_4492172 baseEnd_4492172 := by
    simpa [prefixWord, tailWord_4492172, baseEnd_4492172] using wordTrace_append hprefix tailTrace_4492172
  have hstable : (prefixWord ++ tailWord_4492172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492172).length < 2 ^ (prefixWord ++ tailWord_4492172).sum := by decide
  have hdescent : baseEnd_4492172 < baseStart_4492172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492185 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_4492185 : Nat := 118140960795 + 4492185 * 2 ^ 59
def prefixEnd_4492185 : Nat := 4983230072969 + 3 ^ 40 * 4492185 * 2
def baseEnd_4492185 : Nat := 2306650093917612039228323

theorem tailTrace_4492185 : CollatzResearch.WordTrace tailWord_4492185 prefixEnd_4492185 2306650093917612039228323 := by
  unfold tailWord_4492185
  simp only [CollatzResearch.WordTrace]
  refine ⟨163843447230588423962870009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109228964820392282641913339 163843447230588423962870009)
  ·
    refine ⟨122882585422941317972152507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163843447230588423962870009 122882585422941317972152507)
    ·
      refine ⟨184323878134411976958228761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122882585422941317972152507 184323878134411976958228761)
      ·
        refine ⟨138242908600808982718671571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184323878134411976958228761 138242908600808982718671571)
        ·
          refine ⟨207364362901213474078007357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138242908600808982718671571 207364362901213474078007357)
          ·
            refine ⟨77761636087955052779252759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207364362901213474078007357 77761636087955052779252759)
            ·
              refine ⟨116642454131932579168879139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77761636087955052779252759 116642454131932579168879139)
              ·
                refine ⟨174963681197898868753318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116642454131932579168879139 174963681197898868753318709)
                ·
                  refine ⟨16402845112303018945623629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174963681197898868753318709 16402845112303018945623629)
                  ·
                    refine ⟨6151066917113632104608861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16402845112303018945623629 6151066917113632104608861)
                    ·
                      refine ⟨2306650093917612039228323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151066917113632104608861 2306650093917612039228323)
                      ·
                        rfl

theorem cell23_4492185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_4492185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492185 prefixEnd_4492185 := by exact prefixLift 4492185
  have htrace : WordTrace (prefixWord ++ tailWord_4492185) baseStart_4492185 baseEnd_4492185 := by
    simpa [prefixWord, tailWord_4492185, baseEnd_4492185] using wordTrace_append hprefix tailTrace_4492185
  have hstable : (prefixWord ++ tailWord_4492185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492185).length < 2 ^ (prefixWord ++ tailWord_4492185).sum := by decide
  have hdescent : baseEnd_4492185 < baseStart_4492185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492199 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4492199 : Nat := 118140960795 + 4492199 * 2 ^ 59
def prefixEnd_4492199 : Nat := 4983230072969 + 3 ^ 40 * 4492199 * 2
def baseEnd_4492199 : Nat := 2306657282646774984453259

theorem tailTrace_4492199 : CollatzResearch.WordTrace tailWord_4492199 prefixEnd_4492199 2306657282646774984453259 := by
  unfold tailWord_4492199
  simp only [CollatzResearch.WordTrace]
  refine ⟨163843957852537704353879651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109229305235025136235919767 163843957852537704353879651)
  ·
    refine ⟨245765936778806556530819477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163843957852537704353879651 245765936778806556530819477)
    ·
      refine ⟨11520278286506557337382163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245765936778806556530819477 11520278286506557337382163)
      ·
        refine ⟨17280417429759836006073245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11520278286506557337382163 17280417429759836006073245)
        ·
          refine ⟨6480156536159938502277467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17280417429759836006073245 6480156536159938502277467)
          ·
            refine ⟨9720234804239907753416201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6480156536159938502277467 9720234804239907753416201)
            ·
              refine ⟨7290176103179930815062151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720234804239907753416201 7290176103179930815062151)
              ·
                refine ⟨10935264154769896222593227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290176103179930815062151 10935264154769896222593227)
                ·
                  refine ⟨16402896232154844333889841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10935264154769896222593227 16402896232154844333889841)
                  ·
                    refine ⟨12302172174116133250417381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16402896232154844333889841 12302172174116133250417381)
                    ·
                      refine ⟨2306657282646774984453259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12302172174116133250417381 2306657282646774984453259)
                      ·
                        rfl

theorem cell23_4492199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4492199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492199 prefixEnd_4492199 := by exact prefixLift 4492199
  have htrace : WordTrace (prefixWord ++ tailWord_4492199) baseStart_4492199 baseEnd_4492199 := by
    simpa [prefixWord, tailWord_4492199, baseEnd_4492199] using wordTrace_append hprefix tailTrace_4492199
  have hstable : (prefixWord ++ tailWord_4492199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492199).length < 2 ^ (prefixWord ++ tailWord_4492199).sum := by decide
  have hdescent : baseEnd_4492199 < baseStart_4492199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492230 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4492230 : Nat := 118140960795 + 4492230 * 2 ^ 59
def prefixEnd_4492230 : Nat := 4983230072969 + 3 ^ 40 * 4492230 * 2
def baseEnd_4492230 : Nat := 768891066849021454388539

theorem tailTrace_4492230 : CollatzResearch.WordTrace tailWord_4492230 prefixEnd_4492230 768891066849021454388539 := by
  unfold tailWord_4492230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120159016107043645258067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109230059010283597765505429 5120159016107043645258067)
  ·
    refine ⟨7680238524160565467887101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120159016107043645258067 7680238524160565467887101)
    ·
      refine ⟨2880089446560212050457663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7680238524160565467887101 2880089446560212050457663)
      ·
        refine ⟨4320134169840318075686495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880089446560212050457663 4320134169840318075686495)
        ·
          refine ⟨6480201254760477113529743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320134169840318075686495 6480201254760477113529743)
          ·
            refine ⟨9720301882140715670294615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6480201254760477113529743 9720301882140715670294615)
            ·
              refine ⟨14580452823211073505441923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9720301882140715670294615 14580452823211073505441923)
              ·
                refine ⟨21870679234816610258162885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14580452823211073505441923 21870679234816610258162885)
                ·
                  refine ⟨4100752356528114423405541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21870679234816610258162885 4100752356528114423405541)
                  ·
                    refine ⟨768891066849021454388539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100752356528114423405541 768891066849021454388539)
                    ·
                      rfl

theorem cell23_4492230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4492230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492230 prefixEnd_4492230 := by exact prefixLift 4492230
  have htrace : WordTrace (prefixWord ++ tailWord_4492230) baseStart_4492230 baseEnd_4492230 := by
    simpa [prefixWord, tailWord_4492230, baseEnd_4492230] using wordTrace_append hprefix tailTrace_4492230
  have hstable : (prefixWord ++ tailWord_4492230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492230).length < 2 ^ (prefixWord ++ tailWord_4492230).sum := by decide
  have hdescent : baseEnd_4492230 < baseStart_4492230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492235 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 6]
def baseStart_4492235 : Nat := 118140960795 + 4492235 * 2 ^ 59
def prefixEnd_4492235 : Nat := 4983230072969 + 3 ^ 40 * 4492235 * 2
def baseEnd_4492235 : Nat := 768891922650112281201031

theorem tailTrace_4492235 : CollatzResearch.WordTrace tailWord_4492235 prefixEnd_4492235 768891922650112281201031 := by
  unfold tailWord_4492235
  simp only [CollatzResearch.WordTrace]
  refine ⟨163845270880407282502190159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109230180586938188334793439 163845270880407282502190159)
  ·
    refine ⟨245767906320610923753285239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163845270880407282502190159 245767906320610923753285239)
    ·
      refine ⟨368651859480916385629927859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245767906320610923753285239 368651859480916385629927859)
      ·
        refine ⟨552977789221374578444891789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368651859480916385629927859 552977789221374578444891789)
        ·
          refine ⟨207366670958015466916834421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 552977789221374578444891789 207366670958015466916834421)
          ·
            refine ⟨19440625402313950023453227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207366670958015466916834421 19440625402313950023453227)
            ·
              refine ⟨29160938103470925035179841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19440625402313950023453227 29160938103470925035179841)
              ·
                refine ⟨21870703577603193776384881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29160938103470925035179841 21870703577603193776384881)
                ·
                  refine ⟨16403027683202395332288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21870703577603193776384881 16403027683202395332288661)
                  ·
                    refine ⟨768891922650112281201031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16403027683202395332288661 768891922650112281201031)
                    ·
                      rfl

theorem cell23_4492235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_4492235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492235 prefixEnd_4492235 := by exact prefixLift 4492235
  have htrace : WordTrace (prefixWord ++ tailWord_4492235) baseStart_4492235 baseEnd_4492235 := by
    simpa [prefixWord, tailWord_4492235, baseEnd_4492235] using wordTrace_append hprefix tailTrace_4492235
  have hstable : (prefixWord ++ tailWord_4492235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492235).length < 2 ^ (prefixWord ++ tailWord_4492235).sum := by decide
  have hdescent : baseEnd_4492235 < baseStart_4492235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492237 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4492237 : Nat := 118140960795 + 4492237 * 2 ^ 59
def prefixEnd_4492237 : Nat := 4983230072969 + 3 ^ 40 * 4492237 * 2
def baseEnd_4492237 : Nat := 2306676794911645835778085

theorem tailTrace_4492237 : CollatzResearch.WordTrace tailWord_4492237 prefixEnd_4492237 2306676794911645835778085 := by
  unfold tailWord_4492237
  simp only [CollatzResearch.WordTrace]
  refine ⟨163845343826400036843762965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109230229217600024562508643 163845343826400036843762965)
  ·
    refine ⟨7680250491862501727051389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163845343826400036843762965 7680250491862501727051389)
    ·
      refine ⟨2880093934448438147644271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7680250491862501727051389 2880093934448438147644271)
      ·
        refine ⟨4320140901672657221466407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880093934448438147644271 4320140901672657221466407)
        ·
          refine ⟨6480211352508985832199611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320140901672657221466407 6480211352508985832199611)
          ·
            refine ⟨9720317028763478748299417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6480211352508985832199611 9720317028763478748299417)
            ·
              refine ⟨7290237771572609061224563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720317028763478748299417 7290237771572609061224563)
              ·
                refine ⟨10935356657358913591836845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290237771572609061224563 10935356657358913591836845)
                ·
                  refine ⟨4100758746509592596938817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10935356657358913591836845 4100758746509592596938817)
                  ·
                    refine ⟨3075569059882194447704113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4100758746509592596938817 3075569059882194447704113)
                    ·
                      refine ⟨2306676794911645835778085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075569059882194447704113 2306676794911645835778085)
                      ·
                        rfl

theorem cell23_4492237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4492237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492237 prefixEnd_4492237 := by exact prefixLift 4492237
  have htrace : WordTrace (prefixWord ++ tailWord_4492237) baseStart_4492237 baseEnd_4492237 := by
    simpa [prefixWord, tailWord_4492237, baseEnd_4492237] using wordTrace_append hprefix tailTrace_4492237
  have hstable : (prefixWord ++ tailWord_4492237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492237).length < 2 ^ (prefixWord ++ tailWord_4492237).sum := by decide
  have hdescent : baseEnd_4492237 < baseStart_4492237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492253 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_4492253 : Nat := 118140960795 + 4492253 * 2 ^ 59
def prefixEnd_4492253 : Nat := 4983230072969 + 3 ^ 40 * 4492253 * 2
def baseEnd_4492253 : Nat := 2306685010602117773178011

theorem tailTrace_4492253 : CollatzResearch.WordTrace tailWord_4492253 prefixEnd_4492253 2306685010602117773178011 := by
  unfold tailWord_4492253
  simp only [CollatzResearch.WordTrace]
  refine ⟨163845927394342071576345413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109230618262894714384230275 163845927394342071576345413)
  ·
    refine ⟨30721111386439138420564765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163845927394342071576345413 30721111386439138420564765)
    ·
      refine ⟨11520416769914676907711787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30721111386439138420564765 11520416769914676907711787)
      ·
        refine ⟨17280625154872015361567681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11520416769914676907711787 17280625154872015361567681)
        ·
          refine ⟨12960468866154011521175761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17280625154872015361567681 12960468866154011521175761)
          ·
            refine ⟨9720351649615508640881821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12960468866154011521175761 9720351649615508640881821)
            ·
              refine ⟨3645131868605815740330683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9720351649615508640881821 3645131868605815740330683)
              ·
                refine ⟨5467697802908723610496025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645131868605815740330683 5467697802908723610496025)
                ·
                  refine ⟨4100773352181542707872019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467697802908723610496025 4100773352181542707872019)
                  ·
                    refine ⟨6151160028272314061808029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100773352181542707872019 6151160028272314061808029)
                    ·
                      refine ⟨2306685010602117773178011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151160028272314061808029 2306685010602117773178011)
                      ·
                        rfl

theorem cell23_4492253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_4492253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492253 prefixEnd_4492253 := by exact prefixLift 4492253
  have htrace : WordTrace (prefixWord ++ tailWord_4492253) baseStart_4492253 baseEnd_4492253 := by
    simpa [prefixWord, tailWord_4492253, baseEnd_4492253] using wordTrace_append hprefix tailTrace_4492253
  have hstable : (prefixWord ++ tailWord_4492253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492253).length < 2 ^ (prefixWord ++ tailWord_4492253).sum := by decide
  have hdescent : baseEnd_4492253 < baseStart_4492253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492349 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4492349 : Nat := 118140960795 + 4492349 * 2 ^ 59
def prefixEnd_4492349 : Nat := 4983230072969 + 3 ^ 40 * 4492349 * 2
def baseEnd_4492349 : Nat := 2306734304744949397577569

theorem tailTrace_4492349 : CollatzResearch.WordTrace tailWord_4492349 prefixEnd_4492349 2306734304744949397577569 := by
  unfold tailWord_4492349
  simp only [CollatzResearch.WordTrace]
  refine ⟨163849428801994279971840101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109232952534662853314560067 163849428801994279971840101)
  ·
    refine ⟨30721767900373927494720019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163849428801994279971840101 30721767900373927494720019)
    ·
      refine ⟨46082651850560891242080029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30721767900373927494720019 46082651850560891242080029)
      ·
        refine ⟨17280994443960334215780011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46082651850560891242080029 17280994443960334215780011)
        ·
          refine ⟨25921491665940501323670017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17280994443960334215780011 25921491665940501323670017)
          ·
            refine ⟨19441118749455375992752513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25921491665940501323670017 19441118749455375992752513)
            ·
              refine ⟨14580839062091531994564385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19441118749455375992752513 14580839062091531994564385)
              ·
                refine ⟨10935629296568648995923289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14580839062091531994564385 10935629296568648995923289)
                ·
                  refine ⟨8201721972426486746942467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10935629296568648995923289 8201721972426486746942467)
                  ·
                    refine ⟨12302582958639730120413701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8201721972426486746942467 12302582958639730120413701)
                    ·
                      refine ⟨2306734304744949397577569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12302582958639730120413701 2306734304744949397577569)
                      ·
                        rfl

theorem cell23_4492349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4492349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492349 prefixEnd_4492349 := by exact prefixLift 4492349
  have htrace : WordTrace (prefixWord ++ tailWord_4492349) baseStart_4492349 baseEnd_4492349 := by
    simpa [prefixWord, tailWord_4492349, baseEnd_4492349] using wordTrace_append hprefix tailTrace_4492349
  have hstable : (prefixWord ++ tailWord_4492349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492349).length < 2 ^ (prefixWord ++ tailWord_4492349).sum := by decide
  have hdescent : baseEnd_4492349 < baseStart_4492349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492386 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4492386 : Nat := 118140960795 + 4492386 * 2 ^ 59
def prefixEnd_4492386 : Nat := 4983230072969 + 3 ^ 40 * 4492386 * 2
def baseEnd_4492386 : Nat := 2306753303529165752814899

theorem tailTrace_4492386 : CollatzResearch.WordTrace tailWord_4492386 prefixEnd_4492386 2306753303529165752814899 := by
  unfold tailWord_4492386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40962694575715058822734253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109233852201906823527291341 40962694575715058822734253)
  ·
    refine ⟨15361010465893147058525345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40962694575715058822734253 15361010465893147058525345)
    ·
      refine ⟨11520757849419860293894009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15361010465893147058525345 11520757849419860293894009)
      ·
        refine ⟨8640568387064895220420507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11520757849419860293894009 8640568387064895220420507)
        ·
          refine ⟨12960852580597342830630761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640568387064895220420507 12960852580597342830630761)
          ·
            refine ⟨9720639435448007122973071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12960852580597342830630761 9720639435448007122973071)
            ·
              refine ⟨14580959153172010684459607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9720639435448007122973071 14580959153172010684459607)
              ·
                refine ⟨21871438729758016026689411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14580959153172010684459607 21871438729758016026689411)
                ·
                  refine ⟨32807158094637024040034117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21871438729758016026689411 32807158094637024040034117)
                  ·
                    refine ⟨6151342142744442007506397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32807158094637024040034117 6151342142744442007506397)
                    ·
                      refine ⟨2306753303529165752814899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151342142744442007506397 2306753303529165752814899)
                      ·
                        rfl

theorem cell23_4492386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4492386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492386 prefixEnd_4492386 := by exact prefixLift 4492386
  have htrace : WordTrace (prefixWord ++ tailWord_4492386) baseStart_4492386 baseEnd_4492386 := by
    simpa [prefixWord, tailWord_4492386, baseEnd_4492386] using wordTrace_append hprefix tailTrace_4492386
  have hstable : (prefixWord ++ tailWord_4492386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492386).length < 2 ^ (prefixWord ++ tailWord_4492386).sum := by decide
  have hdescent : baseEnd_4492386 < baseStart_4492386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492399 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_4492399 : Nat := 118140960795 + 4492399 * 2 ^ 59
def prefixEnd_4492399 : Nat := 4983230072969 + 3 ^ 40 * 4492399 * 2
def baseEnd_4492399 : Nat := 2306759978777674201952339

theorem tailTrace_4492399 : CollatzResearch.WordTrace tailWord_4492399 prefixEnd_4492399 2306759978777674201952339 := by
  unfold tailWord_4492399
  simp only [CollatzResearch.WordTrace]
  refine ⟨163851252451813138511160251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109234168301208759007440167 163851252451813138511160251)
  ·
    refine ⟨245776878677719707766740377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163851252451813138511160251 245776878677719707766740377)
    ·
      refine ⟨184332659008289780825055283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245776878677719707766740377 184332659008289780825055283)
      ·
        refine ⟨276498988512434671237582925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184332659008289780825055283 276498988512434671237582925)
        ·
          refine ⟨103687120692163001714093597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276498988512434671237582925 103687120692163001714093597)
          ·
            refine ⟨38882670259561125642785099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103687120692163001714093597 38882670259561125642785099)
            ·
              refine ⟨58324005389341688464177649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38882670259561125642785099 58324005389341688464177649)
              ·
                refine ⟨43743004042006266348133237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58324005389341688464177649 43743004042006266348133237)
                ·
                  refine ⟨4100906628938087470137491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43743004042006266348133237 4100906628938087470137491)
                  ·
                    refine ⟨6151359943407131205206237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100906628938087470137491 6151359943407131205206237)
                    ·
                      refine ⟨2306759978777674201952339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151359943407131205206237 2306759978777674201952339)
                      ·
                        rfl

theorem cell23_4492399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_4492399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492399 prefixEnd_4492399 := by exact prefixLift 4492399
  have htrace : WordTrace (prefixWord ++ tailWord_4492399) baseStart_4492399 baseEnd_4492399 := by
    simpa [prefixWord, tailWord_4492399, baseEnd_4492399] using wordTrace_append hprefix tailTrace_4492399
  have hstable : (prefixWord ++ tailWord_4492399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492399).length < 2 ^ (prefixWord ++ tailWord_4492399).sum := by decide
  have hdescent : baseEnd_4492399 < baseStart_4492399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492432 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_4492432 : Nat := 118140960795 + 4492432 * 2 ^ 59
def prefixEnd_4492432 : Nat := 4983230072969 + 3 ^ 40 * 4492432 * 2
def baseEnd_4492432 : Nat := 768925641213090857613229

theorem tailTrace_4492432 : CollatzResearch.WordTrace tailWord_4492432 prefixEnd_4492432 768925641213090857613229 := by
  unfold tailWord_4492432
  simp only [CollatzResearch.WordTrace]
  refine ⟨81926228030346792573555775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109234970707129056764741033 81926228030346792573555775)
  ·
    refine ⟨122889342045520188860333663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81926228030346792573555775 122889342045520188860333663)
    ·
      refine ⟨184334013068280283290500495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122889342045520188860333663 184334013068280283290500495)
      ·
        refine ⟨276501019602420424935750743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184334013068280283290500495 276501019602420424935750743)
        ·
          refine ⟨414751529403630637403626115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276501019602420424935750743 414751529403630637403626115)
          ·
            refine ⟨622127294105445956105439173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414751529403630637403626115 622127294105445956105439173)
            ·
              refine ⟨116648867644771116769769845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 622127294105445956105439173 116648867644771116769769845)
              ·
                refine ⟨10935831341697292197165923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116648867644771116769769845 10935831341697292197165923)
                ·
                  refine ⟨16403747012545938295748885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10935831341697292197165923 16403747012545938295748885)
                  ·
                    refine ⟨768925641213090857613229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16403747012545938295748885 768925641213090857613229)
                    ·
                      rfl

theorem cell23_4492432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_4492432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492432 prefixEnd_4492432 := by exact prefixLift 4492432
  have htrace : WordTrace (prefixWord ++ tailWord_4492432) baseStart_4492432 baseEnd_4492432 := by
    simpa [prefixWord, tailWord_4492432, baseEnd_4492432] using wordTrace_append hprefix tailTrace_4492432
  have hstable : (prefixWord ++ tailWord_4492432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492432).length < 2 ^ (prefixWord ++ tailWord_4492432).sum := by decide
  have hdescent : baseEnd_4492432 < baseStart_4492432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492449 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_4492449 : Nat := 118140960795 + 4492449 * 2 ^ 59
def prefixEnd_4492449 : Nat := 4983230072969 + 3 ^ 40 * 4492449 * 2
def baseEnd_4492449 : Nat := 768928550936799668775703

theorem tailTrace_4492449 : CollatzResearch.WordTrace tailWord_4492449 prefixEnd_4492449 768928550936799668775703 := by
  unfold tailWord_4492449
  simp only [CollatzResearch.WordTrace]
  refine ⟨163853076101631997050480401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109235384067754664700320267 163853076101631997050480401)
  ·
    refine ⟨122889807076223997787860301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163853076101631997050480401 122889807076223997787860301)
    ·
      refine ⟨46083677653583999170447613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122889807076223997787860301 46083677653583999170447613)
      ·
        refine ⟨17281379120093999688917855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46083677653583999170447613 17281379120093999688917855)
        ·
          refine ⟨25922068680140999533376783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17281379120093999688917855 25922068680140999533376783)
          ·
            refine ⟨38883103020211499300065175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25922068680140999533376783 38883103020211499300065175)
            ·
              refine ⟨58324654530317248950097763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38883103020211499300065175 58324654530317248950097763)
              ·
                refine ⟨87486981795475873425146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58324654530317248950097763 87486981795475873425146645)
                ·
                  refine ⟨4100952271662931566803749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87486981795475873425146645 4100952271662931566803749)
                  ·
                    refine ⟨768928550936799668775703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4100952271662931566803749 768928550936799668775703)
                    ·
                      rfl

theorem cell23_4492449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_4492449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492449 prefixEnd_4492449 := by exact prefixLift 4492449
  have htrace : WordTrace (prefixWord ++ tailWord_4492449) baseStart_4492449 baseEnd_4492449 := by
    simpa [prefixWord, tailWord_4492449, baseEnd_4492449] using wordTrace_append hprefix tailTrace_4492449
  have hstable : (prefixWord ++ tailWord_4492449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492449).length < 2 ^ (prefixWord ++ tailWord_4492449).sum := by decide
  have hdescent : baseEnd_4492449 < baseStart_4492449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492473 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4492473 : Nat := 118140960795 + 4492473 * 2 ^ 59
def prefixEnd_4492473 : Nat := 4983230072969 + 3 ^ 40 * 4492473 * 2
def baseEnd_4492473 : Nat := 2306797976346106912426999

theorem tailTrace_4492473 : CollatzResearch.WordTrace tailWord_4492473 prefixEnd_4492473 2306797976346106912426999 := by
  unfold tailWord_4492473
  simp only [CollatzResearch.WordTrace]
  refine ⟨163853951453545049149354073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109235967635696699432902715 163853951453545049149354073)
  ·
    refine ⟨122890463590158786862015555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163853951453545049149354073 122890463590158786862015555)
    ·
      refine ⟨184335695385238180293023333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122890463590158786862015555 184335695385238180293023333)
      ·
        refine ⟨34562942884732158804941875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184335695385238180293023333 34562942884732158804941875)
        ·
          refine ⟨51844414327098238207412813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34562942884732158804941875 51844414327098238207412813)
          ·
            refine ⟨19441655372661839327779805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51844414327098238207412813 19441655372661839327779805)
            ·
              refine ⟨7290620764748189747917427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19441655372661839327779805 7290620764748189747917427)
              ·
                refine ⟨10935931147122284621876141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290620764748189747917427 10935931147122284621876141)
                ·
                  refine ⟨4100974180170856733203553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10935931147122284621876141 4100974180170856733203553)
                  ·
                    refine ⟨3075730635128142549902665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4100974180170856733203553 3075730635128142549902665)
                    ·
                      refine ⟨2306797976346106912426999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075730635128142549902665 2306797976346106912426999)
                      ·
                        rfl

theorem cell23_4492473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4492473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492473 prefixEnd_4492473 := by exact prefixLift 4492473
  have htrace : WordTrace (prefixWord ++ tailWord_4492473) baseStart_4492473 baseEnd_4492473 := by
    simpa [prefixWord, tailWord_4492473, baseEnd_4492473] using wordTrace_append hprefix tailTrace_4492473
  have hstable : (prefixWord ++ tailWord_4492473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492473).length < 2 ^ (prefixWord ++ tailWord_4492473).sum := by decide
  have hdescent : baseEnd_4492473 < baseStart_4492473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492499 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 7, 2]
def baseStart_4492499 : Nat := 118140960795 + 4492499 * 2 ^ 59
def prefixEnd_4492499 : Nat := 4983230072969 + 3 ^ 40 * 4492499 * 2
def baseEnd_4492499 : Nat := 2306811326843123810701879

theorem tailTrace_4492499 : CollatzResearch.WordTrace tailWord_4492499 prefixEnd_4492499 2306811326843123810701879 := by
  unfold tailWord_4492499
  simp only [CollatzResearch.WordTrace]
  refine ⟨163854899751450855589800551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109236599834300570393200367 163854899751450855589800551)
  ·
    refine ⟨245782349627176283384700827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163854899751450855589800551 245782349627176283384700827)
    ·
      refine ⟨368673524440764425077051241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245782349627176283384700827 368673524440764425077051241)
      ·
        refine ⟨276505143330573318807788431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368673524440764425077051241 276505143330573318807788431)
        ·
          refine ⟨414757714995859978211682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276505143330573318807788431 414757714995859978211682647)
          ·
            refine ⟨622136572493789967317523971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414757714995859978211682647 622136572493789967317523971)
            ·
              refine ⟨933204858740684950976285957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622136572493789967317523971 933204858740684950976285957)
              ·
                refine ⟨174975911013878428308053617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 933204858740684950976285957 174975911013878428308053617)
                ·
                  refine ⟨131231933260408821231040213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174975911013878428308053617 131231933260408821231040213)
                  ·
                    refine ⟨3075748435790831747602505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131231933260408821231040213 3075748435790831747602505)
                    ·
                      refine ⟨2306811326843123810701879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075748435790831747602505 2306811326843123810701879)
                      ·
                        rfl

theorem cell23_4492499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7, 2].length) (baseStart_4492499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492499 prefixEnd_4492499 := by exact prefixLift 4492499
  have htrace : WordTrace (prefixWord ++ tailWord_4492499) baseStart_4492499 baseEnd_4492499 := by
    simpa [prefixWord, tailWord_4492499, baseEnd_4492499] using wordTrace_append hprefix tailTrace_4492499
  have hstable : (prefixWord ++ tailWord_4492499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492499).length < 2 ^ (prefixWord ++ tailWord_4492499).sum := by decide
  have hdescent : baseEnd_4492499 < baseStart_4492499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492523 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 3]
def baseStart_4492523 : Nat := 118140960795 + 4492523 * 2 ^ 59
def prefixEnd_4492523 : Nat := 4983230072969 + 3 ^ 40 * 4492523 * 2
def baseEnd_4492523 : Nat := 2306823650378831716801769

theorem tailTrace_4492523 : CollatzResearch.WordTrace tailWord_4492523 prefixEnd_4492523 2306823650378831716801769 := by
  unfold tailWord_4492523
  simp only [CollatzResearch.WordTrace]
  refine ⟨163855775103363907688674223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109237183402242605125782815 163855775103363907688674223)
  ·
    refine ⟨245783662655045861533011335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163855775103363907688674223 245783662655045861533011335)
    ·
      refine ⟨368675493982568792299517003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245783662655045861533011335 368675493982568792299517003)
      ·
        refine ⟨553013240973853188449275505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368675493982568792299517003 553013240973853188449275505)
        ·
          refine ⟨414759930730389891336956629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553013240973853188449275505 414759930730389891336956629)
          ·
            refine ⟨9720935876493513078209921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 414759930730389891336956629 9720935876493513078209921)
            ·
              refine ⟨7290701907370134808657441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720935876493513078209921 7290701907370134808657441)
              ·
                refine ⟨5468026430527601106493081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7290701907370134808657441 5468026430527601106493081)
                ·
                  refine ⟨4101019822895700829869811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468026430527601106493081 4101019822895700829869811)
                  ·
                    refine ⟨6151529734343551244804717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101019822895700829869811 6151529734343551244804717)
                    ·
                      refine ⟨2306823650378831716801769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151529734343551244804717 2306823650378831716801769)
                      ·
                        rfl

theorem cell23_4492523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 3].length) (baseStart_4492523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492523 prefixEnd_4492523 := by exact prefixLift 4492523
  have htrace : WordTrace (prefixWord ++ tailWord_4492523) baseStart_4492523 baseEnd_4492523 := by
    simpa [prefixWord, tailWord_4492523, baseEnd_4492523] using wordTrace_append hprefix tailTrace_4492523
  have hstable : (prefixWord ++ tailWord_4492523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492523).length < 2 ^ (prefixWord ++ tailWord_4492523).sum := by decide
  have hdescent : baseEnd_4492523 < baseStart_4492523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492549 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_4492549 : Nat := 118140960795 + 4492549 * 2 ^ 59
def prefixEnd_4492549 : Nat := 4983230072969 + 3 ^ 40 * 4492549 * 2
def baseEnd_4492549 : Nat := 2306837000875848615076649

theorem tailTrace_4492549 : CollatzResearch.WordTrace tailWord_4492549 prefixEnd_4492549 2306837000875848615076649 := by
  unfold tailWord_4492549
  simp only [CollatzResearch.WordTrace]
  refine ⟨163856723401269714129120701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109237815600846476086080467 163856723401269714129120701)
  ·
    refine ⟨61446271275476142798420263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163856723401269714129120701 61446271275476142798420263)
    ·
      refine ⟨92169406913214214197630395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61446271275476142798420263 92169406913214214197630395)
      ·
        refine ⟨138254110369821321296445593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92169406913214214197630395 138254110369821321296445593)
        ·
          refine ⟨103690582777365990972334195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138254110369821321296445593 103690582777365990972334195)
          ·
            refine ⟨155535874166048986458501293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103690582777365990972334195 155535874166048986458501293)
            ·
              refine ⟨58325952812268369921937985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155535874166048986458501293 58325952812268369921937985)
              ·
                refine ⟨43744464609201277441453489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58325952812268369921937985 43744464609201277441453489)
                ·
                  refine ⟨32808348456900958081090117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43744464609201277441453489 32808348456900958081090117)
                  ·
                    refine ⟨6151565335668929640204397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32808348456900958081090117 6151565335668929640204397)
                    ·
                      refine ⟨2306837000875848615076649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151565335668929640204397 2306837000875848615076649)
                      ·
                        rfl

theorem cell23_4492549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_4492549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492549 prefixEnd_4492549 := by exact prefixLift 4492549
  have htrace : WordTrace (prefixWord ++ tailWord_4492549) baseStart_4492549 baseEnd_4492549 := by
    simpa [prefixWord, tailWord_4492549, baseEnd_4492549] using wordTrace_append hprefix tailTrace_4492549
  have hstable : (prefixWord ++ tailWord_4492549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492549).length < 2 ^ (prefixWord ++ tailWord_4492549).sum := by decide
  have hdescent : baseEnd_4492549 < baseStart_4492549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492574 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4492574 : Nat := 118140960795 + 4492574 * 2 ^ 59
def prefixEnd_4492574 : Nat := 4983230072969 + 3 ^ 40 * 4492574 * 2
def baseEnd_4492574 : Nat := 2306849837892211017264035

theorem tailTrace_4492574 : CollatzResearch.WordTrace tailWord_4492574 prefixEnd_4492574 2306849837892211017264035 := by
  unfold tailWord_4492574
  simp only [CollatzResearch.WordTrace]
  refine ⟨20482204403272392924847597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109238423484119428932520517 20482204403272392924847597)
  ·
    refine ⟨7680826651227147346817849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20482204403272392924847597 7680826651227147346817849)
    ·
      refine ⟨5760619988420360510113387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7680826651227147346817849 5760619988420360510113387)
      ·
        refine ⟨8640929982630540765170081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760619988420360510113387 8640929982630540765170081)
        ·
          refine ⟨6480697486972905573877561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640929982630540765170081 6480697486972905573877561)
          ·
            refine ⟨4860523115229679180408171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480697486972905573877561 4860523115229679180408171)
            ·
              refine ⟨7290784672844518770612257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860523115229679180408171 7290784672844518770612257)
              ·
                refine ⟨5468088504633389077959193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7290784672844518770612257 5468088504633389077959193)
                ·
                  refine ⟨4101066378475041808469395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468088504633389077959193 4101066378475041808469395)
                  ·
                    refine ⟨6151599567712562712704093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101066378475041808469395 6151599567712562712704093)
                    ·
                      refine ⟨2306849837892211017264035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151599567712562712704093 2306849837892211017264035)
                      ·
                        rfl

theorem cell23_4492574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4492574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492574 prefixEnd_4492574 := by exact prefixLift 4492574
  have htrace : WordTrace (prefixWord ++ tailWord_4492574) baseStart_4492574 baseEnd_4492574 := by
    simpa [prefixWord, tailWord_4492574, baseEnd_4492574] using wordTrace_append hprefix tailTrace_4492574
  have hstable : (prefixWord ++ tailWord_4492574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492574).length < 2 ^ (prefixWord ++ tailWord_4492574).sum := by decide
  have hdescent : baseEnd_4492574 < baseStart_4492574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492586 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_4492586 : Nat := 118140960795 + 4492586 * 2 ^ 59
def prefixEnd_4492586 : Nat := 4983230072969 + 3 ^ 40 * 4492586 * 2
def baseEnd_4492586 : Nat := 256317333295562774479331

theorem tailTrace_4492586 : CollatzResearch.WordTrace tailWord_4492586 prefixEnd_4492586 256317333295562774479331 := by
  unfold tailWord_4492586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40964518225533917362054403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109238715268090446298811741 40964518225533917362054403)
  ·
    refine ⟨61446777338300876043081605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40964518225533917362054403 61446777338300876043081605)
    ·
      refine ⟨11521270750931414258077801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61446777338300876043081605 11521270750931414258077801)
      ·
        refine ⟨8640953063198560693558351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11521270750931414258077801 8640953063198560693558351)
        ·
          refine ⟨12961429594797841040337527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640953063198560693558351 12961429594797841040337527)
          ·
            refine ⟨19442144392196761560506291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12961429594797841040337527 19442144392196761560506291)
            ·
              refine ⟨29163216588295142340759437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19442144392196761560506291 29163216588295142340759437)
              ·
                refine ⟨10936206220610678377784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29163216588295142340759437 10936206220610678377784789)
                ·
                  refine ⟨256317333295562774479331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10936206220610678377784789 256317333295562774479331)
                  ·
                    rfl

theorem cell23_4492586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_4492586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492586 prefixEnd_4492586 := by exact prefixLift 4492586
  have htrace : WordTrace (prefixWord ++ tailWord_4492586) baseStart_4492586 baseEnd_4492586 := by
    simpa [prefixWord, tailWord_4492586, baseEnd_4492586] using wordTrace_append hprefix tailTrace_4492586
  have hstable : (prefixWord ++ tailWord_4492586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492586).length < 2 ^ (prefixWord ++ tailWord_4492586).sum := by decide
  have hdescent : baseEnd_4492586 < baseStart_4492586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492597 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_4492597 : Nat := 118140960795 + 4492597 * 2 ^ 59
def prefixEnd_4492597 : Nat := 4983230072969 + 3 ^ 40 * 4492597 * 2
def baseEnd_4492597 : Nat := 2306861647947264427276429

theorem tailTrace_4492597 : CollatzResearch.WordTrace tailWord_4492597 prefixEnd_4492597 2306861647947264427276429 := by
  unfold tailWord_4492597
  simp only [CollatzResearch.WordTrace]
  refine ⟨163858474105095818326868045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109238982736730545551245363 163858474105095818326868045)
  ·
    refine ⟨61446927789410931872575517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163858474105095818326868045 61446927789410931872575517)
    ·
      refine ⟨23042597921029099452215819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61446927789410931872575517 23042597921029099452215819)
      ·
        refine ⟨34563896881543649178323729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23042597921029099452215819 34563896881543649178323729)
        ·
          refine ⟨25922922661157736883742797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34563896881543649178323729 25922922661157736883742797)
          ·
            refine ⟨9721095997934151331403549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25922922661157736883742797 9721095997934151331403549)
            ·
              refine ⟨3645410999225306749276331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9721095997934151331403549 3645410999225306749276331)
              ·
                refine ⟨5468116498837960123914497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645410999225306749276331 5468116498837960123914497)
                ·
                  refine ⟨4101087374128470092935873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468116498837960123914497 4101087374128470092935873)
                  ·
                    refine ⟨3075815530596352569701905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4101087374128470092935873 3075815530596352569701905)
                    ·
                      refine ⟨2306861647947264427276429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075815530596352569701905 2306861647947264427276429)
                      ·
                        rfl

theorem cell23_4492597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_4492597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492597 prefixEnd_4492597 := by exact prefixLift 4492597
  have htrace : WordTrace (prefixWord ++ tailWord_4492597) baseStart_4492597 baseEnd_4492597 := by
    simpa [prefixWord, tailWord_4492597, baseEnd_4492597] using wordTrace_append hprefix tailTrace_4492597
  have hstable : (prefixWord ++ tailWord_4492597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492597).length < 2 ^ (prefixWord ++ tailWord_4492597).sum := by decide
  have hdescent : baseEnd_4492597 < baseStart_4492597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492637 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 7]
def baseStart_4492637 : Nat := 118140960795 + 4492637 * 2 ^ 59
def prefixEnd_4492637 : Nat := 4983230072969 + 3 ^ 40 * 4492637 * 2
def baseEnd_4492637 : Nat := 256320243019271585641805

theorem tailTrace_4492637 : CollatzResearch.WordTrace tailWord_4492637 prefixEnd_4492637 256320243019271585641805 := by
  unfold tailWord_4492637
  simp only [CollatzResearch.WordTrace]
  refine ⟨163859933024950905158324165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109239955349967270105549443 163859933024950905158324165)
  ·
    refine ⟨30723737442178294717185781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163859933024950905158324165 30723737442178294717185781)
    ·
      refine ⟨2880350385204215129736167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30723737442178294717185781 2880350385204215129736167)
      ·
        refine ⟨4320525577806322694604251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880350385204215129736167 4320525577806322694604251)
        ·
          refine ⟨6480788366709484041906377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320525577806322694604251 6480788366709484041906377)
          ·
            refine ⟨4860591275032113031429783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480788366709484041906377 4860591275032113031429783)
            ·
              refine ⟨7290886912548169547144675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860591275032113031429783 7290886912548169547144675)
              ·
                refine ⟨10936330368822254320717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290886912548169547144675 10936330368822254320717013)
                ·
                  refine ⟨256320243019271585641805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10936330368822254320717013 256320243019271585641805)
                  ·
                    rfl

theorem cell23_4492637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_4492637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492637 prefixEnd_4492637 := by exact prefixLift 4492637
  have htrace : WordTrace (prefixWord ++ tailWord_4492637) baseStart_4492637 baseEnd_4492637 := by
    simpa [prefixWord, tailWord_4492637, baseEnd_4492637] using wordTrace_append hprefix tailTrace_4492637
  have hstable : (prefixWord ++ tailWord_4492637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492637).length < 2 ^ (prefixWord ++ tailWord_4492637).sum := by decide
  have hdescent : baseEnd_4492637 < baseStart_4492637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492649 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_4492649 : Nat := 118140960795 + 4492649 * 2 ^ 59
def prefixEnd_4492649 : Nat := 4983230072969 + 3 ^ 40 * 4492649 * 2
def baseEnd_4492649 : Nat := 2306888348941298223826189

theorem tailTrace_4492649 : CollatzResearch.WordTrace tailWord_4492649 prefixEnd_4492649 2306888348941298223826189 := by
  unfold tailWord_4492649
  simp only [CollatzResearch.WordTrace]
  refine ⟨163860370700907431207761001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109240247133938287471840667 163860370700907431207761001)
  ·
    refine ⟨122895278025680573405820751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163860370700907431207761001 122895278025680573405820751)
    ·
      refine ⟨184342917038520860108731127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122895278025680573405820751 184342917038520860108731127)
      ·
        refine ⟨276514375557781290163096691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184342917038520860108731127 276514375557781290163096691)
        ·
          refine ⟨414771563336671935244645037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276514375557781290163096691 414771563336671935244645037)
          ·
            refine ⟨155539336251251975716741889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414771563336671935244645037 155539336251251975716741889)
            ·
              refine ⟨116654502188438981787556417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155539336251251975716741889 116654502188438981787556417)
              ·
                refine ⟨87490876641329236340667313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116654502188438981787556417 87490876641329236340667313)
                ·
                  refine ⟨65618157480996927255500485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87490876641329236340667313 65618157480996927255500485)
                  ·
                    refine ⟨12303404527686923860406341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65618157480996927255500485 12303404527686923860406341)
                    ·
                      refine ⟨2306888348941298223826189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12303404527686923860406341 2306888348941298223826189)
                      ·
                        rfl

theorem cell23_4492649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_4492649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492649 prefixEnd_4492649 := by exact prefixLift 4492649
  have htrace : WordTrace (prefixWord ++ tailWord_4492649) baseStart_4492649 baseEnd_4492649 := by
    simpa [prefixWord, tailWord_4492649, baseEnd_4492649] using wordTrace_append hprefix tailTrace_4492649
  have hstable : (prefixWord ++ tailWord_4492649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492649).length < 2 ^ (prefixWord ++ tailWord_4492649).sum := by decide
  have hdescent : baseEnd_4492649 < baseStart_4492649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492656 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_4492656 : Nat := 118140960795 + 4492656 * 2 ^ 59
def prefixEnd_4492656 : Nat := 4983230072969 + 3 ^ 40 * 4492656 * 2
def baseEnd_4492656 : Nat := 2306891943305879696438657

theorem tailTrace_4492656 : CollatzResearch.WordTrace tailWord_4492656 prefixEnd_4492656 2306891943305879696438657 := by
  unfold tailWord_4492656
  simp only [CollatzResearch.WordTrace]
  refine ⟨81930313005941035701632911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109240417341254714268843881 81930313005941035701632911)
  ·
    refine ⟨122895469508911553552449367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81930313005941035701632911 122895469508911553552449367)
    ·
      refine ⟨184343204263367330328674051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122895469508911553552449367 184343204263367330328674051)
      ·
        refine ⟨276514806395050995493011077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184343204263367330328674051 276514806395050995493011077)
        ·
          refine ⟨51846526199072061654939577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276514806395050995493011077 51846526199072061654939577)
          ·
            refine ⟨38884894649304046241204683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51846526199072061654939577 38884894649304046241204683)
            ·
              refine ⟨58327341973956069361807025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38884894649304046241204683 58327341973956069361807025)
              ·
                refine ⟨43745506480467052021355269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58327341973956069361807025 43745506480467052021355269)
                ·
                  refine ⟨8202282465087572254004113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43745506480467052021355269 8202282465087572254004113)
                  ·
                    refine ⟨6151711848815679190503085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8202282465087572254004113 6151711848815679190503085)
                    ·
                      refine ⟨2306891943305879696438657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151711848815679190503085 2306891943305879696438657)
                      ·
                        rfl

theorem cell23_4492656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_4492656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492656 prefixEnd_4492656 := by exact prefixLift 4492656
  have htrace : WordTrace (prefixWord ++ tailWord_4492656) baseStart_4492656 baseEnd_4492656 := by
    simpa [prefixWord, tailWord_4492656, baseEnd_4492656] using wordTrace_append hprefix tailTrace_4492656
  have hstable : (prefixWord ++ tailWord_4492656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492656).length < 2 ^ (prefixWord ++ tailWord_4492656).sum := by decide
  have hdescent : baseEnd_4492656 < baseStart_4492656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492697 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 1, 4]
def baseStart_4492697 : Nat := 118140960795 + 4492697 * 2 ^ 59
def prefixEnd_4492697 : Nat := 4983230072969 + 3 ^ 40 * 4492697 * 2
def baseEnd_4492697 : Nat := 768970998670904678675323

theorem tailTrace_4492697 : CollatzResearch.WordTrace tailWord_4492697 prefixEnd_4492697 768970998670904678675323 := by
  unfold tailWord_4492697
  simp only [CollatzResearch.WordTrace]
  refine ⟨163862121404733535405508345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109241414269822356937005563 163862121404733535405508345)
  ·
    refine ⟨122896591053550151554131259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163862121404733535405508345 122896591053550151554131259)
    ·
      refine ⟨184344886580325227331196889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122896591053550151554131259 184344886580325227331196889)
      ·
        refine ⟨138258664935243920498397667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184344886580325227331196889 138258664935243920498397667)
        ·
          refine ⟨207387997402865880747596501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138258664935243920498397667 207387997402865880747596501)
          ·
            refine ⟨4860656189129669080021793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 207387997402865880747596501 4860656189129669080021793)
            ·
              refine ⟨3645492141847251810016345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4860656189129669080021793 3645492141847251810016345)
              ·
                refine ⟨2734119106385438857512259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645492141847251810016345 2734119106385438857512259)
                ·
                  refine ⟨4101178659578158286268389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734119106385438857512259 4101178659578158286268389)
                  ·
                    refine ⟨768970998670904678675323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4101178659578158286268389 768970998670904678675323)
                    ·
                      rfl

theorem cell23_4492697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_4492697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492697 prefixEnd_4492697 := by exact prefixLift 4492697
  have htrace : WordTrace (prefixWord ++ tailWord_4492697) baseStart_4492697 baseEnd_4492697 := by
    simpa [prefixWord, tailWord_4492697, baseEnd_4492697] using wordTrace_append hprefix tailTrace_4492697
  have hstable : (prefixWord ++ tailWord_4492697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492697).length < 2 ^ (prefixWord ++ tailWord_4492697).sum := by decide
  have hdescent : baseEnd_4492697 < baseStart_4492697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492736 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_4492736 : Nat := 118140960795 + 4492736 * 2 ^ 59
def prefixEnd_4492736 : Nat := 4983230072969 + 3 ^ 40 * 4492736 * 2
def baseEnd_4492736 : Nat := 768977673919413127812763

theorem tailTrace_4492736 : CollatzResearch.WordTrace tailWord_4492736 prefixEnd_4492736 768977673919413127812763 := by
  unfold tailWord_4492736
  simp only [CollatzResearch.WordTrace]
  refine ⟨81931771925796122533089031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109242362567728163377452041 81931771925796122533089031)
  ·
    refine ⟨122897657888694183799633547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81931771925796122533089031 122897657888694183799633547)
    ·
      refine ⟨184346486833041275699450321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122897657888694183799633547 184346486833041275699450321)
      ·
        refine ⟨138259865124780956774587741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184346486833041275699450321 138259865124780956774587741)
        ·
          refine ⟨51847449421792858790470403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138259865124780956774587741 51847449421792858790470403)
          ·
            refine ⟨77771174132689288185705605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51847449421792858790470403 77771174132689288185705605)
            ·
              refine ⟨14582095149879241534819801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77771174132689288185705605 14582095149879241534819801)
              ·
                refine ⟨10936571362409431151114851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14582095149879241534819801 10936571362409431151114851)
                ·
                  refine ⟨16404857043614146726672277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10936571362409431151114851 16404857043614146726672277)
                  ·
                    refine ⟨768977673919413127812763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16404857043614146726672277 768977673919413127812763)
                    ·
                      rfl

theorem cell23_4492736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_4492736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492736 prefixEnd_4492736 := by exact prefixLift 4492736
  have htrace : WordTrace (prefixWord ++ tailWord_4492736) baseStart_4492736 baseEnd_4492736 := by
    simpa [prefixWord, tailWord_4492736, baseEnd_4492736] using wordTrace_append hprefix tailTrace_4492736
  have hstable : (prefixWord ++ tailWord_4492736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492736).length < 2 ^ (prefixWord ++ tailWord_4492736).sum := by decide
  have hdescent : baseEnd_4492736 < baseStart_4492736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492740 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4492740 : Nat := 118140960795 + 4492740 * 2 ^ 59
def prefixEnd_4492740 : Nat := 4983230072969 + 3 ^ 40 * 4492740 * 2
def baseEnd_4492740 : Nat := 768978358560285789262757

theorem tailTrace_4492740 : CollatzResearch.WordTrace tailWord_4492740 prefixEnd_4492740 768978358560285789262757 := by
  unfold tailWord_4492740
  simp only [CollatzResearch.WordTrace]
  refine ⟨81931844871788876874661837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109242459829051835832882449 81931844871788876874661837)
  ·
    refine ⟨30724441826920828827998189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81931844871788876874661837 30724441826920828827998189)
    ·
      refine ⟨11521665685095310810499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30724441826920828827998189 11521665685095310810499321)
      ·
        refine ⟨8641249263821483107874491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11521665685095310810499321 8641249263821483107874491)
        ·
          refine ⟨12961873895732224661811737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8641249263821483107874491 12961873895732224661811737)
          ·
            refine ⟨9721405421799168496358803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12961873895732224661811737 9721405421799168496358803)
            ·
              refine ⟨14582108132698752744538205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721405421799168496358803 14582108132698752744538205)
              ·
                refine ⟨5468290549762032279201827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14582108132698752744538205 5468290549762032279201827)
                ·
                  refine ⟨8202435824643048418802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5468290549762032279201827 8202435824643048418802741)
                  ·
                    refine ⟨768978358560285789262757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8202435824643048418802741 768978358560285789262757)
                    ·
                      rfl

theorem cell23_4492740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4492740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492740 prefixEnd_4492740 := by exact prefixLift 4492740
  have htrace : WordTrace (prefixWord ++ tailWord_4492740) baseStart_4492740 baseEnd_4492740 := by
    simpa [prefixWord, tailWord_4492740, baseEnd_4492740] using wordTrace_append hprefix tailTrace_4492740
  have hstable : (prefixWord ++ tailWord_4492740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492740).length < 2 ^ (prefixWord ++ tailWord_4492740).sum := by decide
  have hdescent : baseEnd_4492740 < baseStart_4492740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492743 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_4492743 : Nat := 118140960795 + 4492743 * 2 ^ 59
def prefixEnd_4492743 : Nat := 4983230072969 + 3 ^ 40 * 4492743 * 2
def baseEnd_4492743 : Nat := 2306936616122820856050757

theorem tailTrace_4492743 : CollatzResearch.WordTrace tailWord_4492743 prefixEnd_4492743 2306936616122820856050757 := by
  unfold tailWord_4492743
  simp only [CollatzResearch.WordTrace]
  refine ⟨163863799162566885261682883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109242532775044590174455255 163863799162566885261682883)
  ·
    refine ⟨245795698743850327892524325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163863799162566885261682883 245795698743850327892524325)
    ·
      refine ⟨46086693514471936479848311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245795698743850327892524325 46086693514471936479848311)
      ·
        refine ⟨69130040271707904719772467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46086693514471936479848311 69130040271707904719772467)
        ·
          refine ⟨103695060407561857079658701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69130040271707904719772467 103695060407561857079658701)
          ·
            refine ⟨38885647652835696404872013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103695060407561857079658701 38885647652835696404872013)
            ·
              refine ⟨14582117869813386151827005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38885647652835696404872013 14582117869813386151827005)
              ·
                refine ⟨5468294201180019806935127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14582117869813386151827005 5468294201180019806935127)
                ·
                  refine ⟨8202441301770029710402691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5468294201180019806935127 8202441301770029710402691)
                  ·
                    refine ⟨12303661952655044565604037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8202441301770029710402691 12303661952655044565604037)
                    ·
                      refine ⟨2306936616122820856050757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12303661952655044565604037 2306936616122820856050757)
                      ·
                        rfl

theorem cell23_4492743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_4492743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492743 prefixEnd_4492743 := by exact prefixLift 4492743
  have htrace : WordTrace (prefixWord ++ tailWord_4492743) baseStart_4492743 baseEnd_4492743 := by
    simpa [prefixWord, tailWord_4492743, baseEnd_4492743] using wordTrace_append hprefix tailTrace_4492743
  have hstable : (prefixWord ++ tailWord_4492743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492743).length < 2 ^ (prefixWord ++ tailWord_4492743).sum := by decide
  have hdescent : baseEnd_4492743 < baseStart_4492743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492760 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_4492760 : Nat := 118140960795 + 4492760 * 2 ^ 59
def prefixEnd_4492760 : Nat := 4983230072969 + 3 ^ 40 * 4492760 * 2
def baseEnd_4492760 : Nat := 2306945345293947289538179

theorem tailTrace_4492760 : CollatzResearch.WordTrace tailWord_4492760 prefixEnd_4492760 2306945345293947289538179 := by
  unfold tailWord_4492760
  simp only [CollatzResearch.WordTrace]
  refine ⟨81932209601752648582525867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109242946135670198110034489 81932209601752648582525867)
  ·
    refine ⟨122898314402628972873788801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81932209601752648582525867 122898314402628972873788801)
    ·
      refine ⟨92173735801971729655341601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122898314402628972873788801 92173735801971729655341601)
      ·
        refine ⟨69130301851478797241506201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92173735801971729655341601 69130301851478797241506201)
        ·
          refine ⟨51847726388609097931129651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69130301851478797241506201 51847726388609097931129651)
          ·
            refine ⟨77771589582913646896694477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51847726388609097931129651 77771589582913646896694477)
            ·
              refine ⟨29164346093592617586260429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77771589582913646896694477 29164346093592617586260429)
              ·
                refine ⟨10936629785097231594847661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29164346093592617586260429 10936629785097231594847661)
                ·
                  refine ⟨4101236169411461848067873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10936629785097231594847661 4101236169411461848067873)
                  ·
                    refine ⟨3075927127058596386050905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4101236169411461848067873 3075927127058596386050905)
                    ·
                      refine ⟨2306945345293947289538179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075927127058596386050905 2306945345293947289538179)
                      ·
                        rfl

theorem cell23_4492760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_4492760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492760 prefixEnd_4492760 := by exact prefixLift 4492760
  have htrace : WordTrace (prefixWord ++ tailWord_4492760) baseStart_4492760 baseEnd_4492760 := by
    simpa [prefixWord, tailWord_4492760, baseEnd_4492760] using wordTrace_append hprefix tailTrace_4492760
  have hstable : (prefixWord ++ tailWord_4492760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492760).length < 2 ^ (prefixWord ++ tailWord_4492760).sum := by decide
  have hdescent : baseEnd_4492760 < baseStart_4492760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492773 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4492773 : Nat := 118140960795 + 4492773 * 2 ^ 59
def prefixEnd_4492773 : Nat := 4983230072969 + 3 ^ 40 * 4492773 * 2
def baseEnd_4492773 : Nat := 2306952020542455738675619

theorem tailTrace_4492773 : CollatzResearch.WordTrace tailWord_4492773 prefixEnd_4492773 2306952020542455738675619 := by
  unfold tailWord_4492773
  simp only [CollatzResearch.WordTrace]
  refine ⟨163864893352458200385274973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109243262234972133590183315 163864893352458200385274973)
  ·
    refine ⟨61449335007171825144478115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163864893352458200385274973 61449335007171825144478115)
    ·
      refine ⟨92174002510757737716717173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61449335007171825144478115 92174002510757737716717173)
      ·
        refine ⟨8641312735383537910942235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92174002510757737716717173 8641312735383537910942235)
        ·
          refine ⟨12961969103075306866413353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8641312735383537910942235 12961969103075306866413353)
          ·
            refine ⟨9721476827306480149810015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12961969103075306866413353 9721476827306480149810015)
            ·
              refine ⟨14582215240959720224715023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721476827306480149810015 14582215240959720224715023)
              ·
                refine ⟨21873322861439580337072535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582215240959720224715023 21873322861439580337072535)
                ·
                  refine ⟨32809984292159370505608803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21873322861439580337072535 32809984292159370505608803)
                  ·
                    refine ⟨49214976438239055758413205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32809984292159370505608803 49214976438239055758413205)
                    ·
                      refine ⟨2306952020542455738675619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49214976438239055758413205 2306952020542455738675619)
                      ·
                        rfl

theorem cell23_4492773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4492773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492773 prefixEnd_4492773 := by exact prefixLift 4492773
  have htrace : WordTrace (prefixWord ++ tailWord_4492773) baseStart_4492773 baseEnd_4492773 := by
    simpa [prefixWord, tailWord_4492773, baseEnd_4492773] using wordTrace_append hprefix tailTrace_4492773
  have hstable : (prefixWord ++ tailWord_4492773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492773).length < 2 ^ (prefixWord ++ tailWord_4492773).sum := by decide
  have hdescent : baseEnd_4492773 < baseStart_4492773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492810 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_4492810 : Nat := 118140960795 + 4492810 * 2 ^ 59
def prefixEnd_4492810 : Nat := 4983230072969 + 3 ^ 40 * 4492810 * 2
def baseEnd_4492810 : Nat := 2306971019326672093912949

theorem tailTrace_4492810 : CollatzResearch.WordTrace tailWord_4492810 prefixEnd_4492810 2306971019326672093912949 := by
  unfold tailWord_4492810
  simp only [CollatzResearch.WordTrace]
  refine ⟨40966560713331038926092971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109244161902216103802914589 40966560713331038926092971)
  ·
    refine ⟨61449841069996558389139457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40966560713331038926092971 61449841069996558389139457)
    ·
      refine ⟨46087380802497418791854593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61449841069996558389139457 46087380802497418791854593)
      ·
        refine ⟨34565535601873064093890945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46087380802497418791854593 34565535601873064093890945)
        ·
          refine ⟨25924151701404798070418209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34565535601873064093890945 25924151701404798070418209)
          ·
            refine ⟨19443113776053598552813657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25924151701404798070418209 19443113776053598552813657)
            ·
              refine ⟨14582335332040198914610243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443113776053598552813657 14582335332040198914610243)
              ·
                refine ⟨21873502998060298371915365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582335332040198914610243 21873502998060298371915365)
                ·
                  refine ⟨4101281812136305944734131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21873502998060298371915365 4101281812136305944734131)
                  ·
                    refine ⟨6151922718204458917101197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101281812136305944734131 6151922718204458917101197)
                    ·
                      refine ⟨2306971019326672093912949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6151922718204458917101197 2306971019326672093912949)
                      ·
                        rfl

theorem cell23_4492810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_4492810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492810 prefixEnd_4492810 := by exact prefixLift 4492810
  have htrace : WordTrace (prefixWord ++ tailWord_4492810) baseStart_4492810 baseEnd_4492810 := by
    simpa [prefixWord, tailWord_4492810, baseEnd_4492810] using wordTrace_append hprefix tailTrace_4492810
  have hstable : (prefixWord ++ tailWord_4492810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492810).length < 2 ^ (prefixWord ++ tailWord_4492810).sum := by decide
  have hdescent : baseEnd_4492810 < baseStart_4492810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492811 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 1, 2, 2]
def baseStart_4492811 : Nat := 118140960795 + 4492811 * 2 ^ 59
def prefixEnd_4492811 : Nat := 4983230072969 + 3 ^ 40 * 4492811 * 2
def baseEnd_4492811 : Nat := 2306971532807326590000445

theorem tailTrace_4492811 : CollatzResearch.WordTrace tailWord_4492811 prefixEnd_4492811 2306971532807326590000445 := by
  unfold tailWord_4492811
  simp only [CollatzResearch.WordTrace]
  refine ⟨163866279326320532875158287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109244186217547021916772191 163866279326320532875158287)
  ·
    refine ⟨245799418989480799312737431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163866279326320532875158287 245799418989480799312737431)
    ·
      refine ⟨368699128484221198969106147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245799418989480799312737431 368699128484221198969106147)
      ·
        refine ⟨553048692726331798453659221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368699128484221198969106147 553048692726331798453659221)
        ·
          refine ⟨6481039367886700763128819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 553048692726331798453659221 6481039367886700763128819)
          ·
            refine ⟨9721559051830051144693229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481039367886700763128819 9721559051830051144693229)
            ·
              refine ⟨3645584644436269179259961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9721559051830051144693229 3645584644436269179259961)
              ·
                refine ⟨2734188483327201884444971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645584644436269179259961 2734188483327201884444971)
                ·
                  refine ⟨4101282724990802826667457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734188483327201884444971 4101282724990802826667457)
                  ·
                    refine ⟨3075962043743102120000593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4101282724990802826667457 3075962043743102120000593)
                    ·
                      refine ⟨2306971532807326590000445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3075962043743102120000593 2306971532807326590000445)
                      ·
                        rfl

theorem cell23_4492811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 2, 2].length) (baseStart_4492811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492811 prefixEnd_4492811 := by exact prefixLift 4492811
  have htrace : WordTrace (prefixWord ++ tailWord_4492811) baseStart_4492811 baseEnd_4492811 := by
    simpa [prefixWord, tailWord_4492811, baseEnd_4492811] using wordTrace_append hprefix tailTrace_4492811
  have hstable : (prefixWord ++ tailWord_4492811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492811).length < 2 ^ (prefixWord ++ tailWord_4492811).sum := by decide
  have hdescent : baseEnd_4492811 < baseStart_4492811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492826 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_4492826 : Nat := 118140960795 + 4492826 * 2 ^ 59
def prefixEnd_4492826 : Nat := 4983230072969 + 3 ^ 40 * 4492826 * 2
def baseEnd_4492826 : Nat := 768993078339048010437625

theorem tailTrace_4492826 : CollatzResearch.WordTrace tailWord_4492826 prefixEnd_4492826 768993078339048010437625 := by
  unfold tailWord_4492826
  simp only [CollatzResearch.WordTrace]
  refine ⟨40966706605316547609238583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109244550947510793624636221 40966706605316547609238583)
  ·
    refine ⟨61450059907974821413857875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40966706605316547609238583 61450059907974821413857875)
    ·
      refine ⟨92175089861962232120786813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61450059907974821413857875 92175089861962232120786813)
      ·
        refine ⟨34565658698235837045295055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92175089861962232120786813 34565658698235837045295055)
        ·
          refine ⟨51848488047353755567942583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34565658698235837045295055 51848488047353755567942583)
          ·
            refine ⟨77772732071030633351913875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51848488047353755567942583 77772732071030633351913875)
            ·
              refine ⟨116659098106545950027870813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77772732071030633351913875 116659098106545950027870813)
              ·
                refine ⟨43747161789954731260451555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116659098106545950027870813 43747161789954731260451555)
                ·
                  refine ⟨65620742684932096890677333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43747161789954731260451555 65620742684932096890677333)
                  ·
                    refine ⟨768993078339048010437625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65620742684932096890677333 768993078339048010437625)
                    ·
                      rfl

theorem cell23_4492826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_4492826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492826 prefixEnd_4492826 := by exact prefixLift 4492826
  have htrace : WordTrace (prefixWord ++ tailWord_4492826) baseStart_4492826 baseEnd_4492826 := by
    simpa [prefixWord, tailWord_4492826, baseEnd_4492826] using wordTrace_append hprefix tailTrace_4492826
  have hstable : (prefixWord ++ tailWord_4492826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492826).length < 2 ^ (prefixWord ++ tailWord_4492826).sum := by decide
  have hdescent : baseEnd_4492826 < baseStart_4492826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492853 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4492853 : Nat := 118140960795 + 4492853 * 2 ^ 59
def prefixEnd_4492853 : Nat := 4983230072969 + 3 ^ 40 * 4492853 * 2
def baseEnd_4492853 : Nat := 2306993098994815425675251

theorem tailTrace_4492853 : CollatzResearch.WordTrace tailWord_4492853 prefixEnd_4492853 2306993098994815425675251 := by
  unfold tailWord_4492853
  simp only [CollatzResearch.WordTrace]
  refine ⟨163867811192168374048187213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109245207461445582698791475 163867811192168374048187213)
  ·
    refine ⟨61450429197063140268070205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163867811192168374048187213 61450429197063140268070205)
    ·
      refine ⟨23043910948898677600526327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61450429197063140268070205 23043910948898677600526327)
      ·
        refine ⟨34565866423348016400789491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23043910948898677600526327 34565866423348016400789491)
        ·
          refine ⟨51848799635022024601184237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34565866423348016400789491 51848799635022024601184237)
          ·
            refine ⟨19443299863133259225444089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51848799635022024601184237 19443299863133259225444089)
            ·
              refine ⟨14582474897349944419083067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443299863133259225444089 14582474897349944419083067)
              ·
                refine ⟨21873712346024916628624601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582474897349944419083067 21873712346024916628624601)
                ·
                  refine ⟨16405284259518687471468451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21873712346024916628624601 16405284259518687471468451)
                  ·
                    refine ⟨24607926389278031207202677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16405284259518687471468451 24607926389278031207202677)
                    ·
                      refine ⟨2306993098994815425675251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24607926389278031207202677 2306993098994815425675251)
                      ·
                        rfl

theorem cell23_4492853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4492853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492853 prefixEnd_4492853 := by exact prefixLift 4492853
  have htrace : WordTrace (prefixWord ++ tailWord_4492853) baseStart_4492853 baseEnd_4492853 := by
    simpa [prefixWord, tailWord_4492853, baseEnd_4492853] using wordTrace_append hprefix tailTrace_4492853
  have hstable : (prefixWord ++ tailWord_4492853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492853).length < 2 ^ (prefixWord ++ tailWord_4492853).sum := by decide
  have hdescent : baseEnd_4492853 < baseStart_4492853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492923 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4]
def baseStart_4492923 : Nat := 118140960795 + 4492923 * 2 ^ 59
def prefixEnd_4492923 : Nat := 4983230072969 + 3 ^ 40 * 4492923 * 2
def baseEnd_4492923 : Nat := 2307029042640630151799929

theorem tailTrace_4492923 : CollatzResearch.WordTrace tailWord_4492923 prefixEnd_4492923 2307029042640630151799929 := by
  unfold tailWord_4492923
  simp only [CollatzResearch.WordTrace]
  refine ⟨163870364301914776003235423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109246909534609850668823615 163870364301914776003235423)
  ·
    refine ⟨245805546452872164004853135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163870364301914776003235423 245805546452872164004853135)
    ·
      refine ⟨368708319679308246007279703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245805546452872164004853135 368708319679308246007279703)
      ·
        refine ⟨553062479518962369010919555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368708319679308246007279703 553062479518962369010919555)
        ·
          refine ⟨829593719278443553516379333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553062479518962369010919555 829593719278443553516379333)
          ·
            refine ⟨155548822364708166284321125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 829593719278443553516379333 155548822364708166284321125)
            ·
              refine ⟨29165404193382781178310211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155548822364708166284321125 29165404193382781178310211)
              ·
                refine ⟨43748106290074171767465317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29165404193382781178310211 43748106290074171767465317)
                ·
                  refine ⟨8202769929388907206399747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43748106290074171767465317 8202769929388907206399747)
                  ·
                    refine ⟨12304154894083360809599621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8202769929388907206399747 12304154894083360809599621)
                    ·
                      refine ⟨2307029042640630151799929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12304154894083360809599621 2307029042640630151799929)
                      ·
                        rfl

theorem cell23_4492923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_4492923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492923 prefixEnd_4492923 := by exact prefixLift 4492923
  have htrace : WordTrace (prefixWord ++ tailWord_4492923) baseStart_4492923 baseEnd_4492923 := by
    simpa [prefixWord, tailWord_4492923, baseEnd_4492923] using wordTrace_append hprefix tailTrace_4492923
  have hstable : (prefixWord ++ tailWord_4492923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492923).length < 2 ^ (prefixWord ++ tailWord_4492923).sum := by decide
  have hdescent : baseEnd_4492923 < baseStart_4492923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492940 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_4492940 : Nat := 118140960795 + 4492940 * 2 ^ 59
def prefixEnd_4492940 : Nat := 4983230072969 + 3 ^ 40 * 4492940 * 2
def baseEnd_4492940 : Nat := 2307037771811756585287351

theorem tailTrace_4492940 : CollatzResearch.WordTrace tailWord_4492940 prefixEnd_4492940 2307037771811756585287351 := by
  unfold tailWord_4492940
  simp only [CollatzResearch.WordTrace]
  refine ⟨81935492171426593953302137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109247322895235458604402849 81935492171426593953302137)
  ·
    refine ⟨61451619128569945464976603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81935492171426593953302137 61451619128569945464976603)
    ·
      refine ⟨92177428692854918197464905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61451619128569945464976603 92177428692854918197464905)
      ·
        refine ⟨69133071519641188648098679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92177428692854918197464905 69133071519641188648098679)
        ·
          refine ⟨103699607279461782972148019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69133071519641188648098679 103699607279461782972148019)
          ·
            refine ⟨155549410919192674458222029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103699607279461782972148019 155549410919192674458222029)
            ·
              refine ⟨58331029094697252921833261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155549410919192674458222029 58331029094697252921833261)
              ·
                refine ⟨21874135910511469845687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58331029094697252921833261 21874135910511469845687473)
                ·
                  refine ⟨16405601932883602384265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21874135910511469845687473 16405601932883602384265605)
                  ·
                    refine ⟨3076050362415675447049801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16405601932883602384265605 3076050362415675447049801)
                    ·
                      refine ⟨2307037771811756585287351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076050362415675447049801 2307037771811756585287351)
                      ·
                        rfl

theorem cell23_4492940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_4492940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492940 prefixEnd_4492940 := by exact prefixLift 4492940
  have htrace : WordTrace (prefixWord ++ tailWord_4492940) baseStart_4492940 baseEnd_4492940 := by
    simpa [prefixWord, tailWord_4492940, baseEnd_4492940] using wordTrace_append hprefix tailTrace_4492940
  have hstable : (prefixWord ++ tailWord_4492940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492940).length < 2 ^ (prefixWord ++ tailWord_4492940).sum := by decide
  have hdescent : baseEnd_4492940 < baseStart_4492940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492960 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_4492960 : Nat := 118140960795 + 4492960 * 2 ^ 59
def prefixEnd_4492960 : Nat := 4983230072969 + 3 ^ 40 * 4492960 * 2
def baseEnd_4492960 : Nat := 2307048041424846507037259

theorem tailTrace_4492960 : CollatzResearch.WordTrace tailWord_4492960 prefixEnd_4492960 2307048041424846507037259 := by
  unfold tailWord_4492960
  simp only [CollatzResearch.WordTrace]
  refine ⟨81935856901390365661166167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109247809201853820881554889 81935856901390365661166167)
  ·
    refine ⟨122903785352085548491749251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81935856901390365661166167 122903785352085548491749251)
    ·
      refine ⟨184355678028128322737623877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122903785352085548491749251 184355678028128322737623877)
      ·
        refine ⟨34566689630274060513304477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184355678028128322737623877 34566689630274060513304477)
        ·
          refine ⟨12962508611352772692489179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34566689630274060513304477 12962508611352772692489179)
          ·
            refine ⟨19443762917029159038733769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962508611352772692489179 19443762917029159038733769)
            ·
              refine ⟨14582822187771869279050327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443762917029159038733769 14582822187771869279050327)
              ·
                refine ⟨21874233281657803918575491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582822187771869279050327 21874233281657803918575491)
                ·
                  refine ⟨32811349922486705877863237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21874233281657803918575491 32811349922486705877863237)
                  ·
                    refine ⟨6152128110466257352099357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32811349922486705877863237 6152128110466257352099357)
                    ·
                      refine ⟨2307048041424846507037259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152128110466257352099357 2307048041424846507037259)
                      ·
                        rfl

theorem cell23_4492960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_4492960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492960 prefixEnd_4492960 := by exact prefixLift 4492960
  have htrace : WordTrace (prefixWord ++ tailWord_4492960) baseStart_4492960 baseEnd_4492960 := by
    simpa [prefixWord, tailWord_4492960, baseEnd_4492960] using wordTrace_append hprefix tailTrace_4492960
  have hstable : (prefixWord ++ tailWord_4492960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492960).length < 2 ^ (prefixWord ++ tailWord_4492960).sum := by decide
  have hdescent : baseEnd_4492960 < baseStart_4492960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4492974 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4492974 : Nat := 118140960795 + 4492974 * 2 ^ 59
def prefixEnd_4492974 : Nat := 4983230072969 + 3 ^ 40 * 4492974 * 2
def baseEnd_4492974 : Nat := 2307055230154009452262195

theorem tailTrace_4492974 : CollatzResearch.WordTrace tailWord_4492974 prefixEnd_4492974 2307055230154009452262195 := by
  unfold tailWord_4492974
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484028053091251464167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109248149616486674475561317 20484028053091251464167747)
  ·
    refine ⟨30726042079636877196251621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20484028053091251464167747 30726042079636877196251621)
    ·
      refine ⟨5761132889931914474297179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30726042079636877196251621 5761132889931914474297179)
      ·
        refine ⟨8641699334897871711445769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761132889931914474297179 8641699334897871711445769)
        ·
          refine ⟨6481274501173403783584327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8641699334897871711445769 6481274501173403783584327)
          ·
            refine ⟨9721911751760105675376491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481274501173403783584327 9721911751760105675376491)
            ·
              refine ⟨14582867627640158513064737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721911751760105675376491 14582867627640158513064737)
              ·
                refine ⟨10937150720730118884798553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14582867627640158513064737 10937150720730118884798553)
                ·
                  refine ⟨8202863040547589163598915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10937150720730118884798553 8202863040547589163598915)
                  ·
                    refine ⟨12304294560821383745398373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8202863040547589163598915 12304294560821383745398373)
                    ·
                      refine ⟨2307055230154009452262195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12304294560821383745398373 2307055230154009452262195)
                      ·
                        rfl

theorem cell23_4492974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4492974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4492974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4492974 prefixEnd_4492974 := by exact prefixLift 4492974
  have htrace : WordTrace (prefixWord ++ tailWord_4492974) baseStart_4492974 baseEnd_4492974 := by
    simpa [prefixWord, tailWord_4492974, baseEnd_4492974] using wordTrace_append hprefix tailTrace_4492974
  have hstable : (prefixWord ++ tailWord_4492974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4492974).length < 2 ^ (prefixWord ++ tailWord_4492974).sum := by decide
  have hdescent : baseEnd_4492974 < baseStart_4492974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4492974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493017 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 2, 3, 2]
def baseStart_4493017 : Nat := 118140960795 + 4493017 * 2 ^ 59
def prefixEnd_4493017 : Nat := 4983230072969 + 3 ^ 40 * 4493017 * 2
def baseEnd_4493017 : Nat := 2307077309822152784024497

theorem tailTrace_4493017 : CollatzResearch.WordTrace tailWord_4493017 prefixEnd_4493017 2307077309822152784024497 := by
  unfold tailWord_4493017
  simp only [CollatzResearch.WordTrace]
  refine ⟨163873792763574230057157305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109249195175716153371438203 163873792763574230057157305)
  ·
    refine ⟨122905344572680672542867979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163873792763574230057157305 122905344572680672542867979)
    ·
      refine ⟨184358016859021008814301969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122905344572680672542867979 184358016859021008814301969)
      ·
        refine ⟨138268512644265756610726477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184358016859021008814301969 138268512644265756610726477)
        ·
          refine ⟨51850692241599658729022429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138268512644265756610726477 51850692241599658729022429)
          ·
            refine ⟨19444009590599872023383411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51850692241599658729022429 19444009590599872023383411)
            ·
              refine ⟨29166014385899808035075117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19444009590599872023383411 29166014385899808035075117)
              ·
                refine ⟨10937255394712428013153169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29166014385899808035075117 10937255394712428013153169)
                ·
                  refine ⟨8202941546034321009864877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10937255394712428013153169 8202941546034321009864877)
                  ·
                    refine ⟨3076103079762870378699329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8202941546034321009864877 3076103079762870378699329)
                    ·
                      refine ⟨2307077309822152784024497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076103079762870378699329 2307077309822152784024497)
                      ·
                        rfl

theorem cell23_4493017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_4493017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493017 prefixEnd_4493017 := by exact prefixLift 4493017
  have htrace : WordTrace (prefixWord ++ tailWord_4493017) baseStart_4493017 baseEnd_4493017 := by
    simpa [prefixWord, tailWord_4493017, baseEnd_4493017] using wordTrace_append hprefix tailTrace_4493017
  have hstable : (prefixWord ++ tailWord_4493017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493017).length < 2 ^ (prefixWord ++ tailWord_4493017).sum := by decide
  have hdescent : baseEnd_4493017 < baseStart_4493017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493041 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_4493041 : Nat := 118140960795 + 4493041 * 2 ^ 59
def prefixEnd_4493041 : Nat := 4983230072969 + 3 ^ 40 * 4493041 * 2
def baseEnd_4493041 : Nat := 2307089633357860690124387

theorem tailTrace_4493041 : CollatzResearch.WordTrace tailWord_4493041 prefixEnd_4493041 2307089633357860690124387 := by
  unfold tailWord_4493041
  simp only [CollatzResearch.WordTrace]
  refine ⟨163874668115487282156030977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109249778743658188104020651 163874668115487282156030977)
  ·
    refine ⟨122906001086615461617023233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163874668115487282156030977 122906001086615461617023233)
    ·
      refine ⟨92179500814961596212767425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122906001086615461617023233 92179500814961596212767425)
      ·
        refine ⟨69134625611221197159575569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92179500814961596212767425 69134625611221197159575569)
        ·
          refine ⟨51850969208415897869681677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69134625611221197159575569 51850969208415897869681677)
          ·
            refine ⟨19444113453155961701130629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51850969208415897869681677 19444113453155961701130629)
            ·
              refine ⟨3645771272466742818961993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19444113453155961701130629 3645771272466742818961993)
              ·
                refine ⟨2734328454350057114221495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645771272466742818961993 2734328454350057114221495)
                ·
                  refine ⟨4101492681525085671332243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734328454350057114221495 4101492681525085671332243)
                  ·
                    refine ⟨6152239022287628506998365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101492681525085671332243 6152239022287628506998365)
                    ·
                      refine ⟨2307089633357860690124387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152239022287628506998365 2307089633357860690124387)
                      ·
                        rfl

theorem cell23_4493041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_4493041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493041 prefixEnd_4493041 := by exact prefixLift 4493041
  have htrace : WordTrace (prefixWord ++ tailWord_4493041) baseStart_4493041 baseEnd_4493041 := by
    simpa [prefixWord, tailWord_4493041, baseEnd_4493041] using wordTrace_append hprefix tailTrace_4493041
  have hstable : (prefixWord ++ tailWord_4493041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493041).length < 2 ^ (prefixWord ++ tailWord_4493041).sum := by decide
  have hdescent : baseEnd_4493041 < baseStart_4493041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493043 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_4493043 : Nat := 118140960795 + 4493043 * 2 ^ 59
def prefixEnd_4493043 : Nat := 4983230072969 + 3 ^ 40 * 4493043 * 2
def baseEnd_4493043 : Nat := 2307090660319169682299377

theorem tailTrace_4493043 : CollatzResearch.WordTrace tailWord_4493043 prefixEnd_4493043 2307090660319169682299377 := by
  unfold tailWord_4493043
  simp only [CollatzResearch.WordTrace]
  refine ⟨163874741061480036497603783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109249827374320024331735855 163874741061480036497603783)
  ·
    refine ⟨245812111592220054746405675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163874741061480036497603783 245812111592220054746405675)
    ·
      refine ⟨368718167388330082119608513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245812111592220054746405675 368718167388330082119608513)
      ·
        refine ⟨276538625541247561589706385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368718167388330082119608513 276538625541247561589706385)
        ·
          refine ⟨207403969155935671192279789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276538625541247561589706385 207403969155935671192279789)
          ·
            refine ⟨77776488433475876697104921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207403969155935671192279789 77776488433475876697104921)
            ·
              refine ⟨58332366325106907522828691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77776488433475876697104921 58332366325106907522828691)
              ·
                refine ⟨87498549487660361284243037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58332366325106907522828691 87498549487660361284243037)
                ·
                  refine ⟨32811956057872635481591139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87498549487660361284243037 32811956057872635481591139)
                  ·
                    refine ⟨49217934086808953222386709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32811956057872635481591139 49217934086808953222386709)
                    ·
                      refine ⟨2307090660319169682299377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49217934086808953222386709 2307090660319169682299377)
                      ·
                        rfl

theorem cell23_4493043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_4493043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493043 prefixEnd_4493043 := by exact prefixLift 4493043
  have htrace : WordTrace (prefixWord ++ tailWord_4493043) baseStart_4493043 baseEnd_4493043 := by
    simpa [prefixWord, tailWord_4493043, baseEnd_4493043] using wordTrace_append hprefix tailTrace_4493043
  have hstable : (prefixWord ++ tailWord_4493043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493043).length < 2 ^ (prefixWord ++ tailWord_4493043).sum := by decide
  have hdescent : baseEnd_4493043 < baseStart_4493043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493044 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4493044 : Nat := 118140960795 + 4493044 * 2 ^ 59
def prefixEnd_4493044 : Nat := 4983230072969 + 3 ^ 40 * 4493044 * 2
def baseEnd_4493044 : Nat := 769030391266608059462291

theorem tailTrace_4493044 : CollatzResearch.WordTrace tailWord_4493044 prefixEnd_4493044 769030391266608059462291 := by
  unfold tailWord_4493044
  simp only [CollatzResearch.WordTrace]
  refine ⟨81937388767238206834195093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109249851689650942445593457 81937388767238206834195093)
  ·
    refine ⟨3840815098464290945352895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81937388767238206834195093 3840815098464290945352895)
    ·
      refine ⟨5761222647696436418029343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840815098464290945352895 5761222647696436418029343)
      ·
        refine ⟨8641833971544654627044015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761222647696436418029343 8641833971544654627044015)
        ·
          refine ⟨12962750957316981940566023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8641833971544654627044015 12962750957316981940566023)
          ·
            refine ⟨19444126435975472910849035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962750957316981940566023 19444126435975472910849035)
            ·
              refine ⟨29166189653963209366273553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19444126435975472910849035 29166189653963209366273553)
              ·
                refine ⟨21874642240472407024705165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29166189653963209366273553 21874642240472407024705165)
                ·
                  refine ⟨8202990840177152634264437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21874642240472407024705165 8202990840177152634264437)
                  ·
                    refine ⟨769030391266608059462291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8202990840177152634264437 769030391266608059462291)
                    ·
                      rfl

theorem cell23_4493044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4493044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493044 prefixEnd_4493044 := by exact prefixLift 4493044
  have htrace : WordTrace (prefixWord ++ tailWord_4493044) baseStart_4493044 baseEnd_4493044 := by
    simpa [prefixWord, tailWord_4493044, baseEnd_4493044] using wordTrace_append hprefix tailTrace_4493044
  have hstable : (prefixWord ++ tailWord_4493044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493044).length < 2 ^ (prefixWord ++ tailWord_4493044).sum := by decide
  have hdescent : baseEnd_4493044 < baseStart_4493044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493053 : List Nat := [1, 4, 1, 1, 1, 1, 2, 12]
def baseStart_4493053 : Nat := 118140960795 + 4493053 * 2 ^ 59
def prefixEnd_4493053 : Nat := 4983230072969 + 3 ^ 40 * 4493053 * 2
def baseEnd_4493053 : Nat := 85447992412063505302753

theorem tailTrace_4493053 : CollatzResearch.WordTrace tailWord_4493053 prefixEnd_4493053 85447992412063505302753 := by
  unfold tailWord_4493053
  simp only [CollatzResearch.WordTrace]
  refine ⟨163875105791443808205467813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109250070527629205470311875 163875105791443808205467813)
  ·
    refine ⟨30726582335895714038525215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163875105791443808205467813 30726582335895714038525215)
    ·
      refine ⟨46089873503843571057787823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30726582335895714038525215 46089873503843571057787823)
      ·
        refine ⟨69134810255765356586681735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46089873503843571057787823 69134810255765356586681735)
        ·
          refine ⟨103702215383648034880022603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69134810255765356586681735 103702215383648034880022603)
          ·
            refine ⟨155553323075472052320033905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103702215383648034880022603 155553323075472052320033905)
            ·
              refine ⟨116664992306604039240025429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155553323075472052320033905 116664992306604039240025429)
              ·
                refine ⟨85447992412063505302753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 116664992306604039240025429 85447992412063505302753)
                ·
                  rfl

theorem cell23_4493053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 12].length) (baseStart_4493053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493053 prefixEnd_4493053 := by exact prefixLift 4493053
  have htrace : WordTrace (prefixWord ++ tailWord_4493053) baseStart_4493053 baseEnd_4493053 := by
    simpa [prefixWord, tailWord_4493053, baseEnd_4493053] using wordTrace_append hprefix tailTrace_4493053
  have hstable : (prefixWord ++ tailWord_4493053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493053).length < 2 ^ (prefixWord ++ tailWord_4493053).sum := by decide
  have hdescent : baseEnd_4493053 < baseStart_4493053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493057 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4493057 : Nat := 118140960795 + 4493057 * 2 ^ 59
def prefixEnd_4493057 : Nat := 4983230072969 + 3 ^ 40 * 4493057 * 2
def baseEnd_4493057 : Nat := 769032616349444209174771

theorem tailTrace_4493057 : CollatzResearch.WordTrace tailWord_4493057 prefixEnd_4493057 769032616349444209174771 := by
  unfold tailWord_4493057
  simp only [CollatzResearch.WordTrace]
  refine ⟨163875251683429316888613425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109250167788952877925742283 163875251683429316888613425)
  ·
    refine ⟨122906438762571987666460069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163875251683429316888613425 122906438762571987666460069)
    ·
      refine ⟨23044957267982247687461263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122906438762571987666460069 23044957267982247687461263)
      ·
        refine ⟨34567435901973371531191895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23044957267982247687461263 34567435901973371531191895)
        ·
          refine ⟨51851153852960057296787843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34567435901973371531191895 51851153852960057296787843)
          ·
            refine ⟨77776730779440085945181765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51851153852960057296787843 77776730779440085945181765)
            ·
              refine ⟨14583137021145016114721581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77776730779440085945181765 14583137021145016114721581)
              ·
                refine ⟨5468676382929381043020593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14583137021145016114721581 5468676382929381043020593)
                ·
                  refine ⟨4101507287197035782265445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5468676382929381043020593 4101507287197035782265445)
                  ·
                    refine ⟨769032616349444209174771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4101507287197035782265445 769032616349444209174771)
                    ·
                      rfl

theorem cell23_4493057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4493057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493057 prefixEnd_4493057 := by exact prefixLift 4493057
  have htrace : WordTrace (prefixWord ++ tailWord_4493057) baseStart_4493057 baseEnd_4493057 := by
    simpa [prefixWord, tailWord_4493057, baseEnd_4493057] using wordTrace_append hprefix tailTrace_4493057
  have hstable : (prefixWord ++ tailWord_4493057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493057).length < 2 ^ (prefixWord ++ tailWord_4493057).sum := by decide
  have hdescent : baseEnd_4493057 < baseStart_4493057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493062 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4493062 : Nat := 118140960795 + 4493062 * 2 ^ 59
def prefixEnd_4493062 : Nat := 4983230072969 + 3 ^ 40 * 4493062 * 2
def baseEnd_4493062 : Nat := 2307100416451605107961791

theorem tailTrace_4493062 : CollatzResearch.WordTrace tailWord_4493062 prefixEnd_4493062 2307100416451605107961791 := by
  unfold tailWord_4493062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121107314012850085704545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109250289365607468495030293 5121107314012850085704545)
  ·
    refine ⟨3840830485509637564278409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5121107314012850085704545 3840830485509637564278409)
    ·
      refine ⟨2880622864132228173208807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3840830485509637564278409 2880622864132228173208807)
      ·
        refine ⟨4320934296198342259813211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880622864132228173208807 4320934296198342259813211)
        ·
          refine ⟨6481401444297513389719817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320934296198342259813211 6481401444297513389719817)
          ·
            refine ⟨4861051083223135042289863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6481401444297513389719817 4861051083223135042289863)
            ·
              refine ⟨7291576624834702563434795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861051083223135042289863 7291576624834702563434795)
              ·
                refine ⟨10937364937252053845152193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291576624834702563434795 10937364937252053845152193)
                ·
                  refine ⟨8203023702939040383864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10937364937252053845152193 8203023702939040383864145)
                  ·
                    refine ⟨6152267777204280287898109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8203023702939040383864145 6152267777204280287898109)
                    ·
                      refine ⟨2307100416451605107961791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152267777204280287898109 2307100416451605107961791)
                      ·
                        rfl

theorem cell23_4493062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4493062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493062 prefixEnd_4493062 := by exact prefixLift 4493062
  have htrace : WordTrace (prefixWord ++ tailWord_4493062) baseStart_4493062 baseEnd_4493062 := by
    simpa [prefixWord, tailWord_4493062, baseEnd_4493062] using wordTrace_append hprefix tailTrace_4493062
  have hstable : (prefixWord ++ tailWord_4493062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493062).length < 2 ^ (prefixWord ++ tailWord_4493062).sum := by decide
  have hdescent : baseEnd_4493062 < baseStart_4493062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493064 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_4493064 : Nat := 118140960795 + 4493064 * 2 ^ 59
def prefixEnd_4493064 : Nat := 4983230072969 + 3 ^ 40 * 4493064 * 2
def baseEnd_4493064 : Nat := 2307101443412914100136781

theorem tailTrace_4493064 : CollatzResearch.WordTrace tailWord_4493064 prefixEnd_4493064 2307101443412914100136781 := by
  unfold tailWord_4493064
  simp only [CollatzResearch.WordTrace]
  refine ⟨81937753497201978542059123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109250337996269304722745497 81937753497201978542059123)
  ·
    refine ⟨122906630245802967813088685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81937753497201978542059123 122906630245802967813088685)
    ·
      refine ⟨46089986342176112929908257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122906630245802967813088685 46089986342176112929908257)
      ·
        refine ⟨34567489756632084697431193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46089986342176112929908257 34567489756632084697431193)
        ·
          refine ⟨25925617317474063523073395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34567489756632084697431193 25925617317474063523073395)
          ·
            refine ⟨38888425976211095284610093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25925617317474063523073395 38888425976211095284610093)
            ·
              refine ⟨14583159741079160731728785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38888425976211095284610093 14583159741079160731728785)
              ·
                refine ⟨10937369805809370548796589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14583159741079160731728785 10937369805809370548796589)
                ·
                  refine ⟨4101513677178513955798721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10937369805809370548796589 4101513677178513955798721)
                  ·
                    refine ⟨3076135257883885466849041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4101513677178513955798721 3076135257883885466849041)
                    ·
                      refine ⟨2307101443412914100136781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076135257883885466849041 2307101443412914100136781)
                      ·
                        rfl

theorem cell23_4493064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_4493064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493064 prefixEnd_4493064 := by exact prefixLift 4493064
  have htrace : WordTrace (prefixWord ++ tailWord_4493064) baseStart_4493064 baseEnd_4493064 := by
    simpa [prefixWord, tailWord_4493064, baseEnd_4493064] using wordTrace_append hprefix tailTrace_4493064
  have hstable : (prefixWord ++ tailWord_4493064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493064).length < 2 ^ (prefixWord ++ tailWord_4493064).sum := by decide
  have hdescent : baseEnd_4493064 < baseStart_4493064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493083 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 7]
def baseStart_4493083 : Nat := 118140960795 + 4493083 * 2 ^ 59
def prefixEnd_4493083 : Nat := 4983230072969 + 3 ^ 40 * 4493083 * 2
def baseEnd_4493083 : Nat := 769037066515116508599731

theorem tailTrace_4493083 : CollatzResearch.WordTrace tailWord_4493083 prefixEnd_4493083 769037066515116508599731 := by
  unfold tailWord_4493083
  simp only [CollatzResearch.WordTrace]
  refine ⟨163876199981335123329059903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109250799987556748886039935 163876199981335123329059903)
  ·
    refine ⟨245814299972002684993589855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163876199981335123329059903 245814299972002684993589855)
    ·
      refine ⟨368721449958004027490384783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245814299972002684993589855 368721449958004027490384783)
      ·
        refine ⟨553082174937006041235577175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368721449958004027490384783 553082174937006041235577175)
        ·
          refine ⟨829623262405509061853365763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553082174937006041235577175 829623262405509061853365763)
          ·
            refine ⟨1244434893608263592780048645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829623262405509061853365763 1244434893608263592780048645)
            ·
              refine ⟨233331542551549423646259121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1244434893608263592780048645 233331542551549423646259121)
              ·
                refine ⟨174998656913662067734694341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233331542551549423646259121 174998656913662067734694341)
                ·
                  refine ⟨32812248171311637700255189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174998656913662067734694341 32812248171311637700255189)
                  ·
                    refine ⟨769037066515116508599731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32812248171311637700255189 769037066515116508599731)
                    ·
                      rfl

theorem cell23_4493083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_4493083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493083 prefixEnd_4493083 := by exact prefixLift 4493083
  have htrace : WordTrace (prefixWord ++ tailWord_4493083) baseStart_4493083 baseEnd_4493083 := by
    simpa [prefixWord, tailWord_4493083, baseEnd_4493083] using wordTrace_append hprefix tailTrace_4493083
  have hstable : (prefixWord ++ tailWord_4493083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493083).length < 2 ^ (prefixWord ++ tailWord_4493083).sum := by decide
  have hdescent : baseEnd_4493083 < baseStart_4493083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493114 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_4493114 : Nat := 118140960795 + 4493114 * 2 ^ 59
def prefixEnd_4493114 : Nat := 4983230072969 + 3 ^ 40 * 4493114 * 2
def baseEnd_4493114 : Nat := 2307127117445638904511551

theorem tailTrace_4493114 : CollatzResearch.WordTrace tailWord_4493114 prefixEnd_4493114 2307127117445638904511551 := by
  unfold tailWord_4493114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40969332661055703905859599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109251553762815210415625597 40969332661055703905859599)
  ·
    refine ⟨61453998991583555858789399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40969332661055703905859599 61453998991583555858789399)
    ·
      refine ⟨92180998487375333788184099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61453998991583555858789399 92180998487375333788184099)
      ·
        refine ⟨138271497731063000682276149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92180998487375333788184099 138271497731063000682276149)
        ·
          refine ⟨12962952912287156313963389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138271497731063000682276149 12962952912287156313963389)
          ·
            refine ⟨4861107342107683617736271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12962952912287156313963389 4861107342107683617736271)
            ·
              refine ⟨7291661013161525426604407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861107342107683617736271 7291661013161525426604407)
              ·
                refine ⟨10937491519742288139906611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291661013161525426604407 10937491519742288139906611)
                ·
                  refine ⟨16406237279613432209859917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10937491519742288139906611 16406237279613432209859917)
                  ·
                    refine ⟨6152338979855037078697469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16406237279613432209859917 6152338979855037078697469)
                    ·
                      refine ⟨2307127117445638904511551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152338979855037078697469 2307127117445638904511551)
                      ·
                        rfl

theorem cell23_4493114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_4493114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493114 prefixEnd_4493114 := by exact prefixLift 4493114
  have htrace : WordTrace (prefixWord ++ tailWord_4493114) baseStart_4493114 baseEnd_4493114 := by
    simpa [prefixWord, tailWord_4493114, baseEnd_4493114] using wordTrace_append hprefix tailTrace_4493114
  have hstable : (prefixWord ++ tailWord_4493114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493114).length < 2 ^ (prefixWord ++ tailWord_4493114).sum := by decide
  have hdescent : baseEnd_4493114 < baseStart_4493114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493200 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_4493200 : Nat := 118140960795 + 4493200 * 2 ^ 59
def prefixEnd_4493200 : Nat := 4983230072969 + 3 ^ 40 * 4493200 * 2
def baseEnd_4493200 : Nat := 2307171276781925568036155

theorem tailTrace_4493200 : CollatzResearch.WordTrace tailWord_4493200 prefixEnd_4493200 2307171276781925568036155 := by
  unfold tailWord_4493200
  simp only [CollatzResearch.WordTrace]
  refine ⟨81940233660955626155534527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109253644881274168207379369 81940233660955626155534527)
  ·
    refine ⟨122910350491433439233301791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81940233660955626155534527 122910350491433439233301791)
    ·
      refine ⟨184365525737150158849952687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122910350491433439233301791 184365525737150158849952687)
      ·
        refine ⟨276548288605725238274929031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184365525737150158849952687 276548288605725238274929031)
        ·
          refine ⟨414822432908587857412393547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276548288605725238274929031 414822432908587857412393547)
          ·
            refine ⟨622233649362881786118590321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414822432908587857412393547 622233649362881786118590321)
            ·
              refine ⟨466675237022161339588942741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622233649362881786118590321 466675237022161339588942741)
              ·
                refine ⟨21875401735413812793231691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 466675237022161339588942741 21875401735413812793231691)
                ·
                  refine ⟨32813102603120719189847537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21875401735413812793231691 32813102603120719189847537)
                  ·
                    refine ⟨24609826952340539392385653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32813102603120719189847537 24609826952340539392385653)
                    ·
                      refine ⟨2307171276781925568036155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24609826952340539392385653 2307171276781925568036155)
                      ·
                        rfl

theorem cell23_4493200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_4493200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493200 prefixEnd_4493200 := by exact prefixLift 4493200
  have htrace : WordTrace (prefixWord ++ tailWord_4493200) baseStart_4493200 baseEnd_4493200 := by
    simpa [prefixWord, tailWord_4493200, baseEnd_4493200] using wordTrace_append hprefix tailTrace_4493200
  have hstable : (prefixWord ++ tailWord_4493200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493200).length < 2 ^ (prefixWord ++ tailWord_4493200).sum := by decide
  have hdescent : baseEnd_4493200 < baseStart_4493200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493207 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 2, 5]
def baseStart_4493207 : Nat := 118140960795 + 4493207 * 2 ^ 59
def prefixEnd_4493207 : Nat := 4983230072969 + 3 ^ 40 * 4493207 * 2
def baseEnd_4493207 : Nat := 769058290382169013549541

theorem tailTrace_4493207 : CollatzResearch.WordTrace tailWord_4493207 prefixEnd_4493207 769058290382169013549541 := by
  unfold tailWord_4493207
  simp only [CollatzResearch.WordTrace]
  refine ⟨163880722632885892506573875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109253815088590595004382583 163880722632885892506573875)
  ·
    refine ⟨245821083949328838759860813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163880722632885892506573875 245821083949328838759860813)
    ·
      refine ⟨92182906480998314534947805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245821083949328838759860813 92182906480998314534947805)
      ·
        refine ⟨34568589930374367950605427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92182906480998314534947805 34568589930374367950605427)
        ·
          refine ⟨51852884895561551925908141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34568589930374367950605427 51852884895561551925908141)
          ·
            refine ⟨19444831835835581972215553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51852884895561551925908141 19444831835835581972215553)
            ·
              refine ⟨14583623876876686479161665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19444831835835581972215553 14583623876876686479161665)
              ·
                refine ⟨10937717907657514859371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14583623876876686479161665 10937717907657514859371249)
                ·
                  refine ⟨8203288430743136144528437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10937717907657514859371249 8203288430743136144528437)
                  ·
                    refine ⟨769058290382169013549541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8203288430743136144528437 769058290382169013549541)
                    ·
                      rfl

theorem cell23_4493207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_4493207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493207 prefixEnd_4493207 := by exact prefixLift 4493207
  have htrace : WordTrace (prefixWord ++ tailWord_4493207) baseStart_4493207 baseEnd_4493207 := by
    simpa [prefixWord, tailWord_4493207, baseEnd_4493207] using wordTrace_append hprefix tailTrace_4493207
  have hstable : (prefixWord ++ tailWord_4493207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493207).length < 2 ^ (prefixWord ++ tailWord_4493207).sum := by decide
  have hdescent : baseEnd_4493207 < baseStart_4493207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493247 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_4493247 : Nat := 118140960795 + 4493247 * 2 ^ 59
def prefixEnd_4493247 : Nat := 4983230072969 + 3 ^ 40 * 4493247 * 2
def baseEnd_4493247 : Nat := 2307195410372686884148439

theorem tailTrace_4493247 : CollatzResearch.WordTrace tailWord_4493247 prefixEnd_4493247 2307195410372686884148439 := by
  unfold tailWord_4493247
  simp only [CollatzResearch.WordTrace]
  refine ⟨163882181552740979338029995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109254787701827319558686663 163882181552740979338029995)
  ·
    refine ⟨245823272329111469007044993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163882181552740979338029995 245823272329111469007044993)
    ·
      refine ⟨184367454246833601755283745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245823272329111469007044993 184367454246833601755283745)
      ·
        refine ⟨138275590685125201316462809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184367454246833601755283745 138275590685125201316462809)
        ·
          refine ⟨103706693013843900987347107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138275590685125201316462809 103706693013843900987347107)
          ·
            refine ⟨155560039520765851481020661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103706693013843900987347107 155560039520765851481020661)
            ·
              refine ⟨14583753705071798576345687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155560039520765851481020661 14583753705071798576345687)
              ·
                refine ⟨21875630557607697864518531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14583753705071798576345687 21875630557607697864518531)
                ·
                  refine ⟨32813445836411546796777797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21875630557607697864518531 32813445836411546796777797)
                  ·
                    refine ⟨6152521094327165024395837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32813445836411546796777797 6152521094327165024395837)
                    ·
                      refine ⟨2307195410372686884148439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152521094327165024395837 2307195410372686884148439)
                      ·
                        rfl

theorem cell23_4493247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_4493247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493247 prefixEnd_4493247 := by exact prefixLift 4493247
  have htrace : WordTrace (prefixWord ++ tailWord_4493247) baseStart_4493247 baseEnd_4493247 := by
    simpa [prefixWord, tailWord_4493247, baseEnd_4493247] using wordTrace_append hprefix tailTrace_4493247
  have hstable : (prefixWord ++ tailWord_4493247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493247).length < 2 ^ (prefixWord ++ tailWord_4493247).sum := by decide
  have hdescent : baseEnd_4493247 < baseStart_4493247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493284 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 6]
def baseStart_4493284 : Nat := 118140960795 + 4493284 * 2 ^ 59
def prefixEnd_4493284 : Nat := 4983230072969 + 3 ^ 40 * 4493284 * 2
def baseEnd_4493284 : Nat := 256357156572989248820641

theorem tailTrace_4493284 : CollatzResearch.WordTrace tailWord_4493284 prefixEnd_4493284 256357156572989248820641 := by
  unfold tailWord_4493284
  simp only [CollatzResearch.WordTrace]
  refine ⟨81941765526803467328563453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109255687369071289771417937 81941765526803467328563453)
  ·
    refine ⟨30728162072551300248211295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81941765526803467328563453 30728162072551300248211295)
    ·
      refine ⟨46092243108826950372316943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30728162072551300248211295 46092243108826950372316943)
      ·
        refine ⟨69138364663240425558475415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46092243108826950372316943 69138364663240425558475415)
        ·
          refine ⟨103707546994860638337713123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69138364663240425558475415 103707546994860638337713123)
          ·
            refine ⟨155561320492290957506569685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103707546994860638337713123 155561320492290957506569685)
            ·
              refine ⟨3645968449038069316560227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 155561320492290957506569685 3645968449038069316560227)
              ·
                refine ⟨5468952673557103974840341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645968449038069316560227 5468952673557103974840341)
                ·
                  refine ⟨256357156572989248820641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5468952673557103974840341 256357156572989248820641)
                  ·
                    rfl

theorem cell23_4493284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_4493284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493284 prefixEnd_4493284 := by exact prefixLift 4493284
  have htrace : WordTrace (prefixWord ++ tailWord_4493284) baseStart_4493284 baseEnd_4493284 := by
    simpa [prefixWord, tailWord_4493284, baseEnd_4493284] using wordTrace_append hprefix tailTrace_4493284
  have hstable : (prefixWord ++ tailWord_4493284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493284).length < 2 ^ (prefixWord ++ tailWord_4493284).sum := by decide
  have hdescent : baseEnd_4493284 < baseStart_4493284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493304 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_4493304 : Nat := 118140960795 + 4493304 * 2 ^ 59
def prefixEnd_4493304 : Nat := 4983230072969 + 3 ^ 40 * 4493304 * 2
def baseEnd_4493304 : Nat := 2307224678769993161135677

theorem tailTrace_4493304 : CollatzResearch.WordTrace tailWord_4493304 prefixEnd_4493304 2307224678769993161135677 := by
  unfold tailWord_4493304
  simp only [CollatzResearch.WordTrace]
  refine ⟨81942130256767239036427483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109256173675689652048569977 81942130256767239036427483)
  ·
    refine ⟨122913195385150858554641225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81942130256767239036427483 122913195385150858554641225)
    ·
      refine ⟨92184896538863143915980919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122913195385150858554641225 92184896538863143915980919)
      ·
        refine ⟨138277344808294715873971379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92184896538863143915980919 138277344808294715873971379)
        ·
          refine ⟨207416017212442073810957069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138277344808294715873971379 207416017212442073810957069)
          ·
            refine ⟨77781006454665777679108901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207416017212442073810957069 77781006454665777679108901)
            ·
              refine ⟨14583938710249833314832919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77781006454665777679108901 14583938710249833314832919)
              ·
                refine ⟨21875908065374749972249379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14583938710249833314832919 21875908065374749972249379)
                ·
                  refine ⟨32813862098062124958374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21875908065374749972249379 32813862098062124958374069)
                  ·
                    refine ⟨3076299571693324214847569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32813862098062124958374069 3076299571693324214847569)
                    ·
                      refine ⟨2307224678769993161135677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076299571693324214847569 2307224678769993161135677)
                      ·
                        rfl

theorem cell23_4493304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_4493304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493304 prefixEnd_4493304 := by exact prefixLift 4493304
  have htrace : WordTrace (prefixWord ++ tailWord_4493304) baseStart_4493304 baseEnd_4493304 := by
    simpa [prefixWord, tailWord_4493304, baseEnd_4493304] using wordTrace_append hprefix tailTrace_4493304
  have hstable : (prefixWord ++ tailWord_4493304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493304).length < 2 ^ (prefixWord ++ tailWord_4493304).sum := by decide
  have hdescent : baseEnd_4493304 < baseStart_4493304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493337 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_4493337 : Nat := 118140960795 + 4493337 * 2 ^ 59
def prefixEnd_4493337 : Nat := 4983230072969 + 3 ^ 40 * 4493337 * 2
def baseEnd_4493337 : Nat := 2307241623631591532023025

theorem tailTrace_4493337 : CollatzResearch.WordTrace tailWord_4493337 prefixEnd_4493337 2307241623631591532023025 := by
  unfold tailWord_4493337
  simp only [CollatzResearch.WordTrace]
  refine ⟨163885464122414924708806265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109256976081609949805870843 163885464122414924708806265)
  ·
    refine ⟨122914098091811193531604699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163885464122414924708806265 122914098091811193531604699)
    ·
      refine ⟨184371147137716790297407049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122914098091811193531604699 184371147137716790297407049)
      ·
        refine ⟨138278360353287592723055287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184371147137716790297407049 138278360353287592723055287)
        ·
          refine ⟨207417540529931389084582931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138278360353287592723055287 207417540529931389084582931)
          ·
            refine ⟨311126310794897083626874397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207417540529931389084582931 311126310794897083626874397)
            ·
              refine ⟨116672366548086406360077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311126310794897083626874397 116672366548086406360077899)
              ·
                refine ⟨175008549822129609540116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116672366548086406360077899 175008549822129609540116849)
                ·
                  refine ⟨131256412366597207155087637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175008549822129609540116849 131256412366597207155087637)
                  ·
                    refine ⟨6152644329684244085394733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131256412366597207155087637 6152644329684244085394733)
                    ·
                      refine ⟨2307241623631591532023025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152644329684244085394733 2307241623631591532023025)
                      ·
                        rfl

theorem cell23_4493337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_4493337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493337 prefixEnd_4493337 := by exact prefixLift 4493337
  have htrace : WordTrace (prefixWord ++ tailWord_4493337) baseStart_4493337 baseEnd_4493337 := by
    simpa [prefixWord, tailWord_4493337, baseEnd_4493337] using wordTrace_append hprefix tailTrace_4493337
  have hstable : (prefixWord ++ tailWord_4493337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493337).length < 2 ^ (prefixWord ++ tailWord_4493337).sum := by decide
  have hdescent : baseEnd_4493337 < baseStart_4493337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493347 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_4493347 : Nat := 118140960795 + 4493347 * 2 ^ 59
def prefixEnd_4493347 : Nat := 4983230072969 + 3 ^ 40 * 4493347 * 2
def baseEnd_4493347 : Nat := 2307246758438136492897979

theorem tailTrace_4493347 : CollatzResearch.WordTrace tailWord_4493347 prefixEnd_4493347 2307246758438136492897979 := by
  unfold tailWord_4493347
  simp only [CollatzResearch.WordTrace]
  refine ⟨163885828852378696416670295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109257219234919130944446863 163885828852378696416670295)
  ·
    refine ⟨245828743278568044625005443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163885828852378696416670295 245828743278568044625005443)
    ·
      refine ⟨368743114917852066937508165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245828743278568044625005443 368743114917852066937508165)
      ·
        refine ⟨69139334047097262550782781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368743114917852066937508165 69139334047097262550782781)
        ·
          refine ⟨25927250267661473456543543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69139334047097262550782781 25927250267661473456543543)
          ·
            refine ⟨38890875401492210184815315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25927250267661473456543543 38890875401492210184815315)
            ·
              refine ⟨58336313102238315277222973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38890875401492210184815315 58336313102238315277222973)
              ·
                refine ⟨21876117413339368228958615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58336313102238315277222973 21876117413339368228958615)
                ·
                  refine ⟨32814176120009052343437923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21876117413339368228958615 32814176120009052343437923)
                  ·
                    refine ⟨49221264180013578515156885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32814176120009052343437923 49221264180013578515156885)
                    ·
                      refine ⟨2307246758438136492897979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49221264180013578515156885 2307246758438136492897979)
                      ·
                        rfl

theorem cell23_4493347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_4493347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493347 prefixEnd_4493347 := by exact prefixLift 4493347
  have htrace : WordTrace (prefixWord ++ tailWord_4493347) baseStart_4493347 baseEnd_4493347 := by
    simpa [prefixWord, tailWord_4493347, baseEnd_4493347] using wordTrace_append hprefix tailTrace_4493347
  have hstable : (prefixWord ++ tailWord_4493347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493347).length < 2 ^ (prefixWord ++ tailWord_4493347).sum := by decide
  have hdescent : baseEnd_4493347 < baseStart_4493347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493348 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_4493348 : Nat := 118140960795 + 4493348 * 2 ^ 59
def prefixEnd_4493348 : Nat := 4983230072969 + 3 ^ 40 * 4493348 * 2
def baseEnd_4493348 : Nat := 769082423972930329661825

theorem tailTrace_4493348 : CollatzResearch.WordTrace tailWord_4493348 prefixEnd_4493348 769082423972930329661825 := by
  unfold tailWord_4493348
  simp only [CollatzResearch.WordTrace]
  refine ⟨81942932662687536793728349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109257243550250049058304465 81942932662687536793728349)
  ·
    refine ⟨30728599748507826297648131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81942932662687536793728349 30728599748507826297648131)
    ·
      refine ⟨46092899622761739446472197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30728599748507826297648131 46092899622761739446472197)
      ·
        refine ⟨8642418679267826146213537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46092899622761739446472197 8642418679267826146213537)
        ·
          refine ⟨6481814009450869609660153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8642418679267826146213537 6481814009450869609660153)
          ·
            refine ⟨4861360507088152207245115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6481814009450869609660153 4861360507088152207245115)
            ·
              refine ⟨7292040760632228310867673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861360507088152207245115 7292040760632228310867673)
              ·
                refine ⟨5469030570474171233150755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7292040760632228310867673 5469030570474171233150755)
                ·
                  refine ⟨8203545855711256849726133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469030570474171233150755 8203545855711256849726133)
                  ·
                    refine ⟨769082423972930329661825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8203545855711256849726133 769082423972930329661825)
                    ·
                      rfl

theorem cell23_4493348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_4493348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493348 prefixEnd_4493348 := by exact prefixLift 4493348
  have htrace : WordTrace (prefixWord ++ tailWord_4493348) baseStart_4493348 baseEnd_4493348 := by
    simpa [prefixWord, tailWord_4493348, baseEnd_4493348] using wordTrace_append hprefix tailTrace_4493348
  have hstable : (prefixWord ++ tailWord_4493348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493348).length < 2 ^ (prefixWord ++ tailWord_4493348).sum := by decide
  have hdescent : baseEnd_4493348 < baseStart_4493348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493368 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_4493368 : Nat := 118140960795 + 4493368 * 2 ^ 59
def prefixEnd_4493368 : Nat := 4983230072969 + 3 ^ 40 * 4493368 * 2
def baseEnd_4493368 : Nat := 2307257541531880910735383

theorem tailTrace_4493368 : CollatzResearch.WordTrace tailWord_4493368 prefixEnd_4493368 2307257541531880910735383 := by
  unfold tailWord_4493368
  simp only [CollatzResearch.WordTrace]
  refine ⟨81943297392651308501592379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109257729856868411335456505 81943297392651308501592379)
  ·
    refine ⟨122914946088976962752388569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81943297392651308501592379 122914946088976962752388569)
    ·
      refine ⟨92186209566732722064291427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122914946088976962752388569 92186209566732722064291427)
      ·
        refine ⟨138279314350099083096437141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92186209566732722064291427 138279314350099083096437141)
        ·
          refine ⟨6481842860160894520145491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138279314350099083096437141 6481842860160894520145491)
          ·
            refine ⟨9722764290241341780218237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481842860160894520145491 9722764290241341780218237)
            ·
              refine ⟨3646036608840503167581839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9722764290241341780218237 3646036608840503167581839)
              ·
                refine ⟨5469054913260754751372759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646036608840503167581839 5469054913260754751372759)
                ·
                  refine ⟨8203582369891132127059139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469054913260754751372759 8203582369891132127059139)
                  ·
                    refine ⟨12305373554836698190588709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8203582369891132127059139 12305373554836698190588709)
                    ·
                      refine ⟨2307257541531880910735383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12305373554836698190588709 2307257541531880910735383)
                      ·
                        rfl

theorem cell23_4493368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_4493368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493368 prefixEnd_4493368 := by exact prefixLift 4493368
  have htrace : WordTrace (prefixWord ++ tailWord_4493368) baseStart_4493368 baseEnd_4493368 := by
    simpa [prefixWord, tailWord_4493368, baseEnd_4493368] using wordTrace_append hprefix tailTrace_4493368
  have hstable : (prefixWord ++ tailWord_4493368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493368).length < 2 ^ (prefixWord ++ tailWord_4493368).sum := by decide
  have hdescent : baseEnd_4493368 < baseStart_4493368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493374 : List Nat := [4, 2, 1, 3, 2, 11]
def baseStart_4493374 : Nat := 118140960795 + 4493374 * 2 ^ 59
def prefixEnd_4493374 : Nat := 4983230072969 + 3 ^ 40 * 4493374 * 2
def baseEnd_4493374 : Nat := 9494899680723489247985

theorem tailTrace_4493374 : CollatzResearch.WordTrace tailWord_4493374 prefixEnd_4493374 9494899680723489247985 := by
  unfold tailWord_4493374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485851702910110003487897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109257875748853920018602117 20485851702910110003487897)
  ·
    refine ⟨15364388777182582502615923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20485851702910110003487897 15364388777182582502615923)
    ·
      refine ⟨23046583165773873753923885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15364388777182582502615923 23046583165773873753923885)
      ·
        refine ⟨8642468687165202657721457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23046583165773873753923885 8642468687165202657721457)
        ·
          refine ⟨6481851515373901993291093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8642468687165202657721457 6481851515373901993291093)
          ·
            refine ⟨9494899680723489247985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6481851515373901993291093 9494899680723489247985)
            ·
              rfl

theorem cell23_4493374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 11].length) (baseStart_4493374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493374 prefixEnd_4493374 := by exact prefixLift 4493374
  have htrace : WordTrace (prefixWord ++ tailWord_4493374) baseStart_4493374 baseEnd_4493374 := by
    simpa [prefixWord, tailWord_4493374, baseEnd_4493374] using wordTrace_append hprefix tailTrace_4493374
  have hstable : (prefixWord ++ tailWord_4493374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493374).length < 2 ^ (prefixWord ++ tailWord_4493374).sum := by decide
  have hdescent : baseEnd_4493374 < baseStart_4493374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493398 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4493398 : Nat := 118140960795 + 4493398 * 2 ^ 59
def prefixEnd_4493398 : Nat := 4983230072969 + 3 ^ 40 * 4493398 * 2
def baseEnd_4493398 : Nat := 2307272945951515793360245

theorem tailTrace_4493398 : CollatzResearch.WordTrace tailWord_4493398 prefixEnd_4493398 2307272945951515793360245 := by
  unfold tailWord_4493398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242980560949620757923553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109258459316795954751184565 10242980560949620757923553)
  ·
    refine ⟨7682235420712215568442665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10242980560949620757923553 7682235420712215568442665)
    ·
      refine ⟨5761676565534161676331999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7682235420712215568442665 5761676565534161676331999)
      ·
        refine ⟨8642514848301242514497999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761676565534161676331999 8642514848301242514497999)
        ·
          refine ⟨12963772272451863771746999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642514848301242514497999 12963772272451863771746999)
          ·
            refine ⟨19445658408677795657620499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12963772272451863771746999 19445658408677795657620499)
            ·
              refine ⟨29168487613016693486430749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19445658408677795657620499 29168487613016693486430749)
              ·
                refine ⟨10938182854881260057411531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29168487613016693486430749 10938182854881260057411531)
                ·
                  refine ⟨16407274282321890086117297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10938182854881260057411531 16407274282321890086117297)
                  ·
                    refine ⟨12305455711741417564587973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16407274282321890086117297 12305455711741417564587973)
                    ·
                      refine ⟨2307272945951515793360245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12305455711741417564587973 2307272945951515793360245)
                      ·
                        rfl

theorem cell23_4493398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4493398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493398 prefixEnd_4493398 := by exact prefixLift 4493398
  have htrace : WordTrace (prefixWord ++ tailWord_4493398) baseStart_4493398 baseEnd_4493398 := by
    simpa [prefixWord, tailWord_4493398, baseEnd_4493398] using wordTrace_append hprefix tailTrace_4493398
  have hstable : (prefixWord ++ tailWord_4493398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493398).length < 2 ^ (prefixWord ++ tailWord_4493398).sum := by decide
  have hdescent : baseEnd_4493398 < baseStart_4493398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493401 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_4493401 : Nat := 118140960795 + 4493401 * 2 ^ 59
def prefixEnd_4493401 : Nat := 4983230072969 + 3 ^ 40 * 4493401 * 2
def baseEnd_4493401 : Nat := 2307274486393479281622731

theorem tailTrace_4493401 : CollatzResearch.WordTrace tailWord_4493401 prefixEnd_4493401 2307274486393479281622731 := by
  unfold tailWord_4493401
  simp only [CollatzResearch.WordTrace]
  refine ⟨163887798394183063639136057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109258532262788709092757371 163887798394183063639136057)
  ·
    refine ⟨122915848795637297729352043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163887798394183063639136057 122915848795637297729352043)
    ·
      refine ⟨184373773193455946594028065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122915848795637297729352043 184373773193455946594028065)
      ·
        refine ⟨138280329895091959945521049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184373773193455946594028065 138280329895091959945521049)
        ·
          refine ⟨103710247421318969959140787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138280329895091959945521049 103710247421318969959140787)
          ·
            refine ⟨155565371131978454938711181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103710247421318969959140787 155565371131978454938711181)
            ·
              refine ⟨58337014174491920602016693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155565371131978454938711181 58337014174491920602016693)
              ·
                refine ⟨5469095078858617556439065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58337014174491920602016693 5469095078858617556439065)
                ·
                  refine ⟨4101821309143963167329299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469095078858617556439065 4101821309143963167329299)
                  ·
                    refine ⟨6152731963715944750993949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4101821309143963167329299 6152731963715944750993949)
                    ·
                      refine ⟨2307274486393479281622731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6152731963715944750993949 2307274486393479281622731)
                      ·
                        rfl

theorem cell23_4493401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_4493401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493401 prefixEnd_4493401 := by exact prefixLift 4493401
  have htrace : WordTrace (prefixWord ++ tailWord_4493401) baseStart_4493401 baseEnd_4493401 := by
    simpa [prefixWord, tailWord_4493401, baseEnd_4493401] using wordTrace_append hprefix tailTrace_4493401
  have hstable : (prefixWord ++ tailWord_4493401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493401).length < 2 ^ (prefixWord ++ tailWord_4493401).sum := by decide
  have hdescent : baseEnd_4493401 < baseStart_4493401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493411 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 3, 3, 2]
def baseStart_4493411 : Nat := 118140960795 + 4493411 * 2 ^ 59
def prefixEnd_4493411 : Nat := 4983230072969 + 3 ^ 40 * 4493411 * 2
def baseEnd_4493411 : Nat := 2307279621200024242497685

theorem tailTrace_4493411 : CollatzResearch.WordTrace tailWord_4493411 prefixEnd_4493411 2307279621200024242497685 := by
  unfold tailWord_4493411
  simp only [CollatzResearch.WordTrace]
  refine ⟨163888163124146835347000087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109258775416097890231333391 163888163124146835347000087)
  ·
    refine ⟨245832244686220253020500131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163888163124146835347000087 245832244686220253020500131)
    ·
      refine ⟨368748367029330379530750197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245832244686220253020500131 368748367029330379530750197)
      ·
        refine ⟨34570159408999723081007831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 368748367029330379530750197 34570159408999723081007831)
        ·
          refine ⟨51855239113499584621511747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34570159408999723081007831 51855239113499584621511747)
          ·
            refine ⟨77782858670249376932267621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51855239113499584621511747 77782858670249376932267621)
            ·
              refine ⟨14584286000671758174800179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77782858670249376932267621 14584286000671758174800179)
              ·
                refine ⟨21876429001007637262200269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14584286000671758174800179 21876429001007637262200269)
                ·
                  refine ⟨8203660875377863973325101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21876429001007637262200269 8203660875377863973325101)
                  ·
                    refine ⟨3076372828266698989996913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8203660875377863973325101 3076372828266698989996913)
                    ·
                      refine ⟨2307279621200024242497685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076372828266698989996913 2307279621200024242497685)
                      ·
                        rfl

theorem cell23_4493411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_4493411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493411 prefixEnd_4493411 := by exact prefixLift 4493411
  have htrace : WordTrace (prefixWord ++ tailWord_4493411) baseStart_4493411 baseEnd_4493411 := by
    simpa [prefixWord, tailWord_4493411, baseEnd_4493411] using wordTrace_append hprefix tailTrace_4493411
  have hstable : (prefixWord ++ tailWord_4493411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493411).length < 2 ^ (prefixWord ++ tailWord_4493411).sum := by decide
  have hdescent : baseEnd_4493411 < baseStart_4493411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493417 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_4493417 : Nat := 118140960795 + 4493417 * 2 ^ 59
def prefixEnd_4493417 : Nat := 4983230072969 + 3 ^ 40 * 4493417 * 2
def baseEnd_4493417 : Nat := 769094234027983739674219

theorem tailTrace_4493417 : CollatzResearch.WordTrace tailWord_4493417 prefixEnd_4493417 769094234027983739674219 := by
  unfold tailWord_4493417
  simp only [CollatzResearch.WordTrace]
  refine ⟨163888381962125098371718505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109258921308083398914479003 163888381962125098371718505)
  ·
    refine ⟨122916286471593823778788879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163888381962125098371718505 122916286471593823778788879)
    ·
      refine ⟨184374429707390735668183319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122916286471593823778788879 184374429707390735668183319)
      ·
        refine ⟨276561644561086103502274979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184374429707390735668183319 276561644561086103502274979)
        ·
          refine ⟨414842466841629155253412469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276561644561086103502274979 414842466841629155253412469)
          ·
            refine ⟨38891481266402733305007419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 414842466841629155253412469 38891481266402733305007419)
            ·
              refine ⟨58337221899604099957511129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38891481266402733305007419 58337221899604099957511129)
              ·
                refine ⟨43752916424703074968133347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58337221899604099957511129 43752916424703074968133347)
                ·
                  refine ⟨65629374637054612452200021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43752916424703074968133347 65629374637054612452200021)
                  ·
                    refine ⟨769094234027983739674219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65629374637054612452200021 769094234027983739674219)
                    ·
                      rfl

theorem cell23_4493417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_4493417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493417 prefixEnd_4493417 := by exact prefixLift 4493417
  have htrace : WordTrace (prefixWord ++ tailWord_4493417) baseStart_4493417 baseEnd_4493417 := by
    simpa [prefixWord, tailWord_4493417, baseEnd_4493417] using wordTrace_append hprefix tailTrace_4493417
  have hstable : (prefixWord ++ tailWord_4493417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493417).length < 2 ^ (prefixWord ++ tailWord_4493417).sum := by decide
  have hdescent : baseEnd_4493417 < baseStart_4493417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493457 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_4493457 : Nat := 118140960795 + 4493457 * 2 ^ 59
def prefixEnd_4493457 : Nat := 4983230072969 + 3 ^ 40 * 4493457 * 2
def baseEnd_4493457 : Nat := 2307303241310131062522473

theorem tailTrace_4493457 : CollatzResearch.WordTrace tailWord_4493457 prefixEnd_4493457 2307303241310131062522473 := by
  unfold tailWord_4493457
  simp only [CollatzResearch.WordTrace]
  refine ⟨163889840881980185203174625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109259893921320123468783083 163889840881980185203174625)
  ·
    refine ⟨122917380661485138902380969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163889840881980185203174625 122917380661485138902380969)
    ·
      refine ⟨92188035496113854176785727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122917380661485138902380969 92188035496113854176785727)
      ·
        refine ⟨138282053244170781265178591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92188035496113854176785727 138282053244170781265178591)
        ·
          refine ⟨207423079866256171897767887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138282053244170781265178591 207423079866256171897767887)
          ·
            refine ⟨311134619799384257846651831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207423079866256171897767887 311134619799384257846651831)
            ·
              refine ⟨466701929699076386769977747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311134619799384257846651831 466701929699076386769977747)
              ·
                refine ⟨700052894548614580154966621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466701929699076386769977747 700052894548614580154966621)
                ·
                  refine ⟨262519835455730467558112483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700052894548614580154966621 262519835455730467558112483)
                  ·
                    refine ⟨393779753183595701337168725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 262519835455730467558112483 393779753183595701337168725)
                    ·
                      refine ⟨2307303241310131062522473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 393779753183595701337168725 2307303241310131062522473)
                      ·
                        rfl

theorem cell23_4493457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_4493457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493457 prefixEnd_4493457 := by exact prefixLift 4493457
  have htrace : WordTrace (prefixWord ++ tailWord_4493457) baseStart_4493457 baseEnd_4493457 := by
    simpa [prefixWord, tailWord_4493457, baseEnd_4493457] using wordTrace_append hprefix tailTrace_4493457
  have hstable : (prefixWord ++ tailWord_4493457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493457).length < 2 ^ (prefixWord ++ tailWord_4493457).sum := by decide
  have hdescent : baseEnd_4493457 < baseStart_4493457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_4493467 : Nat := 118140960795 + 4493467 * 2 ^ 59
def prefixEnd_4493467 : Nat := 4983230072969 + 3 ^ 40 * 4493467 * 2
def baseEnd_4493467 : Nat := 2307308376116676023397427

theorem tailTrace_4493467 : CollatzResearch.WordTrace tailWord_4493467 prefixEnd_4493467 2307308376116676023397427 := by
  unfold tailWord_4493467
  simp only [CollatzResearch.WordTrace]
  refine ⟨163890205611943956911038655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109260137074629304607359103 163890205611943956911038655)
  ·
    refine ⟨245835308417915935366557983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163890205611943956911038655 245835308417915935366557983)
    ·
      refine ⟨368752962626873903049836975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245835308417915935366557983 368752962626873903049836975)
      ·
        refine ⟨553129443940310854574755463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368752962626873903049836975 553129443940310854574755463)
        ·
          refine ⟨829694165910466281862133195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553129443940310854574755463 829694165910466281862133195)
          ·
            refine ⟨1244541248865699422793199793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829694165910466281862133195 1244541248865699422793199793)
            ·
              refine ⟨933405936649274567094899845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244541248865699422793199793 933405936649274567094899845)
              ·
                refine ⟨175013613121738981330293721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 933405936649274567094899845 175013613121738981330293721)
                ·
                  refine ⟨131260209841304235997720291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175013613121738981330293721 131260209841304235997720291)
                  ·
                    refine ⟨196890314761956353996580437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131260209841304235997720291 196890314761956353996580437)
                    ·
                      refine ⟨2307308376116676023397427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 196890314761956353996580437 2307308376116676023397427)
                      ·
                        rfl

theorem cell23_4493467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_4493467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493467 prefixEnd_4493467 := by exact prefixLift 4493467
  have htrace : WordTrace (prefixWord ++ tailWord_4493467) baseStart_4493467 baseEnd_4493467 := by
    simpa [prefixWord, tailWord_4493467, baseEnd_4493467] using wordTrace_append hprefix tailTrace_4493467
  have hstable : (prefixWord ++ tailWord_4493467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493467).length < 2 ^ (prefixWord ++ tailWord_4493467).sum := by decide
  have hdescent : baseEnd_4493467 < baseStart_4493467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493501 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4493501 : Nat := 118140960795 + 4493501 * 2 ^ 59
def prefixEnd_4493501 : Nat := 4983230072969 + 3 ^ 40 * 4493501 * 2
def baseEnd_4493501 : Nat := 2307325834458928890372271

theorem tailTrace_4493501 : CollatzResearch.WordTrace tailWord_4493501 prefixEnd_4493501 2307325834458928890372271 := by
  unfold tailWord_4493501
  simp only [CollatzResearch.WordTrace]
  refine ⟨163891445693820780717776357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109260963795880520478517571 163891445693820780717776357)
  ·
    refine ⟨30729646067591396384583067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163891445693820780717776357 30729646067591396384583067)
    ·
      refine ⟨46094469101387094576874601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30729646067591396384583067 46094469101387094576874601)
      ·
        refine ⟨34570851826040320932655951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46094469101387094576874601 34570851826040320932655951)
        ·
          refine ⟨51856277739060481398983927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34570851826040320932655951 51856277739060481398983927)
          ·
            refine ⟨77784416608590722098475891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51856277739060481398983927 77784416608590722098475891)
            ·
              refine ⟨116676624912886083147713837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77784416608590722098475891 116676624912886083147713837)
              ·
                refine ⟨43753734342332281180392689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116676624912886083147713837 43753734342332281180392689)
                ·
                  refine ⟨32815300756749210885294517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43753734342332281180392689 32815300756749210885294517)
                  ·
                    refine ⟨3076434445945238520496361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32815300756749210885294517 3076434445945238520496361)
                    ·
                      refine ⟨2307325834458928890372271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076434445945238520496361 2307325834458928890372271)
                      ·
                        rfl

theorem cell23_4493501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4493501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493501 prefixEnd_4493501 := by exact prefixLift 4493501
  have htrace : WordTrace (prefixWord ++ tailWord_4493501) baseStart_4493501 baseEnd_4493501 := by
    simpa [prefixWord, tailWord_4493501, baseEnd_4493501] using wordTrace_append hprefix tailTrace_4493501
  have hstable : (prefixWord ++ tailWord_4493501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493501).length < 2 ^ (prefixWord ++ tailWord_4493501).sum := by decide
  have hdescent : baseEnd_4493501 < baseStart_4493501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493504 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_4493504 : Nat := 118140960795 + 4493504 * 2 ^ 59
def prefixEnd_4493504 : Nat := 4983230072969 + 3 ^ 40 * 4493504 * 2
def baseEnd_4493504 : Nat := 2307327374900892378634757

theorem tailTrace_4493504 : CollatzResearch.WordTrace tailWord_4493504 prefixEnd_4493504 2307327374900892378634757 := by
  unfold tailWord_4493504
  simp only [CollatzResearch.WordTrace]
  refine ⟨81945777556404956115067783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109261036741873274820090377 81945777556404956115067783)
  ·
    refine ⟨122918666334607434172601675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81945777556404956115067783 122918666334607434172601675)
    ·
      refine ⟨184377999501911151258902513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122918666334607434172601675 184377999501911151258902513)
      ·
        refine ⟨138283499626433363444176885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184377999501911151258902513 138283499626433363444176885)
        ·
          refine ⟨12964078089978127822891583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138283499626433363444176885 12964078089978127822891583)
          ·
            refine ⟨19446117134967191734337375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12964078089978127822891583 19446117134967191734337375)
            ·
              refine ⟨29169175702450787601506063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19446117134967191734337375 29169175702450787601506063)
              ·
                refine ⟨43753763553676181402259095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29169175702450787601506063 43753763553676181402259095)
                ·
                  refine ⟨65630645330514272103388643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43753763553676181402259095 65630645330514272103388643)
                  ·
                    refine ⟨98445967995771408155082965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65630645330514272103388643 98445967995771408155082965)
                    ·
                      refine ⟨2307327374900892378634757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98445967995771408155082965 2307327374900892378634757)
                      ·
                        rfl

theorem cell23_4493504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_4493504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493504 prefixEnd_4493504 := by exact prefixLift 4493504
  have htrace : WordTrace (prefixWord ++ tailWord_4493504) baseStart_4493504 baseEnd_4493504 := by
    simpa [prefixWord, tailWord_4493504, baseEnd_4493504] using wordTrace_append hprefix tailTrace_4493504
  have hstable : (prefixWord ++ tailWord_4493504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493504).length < 2 ^ (prefixWord ++ tailWord_4493504).sum := by decide
  have hdescent : baseEnd_4493504 < baseStart_4493504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493575 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 3, 4]
def baseStart_4493575 : Nat := 118140960795 + 4493575 * 2 ^ 59
def prefixEnd_4493575 : Nat := 4983230072969 + 3 ^ 40 * 4493575 * 2
def baseEnd_4493575 : Nat := 769121277342453866948977

theorem tailTrace_4493575 : CollatzResearch.WordTrace tailWord_4493575 prefixEnd_4493575 769121277342453866948977 := by
  unfold tailWord_4493575
  simp only [CollatzResearch.WordTrace]
  refine ⟨163894144695552691355970179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109262763130368460903980119 163894144695552691355970179)
  ·
    refine ⟨245841217043329037033955269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163894144695552691355970179 245841217043329037033955269)
    ·
      refine ⟨46095228195624194443866613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245841217043329037033955269 46095228195624194443866613)
      ·
        refine ⟨4321427643339768229112495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46095228195624194443866613 4321427643339768229112495)
        ·
          refine ⟨6482141465009652343668743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321427643339768229112495 6482141465009652343668743)
          ·
            refine ⟨9723212197514478515503115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482141465009652343668743 9723212197514478515503115)
            ·
              refine ⟨14584818296271717773254673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9723212197514478515503115 14584818296271717773254673)
              ·
                refine ⟨10938613722203788329941005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14584818296271717773254673 10938613722203788329941005)
                ·
                  refine ⟨4101980145826420623727877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10938613722203788329941005 4101980145826420623727877)
                  ·
                    refine ⟨769121277342453866948977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4101980145826420623727877 769121277342453866948977)
                    ·
                      rfl

theorem cell23_4493575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_4493575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493575 prefixEnd_4493575 := by exact prefixLift 4493575
  have htrace : WordTrace (prefixWord ++ tailWord_4493575) baseStart_4493575 baseEnd_4493575 := by
    simpa [prefixWord, tailWord_4493575, baseEnd_4493575] using wordTrace_append hprefix tailTrace_4493575
  have hstable : (prefixWord ++ tailWord_4493575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493575).length < 2 ^ (prefixWord ++ tailWord_4493575).sum := by decide
  have hdescent : baseEnd_4493575 < baseStart_4493575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493605 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 6]
def baseStart_4493605 : Nat := 118140960795 + 4493605 * 2 ^ 59
def prefixEnd_4493605 : Nat := 4983230072969 + 3 ^ 40 * 4493605 * 2
def baseEnd_4493605 : Nat := 256375470716332942607977

theorem tailTrace_4493605 : CollatzResearch.WordTrace tailWord_4493605 prefixEnd_4493605 256375470716332942607977 := by
  unfold tailWord_4493605
  simp only [CollatzResearch.WordTrace]
  refine ⟨163895238885444006479562269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109263492590296004319708179 163895238885444006479562269)
  ·
    refine ⟨61460714582041502429835851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163895238885444006479562269 61460714582041502429835851)
    ·
      refine ⟨92191071873062253644753777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61460714582041502429835851 92191071873062253644753777)
      ·
        refine ⟨69143303904796690233565333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92191071873062253644753777 69143303904796690233565333)
        ·
          refine ⟨3241092370537344854698375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69143303904796690233565333 3241092370537344854698375)
          ·
            refine ⟨4861638555806017282047563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241092370537344854698375 4861638555806017282047563)
            ·
              refine ⟨7292457833709025923071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861638555806017282047563 7292457833709025923071345)
              ·
                refine ⟨5469343375281769442303509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7292457833709025923071345 5469343375281769442303509)
                ·
                  refine ⟨256375470716332942607977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5469343375281769442303509 256375470716332942607977)
                  ·
                    rfl

theorem cell23_4493605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_4493605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493605 prefixEnd_4493605 := by exact prefixLift 4493605
  have htrace : WordTrace (prefixWord ++ tailWord_4493605) baseStart_4493605 baseEnd_4493605 := by
    simpa [prefixWord, tailWord_4493605, baseEnd_4493605] using wordTrace_append hprefix tailTrace_4493605
  have hstable : (prefixWord ++ tailWord_4493605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493605).length < 2 ^ (prefixWord ++ tailWord_4493605).sum := by decide
  have hdescent : baseEnd_4493605 < baseStart_4493605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493615 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 1, 1, 3]
def baseStart_4493615 : Nat := 118140960795 + 4493615 * 2 ^ 59
def prefixEnd_4493615 : Nat := 4983230072969 + 3 ^ 40 * 4493615 * 2
def baseEnd_4493615 : Nat := 2307384371253541444346747

theorem tailTrace_4493615 : CollatzResearch.WordTrace tailWord_4493615 prefixEnd_4493615 2307384371253541444346747 := by
  unfold tailWord_4493615
  simp only [CollatzResearch.WordTrace]
  refine ⟨163895603615407778187426299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109263735743605185458284199 163895603615407778187426299)
  ·
    refine ⟨245843405423111667281139449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163895603615407778187426299 245843405423111667281139449)
    ·
      refine ⟨184382554067333750460854587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245843405423111667281139449 184382554067333750460854587)
      ·
        refine ⟨276573831101000625691281881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184382554067333750460854587 276573831101000625691281881)
        ·
          refine ⟨207430373325750469268461411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276573831101000625691281881 207430373325750469268461411)
          ·
            refine ⟨311145559988625703902692117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207430373325750469268461411 311145559988625703902692117)
            ·
              refine ⟨14584948124466829870438693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 311145559988625703902692117 14584948124466829870438693)
              ·
                refine ⟨2734677773337530600707255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14584948124466829870438693 2734677773337530600707255)
                ·
                  refine ⟨4102016660006295901060883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734677773337530600707255 4102016660006295901060883)
                  ·
                    refine ⟨6153024990009443851591325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102016660006295901060883 6153024990009443851591325)
                    ·
                      refine ⟨2307384371253541444346747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153024990009443851591325 2307384371253541444346747)
                      ·
                        rfl

theorem cell23_4493615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 1, 3].length) (baseStart_4493615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493615 prefixEnd_4493615 := by exact prefixLift 4493615
  have htrace : WordTrace (prefixWord ++ tailWord_4493615) baseStart_4493615 baseEnd_4493615 := by
    simpa [prefixWord, tailWord_4493615, baseEnd_4493615] using wordTrace_append hprefix tailTrace_4493615
  have hstable : (prefixWord ++ tailWord_4493615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493615).length < 2 ^ (prefixWord ++ tailWord_4493615).sum := by decide
  have hdescent : baseEnd_4493615 < baseStart_4493615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493672 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4493672 : Nat := 118140960795 + 4493672 * 2 ^ 59
def prefixEnd_4493672 : Nat := 4983230072969 + 3 ^ 40 * 4493672 * 2
def baseEnd_4493672 : Nat := 2307413639650847721333985

theorem tailTrace_4493672 : CollatzResearch.WordTrace tailWord_4493672 prefixEnd_4493672 2307413639650847721333985 := by
  unfold tailWord_4493672
  simp only [CollatzResearch.WordTrace]
  refine ⟨81948841288100638461125635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109265121717467517948167513 81948841288100638461125635)
  ·
    refine ⟨122923261932150957691688453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81948841288100638461125635 122923261932150957691688453)
    ·
      refine ⟨23048111612278304567191585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122923261932150957691688453 23048111612278304567191585)
      ·
        refine ⟨17286083709208728425393689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23048111612278304567191585 17286083709208728425393689)
        ·
          refine ⟨12964562781906546319045267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17286083709208728425393689 12964562781906546319045267)
          ·
            refine ⟨19446844172859819478567901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12964562781906546319045267 19446844172859819478567901)
            ·
              refine ⟨7292566564822432304462963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19446844172859819478567901 7292566564822432304462963)
              ·
                refine ⟨10938849847233648456694445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7292566564822432304462963 10938849847233648456694445)
                ·
                  refine ⟨4102068692712618171260417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10938849847233648456694445 4102068692712618171260417)
                  ·
                    refine ⟨3076551519534463628445313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102068692712618171260417 3076551519534463628445313)
                    ·
                      refine ⟨2307413639650847721333985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076551519534463628445313 2307413639650847721333985)
                      ·
                        rfl

theorem cell23_4493672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4493672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493672 prefixEnd_4493672 := by exact prefixLift 4493672
  have htrace : WordTrace (prefixWord ++ tailWord_4493672) baseStart_4493672 baseEnd_4493672 := by
    simpa [prefixWord, tailWord_4493672, baseEnd_4493672] using wordTrace_append hprefix tailTrace_4493672
  have hstable : (prefixWord ++ tailWord_4493672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493672).length < 2 ^ (prefixWord ++ tailWord_4493672).sum := by decide
  have hdescent : baseEnd_4493672 < baseStart_4493672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493682 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_4493682 : Nat := 118140960795 + 4493682 * 2 ^ 59
def prefixEnd_4493682 : Nat := 4983230072969 + 3 ^ 40 * 4493682 * 2
def baseEnd_4493682 : Nat := 769139591485797560736313

theorem tailTrace_4493682 : CollatzResearch.WordTrace tailWord_4493682 prefixEnd_4493682 769139591485797560736313 := by
  unfold tailWord_4493682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40974511826541262157528825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109265364870776699086743533 40974511826541262157528825)
  ·
    refine ⟨30730883869905946618146619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40974511826541262157528825 30730883869905946618146619)
    ·
      refine ⟨46096325804858919927219929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30730883869905946618146619 46096325804858919927219929)
      ·
        refine ⟨34572244353644189945414947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46096325804858919927219929 34572244353644189945414947)
        ·
          refine ⟨51858366530466284918122421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34572244353644189945414947 51858366530466284918122421)
          ·
            refine ⟨4861721862231214211073977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51858366530466284918122421 4861721862231214211073977)
            ·
              refine ⟨3646291396673410658305483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861721862231214211073977 3646291396673410658305483)
              ·
                refine ⟨5469437095010115987458225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646291396673410658305483 5469437095010115987458225)
                ·
                  refine ⟨4102077821257586990593669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469437095010115987458225 4102077821257586990593669)
                  ·
                    refine ⟨769139591485797560736313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102077821257586990593669 769139591485797560736313)
                    ·
                      rfl

theorem cell23_4493682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_4493682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493682 prefixEnd_4493682 := by exact prefixLift 4493682
  have htrace : WordTrace (prefixWord ++ tailWord_4493682) baseStart_4493682 baseEnd_4493682 := by
    simpa [prefixWord, tailWord_4493682, baseEnd_4493682] using wordTrace_append hprefix tailTrace_4493682
  have hstable : (prefixWord ++ tailWord_4493682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493682).length < 2 ^ (prefixWord ++ tailWord_4493682).sum := by decide
  have hdescent : baseEnd_4493682 < baseStart_4493682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493721 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_4493721 : Nat := 118140960795 + 4493721 * 2 ^ 59
def prefixEnd_4493721 : Nat := 4983230072969 + 3 ^ 40 * 4493721 * 2
def baseEnd_4493721 : Nat := 769146266734306009873753

theorem tailTrace_4493721 : CollatzResearch.WordTrace tailWord_4493721 prefixEnd_4493721 769146266734306009873753 := by
  unfold tailWord_4493721
  simp only [CollatzResearch.WordTrace]
  refine ⟨163899469753023758290785017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109266313168682505527190011 163899469753023758290785017)
  ·
    refine ⟨122924602314767818718088763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163899469753023758290785017 122924602314767818718088763)
    ·
      refine ⟨184386903472151728077133145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122924602314767818718088763 184386903472151728077133145)
      ·
        refine ⟨138290177604113796057849859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184386903472151728077133145 138290177604113796057849859)
        ·
          refine ⟨207435266406170694086774789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138290177604113796057849859 207435266406170694086774789)
          ·
            refine ⟨38894112451157005141270273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207435266406170694086774789 38894112451157005141270273)
            ·
              refine ⟨29170584338367753855952705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38894112451157005141270273 29170584338367753855952705)
              ·
                refine ⟨21877938253775815391964529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29170584338367753855952705 21877938253775815391964529)
                ·
                  refine ⟨16408453690331861543973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21877938253775815391964529 16408453690331861543973397)
                  ·
                    refine ⟨769146266734306009873753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16408453690331861543973397 769146266734306009873753)
                    ·
                      rfl

theorem cell23_4493721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_4493721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493721 prefixEnd_4493721 := by exact prefixLift 4493721
  have htrace : WordTrace (prefixWord ++ tailWord_4493721) baseStart_4493721 baseEnd_4493721 := by
    simpa [prefixWord, tailWord_4493721, baseEnd_4493721] using wordTrace_append hprefix tailTrace_4493721
  have hstable : (prefixWord ++ tailWord_4493721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493721).length < 2 ^ (prefixWord ++ tailWord_4493721).sum := by decide
  have hdescent : baseEnd_4493721 < baseStart_4493721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493722 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4493722 : Nat := 118140960795 + 4493722 * 2 ^ 59
def prefixEnd_4493722 : Nat := 4983230072969 + 3 ^ 40 * 4493722 * 2
def baseEnd_4493722 : Nat := 2307439313683572525708755

theorem tailTrace_4493722 : CollatzResearch.WordTrace tailWord_4493722 prefixEnd_4493722 2307439313683572525708755 := by
  unfold tailWord_4493722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40974876556505033865392855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109266337484013423641047613 40974876556505033865392855)
  ·
    refine ⟨61462314834757550798089283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40974876556505033865392855 61462314834757550798089283)
    ·
      refine ⟨92193472252136326197133925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61462314834757550798089283 92193472252136326197133925)
      ·
        refine ⟨17286276047275561161962611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92193472252136326197133925 17286276047275561161962611)
        ·
          refine ⟨25929414070913341742943917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17286276047275561161962611 25929414070913341742943917)
          ·
            refine ⟨9723530276592503153603969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25929414070913341742943917 9723530276592503153603969)
            ·
              refine ⟨7292647707444377365202977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9723530276592503153603969 7292647707444377365202977)
              ·
                refine ⟨5469485780583283023902233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7292647707444377365202977 5469485780583283023902233)
                ·
                  refine ⟨4102114335437462267926675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469485780583283023902233 4102114335437462267926675)
                  ·
                    refine ⟨6153171503156193401890013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102114335437462267926675 6153171503156193401890013)
                    ·
                      refine ⟨2307439313683572525708755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153171503156193401890013 2307439313683572525708755)
                      ·
                        rfl

theorem cell23_4493722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4493722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493722 prefixEnd_4493722 := by exact prefixLift 4493722
  have htrace : WordTrace (prefixWord ++ tailWord_4493722) baseStart_4493722 baseEnd_4493722 := by
    simpa [prefixWord, tailWord_4493722, baseEnd_4493722] using wordTrace_append hprefix tailTrace_4493722
  have hstable : (prefixWord ++ tailWord_4493722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493722).length < 2 ^ (prefixWord ++ tailWord_4493722).sum := by decide
  have hdescent : baseEnd_4493722 < baseStart_4493722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493745 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4493745 : Nat := 118140960795 + 4493745 * 2 ^ 59
def prefixEnd_4493745 : Nat := 4983230072969 + 3 ^ 40 * 4493745 * 2
def baseEnd_4493745 : Nat := 2307451123738625935721149

theorem tailTrace_4493745 : CollatzResearch.WordTrace tailWord_4493745 prefixEnd_4493745 2307451123738625935721149 := by
  unfold tailWord_4493745
  simp only [CollatzResearch.WordTrace]
  refine ⟨163900345104936810389658689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109266896736624540259772459 163900345104936810389658689)
  ·
    refine ⟨122925258828702607792244017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163900345104936810389658689 122925258828702607792244017)
    ·
      refine ⟨92193944121526955844183013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122925258828702607792244017 92193944121526955844183013)
      ·
        refine ⟨17286364522786304220784315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92193944121526955844183013 17286364522786304220784315)
        ·
          refine ⟨25929546784179456331176473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17286364522786304220784315 25929546784179456331176473)
          ·
            refine ⟨19447160088134592248382355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25929546784179456331176473 19447160088134592248382355)
            ·
              refine ⟨29170740132201888372573533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19447160088134592248382355 29170740132201888372573533)
              ·
                refine ⟨10939027549575708139715075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29170740132201888372573533 10939027549575708139715075)
                ·
                  refine ⟨16408541324363562209572613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10939027549575708139715075 16408541324363562209572613)
                  ·
                    refine ⟨3076601498318167914294865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16408541324363562209572613 3076601498318167914294865)
                    ·
                      refine ⟨2307451123738625935721149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076601498318167914294865 2307451123738625935721149)
                      ·
                        rfl

theorem cell23_4493745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4493745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493745 prefixEnd_4493745 := by exact prefixLift 4493745
  have htrace : WordTrace (prefixWord ++ tailWord_4493745) baseStart_4493745 baseEnd_4493745 := by
    simpa [prefixWord, tailWord_4493745, baseEnd_4493745] using wordTrace_append hprefix tailTrace_4493745
  have hstable : (prefixWord ++ tailWord_4493745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493745).length < 2 ^ (prefixWord ++ tailWord_4493745).sum := by decide
  have hdescent : baseEnd_4493745 < baseStart_4493745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493751 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 9]
def baseStart_4493751 : Nat := 118140960795 + 4493751 * 2 ^ 59
def prefixEnd_4493751 : Nat := 4983230072969 + 3 ^ 40 * 4493751 * 2
def baseEnd_4493751 : Nat := 256383800513616990249569

theorem tailTrace_4493751 : CollatzResearch.WordTrace tailWord_4493751 prefixEnd_4493751 256383800513616990249569 := by
  unfold tailWord_4493751
  simp only [CollatzResearch.WordTrace]
  refine ⟨163900563942915073414377107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109267042628610048942918071 163900563942915073414377107)
  ·
    refine ⟨245850845914372610121565661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163900563942915073414377107 245850845914372610121565661)
    ·
      refine ⟨92194067217889728795587123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245850845914372610121565661 92194067217889728795587123)
      ·
        refine ⟨138291100826834593193380685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92194067217889728795587123 138291100826834593193380685)
        ·
          refine ⟨51859162810062972447517757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138291100826834593193380685 51859162810062972447517757)
          ·
            refine ⟨19447186053773614667819159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51859162810062972447517757 19447186053773614667819159)
            ·
              refine ⟨29170779080660422001728739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19447186053773614667819159 29170779080660422001728739)
              ·
                refine ⟨43756168620990633002593109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29170779080660422001728739 43756168620990633002593109)
                ·
                  refine ⟨256383800513616990249569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43756168620990633002593109 256383800513616990249569)
                  ·
                    rfl

theorem cell23_4493751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 9].length) (baseStart_4493751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493751 prefixEnd_4493751 := by exact prefixLift 4493751
  have htrace : WordTrace (prefixWord ++ tailWord_4493751) baseStart_4493751 baseEnd_4493751 := by
    simpa [prefixWord, tailWord_4493751, baseEnd_4493751] using wordTrace_append hprefix tailTrace_4493751
  have hstable : (prefixWord ++ tailWord_4493751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493751).length < 2 ^ (prefixWord ++ tailWord_4493751).sum := by decide
  have hdescent : baseEnd_4493751 < baseStart_4493751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493811 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 8]
def baseStart_4493811 : Nat := 118140960795 + 4493811 * 2 ^ 59
def prefixEnd_4493811 : Nat := 4983230072969 + 3 ^ 40 * 4493811 * 2
def baseEnd_4493811 : Nat := 769161671153940892498615

theorem tailTrace_4493811 : CollatzResearch.WordTrace tailWord_4493811 prefixEnd_4493811 769161671153940892498615 := by
  unfold tailWord_4493811
  simp only [CollatzResearch.WordTrace]
  refine ⟨163902752322697703661561287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109268501548465135774374191 163902752322697703661561287)
  ·
    refine ⟨245854128484046555492341931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163902752322697703661561287 245854128484046555492341931)
    ·
      refine ⟨368781192726069833238512897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245854128484046555492341931 368781192726069833238512897)
      ·
        refine ⟨276585894544552374928884673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368781192726069833238512897 276585894544552374928884673)
        ·
          refine ⟨207439420908414281196663505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276585894544552374928884673 207439420908414281196663505)
          ·
            refine ⟨155579565681310710897497629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207439420908414281196663505 155579565681310710897497629)
            ·
              refine ⟨58342337130491516586561611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155579565681310710897497629 58342337130491516586561611)
              ·
                refine ⟨87513505695737274879842417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58342337130491516586561611 87513505695737274879842417)
                ·
                  refine ⟨65635129271802956159881813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87513505695737274879842417 65635129271802956159881813)
                  ·
                    refine ⟨769161671153940892498615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65635129271802956159881813 769161671153940892498615)
                    ·
                      rfl

theorem cell23_4493811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_4493811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493811 prefixEnd_4493811 := by exact prefixLift 4493811
  have htrace : WordTrace (prefixWord ++ tailWord_4493811) baseStart_4493811 baseEnd_4493811 := by
    simpa [prefixWord, tailWord_4493811, baseEnd_4493811] using wordTrace_append hprefix tailTrace_4493811
  have hstable : (prefixWord ++ tailWord_4493811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493811).length < 2 ^ (prefixWord ++ tailWord_4493811).sum := by decide
  have hdescent : baseEnd_4493811 < baseStart_4493811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493835 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4]
def baseStart_4493835 : Nat := 118140960795 + 4493835 * 2 ^ 59
def prefixEnd_4493835 : Nat := 4983230072969 + 3 ^ 40 * 4493835 * 2
def baseEnd_4493835 : Nat := 2307497336997530583595735

theorem tailTrace_4493835 : CollatzResearch.WordTrace tailWord_4493835 prefixEnd_4493835 2307497336997530583595735 := by
  unfold tailWord_4493835
  simp only [CollatzResearch.WordTrace]
  refine ⟨163903627674610755760434959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109269085116407170506956639 163903627674610755760434959)
  ·
    refine ⟨245855441511916133640652439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163903627674610755760434959 245855441511916133640652439)
    ·
      refine ⟨368783162267874200460978659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245855441511916133640652439 368783162267874200460978659)
      ·
        refine ⟨553174743401811300691467989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368783162267874200460978659 553174743401811300691467989)
        ·
          refine ⟨12965033048479952359956281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 553174743401811300691467989 12965033048479952359956281)
          ·
            refine ⟨9723774786359964269967211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12965033048479952359956281 9723774786359964269967211)
            ·
              refine ⟨14585662179539946404950817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9723774786359964269967211 14585662179539946404950817)
              ·
                refine ⟨10939246634654959803713113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14585662179539946404950817 10939246634654959803713113)
                ·
                  refine ⟨8204434975991219852784835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10939246634654959803713113 8204434975991219852784835)
                  ·
                    refine ⟨12306652463986829779177253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8204434975991219852784835 12306652463986829779177253)
                    ·
                      refine ⟨2307497336997530583595735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12306652463986829779177253 2307497336997530583595735)
                      ·
                        rfl

theorem cell23_4493835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_4493835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493835 prefixEnd_4493835 := by exact prefixLift 4493835
  have htrace : WordTrace (prefixWord ++ tailWord_4493835) baseStart_4493835 baseEnd_4493835 := by
    simpa [prefixWord, tailWord_4493835, baseEnd_4493835] using wordTrace_append hprefix tailTrace_4493835
  have hstable : (prefixWord ++ tailWord_4493835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493835).length < 2 ^ (prefixWord ++ tailWord_4493835).sum := by decide
  have hdescent : baseEnd_4493835 < baseStart_4493835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493868 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_4493868 : Nat := 118140960795 + 4493868 * 2 ^ 59
def prefixEnd_4493868 : Nat := 4983230072969 + 3 ^ 40 * 4493868 * 2
def baseEnd_4493868 : Nat := 2307514281859128954483083

theorem tailTrace_4493868 : CollatzResearch.WordTrace tailWord_4493868 prefixEnd_4493868 2307514281859128954483083 := by
  unfold tailWord_4493868
  simp only [CollatzResearch.WordTrace]
  refine ⟨81952415641745601198193129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109269887522327468264257505 81952415641745601198193129)
  ·
    refine ⟨61464311731309200898644847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81952415641745601198193129 61464311731309200898644847)
    ·
      refine ⟨92196467596963801347967271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61464311731309200898644847 92196467596963801347967271)
      ·
        refine ⟨138294701395445702021950907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92196467596963801347967271 138294701395445702021950907)
        ·
          refine ⟨207442052093168553032926361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138294701395445702021950907 207442052093168553032926361)
          ·
            refine ⟨155581539069876414774694771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207442052093168553032926361 155581539069876414774694771)
            ·
              refine ⟨233372308604814622162042157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155581539069876414774694771 233372308604814622162042157)
              ·
                refine ⟨87514615726805483310765809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233372308604814622162042157 87514615726805483310765809)
                ·
                  refine ⟨65635961795104112483074357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87514615726805483310765809 65635961795104112483074357)
                  ·
                    refine ⟨6153371418291010545288221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65635961795104112483074357 6153371418291010545288221)
                    ·
                      refine ⟨2307514281859128954483083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153371418291010545288221 2307514281859128954483083)
                      ·
                        rfl

theorem cell23_4493868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_4493868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493868 prefixEnd_4493868 := by exact prefixLift 4493868
  have htrace : WordTrace (prefixWord ++ tailWord_4493868) baseStart_4493868 baseEnd_4493868 := by
    simpa [prefixWord, tailWord_4493868, baseEnd_4493868] using wordTrace_append hprefix tailTrace_4493868
  have hstable : (prefixWord ++ tailWord_4493868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493868).length < 2 ^ (prefixWord ++ tailWord_4493868).sum := by decide
  have hdescent : baseEnd_4493868 < baseStart_4493868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493936 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 1, 1, 3]
def baseStart_4493936 : Nat := 118140960795 + 4493936 * 2 ^ 59
def prefixEnd_4493936 : Nat := 4983230072969 + 3 ^ 40 * 4493936 * 2
def baseEnd_4493936 : Nat := 2307549198543634688432771

theorem tailTrace_4493936 : CollatzResearch.WordTrace tailWord_4493936 prefixEnd_4493936 2307549198543634688432771 := by
  unfold tailWord_4493936
  simp only [CollatzResearch.WordTrace]
  refine ⟨81953655723622425004930831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109271540964829900006574441 81953655723622425004930831)
  ·
    refine ⟨122930483585433637507396247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81953655723622425004930831 122930483585433637507396247)
    ·
      refine ⟨184395725378150456261094371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122930483585433637507396247 184395725378150456261094371)
      ·
        refine ⟨276593588067225684391641557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184395725378150456261094371 276593588067225684391641557)
        ·
          refine ⟨6482662220325601977929099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 276593588067225684391641557 6482662220325601977929099)
          ·
            refine ⟨9723993330488402966893649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482662220325601977929099 9723993330488402966893649)
            ·
              refine ⟨7292994997866302225170237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9723993330488402966893649 7292994997866302225170237)
              ·
                refine ⟨2734873124199863334438839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7292994997866302225170237 2734873124199863334438839)
                ·
                  refine ⟨4102309686299795001658259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734873124199863334438839 4102309686299795001658259)
                  ·
                    refine ⟨6153464529449692502487389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102309686299795001658259 6153464529449692502487389)
                    ·
                      refine ⟨2307549198543634688432771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153464529449692502487389 2307549198543634688432771)
                      ·
                        rfl

theorem cell23_4493936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 1, 3].length) (baseStart_4493936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493936 prefixEnd_4493936 := by exact prefixLift 4493936
  have htrace : WordTrace (prefixWord ++ tailWord_4493936) baseStart_4493936 baseEnd_4493936 := by
    simpa [prefixWord, tailWord_4493936, baseEnd_4493936] using wordTrace_append hprefix tailTrace_4493936
  have hstable : (prefixWord ++ tailWord_4493936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493936).length < 2 ^ (prefixWord ++ tailWord_4493936).sum := by decide
  have hdescent : baseEnd_4493936 < baseStart_4493936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493952 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_4493952 : Nat := 118140960795 + 4493952 * 2 ^ 59
def prefixEnd_4493952 : Nat := 4983230072969 + 3 ^ 40 * 4493952 * 2
def baseEnd_4493952 : Nat := 769185804744702208610899

theorem tailTrace_4493952 : CollatzResearch.WordTrace tailWord_4493952 prefixEnd_4493952 769185804744702208610899 := by
  unfold tailWord_4493952
  simp only [CollatzResearch.WordTrace]
  refine ⟨81953947507593442371222055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109271930010124589828296073 81953947507593442371222055)
  ·
    refine ⟨122930921261390163556833083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81953947507593442371222055 122930921261390163556833083)
    ·
      refine ⟨184396381892085245335249625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122930921261390163556833083 184396381892085245335249625)
      ·
        refine ⟨138297286419063934001437219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184396381892085245335249625 138297286419063934001437219)
        ·
          refine ⟨207445929628595901002155829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138297286419063934001437219 207445929628595901002155829)
          ·
            refine ⟨19448055902680865718952109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207445929628595901002155829 19448055902680865718952109)
            ·
              refine ⟨7293020963505324644607041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19448055902680865718952109 7293020963505324644607041)
              ·
                refine ⟨5469765722628993483455281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7293020963505324644607041 5469765722628993483455281)
                ·
                  refine ⟨4102324291971745112591461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469765722628993483455281 4102324291971745112591461)
                  ·
                    refine ⟨769185804744702208610899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102324291971745112591461 769185804744702208610899)
                    ·
                      rfl

theorem cell23_4493952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_4493952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493952 prefixEnd_4493952 := by exact prefixLift 4493952
  have htrace : WordTrace (prefixWord ++ tailWord_4493952) baseStart_4493952 baseEnd_4493952 := by
    simpa [prefixWord, tailWord_4493952, baseEnd_4493952] using wordTrace_append hprefix tailTrace_4493952
  have hstable : (prefixWord ++ tailWord_4493952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493952).length < 2 ^ (prefixWord ++ tailWord_4493952).sum := by decide
  have hdescent : baseEnd_4493952 < baseStart_4493952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493959 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_4493959 : Nat := 118140960795 + 4493959 * 2 ^ 59
def prefixEnd_4493959 : Nat := 4983230072969 + 3 ^ 40 * 4493959 * 2
def baseEnd_4493959 : Nat := 2307561008598688098445165

theorem tailTrace_4493959 : CollatzResearch.WordTrace tailWord_4493959 prefixEnd_4493959 2307561008598688098445165 := by
  unfold tailWord_4493959
  simp only [CollatzResearch.WordTrace]
  refine ⟨163908150326161524937948931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109272100217441016625299287 163908150326161524937948931)
  ·
    refine ⟨245862225489242287406923397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163908150326161524937948931 245862225489242287406923397)
    ·
      refine ⟨46099167279232928888798137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245862225489242287406923397 46099167279232928888798137)
      ·
        refine ⟨34574375459424696666598603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46099167279232928888798137 34574375459424696666598603)
        ·
          refine ⟨51861563189137044999897905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34574375459424696666598603 51861563189137044999897905)
          ·
            refine ⟨38896172391852783749923429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51861563189137044999897905 38896172391852783749923429)
            ·
              refine ⟨7293032323472396953110643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38896172391852783749923429 7293032323472396953110643)
              ·
                refine ⟨10939548485208595429665965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7293032323472396953110643 10939548485208595429665965)
                ·
                  refine ⟨4102330681953223286124737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10939548485208595429665965 4102330681953223286124737)
                  ·
                    refine ⟨3076748011464917464593553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102330681953223286124737 3076748011464917464593553)
                    ·
                      refine ⟨2307561008598688098445165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076748011464917464593553 2307561008598688098445165)
                      ·
                        rfl

theorem cell23_4493959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_4493959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493959 prefixEnd_4493959 := by exact prefixLift 4493959
  have htrace : WordTrace (prefixWord ++ tailWord_4493959) baseStart_4493959 baseEnd_4493959 := by
    simpa [prefixWord, tailWord_4493959, baseEnd_4493959] using wordTrace_append hprefix tailTrace_4493959
  have hstable : (prefixWord ++ tailWord_4493959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493959).length < 2 ^ (prefixWord ++ tailWord_4493959).sum := by decide
  have hdescent : baseEnd_4493959 < baseStart_4493959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493962 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_4493962 : Nat := 118140960795 + 4493962 * 2 ^ 59
def prefixEnd_4493962 : Nat := 4983230072969 + 3 ^ 40 * 4493962 * 2
def baseEnd_4493962 : Nat := 2307562549040651586707651

theorem tailTrace_4493962 : CollatzResearch.WordTrace tailWord_4493962 prefixEnd_4493962 2307562549040651586707651 := by
  unfold tailWord_4493962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40977064936287664112577035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109272173163433770966872093 40977064936287664112577035)
  ·
    refine ⟨61465597404431496168865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40977064936287664112577035 61465597404431496168865553)
    ·
      refine ⟨46099198053323622126649165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61465597404431496168865553 46099198053323622126649165)
      ·
        refine ⟨17287199269996358297493437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46099198053323622126649165 17287199269996358297493437)
        ·
          refine ⟨6482699726248634361560039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17287199269996358297493437 6482699726248634361560039)
          ·
            refine ⟨9724049589372951542340059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482699726248634361560039 9724049589372951542340059)
            ·
              refine ⟨14586074384059427313510089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724049589372951542340059 14586074384059427313510089)
              ·
                refine ⟨10939555788044570485132567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14586074384059427313510089 10939555788044570485132567)
                ·
                  refine ⟨16409333682066855727698851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10939555788044570485132567 16409333682066855727698851)
                  ·
                    refine ⟨24614000523100283591548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16409333682066855727698851 24614000523100283591548277)
                    ·
                      refine ⟨2307562549040651586707651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24614000523100283591548277 2307562549040651586707651)
                      ·
                        rfl

theorem cell23_4493962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_4493962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493962 prefixEnd_4493962 := by exact prefixLift 4493962
  have htrace : WordTrace (prefixWord ++ tailWord_4493962) baseStart_4493962 baseEnd_4493962 := by
    simpa [prefixWord, tailWord_4493962, baseEnd_4493962] using wordTrace_append hprefix tailTrace_4493962
  have hstable : (prefixWord ++ tailWord_4493962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493962).length < 2 ^ (prefixWord ++ tailWord_4493962).sum := by decide
  have hdescent : baseEnd_4493962 < baseStart_4493962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4493972 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4493972 : Nat := 118140960795 + 4493972 * 2 ^ 59
def prefixEnd_4493972 : Nat := 4983230072969 + 3 ^ 40 * 4493972 * 2
def baseEnd_4493972 : Nat := 2307567683847196547582605

theorem tailTrace_4493972 : CollatzResearch.WordTrace tailWord_4493972 prefixEnd_4493972 2307567683847196547582605 := by
  unfold tailWord_4493972
  simp only [CollatzResearch.WordTrace]
  refine ⟨81954312237557214079086085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109272416316742952105448113 81954312237557214079086085)
  ·
    refine ⟨15366433544541977639828641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81954312237557214079086085 15366433544541977639828641)
    ·
      refine ⟨11524825158406483229871481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15366433544541977639828641 11524825158406483229871481)
      ·
        refine ⟨8643618868804862422403611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11524825158406483229871481 8643618868804862422403611)
        ·
          refine ⟨12965428303207293633605417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8643618868804862422403611 12965428303207293633605417)
          ·
            refine ⟨9724071227405470225204063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12965428303207293633605417 9724071227405470225204063)
            ·
              refine ⟨14586106841108205337806095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724071227405470225204063 14586106841108205337806095)
              ·
                refine ⟨21879160261662308006709143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14586106841108205337806095 21879160261662308006709143)
                ·
                  refine ⟨32818740392493462010063715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21879160261662308006709143 32818740392493462010063715)
                  ·
                    refine ⟨49228110588740193015095573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32818740392493462010063715 49228110588740193015095573)
                    ·
                      refine ⟨2307567683847196547582605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49228110588740193015095573 2307567683847196547582605)
                      ·
                        rfl

theorem cell23_4493972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4493972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4493972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4493972 prefixEnd_4493972 := by exact prefixLift 4493972
  have htrace : WordTrace (prefixWord ++ tailWord_4493972) baseStart_4493972 baseEnd_4493972 := by
    simpa [prefixWord, tailWord_4493972, baseEnd_4493972] using wordTrace_append hprefix tailTrace_4493972
  have hstable : (prefixWord ++ tailWord_4493972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4493972).length < 2 ^ (prefixWord ++ tailWord_4493972).sum := by decide
  have hdescent : baseEnd_4493972 < baseStart_4493972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4493972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494002 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_4494002 : Nat := 118140960795 + 4494002 * 2 ^ 59
def prefixEnd_4494002 : Nat := 4983230072969 + 3 ^ 40 * 4494002 * 2
def baseEnd_4494002 : Nat := 2307583088266831430207467

theorem tailTrace_4494002 : CollatzResearch.WordTrace tailWord_4494002 prefixEnd_4494002 2307583088266831430207467 := by
  unfold tailWord_4494002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40977429666251435820441065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109273145776670495521176173 40977429666251435820441065)
  ·
    refine ⟨30733072249688576865330799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40977429666251435820441065 30733072249688576865330799)
    ·
      refine ⟨46099608374532865297996199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30733072249688576865330799 46099608374532865297996199)
      ·
        refine ⟨69149412561799297946994299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46099608374532865297996199 69149412561799297946994299)
        ·
          refine ⟨103724118842698946920491449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69149412561799297946994299 103724118842698946920491449)
          ·
            refine ⟨77793089132024210190368587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103724118842698946920491449 77793089132024210190368587)
            ·
              refine ⟨116689633698036315285552881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77793089132024210190368587 116689633698036315285552881)
              ·
                refine ⟨87517225273527236464164661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116689633698036315285552881 87517225273527236464164661)
                ·
                  refine ⟨8204739869393178418515437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87517225273527236464164661 8204739869393178418515437)
                  ·
                    refine ⟨3076777451022441906943289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8204739869393178418515437 3076777451022441906943289)
                    ·
                      refine ⟨2307583088266831430207467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076777451022441906943289 2307583088266831430207467)
                      ·
                        rfl

theorem cell23_4494002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_4494002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494002 prefixEnd_4494002 := by exact prefixLift 4494002
  have htrace : WordTrace (prefixWord ++ tailWord_4494002) baseStart_4494002 baseEnd_4494002 := by
    simpa [prefixWord, tailWord_4494002, baseEnd_4494002] using wordTrace_append hprefix tailTrace_4494002
  have hstable : (prefixWord ++ tailWord_4494002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494002).length < 2 ^ (prefixWord ++ tailWord_4494002).sum := by decide
  have hdescent : baseEnd_4494002 < baseStart_4494002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494026 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_4494026 : Nat := 118140960795 + 4494026 * 2 ^ 59
def prefixEnd_4494026 : Nat := 4983230072969 + 3 ^ 40 * 4494026 * 2
def baseEnd_4494026 : Nat := 2307595411802539336307357

theorem tailTrace_4494026 : CollatzResearch.WordTrace tailWord_4494026 prefixEnd_4494026 2307595411802539336307357 := by
  unfold tailWord_4494026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40977648504229698845159483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109273729344612530253758621 40977648504229698845159483)
  ·
    refine ⟨61466472756344548267739225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40977648504229698845159483 61466472756344548267739225)
    ·
      refine ⟨46099854567258411200804419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61466472756344548267739225 46099854567258411200804419)
      ·
        refine ⟨69149781850887616801206629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46099854567258411200804419 69149781850887616801206629)
        ·
          refine ⟨12965584097041428150226243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69149781850887616801206629 12965584097041428150226243)
          ·
            refine ⟨19448376145562142225339365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12965584097041428150226243 19448376145562142225339365)
            ·
              refine ⟨3646570527292901667251131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19448376145562142225339365 3646570527292901667251131)
              ·
                refine ⟨5469855790939352500876697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646570527292901667251131 5469855790939352500876697)
                ·
                  refine ⟨4102391843204514375657523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469855790939352500876697 4102391843204514375657523)
                  ·
                    refine ⟨6153587764806771563486285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102391843204514375657523 6153587764806771563486285)
                    ·
                      refine ⟨2307595411802539336307357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153587764806771563486285 2307595411802539336307357)
                      ·
                        rfl

theorem cell23_4494026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_4494026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494026 prefixEnd_4494026 := by exact prefixLift 4494026
  have htrace : WordTrace (prefixWord ++ tailWord_4494026) baseStart_4494026 baseEnd_4494026 := by
    simpa [prefixWord, tailWord_4494026, baseEnd_4494026] using wordTrace_append hprefix tailTrace_4494026
  have hstable : (prefixWord ++ tailWord_4494026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494026).length < 2 ^ (prefixWord ++ tailWord_4494026).sum := by decide
  have hdescent : baseEnd_4494026 < baseStart_4494026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494036 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4494036 : Nat := 118140960795 + 4494036 * 2 ^ 59
def prefixEnd_4494036 : Nat := 4983230072969 + 3 ^ 40 * 4494036 * 2
def baseEnd_4494036 : Nat := 2307600546609084297182311

theorem tailTrace_4494036 : CollatzResearch.WordTrace tailWord_4494036 prefixEnd_4494036 2307600546609084297182311 := by
  unfold tailWord_4494036
  simp only [CollatzResearch.WordTrace]
  refine ⟨81955479373441283544250981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109273972497921711392334641 81955479373441283544250981)
  ·
    refine ⟨15366652382520240664547059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81955479373441283544250981 15366652382520240664547059)
    ·
      refine ⟨23049978573780360996820589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15366652382520240664547059 23049978573780360996820589)
      ·
        refine ⟨8643741965167635373807721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23049978573780360996820589 8643741965167635373807721)
        ·
          refine ⟨6482806473875726530355791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8643741965167635373807721 6482806473875726530355791)
          ·
            refine ⟨9724209710813589795533687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482806473875726530355791 9724209710813589795533687)
            ·
              refine ⟨14586314566220384693300531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724209710813589795533687 14586314566220384693300531)
              ·
                refine ⟨21879471849330577039950797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14586314566220384693300531 21879471849330577039950797)
                ·
                  refine ⟨8204801943498966389981549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21879471849330577039950797 8204801943498966389981549)
                  ·
                    refine ⟨3076800728812112396243081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8204801943498966389981549 3076800728812112396243081)
                    ·
                      refine ⟨2307600546609084297182311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076800728812112396243081 2307600546609084297182311)
                      ·
                        rfl

theorem cell23_4494036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4494036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494036 prefixEnd_4494036 := by exact prefixLift 4494036
  have htrace : WordTrace (prefixWord ++ tailWord_4494036) baseStart_4494036 baseEnd_4494036 := by
    simpa [prefixWord, tailWord_4494036, baseEnd_4494036] using wordTrace_append hprefix tailTrace_4494036
  have hstable : (prefixWord ++ tailWord_4494036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494036).length < 2 ^ (prefixWord ++ tailWord_4494036).sum := by decide
  have hdescent : baseEnd_4494036 < baseStart_4494036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494049 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_4494049 : Nat := 118140960795 + 4494049 * 2 ^ 59
def prefixEnd_4494049 : Nat := 4983230072969 + 3 ^ 40 * 4494049 * 2
def baseEnd_4494049 : Nat := 2307607221857592746319751

theorem tailTrace_4494049 : CollatzResearch.WordTrace tailWord_4494049 prefixEnd_4494049 2307607221857592746319751 := by
  unfold tailWord_4494049
  simp only [CollatzResearch.WordTrace]
  refine ⟨163911432895835470308725201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109274288597223646872483467 163911432895835470308725201)
  ·
    refine ⟨122933574671876602731543901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163911432895835470308725201 122933574671876602731543901)
    ·
      refine ⟨46100090501953726024328963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122933574671876602731543901 46100090501953726024328963)
      ·
        refine ⟨69150135752930589036493445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46100090501953726024328963 69150135752930589036493445)
        ·
          refine ⟨12965650453674485444342521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69150135752930589036493445 12965650453674485444342521)
          ·
            refine ⟨9724237840255864083256891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12965650453674485444342521 9724237840255864083256891)
            ·
              refine ⟨14586356760383796124885337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724237840255864083256891 14586356760383796124885337)
              ·
                refine ⟨10939767570287847093664003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14586356760383796124885337 10939767570287847093664003)
                ·
                  refine ⟨16409651355431770640496005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10939767570287847093664003 16409651355431770640496005)
                  ·
                    refine ⟨3076809629143456995093001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16409651355431770640496005 3076809629143456995093001)
                    ·
                      refine ⟨2307607221857592746319751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076809629143456995093001 2307607221857592746319751)
                      ·
                        rfl

theorem cell23_4494049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_4494049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494049 prefixEnd_4494049 := by exact prefixLift 4494049
  have htrace : WordTrace (prefixWord ++ tailWord_4494049) baseStart_4494049 baseEnd_4494049 := by
    simpa [prefixWord, tailWord_4494049, baseEnd_4494049] using wordTrace_append hprefix tailTrace_4494049
  have hstable : (prefixWord ++ tailWord_4494049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494049).length < 2 ^ (prefixWord ++ tailWord_4494049).sum := by decide
  have hdescent : baseEnd_4494049 < baseStart_4494049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494066 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4494066 : Nat := 118140960795 + 4494066 * 2 ^ 59
def prefixEnd_4494066 : Nat := 4983230072969 + 3 ^ 40 * 4494066 * 2
def baseEnd_4494066 : Nat := 2307615951028719179807173

theorem tailTrace_4494066 : CollatzResearch.WordTrace tailWord_4494066 prefixEnd_4494066 2307615951028719179807173 := by
  unfold tailWord_4494066
  simp only [CollatzResearch.WordTrace]
  refine ⟨40978013234193470553023513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109274701957849254808062701 40978013234193470553023513)
  ·
    refine ⟨30733509925645102914767635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40978013234193470553023513 30733509925645102914767635)
    ·
      refine ⟨46100264888467654372151453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30733509925645102914767635 46100264888467654372151453)
      ·
        refine ⟨17287599333175370389556795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46100264888467654372151453 17287599333175370389556795)
        ·
          refine ⟨25931398999763055584335193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17287599333175370389556795 25931398999763055584335193)
          ·
            refine ⟨19448549249822291688251395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25931398999763055584335193 19448549249822291688251395)
            ·
              refine ⟨29172823874733437532377093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19448549249822291688251395 29172823874733437532377093)
              ·
                refine ⟨5469904476512519537320705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29172823874733437532377093 5469904476512519537320705)
                ·
                  refine ⟨4102428357384389652990529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5469904476512519537320705 4102428357384389652990529)
                  ·
                    refine ⟨3076821268038292239742897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102428357384389652990529 3076821268038292239742897)
                    ·
                      refine ⟨2307615951028719179807173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076821268038292239742897 2307615951028719179807173)
                      ·
                        rfl

theorem cell23_4494066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4494066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494066 prefixEnd_4494066 := by exact prefixLift 4494066
  have htrace : WordTrace (prefixWord ++ tailWord_4494066) baseStart_4494066 baseEnd_4494066 := by
    simpa [prefixWord, tailWord_4494066, baseEnd_4494066] using wordTrace_append hprefix tailTrace_4494066
  have hstable : (prefixWord ++ tailWord_4494066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494066).length < 2 ^ (prefixWord ++ tailWord_4494066).sum := by decide
  have hdescent : baseEnd_4494066 < baseStart_4494066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494072 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 5]
def baseStart_4494072 : Nat := 118140960795 + 4494072 * 2 ^ 59
def prefixEnd_4494072 : Nat := 4983230072969 + 3 ^ 40 * 4494072 * 2
def baseEnd_4494072 : Nat := 256402114656960684036905

theorem tailTrace_4494072 : CollatzResearch.WordTrace tailWord_4494072 prefixEnd_4494072 256402114656960684036905 := by
  unfold tailWord_4494072
  simp only [CollatzResearch.WordTrace]
  refine ⟨81956135887376072618406235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109274847849834763491208313 81956135887376072618406235)
  ·
    refine ⟨122934203831064108927609353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81956135887376072618406235 122934203831064108927609353)
    ·
      refine ⟨92200652873298081695707015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122934203831064108927609353 92200652873298081695707015)
      ·
        refine ⟨138300979309947122543560523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92200652873298081695707015 138300979309947122543560523)
        ·
          refine ⟨207451468964920683815340785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138300979309947122543560523 207451468964920683815340785)
          ·
            refine ⟨155588601723690512861505589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207451468964920683815340785 155588601723690512861505589)
            ·
              refine ⟨14586431411595985580766149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155588601723690512861505589 14586431411595985580766149)
              ·
                refine ⟨2734955889674247296393653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14586431411595985580766149 2734955889674247296393653)
                ·
                  refine ⟨256402114656960684036905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734955889674247296393653 256402114656960684036905)
                  ·
                    rfl

theorem cell23_4494072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 5].length) (baseStart_4494072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494072 prefixEnd_4494072 := by exact prefixLift 4494072
  have htrace : WordTrace (prefixWord ++ tailWord_4494072) baseStart_4494072 baseEnd_4494072 := by
    simpa [prefixWord, tailWord_4494072, baseEnd_4494072] using wordTrace_append hprefix tailTrace_4494072
  have hstable : (prefixWord ++ tailWord_4494072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494072).length < 2 ^ (prefixWord ++ tailWord_4494072).sum := by decide
  have hdescent : baseEnd_4494072 < baseStart_4494072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494085 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_4494085 : Nat := 118140960795 + 4494085 * 2 ^ 59
def prefixEnd_4494085 : Nat := 4983230072969 + 3 ^ 40 * 4494085 * 2
def baseEnd_4494085 : Nat := 769208569053718201823195

theorem tailTrace_4494085 : CollatzResearch.WordTrace tailWord_4494085 prefixEnd_4494085 769208569053718201823195 := by
  unfold tailWord_4494085
  simp only [CollatzResearch.WordTrace]
  refine ⟨163912745923705048457035709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109275163949136698971357139 163912745923705048457035709)
  ·
    refine ⟨61467279721389393171388391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163912745923705048457035709 61467279721389393171388391)
    ·
      refine ⟨92200919582084089757082587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61467279721389393171388391 92200919582084089757082587)
      ·
        refine ⟨138301379373126134635623881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92200919582084089757082587 138301379373126134635623881)
        ·
          refine ⟨103726034529844600976717911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138301379373126134635623881 103726034529844600976717911)
          ·
            refine ⟨155589051794766901465076867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103726034529844600976717911 155589051794766901465076867)
            ·
              refine ⟨233383577692150352197615301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155589051794766901465076867 233383577692150352197615301)
              ·
                refine ⟨43759420817278191037052869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233383577692150352197615301 43759420817278191037052869)
                ·
                  refine ⟨8204891403239660819447413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43759420817278191037052869 8204891403239660819447413)
                  ·
                    refine ⟨769208569053718201823195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8204891403239660819447413 769208569053718201823195)
                    ·
                      rfl

theorem cell23_4494085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_4494085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494085 prefixEnd_4494085 := by exact prefixLift 4494085
  have htrace : WordTrace (prefixWord ++ tailWord_4494085) baseStart_4494085 baseEnd_4494085 := by
    simpa [prefixWord, tailWord_4494085, baseEnd_4494085] using wordTrace_append hprefix tailTrace_4494085
  have hstable : (prefixWord ++ tailWord_4494085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494085).length < 2 ^ (prefixWord ++ tailWord_4494085).sum := by decide
  have hdescent : baseEnd_4494085 < baseStart_4494085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494092 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_4494092 : Nat := 118140960795 + 4494092 * 2 ^ 59
def prefixEnd_4494092 : Nat := 4983230072969 + 3 ^ 40 * 4494092 * 2
def baseEnd_4494092 : Nat := 2307629301525736078082053

theorem tailTrace_4494092 : CollatzResearch.WordTrace tailWord_4494092 prefixEnd_4494092 2307629301525736078082053 := by
  unfold tailWord_4494092
  simp only [CollatzResearch.WordTrace]
  refine ⟨81956500617339844326270265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109275334156453125768360353 81956500617339844326270265)
  ·
    refine ⟨61467375463004883244702699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81956500617339844326270265 61467375463004883244702699)
    ·
      refine ⟨92201063194507324867054049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61467375463004883244702699 92201063194507324867054049)
      ·
        refine ⟨69150797395880493650290537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92201063194507324867054049 69150797395880493650290537)
        ·
          refine ⟨51863098046910370237717903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69150797395880493650290537 51863098046910370237717903)
          ·
            refine ⟨77794647070365555356576855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51863098046910370237717903 77794647070365555356576855)
            ·
              refine ⟨116691970605548333034865283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77794647070365555356576855 116691970605548333034865283)
              ·
                refine ⟨175037955908322499552297925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116691970605548333034865283 175037955908322499552297925)
                ·
                  refine ⟨32819616732810468666055861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175037955908322499552297925 32819616732810468666055861)
                  ·
                    refine ⟨3076839068700981437442737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32819616732810468666055861 3076839068700981437442737)
                    ·
                      refine ⟨2307629301525736078082053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076839068700981437442737 2307629301525736078082053)
                      ·
                        rfl

theorem cell23_4494092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_4494092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494092 prefixEnd_4494092 := by exact prefixLift 4494092
  have htrace : WordTrace (prefixWord ++ tailWord_4494092) baseStart_4494092 baseEnd_4494092 := by
    simpa [prefixWord, tailWord_4494092, baseEnd_4494092] using wordTrace_append hprefix tailTrace_4494092
  have hstable : (prefixWord ++ tailWord_4494092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494092).length < 2 ^ (prefixWord ++ tailWord_4494092).sum := by decide
  have hdescent : baseEnd_4494092 < baseStart_4494092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494135 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_4494135 : Nat := 118140960795 + 4494135 * 2 ^ 59
def prefixEnd_4494135 : Nat := 4983230072969 + 3 ^ 40 * 4494135 * 2
def baseEnd_4494135 : Nat := 2307651381193879409844355

theorem tailTrace_4494135 : CollatzResearch.WordTrace tailWord_4494135 prefixEnd_4494135 2307651381193879409844355 := by
  unfold tailWord_4494135
  simp only [CollatzResearch.WordTrace]
  refine ⟨163914569573523906996355859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109276379715682604664237239 163914569573523906996355859)
  ·
    refine ⟨245871854360285860494533789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163914569573523906996355859 245871854360285860494533789)
    ·
      refine ⟨92201945385107197685450171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245871854360285860494533789 92201945385107197685450171)
      ·
        refine ⟨138302918077660796528175257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92201945385107197685450171 138302918077660796528175257)
        ·
          refine ⟨103727188558245597396131443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138302918077660796528175257 103727188558245597396131443)
          ·
            refine ⟨155590782837368396094197165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103727188558245597396131443 155590782837368396094197165)
            ·
              refine ⟨58346543564013148535323937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155590782837368396094197165 58346543564013148535323937)
              ·
                refine ⟨43759907673009861401492953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58346543564013148535323937 43759907673009861401492953)
                ·
                  refine ⟨32819930754757396051119715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43759907673009861401492953 32819930754757396051119715)
                  ·
                    refine ⟨49229896132136094076679573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32819930754757396051119715 49229896132136094076679573)
                    ·
                      refine ⟨2307651381193879409844355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49229896132136094076679573 2307651381193879409844355)
                      ·
                        rfl

theorem cell23_4494135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_4494135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494135 prefixEnd_4494135 := by exact prefixLift 4494135
  have htrace : WordTrace (prefixWord ++ tailWord_4494135) baseStart_4494135 baseEnd_4494135 := by
    simpa [prefixWord, tailWord_4494135, baseEnd_4494135] using wordTrace_append hprefix tailTrace_4494135
  have hstable : (prefixWord ++ tailWord_4494135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494135).length < 2 ^ (prefixWord ++ tailWord_4494135).sum := by decide
  have hdescent : baseEnd_4494135 < baseStart_4494135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494183 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 1, 4]
def baseStart_4494183 : Nat := 118140960795 + 4494183 * 2 ^ 59
def prefixEnd_4494183 : Nat := 4983230072969 + 3 ^ 40 * 4494183 * 2
def baseEnd_4494183 : Nat := 769225342755098407348045

theorem tailTrace_4494183 : CollatzResearch.WordTrace tailWord_4494183 prefixEnd_4494183 769225342755098407348045 := by
  unfold tailWord_4494183
  simp only [CollatzResearch.WordTrace]
  refine ⟨163916320277350011194103203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109277546851566674129402135 163916320277350011194103203)
  ·
    refine ⟨245874480416025016791154805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163916320277350011194103203 245874480416025016791154805)
    ·
      refine ⟨23050732539002345324170763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245874480416025016791154805 23050732539002345324170763)
      ·
        refine ⟨34576098808503517986256145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23050732539002345324170763 34576098808503517986256145)
        ·
          refine ⟨25932074106377638489692109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34576098808503517986256145 25932074106377638489692109)
          ·
            refine ⟨9724527789891614433634541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25932074106377638489692109 9724527789891614433634541)
            ·
              refine ⟨3646697921209355412612953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9724527789891614433634541 3646697921209355412612953)
              ·
                refine ⟨2735023440907016559459715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3646697921209355412612953 2735023440907016559459715)
                ·
                  refine ⟨4102535161360524839189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735023440907016559459715 4102535161360524839189573)
                  ·
                    refine ⟨769225342755098407348045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4102535161360524839189573 769225342755098407348045)
                    ·
                      rfl

theorem cell23_4494183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_4494183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494183 prefixEnd_4494183 := by exact prefixLift 4494183
  have htrace : WordTrace (prefixWord ++ tailWord_4494183) baseStart_4494183 baseEnd_4494183 := by
    simpa [prefixWord, tailWord_4494183, baseEnd_4494183] using wordTrace_append hprefix tailTrace_4494183
  have hstable : (prefixWord ++ tailWord_4494183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494183).length < 2 ^ (prefixWord ++ tailWord_4494183).sum := by decide
  have hdescent : baseEnd_4494183 < baseStart_4494183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494185 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_4494185 : Nat := 118140960795 + 4494185 * 2 ^ 59
def prefixEnd_4494185 : Nat := 4983230072969 + 3 ^ 40 * 4494185 * 2
def baseEnd_4494185 : Nat := 2307677055226604214219125

theorem tailTrace_4494185 : CollatzResearch.WordTrace tailWord_4494185 prefixEnd_4494185 2307677055226604214219125 := by
  unfold tailWord_4494185
  simp only [CollatzResearch.WordTrace]
  refine ⟨163916393223342765535676009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109277595482228510357117339 163916393223342765535676009)
  ·
    refine ⟨122937294917507074151757007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163916393223342765535676009 122937294917507074151757007)
    ·
      refine ⟨184405942376260611227635511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122937294917507074151757007 184405942376260611227635511)
      ·
        refine ⟨276608913564390916841453267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184405942376260611227635511 276608913564390916841453267)
        ·
          refine ⟨414913370346586375262179901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276608913564390916841453267 414913370346586375262179901)
          ·
            refine ⟨155592513879969890723317463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414913370346586375262179901 155592513879969890723317463)
            ·
              refine ⟨233388770819954836084976195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155592513879969890723317463 233388770819954836084976195)
              ·
                refine ⟨350083156229932254127464293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233388770819954836084976195 350083156229932254127464293)
                ·
                  refine ⟨65640591793112297648899555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350083156229932254127464293 65640591793112297648899555)
                  ·
                    refine ⟨98460887689668446473349333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65640591793112297648899555 98460887689668446473349333)
                    ·
                      refine ⟨2307677055226604214219125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98460887689668446473349333 2307677055226604214219125)
                      ·
                        rfl

theorem cell23_4494185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_4494185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494185 prefixEnd_4494185 := by exact prefixLift 4494185
  have htrace : WordTrace (prefixWord ++ tailWord_4494185) baseStart_4494185 baseEnd_4494185 := by
    simpa [prefixWord, tailWord_4494185, baseEnd_4494185] using wordTrace_append hprefix tailTrace_4494185
  have hstable : (prefixWord ++ tailWord_4494185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494185).length < 2 ^ (prefixWord ++ tailWord_4494185).sum := by decide
  have hdescent : baseEnd_4494185 < baseStart_4494185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494210 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4494210 : Nat := 118140960795 + 4494210 * 2 ^ 59
def prefixEnd_4494210 : Nat := 4983230072969 + 3 ^ 40 * 4494210 * 2
def baseEnd_4494210 : Nat := 2307689892242966616406511

theorem tailTrace_4494210 : CollatzResearch.WordTrace tailWord_4494210 prefixEnd_4494210 2307689892242966616406511 := by
  unfold tailWord_4494210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40979326262063048701334021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109278203365501463203557389 40979326262063048701334021)
  ·
    refine ⟨7683623674136821631500129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40979326262063048701334021 7683623674136821631500129)
    ·
      refine ⟨5762717755602616223625097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7683623674136821631500129 5762717755602616223625097)
      ·
        refine ⟨4322038316701962167718823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762717755602616223625097 4322038316701962167718823)
        ·
          refine ⟨6483057475052943251578235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322038316701962167718823 6483057475052943251578235)
          ·
            refine ⟨9724586212579414877367353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483057475052943251578235 9724586212579414877367353)
            ·
              refine ⟨7293439659434561158025515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9724586212579414877367353 7293439659434561158025515)
              ·
                refine ⟨10940159489151841737038273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7293439659434561158025515 10940159489151841737038273)
                ·
                  refine ⟨8205119616863881302778705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10940159489151841737038273 8205119616863881302778705)
                  ·
                    refine ⟨6153839712647910977084029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8205119616863881302778705 6153839712647910977084029)
                    ·
                      refine ⟨2307689892242966616406511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153839712647910977084029 2307689892242966616406511)
                      ·
                        rfl

theorem cell23_4494210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4494210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494210 prefixEnd_4494210 := by exact prefixLift 4494210
  have htrace : WordTrace (prefixWord ++ tailWord_4494210) baseStart_4494210 baseEnd_4494210 := by
    simpa [prefixWord, tailWord_4494210, baseEnd_4494210] using wordTrace_append hprefix tailTrace_4494210
  have hstable : (prefixWord ++ tailWord_4494210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494210).length < 2 ^ (prefixWord ++ tailWord_4494210).sum := by decide
  have hdescent : baseEnd_4494210 < baseStart_4494210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494216 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4494216 : Nat := 118140960795 + 4494216 * 2 ^ 59
def prefixEnd_4494216 : Nat := 4983230072969 + 3 ^ 40 * 4494216 * 2
def baseEnd_4494216 : Nat := 2307692973126893592931483

theorem tailTrace_4494216 : CollatzResearch.WordTrace tailWord_4494216 prefixEnd_4494216 2307692973126893592931483 := by
  unfold tailWord_4494216
  simp only [CollatzResearch.WordTrace]
  refine ⟨81958761943115228915027251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109278349257486971886703001 81958761943115228915027251)
  ·
    refine ⟨122938142914672843372540877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81958761943115228915027251 122938142914672843372540877)
    ·
      refine ⟨46101803593002316264702829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122938142914672843372540877 46101803593002316264702829)
      ·
        refine ⟨17288176347375868599263561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46101803593002316264702829 17288176347375868599263561)
        ·
          refine ⟨12966132260531901449447671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17288176347375868599263561 12966132260531901449447671)
          ·
            refine ⟨19449198390797852174171507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966132260531901449447671 19449198390797852174171507)
            ·
              refine ⟨29173797586196778261257261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19449198390797852174171507 29173797586196778261257261)
              ·
                refine ⟨10940174094823791847971473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29173797586196778261257261 10940174094823791847971473)
                ·
                  refine ⟨8205130571117843885978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10940174094823791847971473 8205130571117843885978605)
                  ·
                    refine ⟨3076923964169191457241977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8205130571117843885978605 3076923964169191457241977)
                    ·
                      refine ⟨2307692973126893592931483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3076923964169191457241977 2307692973126893592931483)
                      ·
                        rfl

theorem cell23_4494216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4494216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494216 prefixEnd_4494216 := by exact prefixLift 4494216
  have htrace : WordTrace (prefixWord ++ tailWord_4494216) baseStart_4494216 baseEnd_4494216 := by
    simpa [prefixWord, tailWord_4494216, baseEnd_4494216] using wordTrace_append hprefix tailTrace_4494216
  have hstable : (prefixWord ++ tailWord_4494216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494216).length < 2 ^ (prefixWord ++ tailWord_4494216).sum := by decide
  have hdescent : baseEnd_4494216 < baseStart_4494216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494279 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_4494279 : Nat := 118140960795 + 4494279 * 2 ^ 59
def prefixEnd_4494279 : Nat := 4983230072969 + 3 ^ 40 * 4494279 * 2
def baseEnd_4494279 : Nat := 2307725322408126846443693

theorem tailTrace_4494279 : CollatzResearch.WordTrace tailWord_4494279 prefixEnd_4494279 2307725322408126846443693 := by
  unfold tailWord_4494279
  simp only [CollatzResearch.WordTrace]
  refine ⟨163919821685002219589597891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109279881123334813059731927 163919821685002219589597891)
  ·
    refine ⟨245879732527503329384396837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163919821685002219589597891 245879732527503329384396837)
    ·
      refine ⟨46102449848906874259574407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245879732527503329384396837 46102449848906874259574407)
      ·
        refine ⟨69153674773360311389361611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46102449848906874259574407 69153674773360311389361611)
        ·
          refine ⟨103730512160040467084042417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69153674773360311389361611 103730512160040467084042417)
          ·
            refine ⟨77797884120030350313031813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103730512160040467084042417 77797884120030350313031813)
            ·
              refine ⟨14587103272505690683693465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77797884120030350313031813 14587103272505690683693465)
              ·
                refine ⟨10940327454379268012770099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14587103272505690683693465 10940327454379268012770099)
                ·
                  refine ⟨16410491181568902019155149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10940327454379268012770099 16410491181568902019155149)
                  ·
                    refine ⟨6153934193088338257183181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16410491181568902019155149 6153934193088338257183181)
                    ·
                      refine ⟨2307725322408126846443693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153934193088338257183181 2307725322408126846443693)
                      ·
                        rfl

theorem cell23_4494279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_4494279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494279 prefixEnd_4494279 := by exact prefixLift 4494279
  have htrace : WordTrace (prefixWord ++ tailWord_4494279) baseStart_4494279 baseEnd_4494279 := by
    simpa [prefixWord, tailWord_4494279, baseEnd_4494279] using wordTrace_append hprefix tailTrace_4494279
  have hstable : (prefixWord ++ tailWord_4494279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494279).length < 2 ^ (prefixWord ++ tailWord_4494279).sum := by decide
  have hdescent : baseEnd_4494279 < baseStart_4494279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494280 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_4494280 : Nat := 118140960795 + 4494280 * 2 ^ 59
def prefixEnd_4494280 : Nat := 4983230072969 + 3 ^ 40 * 4494280 * 2
def baseEnd_4494280 : Nat := 2307725835888781342531189

theorem tailTrace_4494280 : CollatzResearch.WordTrace tailWord_4494280 prefixEnd_4494280 2307725835888781342531189 := by
  unfold tailWord_4494280
  simp only [CollatzResearch.WordTrace]
  refine ⟨81959929078999298380192147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109279905438665731173589529 81959929078999298380192147)
  ·
    refine ⟨122939893618498947570288221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81959929078999298380192147 122939893618498947570288221)
    ·
      refine ⟨46102460106937105338858083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122939893618498947570288221 46102460106937105338858083)
      ·
        refine ⟨69153690160405658008287125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46102460106937105338858083 69153690160405658008287125)
        ·
          refine ⟨3241579226269015219138459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69153690160405658008287125 3241579226269015219138459)
          ·
            refine ⟨4862368839403522828707689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241579226269015219138459 4862368839403522828707689)
            ·
              refine ⟨3646776629552642121530767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862368839403522828707689 3646776629552642121530767)
              ·
                refine ⟨5470164944328963182296151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646776629552642121530767 5470164944328963182296151)
                ·
                  refine ⟨8205247416493444773444227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470164944328963182296151 8205247416493444773444227)
                  ·
                    refine ⟨12307871124740167160166341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8205247416493444773444227 12307871124740167160166341)
                    ·
                      refine ⟨2307725835888781342531189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12307871124740167160166341 2307725835888781342531189)
                      ·
                        rfl

theorem cell23_4494280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_4494280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494280 prefixEnd_4494280 := by exact prefixLift 4494280
  have htrace : WordTrace (prefixWord ++ tailWord_4494280) baseStart_4494280 baseEnd_4494280 := by
    simpa [prefixWord, tailWord_4494280, baseEnd_4494280] using wordTrace_append hprefix tailTrace_4494280
  have hstable : (prefixWord ++ tailWord_4494280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494280).length < 2 ^ (prefixWord ++ tailWord_4494280).sum := by decide
  have hdescent : baseEnd_4494280 < baseStart_4494280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494283 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 1, 2, 3]
def baseStart_4494283 : Nat := 118140960795 + 4494283 * 2 ^ 59
def prefixEnd_4494283 : Nat := 4983230072969 + 3 ^ 40 * 4494283 * 2
def baseEnd_4494283 : Nat := 2307727376330744830793675

theorem tailTrace_4494283 : CollatzResearch.WordTrace tailWord_4494283 prefixEnd_4494283 2307727376330744830793675 := by
  unfold tailWord_4494283
  simp only [CollatzResearch.WordTrace]
  refine ⟨163919967576987728272743503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109279978384658485515162335 163919967576987728272743503)
  ·
    refine ⟨245879951365481592409115255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163919967576987728272743503 245879951365481592409115255)
    ·
      refine ⟨368819927048222388613672883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245879951365481592409115255 368819927048222388613672883)
      ·
        refine ⟨553229890572333582920509325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368819927048222388613672883 553229890572333582920509325)
        ·
          refine ⟨207461208964625093595190997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 553229890572333582920509325 207461208964625093595190997)
          ·
            refine ⟨4862372085108400631137289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 207461208964625093595190997 4862372085108400631137289)
            ·
              refine ⟨3646779063831300473352967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862372085108400631137289 3646779063831300473352967)
              ·
                refine ⟨5470168595746950710029451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646779063831300473352967 5470168595746950710029451)
                ·
                  refine ⟨8205252893620426065044177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470168595746950710029451 8205252893620426065044177)
                  ·
                    refine ⟨6153939670215319548783133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8205252893620426065044177 6153939670215319548783133)
                    ·
                      refine ⟨2307727376330744830793675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153939670215319548783133 2307727376330744830793675)
                      ·
                        rfl

theorem cell23_4494283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 2, 3].length) (baseStart_4494283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494283 prefixEnd_4494283 := by exact prefixLift 4494283
  have htrace : WordTrace (prefixWord ++ tailWord_4494283) baseStart_4494283 baseEnd_4494283 := by
    simpa [prefixWord, tailWord_4494283, baseEnd_4494283] using wordTrace_append hprefix tailTrace_4494283
  have hstable : (prefixWord ++ tailWord_4494283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494283).length < 2 ^ (prefixWord ++ tailWord_4494283).sum := by decide
  have hdescent : baseEnd_4494283 < baseStart_4494283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494296 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_4494296 : Nat := 118140960795 + 4494296 * 2 ^ 59
def prefixEnd_4494296 : Nat := 4983230072969 + 3 ^ 40 * 4494296 * 2
def baseEnd_4494296 : Nat := 2307734051579253279931115

theorem tailTrace_4494296 : CollatzResearch.WordTrace tailWord_4494296 prefixEnd_4494296 2307734051579253279931115 := by
  unfold tailWord_4494296
  simp only [CollatzResearch.WordTrace]
  refine ⟨81960220862970315746483371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109280294483960420995311161 81960220862970315746483371)
  ·
    refine ⟨122940331294455473619725057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81960220862970315746483371 122940331294455473619725057)
    ·
      refine ⟨92205248470841605214793793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122940331294455473619725057 92205248470841605214793793)
      ·
        refine ⟨69153936353131203911095345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92205248470841605214793793 69153936353131203911095345)
        ·
          refine ⟨51865452264848402933321509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69153936353131203911095345 51865452264848402933321509)
          ·
            refine ⟨9724772299659075549997783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51865452264848402933321509 9724772299659075549997783)
            ·
              refine ⟨14587158449488613324996675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724772299659075549997783 14587158449488613324996675)
              ·
                refine ⟨21880737674232919987495013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14587158449488613324996675 21880737674232919987495013)
                ·
                  refine ⟨4102638313918672497655315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21880737674232919987495013 4102638313918672497655315)
                  ·
                    refine ⟨6153957470878008746482973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102638313918672497655315 6153957470878008746482973)
                    ·
                      refine ⟨2307734051579253279931115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6153957470878008746482973 2307734051579253279931115)
                      ·
                        rfl

theorem cell23_4494296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_4494296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494296 prefixEnd_4494296 := by exact prefixLift 4494296
  have htrace : WordTrace (prefixWord ++ tailWord_4494296) baseStart_4494296 baseEnd_4494296 := by
    simpa [prefixWord, tailWord_4494296, baseEnd_4494296] using wordTrace_append hprefix tailTrace_4494296
  have hstable : (prefixWord ++ tailWord_4494296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494296).length < 2 ^ (prefixWord ++ tailWord_4494296).sum := by decide
  have hdescent : baseEnd_4494296 < baseStart_4494296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494370 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_4494370 : Nat := 118140960795 + 4494370 * 2 ^ 59
def prefixEnd_4494370 : Nat := 4983230072969 + 3 ^ 40 * 4494370 * 2
def baseEnd_4494370 : Nat := 2307772049147685990405775

theorem tailTrace_4494370 : CollatzResearch.WordTrace tailWord_4494370 prefixEnd_4494370 2307772049147685990405775 := by
  unfold tailWord_4494370
  simp only [CollatzResearch.WordTrace]
  refine ⟨40980785181918135532790141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109282093818448361420773709 40980785181918135532790141)
  ·
    refine ⟨15367794443219300824796303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40980785181918135532790141 15367794443219300824796303)
    ·
      refine ⟨23051691664828951237194455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15367794443219300824796303 23051691664828951237194455)
      ·
        refine ⟨34577537497243426855791683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23051691664828951237194455 34577537497243426855791683)
        ·
          refine ⟨51866306245865140283687525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34577537497243426855791683 51866306245865140283687525)
          ·
            refine ⟨9724932421099713803191411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51866306245865140283687525 9724932421099713803191411)
            ·
              refine ⟨14587398631649570704787117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9724932421099713803191411 14587398631649570704787117)
              ·
                refine ⟨5470274486868589014295169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14587398631649570704787117 5470274486868589014295169)
                ·
                  refine ⟨4102705865151441760721377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470274486868589014295169 4102705865151441760721377)
                  ·
                    refine ⟨3077029398863581320541033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102705865151441760721377 3077029398863581320541033)
                    ·
                      refine ⟨2307772049147685990405775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077029398863581320541033 2307772049147685990405775)
                      ·
                        rfl

theorem cell23_4494370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_4494370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494370 prefixEnd_4494370 := by exact prefixLift 4494370
  have htrace : WordTrace (prefixWord ++ tailWord_4494370) baseStart_4494370 baseEnd_4494370 := by
    simpa [prefixWord, tailWord_4494370, baseEnd_4494370] using wordTrace_append hprefix tailTrace_4494370
  have hstable : (prefixWord ++ tailWord_4494370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494370).length < 2 ^ (prefixWord ++ tailWord_4494370).sum := by decide
  have hdescent : baseEnd_4494370 < baseStart_4494370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494409 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_4494409 : Nat := 118140960795 + 4494409 * 2 ^ 59
def prefixEnd_4494409 : Nat := 4983230072969 + 3 ^ 40 * 4494409 * 2
def baseEnd_4494409 : Nat := 2307792074893211337818095

theorem tailTrace_4494409 : CollatzResearch.WordTrace tailWord_4494409 prefixEnd_4494409 2307792074893211337818095 := by
  unfold tailWord_4494409
  simp only [CollatzResearch.WordTrace]
  refine ⟨163924563174531251791830281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109283042116354167861220187 163924563174531251791830281)
  ·
    refine ⟨122943422380898438843872711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163924563174531251791830281 122943422380898438843872711)
    ·
      refine ⟨184415133571347658265809067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122943422380898438843872711 184415133571347658265809067)
      ·
        refine ⟨276622700357021487398713601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184415133571347658265809067 276622700357021487398713601)
        ·
          refine ⟨207467025267766115549035201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276622700357021487398713601 207467025267766115549035201)
          ·
            refine ⟨155600268950824586661776401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207467025267766115549035201 155600268950824586661776401)
            ·
              refine ⟨116700201713118439996332301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155600268950824586661776401 116700201713118439996332301)
              ·
                refine ⟨43762575642419414998624613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116700201713118439996332301 43762575642419414998624613)
                ·
                  refine ⟨8205482932953640312242115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43762575642419414998624613 8205482932953640312242115)
                  ·
                    refine ⟨12308224399430460468363173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8205482932953640312242115 12308224399430460468363173)
                    ·
                      refine ⟨2307792074893211337818095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12308224399430460468363173 2307792074893211337818095)
                      ·
                        rfl

theorem cell23_4494409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_4494409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494409 prefixEnd_4494409 := by exact prefixLift 4494409
  have htrace : WordTrace (prefixWord ++ tailWord_4494409) baseStart_4494409 baseEnd_4494409 := by
    simpa [prefixWord, tailWord_4494409, baseEnd_4494409] using wordTrace_append hprefix tailTrace_4494409
  have hstable : (prefixWord ++ tailWord_4494409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494409).length < 2 ^ (prefixWord ++ tailWord_4494409).sum := by decide
  have hdescent : baseEnd_4494409 < baseStart_4494409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494413 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4494413 : Nat := 118140960795 + 4494413 * 2 ^ 59
def prefixEnd_4494413 : Nat := 4983230072969 + 3 ^ 40 * 4494413 * 2
def baseEnd_4494413 : Nat := 2307794128815829322168077

theorem tailTrace_4494413 : CollatzResearch.WordTrace tailWord_4494413 prefixEnd_4494413 2307794128815829322168077 := by
  unfold tailWord_4494413
  simp only [CollatzResearch.WordTrace]
  refine ⟨163924709066516760474975893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109283139377677840316650595 163924709066516760474975893)
  ·
    refine ⟨7683970737492973147264495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163924709066516760474975893 7683970737492973147264495)
    ·
      refine ⟨11525956106239459720896743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7683970737492973147264495 11525956106239459720896743)
      ·
        refine ⟨17288934159359189581345115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11525956106239459720896743 17288934159359189581345115)
        ·
          refine ⟨25933401239038784372017673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17288934159359189581345115 25933401239038784372017673)
          ·
            refine ⟨19450050929279088279013255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25933401239038784372017673 19450050929279088279013255)
            ·
              refine ⟨29175076393918632418519883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19450050929279088279013255 29175076393918632418519883)
              ·
                refine ⟨43762614590877948627779825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29175076393918632418519883 43762614590877948627779825)
                ·
                  refine ⟨32821960943158461470834869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43762614590877948627779825 32821960943158461470834869)
                  ·
                    refine ⟨3077058838421105762890769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32821960943158461470834869 3077058838421105762890769)
                    ·
                      refine ⟨2307794128815829322168077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077058838421105762890769 2307794128815829322168077)
                      ·
                        rfl

theorem cell23_4494413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4494413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494413 prefixEnd_4494413 := by exact prefixLift 4494413
  have htrace : WordTrace (prefixWord ++ tailWord_4494413) baseStart_4494413 baseEnd_4494413 := by
    simpa [prefixWord, tailWord_4494413, baseEnd_4494413] using wordTrace_append hprefix tailTrace_4494413
  have hstable : (prefixWord ++ tailWord_4494413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494413).length < 2 ^ (prefixWord ++ tailWord_4494413).sum := by decide
  have hdescent : baseEnd_4494413 < baseStart_4494413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494440 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_4494440 : Nat := 118140960795 + 4494440 * 2 ^ 59
def prefixEnd_4494440 : Nat := 4983230072969 + 3 ^ 40 * 4494440 * 2
def baseEnd_4494440 : Nat := 769269330931166905510151

theorem tailTrace_4494440 : CollatzResearch.WordTrace tailWord_4494440 prefixEnd_4494440 769269330931166905510151 := by
  unfold tailWord_4494440
  simp only [CollatzResearch.WordTrace]
  refine ⟨81962846918709472043104387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109283795891612629390805849 81962846918709472043104387)
  ·
    refine ⟨122944270378064208064656581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81962846918709472043104387 122944270378064208064656581)
    ·
      refine ⟨23052050695887039012123109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122944270378064208064656581 23052050695887039012123109)
      ·
        refine ⟨4322259505478819814773083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23052050695887039012123109 4322259505478819814773083)
        ·
          refine ⟨6483389258218229722159625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322259505478819814773083 6483389258218229722159625)
          ·
            refine ⟨4862541943663672291619719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483389258218229722159625 4862541943663672291619719)
            ·
              refine ⟨7293812915495508437429579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862541943663672291619719 7293812915495508437429579)
              ·
                refine ⟨10940719373243262656144369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7293812915495508437429579 10940719373243262656144369)
                ·
                  refine ⟨8205539529932446992108277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10940719373243262656144369 8205539529932446992108277)
                  ·
                    refine ⟨769269330931166905510151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8205539529932446992108277 769269330931166905510151)
                    ·
                      rfl

theorem cell23_4494440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_4494440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494440 prefixEnd_4494440 := by exact prefixLift 4494440
  have htrace : WordTrace (prefixWord ++ tailWord_4494440) baseStart_4494440 baseEnd_4494440 := by
    simpa [prefixWord, tailWord_4494440, baseEnd_4494440] using wordTrace_append hprefix tailTrace_4494440
  have hstable : (prefixWord ++ tailWord_4494440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494440).length < 2 ^ (prefixWord ++ tailWord_4494440).sum := by decide
  have hdescent : baseEnd_4494440 < baseStart_4494440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494459 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3]
def baseStart_4494459 : Nat := 118140960795 + 4494459 * 2 ^ 59
def prefixEnd_4494459 : Nat := 4983230072969 + 3 ^ 40 * 4494459 * 2
def baseEnd_4494459 : Nat := 2307817748925936142192865

theorem tailTrace_4494459 : CollatzResearch.WordTrace tailWord_4494459 prefixEnd_4494459 2307817748925936142192865 := by
  unfold tailWord_4494459
  simp only [CollatzResearch.WordTrace]
  refine ⟨163926386824350110331150431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109284257882900073554100287 163926386824350110331150431)
  ·
    refine ⟨245889580236525165496725647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163926386824350110331150431 245889580236525165496725647)
    ·
      refine ⟨368834370354787748245088471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245889580236525165496725647 368834370354787748245088471)
      ·
        refine ⟨553251555532181622367632707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368834370354787748245088471 553251555532181622367632707)
        ·
          refine ⟨829877333298272433551449061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553251555532181622367632707 829877333298272433551449061)
          ·
            refine ⟨155601999993426081290896699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 829877333298272433551449061 155601999993426081290896699)
            ·
              refine ⟨233402999990139121936345049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155601999993426081290896699 233402999990139121936345049)
              ·
                refine ⟨175052249992604341452258787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233402999990139121936345049 175052249992604341452258787)
                ·
                  refine ⟨262578374988906512178388181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175052249992604341452258787 262578374988906512178388181)
                  ·
                    refine ⟨6154180663802496379180973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 262578374988906512178388181 6154180663802496379180973)
                    ·
                      refine ⟨2307817748925936142192865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6154180663802496379180973 2307817748925936142192865)
                      ·
                        rfl

theorem cell23_4494459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 3].length) (baseStart_4494459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494459 prefixEnd_4494459 := by exact prefixLift 4494459
  have htrace : WordTrace (prefixWord ++ tailWord_4494459) baseStart_4494459 baseEnd_4494459 := by
    simpa [prefixWord, tailWord_4494459, baseEnd_4494459] using wordTrace_append hprefix tailTrace_4494459
  have hstable : (prefixWord ++ tailWord_4494459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494459).length < 2 ^ (prefixWord ++ tailWord_4494459).sum := by decide
  have hdescent : baseEnd_4494459 < baseStart_4494459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494493 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_4494493 : Nat := 118140960795 + 4494493 * 2 ^ 59
def prefixEnd_4494493 : Nat := 4983230072969 + 3 ^ 40 * 4494493 * 2
def baseEnd_4494493 : Nat := 2307835207268189009167709

theorem tailTrace_4494493 : CollatzResearch.WordTrace tailWord_4494493 prefixEnd_4494493 2307835207268189009167709 := by
  unfold tailWord_4494493
  simp only [CollatzResearch.WordTrace]
  refine ⟨163927626906226934137888133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109285084604151289425258755 163927626906226934137888133)
  ·
    refine ⟨30736430044917550150854025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163927626906226934137888133 30736430044917550150854025)
    ·
      refine ⟨23052322533688162613140519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30736430044917550150854025 23052322533688162613140519)
      ·
        refine ⟨34578483800532243919710779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23052322533688162613140519 34578483800532243919710779)
        ·
          refine ⟨51867725700798365879566169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34578483800532243919710779 51867725700798365879566169)
          ·
            refine ⟨38900794275598774409674627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51867725700798365879566169 38900794275598774409674627)
            ·
              refine ⟨58351191413398161614511941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38900794275598774409674627 58351191413398161614511941)
              ·
                refine ⟨10940848390012155302720989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58351191413398161614511941 10940848390012155302720989)
                ·
                  refine ⟨4102818146254558238520371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10940848390012155302720989 4102818146254558238520371)
                  ·
                    refine ⟨6154227219381837357780557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102818146254558238520371 6154227219381837357780557)
                    ·
                      refine ⟨2307835207268189009167709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6154227219381837357780557 2307835207268189009167709)
                      ·
                        rfl

theorem cell23_4494493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_4494493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494493 prefixEnd_4494493 := by exact prefixLift 4494493
  have htrace : WordTrace (prefixWord ++ tailWord_4494493) baseStart_4494493 baseEnd_4494493 := by
    simpa [prefixWord, tailWord_4494493, baseEnd_4494493] using wordTrace_append hprefix tailTrace_4494493
  have hstable : (prefixWord ++ tailWord_4494493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494493).length < 2 ^ (prefixWord ++ tailWord_4494493).sum := by decide
  have hdescent : baseEnd_4494493 < baseStart_4494493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494499 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_4494499 : Nat := 118140960795 + 4494499 * 2 ^ 59
def prefixEnd_4494499 : Nat := 4983230072969 + 3 ^ 40 * 4494499 * 2
def baseEnd_4494499 : Nat := 2307838288152115985692681

theorem tailTrace_4494499 : CollatzResearch.WordTrace tailWord_4494499 prefixEnd_4494499 2307838288152115985692681 := by
  unfold tailWord_4494499
  simp only [CollatzResearch.WordTrace]
  refine ⟨163927845744205197162606551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109285230496136798108404367 163927845744205197162606551)
  ·
    refine ⟨245891768616307795743909827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163927845744205197162606551 245891768616307795743909827)
    ·
      refine ⟨368837652924461693615864741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245891768616307795743909827 368837652924461693615864741)
      ·
        refine ⟨69157059923336567552974639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368837652924461693615864741 69157059923336567552974639)
        ·
          refine ⟨103735589885004851329461959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69157059923336567552974639 103735589885004851329461959)
          ·
            refine ⟨155603384827507276994192939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103735589885004851329461959 155603384827507276994192939)
            ·
              refine ⟨233405077241260915491289409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155603384827507276994192939 233405077241260915491289409)
              ·
                refine ⟨175053807930945686618467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233405077241260915491289409 175053807930945686618467057)
                ·
                  refine ⟨131290355948209264963850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175053807930945686618467057 131290355948209264963850293)
                  ·
                    refine ⟨12308470870144618590360965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131290355948209264963850293 12308470870144618590360965)
                    ·
                      refine ⟨2307838288152115985692681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12308470870144618590360965 2307838288152115985692681)
                      ·
                        rfl

theorem cell23_4494499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_4494499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494499 prefixEnd_4494499 := by exact prefixLift 4494499
  have htrace : WordTrace (prefixWord ++ tailWord_4494499) baseStart_4494499 baseEnd_4494499 := by
    simpa [prefixWord, tailWord_4494499, baseEnd_4494499] using wordTrace_append hprefix tailTrace_4494499
  have hstable : (prefixWord ++ tailWord_4494499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494499).length < 2 ^ (prefixWord ++ tailWord_4494499).sum := by decide
  have hdescent : baseEnd_4494499 < baseStart_4494499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494513 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_4494513 : Nat := 118140960795 + 4494513 * 2 ^ 59
def prefixEnd_4494513 : Nat := 4983230072969 + 3 ^ 40 * 4494513 * 2
def baseEnd_4494513 : Nat := 769281825627092976972539

theorem tailTrace_4494513 : CollatzResearch.WordTrace tailWord_4494513 prefixEnd_4494513 769281825627092976972539 := by
  unfold tailWord_4494513
  simp only [CollatzResearch.WordTrace]
  refine ⟨163928356366154477553616193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109285570910769651702410795 163928356366154477553616193)
  ·
    refine ⟨122946267274615858165212145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163928356366154477553616193 122946267274615858165212145)
    ·
      refine ⟨92209700455961893623909109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122946267274615858165212145 92209700455961893623909109)
      ·
        refine ⟨8644659417746427527241479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92209700455961893623909109 8644659417746427527241479)
        ·
          refine ⟨12966989126619641290862219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8644659417746427527241479 12966989126619641290862219)
          ·
            refine ⟨19450483689929461936293329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12966989126619641290862219 19450483689929461936293329)
            ·
              refine ⟨14587862767447096452219997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19450483689929461936293329 14587862767447096452219997)
              ·
                refine ⟨5470448537792661169582499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14587862767447096452219997 5470448537792661169582499)
                ·
                  refine ⟨8205672806688991754373749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470448537792661169582499 8205672806688991754373749)
                  ·
                    refine ⟨769281825627092976972539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8205672806688991754373749 769281825627092976972539)
                    ·
                      rfl

theorem cell23_4494513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_4494513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494513 prefixEnd_4494513 := by exact prefixLift 4494513
  have htrace : WordTrace (prefixWord ++ tailWord_4494513) baseStart_4494513 baseEnd_4494513 := by
    simpa [prefixWord, tailWord_4494513, baseEnd_4494513] using wordTrace_append hprefix tailTrace_4494513
  have hstable : (prefixWord ++ tailWord_4494513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494513).length < 2 ^ (prefixWord ++ tailWord_4494513).sum := by decide
  have hdescent : baseEnd_4494513 < baseStart_4494513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494536 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_4494536 : Nat := 118140960795 + 4494536 * 2 ^ 59
def prefixEnd_4494536 : Nat := 4983230072969 + 3 ^ 40 * 4494536 * 2
def baseEnd_4494536 : Nat := 2307857286936332340930011

theorem tailTrace_4494536 : CollatzResearch.WordTrace tailWord_4494536 prefixEnd_4494536 2307857286936332340930011 := by
  unfold tailWord_4494536
  simp only [CollatzResearch.WordTrace]
  refine ⟨81964597622535576240851731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109286130163380768321135641 81964597622535576240851731)
  ·
    refine ⟨122946896433803364361277597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81964597622535576240851731 122946896433803364361277597)
    ·
      refine ⟨46105086162676261635479099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122946896433803364361277597 46105086162676261635479099)
      ·
        refine ⟨69157629244014392453218649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46105086162676261635479099 69157629244014392453218649)
        ·
          refine ⟨51868221933010794339913987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69157629244014392453218649 51868221933010794339913987)
          ·
            refine ⟨77802332899516191509870981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51868221933010794339913987 77802332899516191509870981)
            ·
              refine ⟨14587937418659285908100809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77802332899516191509870981 14587937418659285908100809)
              ·
                refine ⟨10940953063994464431075607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14587937418659285908100809 10940953063994464431075607)
                ·
                  refine ⟨16411429595991696646613411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10940953063994464431075607 16411429595991696646613411)
                  ·
                    refine ⟨24617144393987544969920117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16411429595991696646613411 24617144393987544969920117)
                    ·
                      refine ⟨2307857286936332340930011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24617144393987544969920117 2307857286936332340930011)
                      ·
                        rfl

theorem cell23_4494536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_4494536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494536 prefixEnd_4494536 := by exact prefixLift 4494536
  have htrace : WordTrace (prefixWord ++ tailWord_4494536) baseStart_4494536 baseEnd_4494536 := by
    simpa [prefixWord, tailWord_4494536, baseEnd_4494536] using wordTrace_append hprefix tailTrace_4494536
  have hstable : (prefixWord ++ tailWord_4494536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494536).length < 2 ^ (prefixWord ++ tailWord_4494536).sum := by decide
  have hdescent : baseEnd_4494536 < baseStart_4494536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494546 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4494546 : Nat := 118140960795 + 4494546 * 2 ^ 59
def prefixEnd_4494546 : Nat := 4983230072969 + 3 ^ 40 * 4494546 * 2
def baseEnd_4494546 : Nat := 2307862421742877301804965

theorem tailTrace_4494546 : CollatzResearch.WordTrace tailWord_4494546 prefixEnd_4494546 2307862421742877301804965 := by
  unfold tailWord_4494546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40982389993758731047391873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109286373316689949459711661 40982389993758731047391873)
  ·
    refine ⟨30736792495319048285543905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40982389993758731047391873 30736792495319048285543905)
    ·
      refine ⟨23052594371489286214157929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30736792495319048285543905 23052594371489286214157929)
      ·
        refine ⟨17289445778616964660618447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23052594371489286214157929 17289445778616964660618447)
        ·
          refine ⟨25934168667925446990927671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17289445778616964660618447 25934168667925446990927671)
          ·
            refine ⟨38901253001888170486391507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25934168667925446990927671 38901253001888170486391507)
            ·
              refine ⟨58351879502832255729587261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38901253001888170486391507 58351879502832255729587261)
              ·
                refine ⟨21881954813562095898595223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58351879502832255729587261 21881954813562095898595223)
                ·
                  refine ⟨32822932220343143847892835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21881954813562095898595223 32822932220343143847892835)
                  ·
                    refine ⟨49234398330514715771839253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32822932220343143847892835 49234398330514715771839253)
                    ·
                      refine ⟨2307862421742877301804965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49234398330514715771839253 2307862421742877301804965)
                      ·
                        rfl

theorem cell23_4494546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4494546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494546 prefixEnd_4494546 := by exact prefixLift 4494546
  have htrace : WordTrace (prefixWord ++ tailWord_4494546) baseStart_4494546 baseEnd_4494546 := by
    simpa [prefixWord, tailWord_4494546, baseEnd_4494546] using wordTrace_append hprefix tailTrace_4494546
  have hstable : (prefixWord ++ tailWord_4494546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494546).length < 2 ^ (prefixWord ++ tailWord_4494546).sum := by decide
  have hdescent : baseEnd_4494546 < baseStart_4494546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494567 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4494567 : Nat := 118140960795 + 4494567 * 2 ^ 59
def prefixEnd_4494567 : Nat := 4983230072969 + 3 ^ 40 * 4494567 * 2
def baseEnd_4494567 : Nat := 2307873204836621719642369

theorem tailTrace_4494567 : CollatzResearch.WordTrace tailWord_4494567 prefixEnd_4494567 2307873204836621719642369 := by
  unfold tailWord_4494567
  simp only [CollatzResearch.WordTrace]
  refine ⟨163930325907958844776081955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109286883938639229850721303 163930325907958844776081955)
  ·
    refine ⟨245895488861938267164122933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163930325907958844776081955 245895488861938267164122933)
    ·
      refine ⟨23052702080806712546636525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245895488861938267164122933 23052702080806712546636525)
      ·
        refine ⟨8644763280302517204988697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23052702080806712546636525 8644763280302517204988697)
        ·
          refine ⟨6483572460226887903741523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8644763280302517204988697 6483572460226887903741523)
          ·
            refine ⟨9725358690340331855612285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483572460226887903741523 9725358690340331855612285)
            ·
              refine ⟨3647009508877624445854607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9725358690340331855612285 3647009508877624445854607)
              ·
                refine ⟨5470514263316436668781911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647009508877624445854607 5470514263316436668781911)
                ·
                  refine ⟨8205771394974655003172867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470514263316436668781911 8205771394974655003172867)
                  ·
                    refine ⟨12308657092461982504759301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8205771394974655003172867 12308657092461982504759301)
                    ·
                      refine ⟨2307873204836621719642369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12308657092461982504759301 2307873204836621719642369)
                      ·
                        rfl

theorem cell23_4494567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4494567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494567 prefixEnd_4494567 := by exact prefixLift 4494567
  have htrace : WordTrace (prefixWord ++ tailWord_4494567) baseStart_4494567 baseEnd_4494567 := by
    simpa [prefixWord, tailWord_4494567, baseEnd_4494567] using wordTrace_append hprefix tailTrace_4494567
  have hstable : (prefixWord ++ tailWord_4494567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494567).length < 2 ^ (prefixWord ++ tailWord_4494567).sum := by decide
  have hdescent : baseEnd_4494567 < baseStart_4494567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494569 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_4494569 : Nat := 118140960795 + 4494569 * 2 ^ 59
def prefixEnd_4494569 : Nat := 4983230072969 + 3 ^ 40 * 4494569 * 2
def baseEnd_4494569 : Nat := 769291410599310237272453

theorem tailTrace_4494569 : CollatzResearch.WordTrace tailWord_4494569 prefixEnd_4494569 769291410599310237272453 := by
  unfold tailWord_4494569
  simp only [CollatzResearch.WordTrace]
  refine ⟨163930398853951599117654761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109286932569301066078436507 163930398853951599117654761)
  ·
    refine ⟨122947799140463699338241071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163930398853951599117654761 122947799140463699338241071)
    ·
      refine ⟨184421698710695549007361607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122947799140463699338241071 184421698710695549007361607)
      ·
        refine ⟨276632548066043323511042411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184421698710695549007361607 276632548066043323511042411)
        ·
          refine ⟨414948822099064985266563617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276632548066043323511042411 414948822099064985266563617)
          ·
            refine ⟨311211616574298738949922713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414948822099064985266563617 311211616574298738949922713)
            ·
              refine ⟨233408712430724054212442035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311211616574298738949922713 233408712430724054212442035)
              ·
                refine ⟨350113068646086081318663053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233408712430724054212442035 350113068646086081318663053)
                ·
                  refine ⟨131292400742282280494498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350113068646086081318663053 131292400742282280494498645)
                  ·
                    refine ⟨769291410599310237272453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131292400742282280494498645 769291410599310237272453)
                    ·
                      rfl

theorem cell23_4494569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_4494569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494569 prefixEnd_4494569 := by exact prefixLift 4494569
  have htrace : WordTrace (prefixWord ++ tailWord_4494569) baseStart_4494569 baseEnd_4494569 := by
    simpa [prefixWord, tailWord_4494569, baseEnd_4494569] using wordTrace_append hprefix tailTrace_4494569
  have hstable : (prefixWord ++ tailWord_4494569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494569).length < 2 ^ (prefixWord ++ tailWord_4494569).sum := by decide
  have hdescent : baseEnd_4494569 < baseStart_4494569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494600 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_4494600 : Nat := 118140960795 + 4494600 * 2 ^ 59
def prefixEnd_4494600 : Nat := 4983230072969 + 3 ^ 40 * 4494600 * 2
def baseEnd_4494600 : Nat := 2307890149698220090529717

theorem tailTrace_4494600 : CollatzResearch.WordTrace tailWord_4494600 prefixEnd_4494600 2307890149698220090529717 := by
  unfold tailWord_4494600
  simp only [CollatzResearch.WordTrace]
  refine ⟨81965764758419645706016627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109287686344559527608022169 81965764758419645706016627)
  ·
    refine ⟨122948647137629468559024941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81965764758419645706016627 122948647137629468559024941)
    ·
      refine ⟨46105742676611050709634353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122948647137629468559024941 46105742676611050709634353)
      ·
        refine ⟨34579307007458288032225765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46105742676611050709634353 34579307007458288032225765)
        ·
          refine ⟨6483620063898429006042331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34579307007458288032225765 6483620063898429006042331)
          ·
            refine ⟨9725430095847643509063497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6483620063898429006042331 9725430095847643509063497)
            ·
              refine ⟨7294072571885732631797623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9725430095847643509063497 7294072571885732631797623)
              ·
                refine ⟨10941108857828598947696435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7294072571885732631797623 10941108857828598947696435)
                ·
                  refine ⟨16411663286742898421544653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10941108857828598947696435 16411663286742898421544653)
                  ·
                    refine ⟨6154373732528586908079245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16411663286742898421544653 6154373732528586908079245)
                    ·
                      refine ⟨2307890149698220090529717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6154373732528586908079245 2307890149698220090529717)
                      ·
                        rfl

theorem cell23_4494600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_4494600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494600 prefixEnd_4494600 := by exact prefixLift 4494600
  have htrace : WordTrace (prefixWord ++ tailWord_4494600) baseStart_4494600 baseEnd_4494600 := by
    simpa [prefixWord, tailWord_4494600, baseEnd_4494600] using wordTrace_append hprefix tailTrace_4494600
  have hstable : (prefixWord ++ tailWord_4494600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494600).length < 2 ^ (prefixWord ++ tailWord_4494600).sum := by decide
  have hdescent : baseEnd_4494600 < baseStart_4494600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494627 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 1, 3, 2]
def baseStart_4494627 : Nat := 118140960795 + 4494627 * 2 ^ 59
def prefixEnd_4494627 : Nat := 4983230072969 + 3 ^ 40 * 4494627 * 2
def baseEnd_4494627 : Nat := 2307904013675891484892093

theorem tailTrace_4494627 : CollatzResearch.WordTrace tailWord_4494627 prefixEnd_4494627 2307904013675891484892093 := by
  unfold tailWord_4494627
  simp only [CollatzResearch.WordTrace]
  refine ⟨163932514287741475023266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109288342858494316682177423 163932514287741475023266135)
  ·
    refine ⟨245898771431612212534899203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163932514287741475023266135 245898771431612212534899203)
    ·
      refine ⟨368848157147418318802348805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245898771431612212534899203 368848157147418318802348805)
      ·
        refine ⟨69159029465140934775440401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368848157147418318802348805 69159029465140934775440401)
        ·
          refine ⟨51869272098855701081580301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69159029465140934775440401 51869272098855701081580301)
          ·
            refine ⟨19450977037070887905592613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51869272098855701081580301 19450977037070887905592613)
            ·
              refine ⟨3647058194450791482298615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19450977037070887905592613 3647058194450791482298615)
              ·
                refine ⟨5470587291676187223447923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647058194450791482298615 5470587291676187223447923)
                ·
                  refine ⟨8205880937514280835171885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5470587291676187223447923 8205880937514280835171885)
                  ·
                    refine ⟨3077205351567855313189457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8205880937514280835171885 3077205351567855313189457)
                    ·
                      refine ⟨2307904013675891484892093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077205351567855313189457 2307904013675891484892093)
                      ·
                        rfl

theorem cell23_4494627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_4494627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494627 prefixEnd_4494627 := by exact prefixLift 4494627
  have htrace : WordTrace (prefixWord ++ tailWord_4494627) baseStart_4494627 baseEnd_4494627 := by
    simpa [prefixWord, tailWord_4494627, baseEnd_4494627] using wordTrace_append hprefix tailTrace_4494627
  have hstable : (prefixWord ++ tailWord_4494627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494627).length < 2 ^ (prefixWord ++ tailWord_4494627).sum := by decide
  have hdescent : baseEnd_4494627 < baseStart_4494627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494634 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4494634 : Nat := 118140960795 + 4494634 * 2 ^ 59
def prefixEnd_4494634 : Nat := 4983230072969 + 3 ^ 40 * 4494634 * 2
def baseEnd_4494634 : Nat := 2307907608040472957504561

theorem tailTrace_4494634 : CollatzResearch.WordTrace tailWord_4494634 prefixEnd_4494634 2307907608040472957504561 := by
  unfold tailWord_4494634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40983192399679028804692739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109288513065810743479180637 40983192399679028804692739)
  ·
    refine ⟨61474788599518543207039109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40983192399679028804692739 61474788599518543207039109)
    ·
      refine ⟨11526522862409726851319833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61474788599518543207039109 11526522862409726851319833)
      ·
        refine ⟨8644892146807295138489875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11526522862409726851319833 8644892146807295138489875)
        ·
          refine ⟨12967338220210942707734813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8644892146807295138489875 12967338220210942707734813)
          ·
            refine ⟨4862751832579103515400555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12967338220210942707734813 4862751832579103515400555)
            ·
              refine ⟨7294127748868655273100833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862751832579103515400555 7294127748868655273100833)
              ·
                refine ⟨5470595811651491454825625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7294127748868655273100833 5470595811651491454825625)
                ·
                  refine ⟨4102946858738618591119219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470595811651491454825625 4102946858738618591119219)
                  ·
                    refine ⟨6154420288107927886678829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4102946858738618591119219 6154420288107927886678829)
                    ·
                      refine ⟨2307907608040472957504561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6154420288107927886678829 2307907608040472957504561)
                      ·
                        rfl

theorem cell23_4494634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4494634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494634 prefixEnd_4494634 := by exact prefixLift 4494634
  have htrace : WordTrace (prefixWord ++ tailWord_4494634) baseStart_4494634 baseEnd_4494634 := by
    simpa [prefixWord, tailWord_4494634, baseEnd_4494634] using wordTrace_append hprefix tailTrace_4494634
  have hstable : (prefixWord ++ tailWord_4494634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494634).length < 2 ^ (prefixWord ++ tailWord_4494634).sum := by decide
  have hdescent : baseEnd_4494634 < baseStart_4494634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494640 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2]
def baseStart_4494640 : Nat := 118140960795 + 4494640 * 2 ^ 59
def prefixEnd_4494640 : Nat := 4983230072969 + 3 ^ 40 * 4494640 * 2
def baseEnd_4494640 : Nat := 2307910688924399934029533

theorem tailTrace_4494640 : CollatzResearch.WordTrace tailWord_4494640 prefixEnd_4494640 2307910688924399934029533 := by
  unfold tailWord_4494640
  simp only [CollatzResearch.WordTrace]
  refine ⟨81966494218347189121744687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109288658957796252162326249 81966494218347189121744687)
  ·
    refine ⟨122949741327520783682617031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81966494218347189121744687 122949741327520783682617031)
    ·
      refine ⟨184424611991281175523925547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122949741327520783682617031 184424611991281175523925547)
      ·
        refine ⟨276636917986921763285888321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184424611991281175523925547 276636917986921763285888321)
        ·
          refine ⟨207477688490191322464416241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276636917986921763285888321 207477688490191322464416241)
          ·
            refine ⟨155608266367643491848312181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207477688490191322464416241 155608266367643491848312181)
            ·
              refine ⟨14588274971966577360779267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155608266367643491848312181 14588274971966577360779267)
              ·
                refine ⟨21882412457949866041168901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14588274971966577360779267 21882412457949866041168901)
                ·
                  refine ⟨4102952335865599882719169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21882412457949866041168901 4102952335865599882719169)
                  ·
                    refine ⟨3077214251899199912039377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4102952335865599882719169 3077214251899199912039377)
                    ·
                      refine ⟨2307910688924399934029533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077214251899199912039377 2307910688924399934029533)
                      ·
                        rfl

theorem cell23_4494640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2].length) (baseStart_4494640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494640 prefixEnd_4494640 := by exact prefixLift 4494640
  have htrace : WordTrace (prefixWord ++ tailWord_4494640) baseStart_4494640 baseEnd_4494640 := by
    simpa [prefixWord, tailWord_4494640, baseEnd_4494640] using wordTrace_append hprefix tailTrace_4494640
  have hstable : (prefixWord ++ tailWord_4494640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494640).length < 2 ^ (prefixWord ++ tailWord_4494640).sum := by decide
  have hdescent : baseEnd_4494640 < baseStart_4494640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494657 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4494657 : Nat := 118140960795 + 4494657 * 2 ^ 59
def prefixEnd_4494657 : Nat := 4983230072969 + 3 ^ 40 * 4494657 * 2
def baseEnd_4494657 : Nat := 2307919418095526367516955

theorem tailTrace_4494657 : CollatzResearch.WordTrace tailWord_4494657 prefixEnd_4494657 2307919418095526367516955 := by
  unfold tailWord_4494657
  simp only [CollatzResearch.WordTrace]
  refine ⟨163933608477632790146858225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109289072318421860097905483 163933608477632790146858225)
  ·
    refine ⟨122950206358224592610143669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163933608477632790146858225 122950206358224592610143669)
    ·
      refine ⟨11526581846083555557200969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122950206358224592610143669 11526581846083555557200969)
      ·
        refine ⟨8644936384562666667900727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11526581846083555557200969 8644936384562666667900727)
        ·
          refine ⟨12967404576844000001851091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8644936384562666667900727 12967404576844000001851091)
          ·
            refine ⟨19451106865266000002776637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12967404576844000001851091 19451106865266000002776637)
            ·
              refine ⟨7294165074474750001041239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19451106865266000002776637 7294165074474750001041239)
              ·
                refine ⟨10941247611712125001561859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7294165074474750001041239 10941247611712125001561859)
                ·
                  refine ⟨16411871417568187502342789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10941247611712125001561859 16411871417568187502342789)
                  ·
                    refine ⟨3077225890794035156689273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16411871417568187502342789 3077225890794035156689273)
                    ·
                      refine ⟨2307919418095526367516955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077225890794035156689273 2307919418095526367516955)
                      ·
                        rfl

theorem cell23_4494657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4494657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494657 prefixEnd_4494657 := by exact prefixLift 4494657
  have htrace : WordTrace (prefixWord ++ tailWord_4494657) baseStart_4494657 baseEnd_4494657 := by
    simpa [prefixWord, tailWord_4494657, baseEnd_4494657] using wordTrace_append hprefix tailTrace_4494657
  have hstable : (prefixWord ++ tailWord_4494657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494657).length < 2 ^ (prefixWord ++ tailWord_4494657).sum := by decide
  have hdescent : baseEnd_4494657 < baseStart_4494657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494693 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_4494693 : Nat := 118140960795 + 4494693 * 2 ^ 59
def prefixEnd_4494693 : Nat := 4983230072969 + 3 ^ 40 * 4494693 * 2
def baseEnd_4494693 : Nat := 769312634466362742222263

theorem tailTrace_4494693 : CollatzResearch.WordTrace tailWord_4494693 prefixEnd_4494693 769312634466362742222263 := by
  unfold tailWord_4494693
  simp only [CollatzResearch.WordTrace]
  refine ⟨163934921505502368295168733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109289947670334912196779155 163934921505502368295168733)
  ·
    refine ⟨61475595564563388110688275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163934921505502368295168733 61475595564563388110688275)
    ·
      refine ⟨92213393346845082166032413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61475595564563388110688275 92213393346845082166032413)
      ·
        refine ⟨34580022505066905812262155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92213393346845082166032413 34580022505066905812262155)
        ·
          refine ⟨51870033757600358718393233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34580022505066905812262155 51870033757600358718393233)
          ·
            refine ⟨38902525318200269038794925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51870033757600358718393233 38902525318200269038794925)
            ·
              refine ⟨14588446994325100889548097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38902525318200269038794925 14588446994325100889548097)
              ·
                refine ⟨10941335245743825667161073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14588446994325100889548097 10941335245743825667161073)
                ·
                  refine ⟨8206001434307869250370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10941335245743825667161073 8206001434307869250370805)
                  ·
                    refine ⟨769312634466362742222263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8206001434307869250370805 769312634466362742222263)
                    ·
                      rfl

theorem cell23_4494693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_4494693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494693 prefixEnd_4494693 := by exact prefixLift 4494693
  have htrace : WordTrace (prefixWord ++ tailWord_4494693) baseStart_4494693 baseEnd_4494693 := by
    simpa [prefixWord, tailWord_4494693, baseEnd_4494693] using wordTrace_append hprefix tailTrace_4494693
  have hstable : (prefixWord ++ tailWord_4494693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494693).length < 2 ^ (prefixWord ++ tailWord_4494693).sum := by decide
  have hdescent : baseEnd_4494693 < baseStart_4494693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494804 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4494804 : Nat := 118140960795 + 4494804 * 2 ^ 59
def prefixEnd_4494804 : Nat := 4983230072969 + 3 ^ 40 * 4494804 * 2
def baseEnd_4494804 : Nat := 256443877750193032486531

theorem tailTrace_4494804 : CollatzResearch.WordTrace tailWord_4494804 prefixEnd_4494804 256443877750193032486531 := by
  unfold tailWord_4494804
  simp only [CollatzResearch.WordTrace]
  refine ⟨81969485004050117126229733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109292646672066822834972977 81969485004050117126229733)
  ·
    refine ⟨15369278438259396961168075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81969485004050117126229733 15369278438259396961168075)
    ·
      refine ⟨23053917657389095441752113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15369278438259396961168075 23053917657389095441752113)
      ·
        refine ⟨17290438243041821581314085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23053917657389095441752113 17290438243041821581314085)
        ·
          refine ⟨3241957170570341546496391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17290438243041821581314085 3241957170570341546496391)
          ·
            refine ⟨4862935755855512319744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241957170570341546496391 4862935755855512319744587)
            ·
              refine ⟨7294403633783268479616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862935755855512319744587 7294403633783268479616881)
              ·
                refine ⟨5470802725337451359712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7294403633783268479616881 5470802725337451359712661)
                ·
                  refine ⟨256443877750193032486531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5470802725337451359712661 256443877750193032486531)
                  ·
                    rfl

theorem cell23_4494804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4494804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494804 prefixEnd_4494804 := by exact prefixLift 4494804
  have htrace : WordTrace (prefixWord ++ tailWord_4494804) baseStart_4494804 baseEnd_4494804 := by
    simpa [prefixWord, tailWord_4494804, baseEnd_4494804] using wordTrace_append hprefix tailTrace_4494804
  have hstable : (prefixWord ++ tailWord_4494804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494804).length < 2 ^ (prefixWord ++ tailWord_4494804).sum := by decide
  have hdescent : baseEnd_4494804 < baseStart_4494804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494860 : List Nat := [2, 2, 1, 2, 5, 2, 9]
def baseStart_4494860 : Nat := 118140960795 + 4494860 * 2 ^ 59
def prefixEnd_4494860 : Nat := 4983230072969 + 3 ^ 40 * 4494860 * 2
def baseEnd_4494860 : Nat := 28494119193436902139241

theorem tailTrace_4494860 : CollatzResearch.WordTrace tailWord_4494860 prefixEnd_4494860 28494119193436902139241 := by
  unfold tailWord_4494860
  simp only [CollatzResearch.WordTrace]
  refine ⟨81970506247948677908249017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109294008330598237210998689 81970506247948677908249017)
  ·
    refine ⟨61477879685961508431186763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81970506247948677908249017 61477879685961508431186763)
    ·
      refine ⟨92216819528942262646780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61477879685961508431186763 92216819528942262646780145)
      ·
        refine ⟨69162614646706696985085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92216819528942262646780145 69162614646706696985085109)
        ·
          refine ⟨6483995123128752842351729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69162614646706696985085109 6483995123128752842351729)
          ·
            refine ⟨4862996342346564631763797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483995123128752842351729 4862996342346564631763797)
            ·
              refine ⟨28494119193436902139241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4862996342346564631763797 28494119193436902139241)
              ·
                rfl

theorem cell23_4494860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 9].length) (baseStart_4494860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494860 prefixEnd_4494860 := by exact prefixLift 4494860
  have htrace : WordTrace (prefixWord ++ tailWord_4494860) baseStart_4494860 baseEnd_4494860 := by
    simpa [prefixWord, tailWord_4494860, baseEnd_4494860] using wordTrace_append hprefix tailTrace_4494860
  have hstable : (prefixWord ++ tailWord_4494860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494860).length < 2 ^ (prefixWord ++ tailWord_4494860).sum := by decide
  have hdescent : baseEnd_4494860 < baseStart_4494860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494923 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_4494923 : Nat := 118140960795 + 4494923 * 2 ^ 59
def prefixEnd_4494923 : Nat := 4983230072969 + 3 ^ 40 * 4494923 * 2
def baseEnd_4494923 : Nat := 2308056003949622326790731

theorem tailTrace_4494923 : CollatzResearch.WordTrace tailWord_4494923 prefixEnd_4494923 2308056003949622326790731 := by
  unfold tailWord_4494923
  simp only [CollatzResearch.WordTrace]
  refine ⟨163943310294669117576041423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109295540196446078384027615 163943310294669117576041423)
  ·
    refine ⟨245914965442003676364062135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163943310294669117576041423 245914965442003676364062135)
    ·
      refine ⟨368872448163005514546093203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245914965442003676364062135 368872448163005514546093203)
      ·
        refine ⟨553308672244508271819139805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368872448163005514546093203 553308672244508271819139805)
        ·
          refine ⟨207490752091690601932177427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 553308672244508271819139805 207490752091690601932177427)
          ·
            refine ⟨311236128137535902898266141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207490752091690601932177427 311236128137535902898266141)
            ·
              refine ⟨116713548051575963586849803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311236128137535902898266141 116713548051575963586849803)
              ·
                refine ⟨175070322077363945380274705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116713548051575963586849803 175070322077363945380274705)
                ·
                  refine ⟨131302741558022959035206029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175070322077363945380274705 131302741558022959035206029)
                  ·
                    refine ⟨49238528084258609638202261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131302741558022959035206029 49238528084258609638202261)
                    ·
                      refine ⟨2308056003949622326790731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49238528084258609638202261 2308056003949622326790731)
                      ·
                        rfl

theorem cell23_4494923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_4494923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494923 prefixEnd_4494923 := by exact prefixLift 4494923
  have htrace : WordTrace (prefixWord ++ tailWord_4494923) baseStart_4494923 baseEnd_4494923 := by
    simpa [prefixWord, tailWord_4494923, baseEnd_4494923] using wordTrace_append hprefix tailTrace_4494923
  have hstable : (prefixWord ++ tailWord_4494923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494923).length < 2 ^ (prefixWord ++ tailWord_4494923).sum := by decide
  have hdescent : baseEnd_4494923 < baseStart_4494923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
