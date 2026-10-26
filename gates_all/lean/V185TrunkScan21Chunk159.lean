import V185TrunkScan21Chunk158

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1939296 : List Nat := [2, 1, 1, 3, 3, 2, 2, 7]
def baseStart_1939296 : Nat := 118140960795 + 1939296 * 2 ^ 59
def prefixEnd_1939296 : Nat := 4983230072969 + 3 ^ 40 * 1939296 * 2
def baseEnd_1939296 : Nat := 147524589532111070989829

theorem tailTrace_1939296 : CollatzResearch.WordTrace tailWord_1939296 prefixEnd_1939296 147524589532111070989829 := by
  unfold tailWord_1939296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35365967991134636116650871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47154623988179514822201161 35365967991134636116650871)
  ·
    refine ⟨53048951986701954174976307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35365967991134636116650871 53048951986701954174976307)
    ·
      refine ⟨79573427980052931262464461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53048951986701954174976307 79573427980052931262464461)
      ·
        refine ⟨29840035492519849223424173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79573427980052931262464461 29840035492519849223424173)
        ·
          refine ⟨11190013309694943458784065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29840035492519849223424173 11190013309694943458784065)
          ·
            refine ⟨8392509982271207594088049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190013309694943458784065 8392509982271207594088049)
            ·
              refine ⟨6294382486703405695566037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392509982271207594088049 6294382486703405695566037)
              ·
                refine ⟨147524589532111070989829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6294382486703405695566037 147524589532111070989829)
                ·
                  rfl

theorem cell21_1939296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_1939296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939296 prefixEnd_1939296 := by exact prefixLift 1939296
  have htrace : WordTrace (prefixWord ++ tailWord_1939296) baseStart_1939296 baseEnd_1939296 := by
    simpa [prefixWord, tailWord_1939296, baseEnd_1939296] using wordTrace_append hprefix tailTrace_1939296
  have hstable : (prefixWord ++ tailWord_1939296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939296).length < 2 ^ (prefixWord ++ tailWord_1939296).sum := by decide
  have hdescent : baseEnd_1939296 < baseStart_1939296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939434 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1939434 : Nat := 118140960795 + 1939434 * 2 ^ 59
def prefixEnd_1939434 : Nat := 4983230072969 + 3 ^ 40 * 1939434 * 2
def baseEnd_1939434 : Nat := 442605262076475639669205

theorem tailTrace_1939434 : CollatzResearch.WordTrace tailWord_1939434 prefixEnd_1939434 442605262076475639669205 := by
  unfold tailWord_1939434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684242313942330450456339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47157979503846214534550237 17684242313942330450456339)
  ·
    refine ⟨26526363470913495675684509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17684242313942330450456339 26526363470913495675684509)
    ·
      refine ⟨9947386301592560878381691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26526363470913495675684509 9947386301592560878381691)
      ·
        refine ⟨14921079452388841317572537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947386301592560878381691 14921079452388841317572537)
        ·
          refine ⟨11190809589291630988179403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14921079452388841317572537 11190809589291630988179403)
          ·
            refine ⟨16786214383937446482269105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190809589291630988179403 16786214383937446482269105)
            ·
              refine ⟨12589660787953084861701829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16786214383937446482269105 12589660787953084861701829)
              ·
                refine ⟨2360561397741203411569093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12589660787953084861701829 2360561397741203411569093)
                ·
                  refine ⟨442605262076475639669205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360561397741203411569093 442605262076475639669205)
                  ·
                    rfl

theorem cell21_1939434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1939434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939434 prefixEnd_1939434 := by exact prefixLift 1939434
  have htrace : WordTrace (prefixWord ++ tailWord_1939434) baseStart_1939434 baseEnd_1939434 := by
    simpa [prefixWord, tailWord_1939434, baseEnd_1939434] using wordTrace_append hprefix tailTrace_1939434
  have hstable : (prefixWord ++ tailWord_1939434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939434).length < 2 ^ (prefixWord ++ tailWord_1939434).sum := by decide
  have hdescent : baseEnd_1939434 < baseStart_1939434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939589 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 3]
def baseStart_1939589 : Nat := 118140960795 + 1939589 * 2 ^ 59
def prefixEnd_1939589 : Nat := 4983230072969 + 3 ^ 40 * 1939589 * 2
def baseEnd_1939589 : Nat := 442640635188229814585555

theorem tailTrace_1939589 : CollatzResearch.WordTrace tailWord_1939589 prefixEnd_1939589 442640635188229814585555 := by
  unfold tailWord_1939589
  simp only [CollatzResearch.WordTrace]
  refine ⟨70742622570207783273717821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47161748380138522182478547 70742622570207783273717821)
  ·
    refine ⟨26528483463827918727644183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70742622570207783273717821 26528483463827918727644183)
    ·
      refine ⟨39792725195741878091466275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26528483463827918727644183 39792725195741878091466275)
      ·
        refine ⟨59689087793612817137199413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39792725195741878091466275 59689087793612817137199413)
        ·
          refine ⟨5595851980651201606612445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59689087793612817137199413 5595851980651201606612445)
          ·
            refine ⟨2098444492744200602479667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5595851980651201606612445 2098444492744200602479667)
            ·
              refine ⟨3147666739116300903719501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098444492744200602479667 3147666739116300903719501)
              ·
                refine ⟨1180375027168612838894813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3147666739116300903719501 1180375027168612838894813)
                ·
                  refine ⟨442640635188229814585555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180375027168612838894813 442640635188229814585555)
                  ·
                    rfl

theorem cell21_1939589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_1939589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939589 prefixEnd_1939589 := by exact prefixLift 1939589
  have htrace : WordTrace (prefixWord ++ tailWord_1939589) baseStart_1939589 baseEnd_1939589 := by
    simpa [prefixWord, tailWord_1939589, baseEnd_1939589] using wordTrace_append hprefix tailTrace_1939589
  have hstable : (prefixWord ++ tailWord_1939589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939589).length < 2 ^ (prefixWord ++ tailWord_1939589).sum := by decide
  have hdescent : baseEnd_1939589 < baseStart_1939589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939620 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1939620 : Nat := 118140960795 + 1939620 * 2 ^ 59
def prefixEnd_1939620 : Nat := 4983230072969 + 3 ^ 40 * 1939620 * 2
def baseEnd_1939620 : Nat := 442647709810580649568825

theorem tailTrace_1939620 : CollatzResearch.WordTrace tailWord_1939620 prefixEnd_1939620 442647709810580649568825 := by
  unfold tailWord_1939620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35371876616547737784048157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47162502155396983712064209 35371876616547737784048157)
  ·
    refine ⟨13264453731205401669018059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35371876616547737784048157 13264453731205401669018059)
    ·
      refine ⟨19896680596808102503527089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264453731205401669018059 19896680596808102503527089)
      ·
        refine ⟨14922510447606076877645317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19896680596808102503527089 14922510447606076877645317)
        ·
          refine ⟨2797970708926139414558497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14922510447606076877645317 2797970708926139414558497)
          ·
            refine ⟨2098478031694604560918873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797970708926139414558497 2098478031694604560918873)
            ·
              refine ⟨1573858523770953420689155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098478031694604560918873 1573858523770953420689155)
              ·
                refine ⟨2360787785656430131033733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573858523770953420689155 2360787785656430131033733)
                ·
                  refine ⟨442647709810580649568825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360787785656430131033733 442647709810580649568825)
                  ·
                    rfl

theorem cell21_1939620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1939620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939620 prefixEnd_1939620 := by exact prefixLift 1939620
  have htrace : WordTrace (prefixWord ++ tailWord_1939620) baseStart_1939620 baseEnd_1939620 := by
    simpa [prefixWord, tailWord_1939620, baseEnd_1939620] using wordTrace_append hprefix tailTrace_1939620
  have hstable : (prefixWord ++ tailWord_1939620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939620).length < 2 ^ (prefixWord ++ tailWord_1939620).sum := by decide
  have hdescent : baseEnd_1939620 < baseStart_1939620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939662 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1939662 : Nat := 118140960795 + 1939662 * 2 ^ 59
def prefixEnd_1939662 : Nat := 4983230072969 + 3 ^ 40 * 1939662 * 2
def baseEnd_1939662 : Nat := 442657294782797909868739

theorem tailTrace_1939662 : CollatzResearch.WordTrace tailWord_1939662 prefixEnd_1939662 442657294782797909868739 := by
  unfold tailWord_1939662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843160637367914592640655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47163523399295544494083493 8843160637367914592640655)
  ·
    refine ⟨13264740956051871888960983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843160637367914592640655 13264740956051871888960983)
    ·
      refine ⟨19897111434077807833441475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13264740956051871888960983 19897111434077807833441475)
      ·
        refine ⟨29845667151116711750162213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19897111434077807833441475 29845667151116711750162213)
        ·
          refine ⟨5596062590834383453155415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29845667151116711750162213 5596062590834383453155415)
          ·
            refine ⟨8394093886251575179733123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596062590834383453155415 8394093886251575179733123)
            ·
              refine ⟨12591140829377362769599685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394093886251575179733123 12591140829377362769599685)
              ·
                refine ⟨2360838905508255519299941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12591140829377362769599685 2360838905508255519299941)
                ·
                  refine ⟨442657294782797909868739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360838905508255519299941 442657294782797909868739)
                  ·
                    rfl

theorem cell21_1939662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1939662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939662 prefixEnd_1939662 := by exact prefixLift 1939662
  have htrace : WordTrace (prefixWord ++ tailWord_1939662) baseStart_1939662 baseEnd_1939662 := by
    simpa [prefixWord, tailWord_1939662, baseEnd_1939662] using wordTrace_append hprefix tailTrace_1939662
  have hstable : (prefixWord ++ tailWord_1939662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939662).length < 2 ^ (prefixWord ++ tailWord_1939662).sum := by decide
  have hdescent : baseEnd_1939662 < baseStart_1939662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939682 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1939682 : Nat := 118140960795 + 1939682 * 2 ^ 59
def prefixEnd_1939682 : Nat := 4983230072969 + 3 ^ 40 * 1939682 * 2
def baseEnd_1939682 : Nat := 442661859055282319535365

theorem tailTrace_1939682 : CollatzResearch.WordTrace tailWord_1939682 prefixEnd_1939682 442661859055282319535365 := by
  unfold tailWord_1939682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686503639717715039213325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47164009705913906771235533 17686503639717715039213325)
  ·
    refine ⟨6632438864894143139704997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17686503639717715039213325 6632438864894143139704997)
    ·
      refine ⟨1243582287167651838694687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6632438864894143139704997 1243582287167651838694687)
      ·
        refine ⟨1865373430751477758042031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243582287167651838694687 1865373430751477758042031)
        ·
          refine ⟨2798060146127216637063047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865373430751477758042031 2798060146127216637063047)
          ·
            refine ⟨4197090219190824955594571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798060146127216637063047 4197090219190824955594571)
            ·
              refine ⟨6295635328786237433391857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197090219190824955594571 6295635328786237433391857)
              ·
                refine ⟨4721726496589678075043893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295635328786237433391857 4721726496589678075043893)
                ·
                  refine ⟨442661859055282319535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721726496589678075043893 442661859055282319535365)
                  ·
                    rfl

theorem cell21_1939682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1939682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939682 prefixEnd_1939682 := by exact prefixLift 1939682
  have htrace : WordTrace (prefixWord ++ tailWord_1939682) baseStart_1939682 baseEnd_1939682 := by
    simpa [prefixWord, tailWord_1939682, baseEnd_1939682] using wordTrace_append hprefix tailTrace_1939682
  have hstable : (prefixWord ++ tailWord_1939682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939682).length < 2 ^ (prefixWord ++ tailWord_1939682).sum := by decide
  have hdescent : baseEnd_1939682 < baseStart_1939682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939721 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_1939721 : Nat := 118140960795 + 1939721 * 2 ^ 59
def prefixEnd_1939721 : Nat := 4983230072969 + 3 ^ 40 * 1939721 * 2
def baseEnd_1939721 : Nat := 442670759386626918385285

theorem tailTrace_1939721 : CollatzResearch.WordTrace tailWord_1939721 prefixEnd_1939721 442670759386626918385285 := by
  unfold tailWord_1939721
  simp only [CollatzResearch.WordTrace]
  refine ⟨70747437005729569817523017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47164958003819713211682011 70747437005729569817523017)
  ·
    refine ⟨53060577754297177363142263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70747437005729569817523017 53060577754297177363142263)
    ·
      refine ⟨79590866631445766044713395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53060577754297177363142263 79590866631445766044713395)
      ·
        refine ⟨119386299947168649067070093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79590866631445766044713395 119386299947168649067070093)
        ·
          refine ⟨44769862480188243400151285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119386299947168649067070093 44769862480188243400151285)
          ·
            refine ⟨4197174607517647818764183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44769862480188243400151285 4197174607517647818764183)
            ·
              refine ⟨6295761911276471728146275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197174607517647818764183 6295761911276471728146275)
              ·
                refine ⟨9443642866914707592219413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295761911276471728146275 9443642866914707592219413)
                ·
                  refine ⟨442670759386626918385285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9443642866914707592219413 442670759386626918385285)
                  ·
                    rfl

theorem cell21_1939721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_1939721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939721 prefixEnd_1939721 := by exact prefixLift 1939721
  have htrace : WordTrace (prefixWord ++ tailWord_1939721) baseStart_1939721 baseEnd_1939721 := by
    simpa [prefixWord, tailWord_1939721, baseEnd_1939721] using wordTrace_append hprefix tailTrace_1939721
  have hstable : (prefixWord ++ tailWord_1939721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939721).length < 2 ^ (prefixWord ++ tailWord_1939721).sum := by decide
  have hdescent : baseEnd_1939721 < baseStart_1939721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939811 : List Nat := [1, 1, 1, 5, 2, 1, 1, 9]
def baseStart_1939811 : Nat := 118140960795 + 1939811 * 2 ^ 59
def prefixEnd_1939811 : Nat := 4983230072969 + 3 ^ 40 * 1939811 * 2
def baseEnd_1939811 : Nat := 147563766204268920628367

theorem tailTrace_1939811 : CollatzResearch.WordTrace tailWord_1939811 prefixEnd_1939811 147563766204268920628367 := by
  unfold tailWord_1939811
  simp only [CollatzResearch.WordTrace]
  refine ⟨70750719575403515188299287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47167146383602343458866191 70750719575403515188299287)
  ·
    refine ⟨106126079363105272782448931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70750719575403515188299287 106126079363105272782448931)
    ·
      refine ⟨159189119044657909173673397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106126079363105272782448931 159189119044657909173673397)
      ·
        refine ⟨14923979910436678985031881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159189119044657909173673397 14923979910436678985031881)
        ·
          refine ⟨11192984932827509238773911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14923979910436678985031881 11192984932827509238773911)
          ·
            refine ⟨16789477399241263858160867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192984932827509238773911 16789477399241263858160867)
            ·
              refine ⟨25184216098861895787241301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16789477399241263858160867 25184216098861895787241301)
              ·
                refine ⟨147563766204268920628367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25184216098861895787241301 147563766204268920628367)
                ·
                  rfl

theorem cell21_1939811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_1939811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939811 prefixEnd_1939811 := by exact prefixLift 1939811
  have htrace : WordTrace (prefixWord ++ tailWord_1939811) baseStart_1939811 baseEnd_1939811 := by
    simpa [prefixWord, tailWord_1939811, baseEnd_1939811] using wordTrace_append hprefix tailTrace_1939811
  have hstable : (prefixWord ++ tailWord_1939811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939811).length < 2 ^ (prefixWord ++ tailWord_1939811).sum := by decide
  have hdescent : baseEnd_1939811 < baseStart_1939811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939882 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1939882 : Nat := 118140960795 + 1939882 * 2 ^ 59
def prefixEnd_1939882 : Nat := 4983230072969 + 3 ^ 40 * 1939882 * 2
def baseEnd_1939882 : Nat := 442707501780126416201623

theorem tailTrace_1939882 : CollatzResearch.WordTrace tailWord_1939882 prefixEnd_1939882 442707501780126416201623 := by
  unfold tailWord_1939882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688327289536573578533475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47168872772097529542755933 17688327289536573578533475)
  ·
    refine ⟨26532490934304860367800213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17688327289536573578533475 26532490934304860367800213)
    ·
      refine ⟨1243710512545540329740635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26532490934304860367800213 1243710512545540329740635)
      ·
        refine ⟨1865565768818310494610953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243710512545540329740635 1865565768818310494610953)
        ·
          refine ⟨1399174326613732870958215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865565768818310494610953 1399174326613732870958215)
          ·
            refine ⟨2098761489920599306437323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399174326613732870958215 2098761489920599306437323)
            ·
              refine ⟨3148142234880898959655985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098761489920599306437323 3148142234880898959655985)
              ·
                refine ⟨2361106676160674219741989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148142234880898959655985 2361106676160674219741989)
                ·
                  refine ⟨442707501780126416201623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361106676160674219741989 442707501780126416201623)
                  ·
                    rfl

theorem cell21_1939882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1939882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939882 prefixEnd_1939882 := by exact prefixLift 1939882
  have htrace : WordTrace (prefixWord ++ tailWord_1939882) baseStart_1939882 baseEnd_1939882 := by
    simpa [prefixWord, tailWord_1939882, baseEnd_1939882] using wordTrace_append hprefix tailTrace_1939882
  have hstable : (prefixWord ++ tailWord_1939882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939882).length < 2 ^ (prefixWord ++ tailWord_1939882).sum := by decide
  have hdescent : baseEnd_1939882 < baseStart_1939882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939938 : List Nat := [3, 3, 3, 2, 1, 2, 7]
def baseStart_1939938 : Nat := 118140960795 + 1939938 * 2 ^ 59
def prefixEnd_1939938 : Nat := 4983230072969 + 3 ^ 40 * 1939938 * 2
def baseEnd_1939938 : Nat := 49191142415898084807575

theorem tailTrace_1939938 : CollatzResearch.WordTrace tailWord_1939938 prefixEnd_1939938 49191142415898084807575 := by
  unfold tailWord_1939938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688837911485853969543117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47170234430628943918781645 17688837911485853969543117)
  ·
    refine ⟨6633314216807195238578669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17688837911485853969543117 6633314216807195238578669)
    ·
      refine ⟨2487492831302698214467001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6633314216807195238578669 2487492831302698214467001)
      ·
        refine ⟨1865619623477023660850251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2487492831302698214467001 1865619623477023660850251)
        ·
          refine ⟨2798429435215535491275377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865619623477023660850251 2798429435215535491275377)
          ·
            refine ⟨2098822076411651618456533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798429435215535491275377 2098822076411651618456533)
            ·
              refine ⟨49191142415898084807575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2098822076411651618456533 49191142415898084807575)
              ·
                rfl

theorem cell21_1939938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 7].length) (baseStart_1939938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939938 prefixEnd_1939938 := by exact prefixLift 1939938
  have htrace : WordTrace (prefixWord ++ tailWord_1939938) baseStart_1939938 baseEnd_1939938 := by
    simpa [prefixWord, tailWord_1939938, baseEnd_1939938] using wordTrace_append hprefix tailTrace_1939938
  have hstable : (prefixWord ++ tailWord_1939938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939938).length < 2 ^ (prefixWord ++ tailWord_1939938).sum := by decide
  have hdescent : baseEnd_1939938 < baseStart_1939938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939952 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_1939952 : Nat := 118140960795 + 1939952 * 2 ^ 59
def prefixEnd_1939952 : Nat := 4983230072969 + 3 ^ 40 * 1939952 * 2
def baseEnd_1939952 : Nat := 442723476733821850034813

theorem tailTrace_1939952 : CollatzResearch.WordTrace tailWord_1939952 prefixEnd_1939952 442723476733821850034813 := by
  unfold tailWord_1939952
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377931133946348134591055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47170574845261797512788073 35377931133946348134591055)
  ·
    refine ⟨53066896700919522201886583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35377931133946348134591055 53066896700919522201886583)
    ·
      refine ⟨79600345051379283302829875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53066896700919522201886583 79600345051379283302829875)
      ·
        refine ⟨119400517577068924954244813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79600345051379283302829875 119400517577068924954244813)
        ·
          refine ⟨44775194091400846857841805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119400517577068924954244813 44775194091400846857841805)
          ·
            refine ⟨16790697784275317571690677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44775194091400846857841805 16790697784275317571690677)
            ·
              refine ⟨1574127917275811022346001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16790697784275317571690677 1574127917275811022346001)
              ·
                refine ⟨1180595937956858266759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574127917275811022346001 1180595937956858266759501)
                ·
                  refine ⟨442723476733821850034813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180595937956858266759501 442723476733821850034813)
                  ·
                    rfl

theorem cell21_1939952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_1939952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939952 prefixEnd_1939952 := by exact prefixLift 1939952
  have htrace : WordTrace (prefixWord ++ tailWord_1939952) baseStart_1939952 baseEnd_1939952 := by
    simpa [prefixWord, tailWord_1939952, baseEnd_1939952] using wordTrace_append hprefix tailTrace_1939952
  have hstable : (prefixWord ++ tailWord_1939952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939952).length < 2 ^ (prefixWord ++ tailWord_1939952).sum := by decide
  have hdescent : baseEnd_1939952 < baseStart_1939952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940014 : List Nat := [4, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1940014 : Nat := 118140960795 + 1940014 * 2 ^ 59
def prefixEnd_1940014 : Nat := 4983230072969 + 3 ^ 40 * 1940014 * 2
def baseEnd_1940014 : Nat := 147579208659507840000451

theorem tailTrace_1940014 : CollatzResearch.WordTrace tailWord_1940014 prefixEnd_1940014 147579208659507840000451 := by
  unfold tailWord_1940014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844765449208510107242387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47172082395778720571959397 8844765449208510107242387)
  ·
    refine ⟨13267148173812765160863581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844765449208510107242387 13267148173812765160863581)
    ·
      refine ⟨4975180565179786935323843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13267148173812765160863581 4975180565179786935323843)
      ·
        refine ⟨7462770847769680402985765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975180565179786935323843 7462770847769680402985765)
        ·
          refine ⟨1399269533956815075559831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7462770847769680402985765 1399269533956815075559831)
          ·
            refine ⟨2098904300935222613339747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399269533956815075559831 2098904300935222613339747)
            ·
              refine ⟨3148356451402833920009621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098904300935222613339747 3148356451402833920009621)
              ·
                refine ⟨147579208659507840000451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148356451402833920009621 147579208659507840000451)
                ·
                  rfl

theorem cell21_1940014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1940014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940014 prefixEnd_1940014 := by exact prefixLift 1940014
  have htrace : WordTrace (prefixWord ++ tailWord_1940014) baseStart_1940014 baseEnd_1940014 := by
    simpa [prefixWord, tailWord_1940014, baseEnd_1940014] using wordTrace_append hprefix tailTrace_1940014
  have hstable : (prefixWord ++ tailWord_1940014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940014).length < 2 ^ (prefixWord ++ tailWord_1940014).sum := by decide
  have hdescent : baseEnd_1940014 < baseStart_1940014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940025 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 4]
def baseStart_1940025 : Nat := 118140960795 + 1940025 * 2 ^ 59
def prefixEnd_1940025 : Nat := 4983230072969 + 3 ^ 40 * 1940025 * 2
def baseEnd_1940025 : Nat := 442740136328389945317997

theorem tailTrace_1940025 : CollatzResearch.WordTrace tailWord_1940025 prefixEnd_1940025 442740136328389945317997 := by
  unfold tailWord_1940025
  simp only [CollatzResearch.WordTrace]
  refine ⟨70758524796628229736589529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47172349864418819824393019 70758524796628229736589529)
  ·
    refine ⟨53068893597471172302442147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70758524796628229736589529 53068893597471172302442147)
    ·
      refine ⟨79603340396206758453663221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53068893597471172302442147 79603340396206758453663221)
      ·
        refine ⟨7462813162144383605030927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79603340396206758453663221 7462813162144383605030927)
        ·
          refine ⟨11194219743216575407546391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462813162144383605030927 11194219743216575407546391)
          ·
            refine ⟨16791329614824863111319587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11194219743216575407546391 16791329614824863111319587)
            ·
              refine ⟨25186994422237294666979381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791329614824863111319587 25186994422237294666979381)
              ·
                refine ⟨2361280727084746375029317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25186994422237294666979381 2361280727084746375029317)
                ·
                  refine ⟨442740136328389945317997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361280727084746375029317 442740136328389945317997)
                  ·
                    rfl

theorem cell21_1940025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_1940025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940025 prefixEnd_1940025 := by exact prefixLift 1940025
  have htrace : WordTrace (prefixWord ++ tailWord_1940025) baseStart_1940025 baseEnd_1940025 := by
    simpa [prefixWord, tailWord_1940025, baseEnd_1940025] using wordTrace_append hprefix tailTrace_1940025
  have hstable : (prefixWord ++ tailWord_1940025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940025).length < 2 ^ (prefixWord ++ tailWord_1940025).sum := by decide
  have hdescent : baseEnd_1940025 < baseStart_1940025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940045 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1940045 : Nat := 118140960795 + 1940045 * 2 ^ 59
def prefixEnd_1940045 : Nat := 4983230072969 + 3 ^ 40 * 1940045 * 2
def baseEnd_1940045 : Nat := 442744700600874354984623

theorem tailTrace_1940045 : CollatzResearch.WordTrace tailWord_1940045 prefixEnd_1940045 442744700600874354984623 := by
  unfold tailWord_1940045
  simp only [CollatzResearch.WordTrace]
  refine ⟨70759254256555773152317589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47172836171037182101545059 70759254256555773152317589)
  ·
    refine ⟨3316840043276051866514887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70759254256555773152317589 3316840043276051866514887)
    ·
      refine ⟨4975260064914077799772331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316840043276051866514887 4975260064914077799772331)
      ·
        refine ⟨7462890097371116699658497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975260064914077799772331 7462890097371116699658497)
        ·
          refine ⟨5597167573028337524743873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7462890097371116699658497 5597167573028337524743873)
          ·
            refine ⟨4197875679771253143557905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5597167573028337524743873 4197875679771253143557905)
            ·
              refine ⟨3148406759828439857668429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197875679771253143557905 3148406759828439857668429)
              ·
                refine ⟨1180652534935664946625661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3148406759828439857668429 1180652534935664946625661)
                ·
                  refine ⟨442744700600874354984623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180652534935664946625661 442744700600874354984623)
                  ·
                    rfl

theorem cell21_1940045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1940045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940045 prefixEnd_1940045 := by exact prefixLift 1940045
  have htrace : WordTrace (prefixWord ++ tailWord_1940045) baseStart_1940045 baseEnd_1940045 := by
    simpa [prefixWord, tailWord_1940045, baseEnd_1940045] using wordTrace_append hprefix tailTrace_1940045
  have hstable : (prefixWord ++ tailWord_1940045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940045).length < 2 ^ (prefixWord ++ tailWord_1940045).sum := by decide
  have hdescent : baseEnd_1940045 < baseStart_1940045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940062 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1940062 : Nat := 118140960795 + 1940062 * 2 ^ 59
def prefixEnd_1940062 : Nat := 4983230072969 + 3 ^ 40 * 1940062 * 2
def baseEnd_1940062 : Nat := 442748580232486103201255

theorem tailTrace_1940062 : CollatzResearch.WordTrace tailWord_1940062 prefixEnd_1940062 442748580232486103201255 := by
  unfold tailWord_1940062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844984287186773131960805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47173249531662790037124293 8844984287186773131960805)
  ·
    refine ⟨1658434553847519962242651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8844984287186773131960805 1658434553847519962242651)
    ·
      refine ⟨2487651830771279943363977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658434553847519962242651 2487651830771279943363977)
      ·
        refine ⟨1865738873078459957522983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2487651830771279943363977 1865738873078459957522983)
        ·
          refine ⟨2798608309617689936284475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865738873078459957522983 2798608309617689936284475)
          ·
            refine ⟨4197912464426534904426713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798608309617689936284475 4197912464426534904426713)
            ·
              refine ⟨3148434348319901178320035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197912464426534904426713 3148434348319901178320035)
              ·
                refine ⟨4722651522479851767480053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148434348319901178320035 4722651522479851767480053)
                ·
                  refine ⟨442748580232486103201255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4722651522479851767480053 442748580232486103201255)
                  ·
                    rfl

theorem cell21_1940062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1940062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940062 prefixEnd_1940062 := by exact prefixLift 1940062
  have htrace : WordTrace (prefixWord ++ tailWord_1940062) baseStart_1940062 baseEnd_1940062 := by
    simpa [prefixWord, tailWord_1940062, baseEnd_1940062] using wordTrace_append hprefix tailTrace_1940062
  have hstable : (prefixWord ++ tailWord_1940062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940062).length < 2 ^ (prefixWord ++ tailWord_1940062).sum := by decide
  have hdescent : baseEnd_1940062 < baseStart_1940062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940135 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_1940135 : Nat := 118140960795 + 1940135 * 2 ^ 59
def prefixEnd_1940135 : Nat := 4983230072969 + 3 ^ 40 * 1940135 * 2
def baseEnd_1940135 : Nat := 442765239827054198484439

theorem tailTrace_1940135 : CollatzResearch.WordTrace tailWord_1940135 prefixEnd_1940135 442765239827054198484439 := by
  unfold tailWord_1940135
  simp only [CollatzResearch.WordTrace]
  refine ⟨70762536826229718523093859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47175024550819812348729239 70762536826229718523093859)
  ·
    refine ⟨106143805239344577784640789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70762536826229718523093859 106143805239344577784640789)
    ·
      refine ⟨4975490870594277083655037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106143805239344577784640789 4975490870594277083655037)
      ·
        refine ⟨1865809076472853906370639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4975490870594277083655037 1865809076472853906370639)
        ·
          refine ⟨2798713614709280859555959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865809076472853906370639 2798713614709280859555959)
          ·
            refine ⟨4198070422063921289333939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798713614709280859555959 4198070422063921289333939)
            ·
              refine ⟨6297105633095881934000909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198070422063921289333939 6297105633095881934000909)
              ·
                refine ⟨2361414612410955725250341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6297105633095881934000909 2361414612410955725250341)
                ·
                  refine ⟨442765239827054198484439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361414612410955725250341 442765239827054198484439)
                  ·
                    rfl

theorem cell21_1940135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_1940135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940135 prefixEnd_1940135 := by exact prefixLift 1940135
  have htrace : WordTrace (prefixWord ++ tailWord_1940135) baseStart_1940135 baseEnd_1940135 := by
    simpa [prefixWord, tailWord_1940135, baseEnd_1940135] using wordTrace_append hprefix tailTrace_1940135
  have hstable : (prefixWord ++ tailWord_1940135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940135).length < 2 ^ (prefixWord ++ tailWord_1940135).sum := by decide
  have hdescent : baseEnd_1940135 < baseStart_1940135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940166 : List Nat := [6, 1, 2, 1, 3, 8]
def baseStart_1940166 : Nat := 118140960795 + 1940166 * 2 ^ 59
def prefixEnd_1940166 : Nat := 4983230072969 + 3 ^ 40 * 1940166 * 2
def baseEnd_1940166 : Nat := 16398974609237223461767

theorem tailTrace_1940166 : CollatzResearch.WordTrace tailWord_1940166 prefixEnd_1940166 16398974609237223461767 := by
  unfold tailWord_1940166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211364609034919088046011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47175778326078273878314901 2211364609034919088046011)
  ·
    refine ⟨3317046913552378632069017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211364609034919088046011 3317046913552378632069017)
    ·
      refine ⟨2487785185164283974051763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317046913552378632069017 2487785185164283974051763)
      ·
        refine ⟨3731677777746425961077645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487785185164283974051763 3731677777746425961077645)
        ·
          refine ⟨1399379166654909735404117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3731677777746425961077645 1399379166654909735404117)
          ·
            refine ⟨16398974609237223461767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1399379166654909735404117 16398974609237223461767)
            ·
              rfl

theorem cell21_1940166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 8].length) (baseStart_1940166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940166 prefixEnd_1940166 := by exact prefixLift 1940166
  have htrace : WordTrace (prefixWord ++ tailWord_1940166) baseStart_1940166 baseEnd_1940166 := by
    simpa [prefixWord, tailWord_1940166, baseEnd_1940166] using wordTrace_append hprefix tailTrace_1940166
  have hstable : (prefixWord ++ tailWord_1940166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940166).length < 2 ^ (prefixWord ++ tailWord_1940166).sum := by decide
  have hdescent : baseEnd_1940166 < baseStart_1940166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940177 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_1940177 : Nat := 118140960795 + 1940177 * 2 ^ 59
def prefixEnd_1940177 : Nat := 4983230072969 + 3 ^ 40 * 1940177 * 2
def baseEnd_1940177 : Nat := 442774824799271458784353

theorem tailTrace_1940177 : CollatzResearch.WordTrace tailWord_1940177 prefixEnd_1940177 442774824799271458784353 := by
  unfold tailWord_1940177
  simp only [CollatzResearch.WordTrace]
  refine ⟨70764068692077559696122785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47176045794718373130748523 70764068692077559696122785)
  ·
    refine ⟨53073051519058169772092089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70764068692077559696122785 53073051519058169772092089)
    ·
      refine ⟨39804788639293627329069067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53073051519058169772092089 39804788639293627329069067)
      ·
        refine ⟨59707182958940440993603601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39804788639293627329069067 59707182958940440993603601)
        ·
          refine ⟨44780387219205330745202701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59707182958940440993603601 44780387219205330745202701)
          ·
            refine ⟨16792645207201999029451013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44780387219205330745202701 16792645207201999029451013)
            ·
              refine ⟨3148620976350374818022065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16792645207201999029451013 3148620976350374818022065)
              ·
                refine ⟨2361465732262781113516549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148620976350374818022065 2361465732262781113516549)
                ·
                  refine ⟨442774824799271458784353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361465732262781113516549 442774824799271458784353)
                  ·
                    rfl

theorem cell21_1940177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_1940177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940177 prefixEnd_1940177 := by exact prefixLift 1940177
  have htrace : WordTrace (prefixWord ++ tailWord_1940177) baseStart_1940177 baseEnd_1940177 := by
    simpa [prefixWord, tailWord_1940177, baseEnd_1940177] using wordTrace_append hprefix tailTrace_1940177
  have hstable : (prefixWord ++ tailWord_1940177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940177).length < 2 ^ (prefixWord ++ tailWord_1940177).sum := by decide
  have hdescent : baseEnd_1940177 < baseStart_1940177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940191 : List Nat := [1, 1, 2, 3, 2, 3, 3, 6]
def baseStart_1940191 : Nat := 118140960795 + 1940191 * 2 ^ 59
def prefixEnd_1940191 : Nat := 4983230072969 + 3 ^ 40 * 1940191 * 2
def baseEnd_1940191 : Nat := 147592673263336848516997

theorem tailTrace_1940191 : CollatzResearch.WordTrace tailWord_1940191 prefixEnd_1940191 147592673263336848516997 := by
  unfold tailWord_1940191
  simp only [CollatzResearch.WordTrace]
  refine ⟨70764579314026840087132427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47176386209351226724754951 70764579314026840087132427)
  ·
    refine ⟨106146868971040260130698641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70764579314026840087132427 106146868971040260130698641)
    ·
      refine ⟨79610151728280195098023981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106146868971040260130698641 79610151728280195098023981)
      ·
        refine ⟨29853806898105073161758993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79610151728280195098023981 29853806898105073161758993)
        ·
          refine ⟨22390355173578804871319245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29853806898105073161758993 22390355173578804871319245)
          ·
            refine ⟨8396383190092051826744717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22390355173578804871319245 8396383190092051826744717)
            ·
              refine ⟨3148643696284519435029269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8396383190092051826744717 3148643696284519435029269)
              ·
                refine ⟨147592673263336848516997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148643696284519435029269 147592673263336848516997)
                ·
                  rfl

theorem cell21_1940191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_1940191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940191 prefixEnd_1940191 := by exact prefixLift 1940191
  have htrace : WordTrace (prefixWord ++ tailWord_1940191) baseStart_1940191 baseEnd_1940191 := by
    simpa [prefixWord, tailWord_1940191, baseEnd_1940191] using wordTrace_append hprefix tailTrace_1940191
  have hstable : (prefixWord ++ tailWord_1940191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940191).length < 2 ^ (prefixWord ++ tailWord_1940191).sum := by decide
  have hdescent : baseEnd_1940191 < baseStart_1940191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940301 : List Nat := [1, 6, 1, 2, 2, 1, 2, 6]
def baseStart_1940301 : Nat := 118140960795 + 1940301 * 2 ^ 59
def prefixEnd_1940301 : Nat := 4983230072969 + 3 ^ 40 * 1940301 * 2
def baseEnd_1940301 : Nat := 147601041096224932905811

theorem tailTrace_1940301 : CollatzResearch.WordTrace tailWord_1940301 prefixEnd_1940301 147601041096224932905811 := by
  unfold tailWord_1940301
  simp only [CollatzResearch.WordTrace]
  refine ⟨70768591343628328873636757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47179060895752219249091171 70768591343628328873636757)
  ·
    refine ⟨3317277719232577915951723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70768591343628328873636757 3317277719232577915951723)
    ·
      refine ⟨4975916578848866873927585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317277719232577915951723 4975916578848866873927585)
      ·
        refine ⟨3731937434136650155445689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975916578848866873927585 3731937434136650155445689)
        ·
          refine ⟨2798953075602487616584267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731937434136650155445689 2798953075602487616584267)
          ·
            refine ⟨4198429613403731424876401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798953075602487616584267 4198429613403731424876401)
            ·
              refine ⟨3148822210052798568657301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198429613403731424876401 3148822210052798568657301)
              ·
                refine ⟨147601041096224932905811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148822210052798568657301 147601041096224932905811)
                ·
                  rfl

theorem cell21_1940301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 6].length) (baseStart_1940301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940301 prefixEnd_1940301 := by exact prefixLift 1940301
  have htrace : WordTrace (prefixWord ++ tailWord_1940301) baseStart_1940301 baseEnd_1940301 := by
    simpa [prefixWord, tailWord_1940301, baseEnd_1940301] using wordTrace_append hprefix tailTrace_1940301
  have hstable : (prefixWord ++ tailWord_1940301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940301).length < 2 ^ (prefixWord ++ tailWord_1940301).sum := by decide
  have hdescent : baseEnd_1940301 < baseStart_1940301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940360 : List Nat := [2, 1, 3, 3, 2, 3, 1, 6]
def baseStart_1940360 : Nat := 118140960795 + 1940360 * 2 ^ 59
def prefixEnd_1940360 : Nat := 4983230072969 + 3 ^ 40 * 1940360 * 2
def baseEnd_1940360 : Nat := 147605529297501269077993

theorem tailTrace_1940360 : CollatzResearch.WordTrace tailWord_1940360 prefixEnd_1940360 147605529297501269077993 := by
  unfold tailWord_1940360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385371625207290975017267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47180495500276387966689689 35385371625207290975017267)
  ·
    refine ⟨53078057437810936462525901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35385371625207290975017267 53078057437810936462525901)
    ·
      refine ⟨19904271539179101173447213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53078057437810936462525901 19904271539179101173447213)
      ·
        refine ⟨7464101827192162940042705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19904271539179101173447213 7464101827192162940042705)
        ·
          refine ⟨5598076370394122205032029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464101827192162940042705 5598076370394122205032029)
          ·
            refine ⟨2099278638897795826887011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5598076370394122205032029 2099278638897795826887011)
            ·
              refine ⟨3148917958346693740330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099278638897795826887011 3148917958346693740330517)
              ·
                refine ⟨147605529297501269077993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148917958346693740330517 147605529297501269077993)
                ·
                  rfl

theorem cell21_1940360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_1940360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940360 prefixEnd_1940360 := by exact prefixLift 1940360
  have htrace : WordTrace (prefixWord ++ tailWord_1940360) baseStart_1940360 baseEnd_1940360 := by
    simpa [prefixWord, tailWord_1940360, baseEnd_1940360] using wordTrace_append hprefix tailTrace_1940360
  have hstable : (prefixWord ++ tailWord_1940360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940360).length < 2 ^ (prefixWord ++ tailWord_1940360).sum := by decide
  have hdescent : baseEnd_1940360 < baseStart_1940360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940388 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1940388 : Nat := 118140960795 + 1940388 * 2 ^ 59
def prefixEnd_1940388 : Nat := 4983230072969 + 3 ^ 40 * 1940388 * 2
def baseEnd_1940388 : Nat := 442822977873981980767255

theorem tailTrace_1940388 : CollatzResearch.WordTrace tailWord_1940388 prefixEnd_1940388 442822977873981980767255 := by
  unfold tailWord_1940388
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385882247156571366026909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47181176329542095154702545 35385882247156571366026909)
  ·
    refine ⟨13269705842683714262260091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35385882247156571366026909 13269705842683714262260091)
    ·
      refine ⟨19904558764025571393390137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13269705842683714262260091 19904558764025571393390137)
      ·
        refine ⟨14928419073019178545042603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19904558764025571393390137 14928419073019178545042603)
        ·
          refine ⟨22392628609528767817563905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928419073019178545042603 22392628609528767817563905)
          ·
            refine ⟨16794471457146575863172929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22392628609528767817563905 16794471457146575863172929)
            ·
              refine ⟨12595853592859931897379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16794471457146575863172929 12595853592859931897379697)
              ·
                refine ⟨9446890194644948923034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12595853592859931897379697 9446890194644948923034773)
                ·
                  refine ⟨442822977873981980767255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9446890194644948923034773 442822977873981980767255)
                  ·
                    rfl

theorem cell21_1940388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1940388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940388 prefixEnd_1940388 := by exact prefixLift 1940388
  have htrace : WordTrace (prefixWord ++ tailWord_1940388) baseStart_1940388 baseEnd_1940388 := by
    simpa [prefixWord, tailWord_1940388, baseEnd_1940388] using wordTrace_append hprefix tailTrace_1940388
  have hstable : (prefixWord ++ tailWord_1940388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940388).length < 2 ^ (prefixWord ++ tailWord_1940388).sum := by decide
  have hdescent : baseEnd_1940388 < baseStart_1940388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940433 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_1940433 : Nat := 118140960795 + 1940433 * 2 ^ 59
def prefixEnd_1940433 : Nat := 4983230072969 + 3 ^ 40 * 1940433 * 2
def baseEnd_1940433 : Nat := 442833247487071902517163

theorem tailTrace_1940433 : CollatzResearch.WordTrace tailWord_1940433 prefixEnd_1940433 442833247487071902517163 := by
  unfold tailWord_1940433
  simp only [CollatzResearch.WordTrace]
  refine ⟨70773405779150115417441953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47182270519433410278294635 70773405779150115417441953)
  ·
    refine ⟨53080054334362586563081465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70773405779150115417441953 53080054334362586563081465)
    ·
      refine ⟨39810040750771939922311099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53080054334362586563081465 39810040750771939922311099)
      ·
        refine ⟨59715061126157909883466649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39810040750771939922311099 59715061126157909883466649)
        ·
          refine ⟨44786295844618432412599987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59715061126157909883466649 44786295844618432412599987)
          ·
            refine ⟨67179443766927648618899981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44786295844618432412599987 67179443766927648618899981)
            ·
              refine ⟨25192291412597868232087493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67179443766927648618899981 25192291412597868232087493)
              ·
                refine ⟨4723554639862100293516405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25192291412597868232087493 4723554639862100293516405)
                ·
                  refine ⟨442833247487071902517163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723554639862100293516405 442833247487071902517163)
                  ·
                    rfl

theorem cell21_1940433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_1940433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940433 prefixEnd_1940433 := by exact prefixLift 1940433
  have htrace : WordTrace (prefixWord ++ tailWord_1940433) baseStart_1940433 baseEnd_1940433 := by
    simpa [prefixWord, tailWord_1940433, baseEnd_1940433] using wordTrace_append hprefix tailTrace_1940433
  have hstable : (prefixWord ++ tailWord_1940433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940433).length < 2 ^ (prefixWord ++ tailWord_1940433).sum := by decide
  have hdescent : baseEnd_1940433 < baseStart_1940433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940436 : List Nat := [2, 4, 1, 2, 1, 2, 4, 5]
def baseStart_1940436 : Nat := 118140960795 + 1940436 * 2 ^ 59
def prefixEnd_1940436 : Nat := 4983230072969 + 3 ^ 40 * 1940436 * 2
def baseEnd_1940436 : Nat := 147611310709314854655719

theorem tailTrace_1940436 : CollatzResearch.WordTrace tailWord_1940436 prefixEnd_1940436 147611310709314854655719 := by
  unfold tailWord_1940436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386757599069623464900581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47182343465426164619867441 35386757599069623464900581)
  ·
    refine ⟨6635017049825554399668859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35386757599069623464900581 6635017049825554399668859)
    ·
      refine ⟨9952525574738331599503289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635017049825554399668859 9952525574738331599503289)
      ·
        refine ⟨7464394181053748699627467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9952525574738331599503289 7464394181053748699627467)
        ·
          refine ⟨11196591271580623049441201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464394181053748699627467 11196591271580623049441201)
          ·
            refine ⟨8397443453685467287080901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11196591271580623049441201 8397443453685467287080901)
            ·
              refine ⟨1574520647566025116327669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8397443453685467287080901 1574520647566025116327669)
              ·
                refine ⟨147611310709314854655719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574520647566025116327669 147611310709314854655719)
                ·
                  rfl

theorem cell21_1940436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_1940436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940436 prefixEnd_1940436 := by exact prefixLift 1940436
  have htrace : WordTrace (prefixWord ++ tailWord_1940436) baseStart_1940436 baseEnd_1940436 := by
    simpa [prefixWord, tailWord_1940436, baseEnd_1940436] using wordTrace_append hprefix tailTrace_1940436
  have hstable : (prefixWord ++ tailWord_1940436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940436).length < 2 ^ (prefixWord ++ tailWord_1940436).sum := by decide
  have hdescent : baseEnd_1940436 < baseStart_1940436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940453 : List Nat := [1, 3, 1, 6, 2, 1, 7]
def baseStart_1940453 : Nat := 118140960795 + 1940453 * 2 ^ 59
def prefixEnd_1940453 : Nat := 4983230072969 + 3 ^ 40 * 1940453 * 2
def baseEnd_1940453 : Nat := 49204201306617368020421

theorem tailTrace_1940453 : CollatzResearch.WordTrace tailWord_1940453 prefixEnd_1940453 49204201306617368020421 := by
  unfold tailWord_1940453
  simp only [CollatzResearch.WordTrace]
  refine ⟨70774135239077658833170013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47182756826051772555446675 70774135239077658833170013)
  ·
    refine ⟨26540300714654122062438755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70774135239077658833170013 26540300714654122062438755)
    ·
      refine ⟨39810451071981183093658133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26540300714654122062438755 39810451071981183093658133)
      ·
        refine ⟨1866114893999117957515225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39810451071981183093658133 1866114893999117957515225)
        ·
          refine ⟨1399586170499338468136419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866114893999117957515225 1399586170499338468136419)
          ·
            refine ⟨2099379255749007702204629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399586170499338468136419 2099379255749007702204629)
            ·
              refine ⟨49204201306617368020421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2099379255749007702204629 49204201306617368020421)
              ·
                rfl

theorem cell21_1940453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 7].length) (baseStart_1940453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940453 prefixEnd_1940453 := by exact prefixLift 1940453
  have htrace : WordTrace (prefixWord ++ tailWord_1940453) baseStart_1940453 baseEnd_1940453 := by
    simpa [prefixWord, tailWord_1940453, baseEnd_1940453] using wordTrace_append hprefix tailTrace_1940453
  have hstable : (prefixWord ++ tailWord_1940453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940453).length < 2 ^ (prefixWord ++ tailWord_1940453).sum := by decide
  have hdescent : baseEnd_1940453 < baseStart_1940453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940464 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_1940464 : Nat := 118140960795 + 1940464 * 2 ^ 59
def prefixEnd_1940464 : Nat := 4983230072969 + 3 ^ 40 * 1940464 * 2
def baseEnd_1940464 : Nat := 442840322109422737500433

theorem tailTrace_1940464 : CollatzResearch.WordTrace tailWord_1940464 prefixEnd_1940464 442840322109422737500433 := by
  unfold tailWord_1940464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35387268221018903855910223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47183024294691871807880297 35387268221018903855910223)
  ·
    refine ⟨53080902331528355783865335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35387268221018903855910223 53080902331528355783865335)
    ·
      refine ⟨79621353497292533675798003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53080902331528355783865335 79621353497292533675798003)
      ·
        refine ⟨119432030245938800513697005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79621353497292533675798003 119432030245938800513697005)
        ·
          refine ⟨44787011342227050192636377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119432030245938800513697005 44787011342227050192636377)
          ·
            refine ⟨33590258506670287644477283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44787011342227050192636377 33590258506670287644477283)
            ·
              refine ⟨50385387760005431466715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33590258506670287644477283 50385387760005431466715925)
              ·
                refine ⟨2361815051250254600002309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50385387760005431466715925 2361815051250254600002309)
                ·
                  refine ⟨442840322109422737500433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361815051250254600002309 442840322109422737500433)
                  ·
                    rfl

theorem cell21_1940464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_1940464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940464 prefixEnd_1940464 := by exact prefixLift 1940464
  have htrace : WordTrace (prefixWord ++ tailWord_1940464) baseStart_1940464 baseEnd_1940464 := by
    simpa [prefixWord, tailWord_1940464, baseEnd_1940464] using wordTrace_append hprefix tailTrace_1940464
  have hstable : (prefixWord ++ tailWord_1940464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940464).length < 2 ^ (prefixWord ++ tailWord_1940464).sum := by decide
  have hdescent : baseEnd_1940464 < baseStart_1940464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940481 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 4]
def baseStart_1940481 : Nat := 118140960795 + 1940481 * 2 ^ 59
def prefixEnd_1940481 : Nat := 4983230072969 + 3 ^ 40 * 1940481 * 2
def baseEnd_1940481 : Nat := 442844201741034485717065

theorem tailTrace_1940481 : CollatzResearch.WordTrace tailWord_1940481 prefixEnd_1940481 442844201741034485717065 := by
  unfold tailWord_1940481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70775156482976219615189297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47183437655317479743459531 70775156482976219615189297)
  ·
    refine ⟨53081367362232164711391973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70775156482976219615189297 53081367362232164711391973)
    ·
      refine ⟨9952756380418530883385995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53081367362232164711391973 9952756380418530883385995)
      ·
        refine ⟨14929134570627796325078993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952756380418530883385995 14929134570627796325078993)
        ·
          refine ⟨11196850927970847243809245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14929134570627796325078993 11196850927970847243809245)
          ·
            refine ⟨4198819097989067716428467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11196850927970847243809245 4198819097989067716428467)
            ·
              refine ⟨6298228646983601574642701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198819097989067716428467 6298228646983601574642701)
              ·
                refine ⟨2361835742618850590491013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298228646983601574642701 2361835742618850590491013)
                ·
                  refine ⟨442844201741034485717065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361835742618850590491013 442844201741034485717065)
                  ·
                    rfl

theorem cell21_1940481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_1940481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940481 prefixEnd_1940481 := by exact prefixLift 1940481
  have htrace : WordTrace (prefixWord ++ tailWord_1940481) baseStart_1940481 baseEnd_1940481 := by
    simpa [prefixWord, tailWord_1940481, baseEnd_1940481] using wordTrace_append hprefix tailTrace_1940481
  have hstable : (prefixWord ++ tailWord_1940481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940481).length < 2 ^ (prefixWord ++ tailWord_1940481).sum := by decide
  have hdescent : baseEnd_1940481 < baseStart_1940481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940512 : List Nat := [2, 1, 1, 7, 2, 8]
def baseStart_1940512 : Nat := 118140960795 + 1940512 * 2 ^ 59
def prefixEnd_1940512 : Nat := 4983230072969 + 3 ^ 40 * 1940512 * 2
def baseEnd_1940512 : Nat := 16401899124569826692605

theorem tailTrace_1940512 : CollatzResearch.WordTrace tailWord_1940512 prefixEnd_1940512 16401899124569826692605 := by
  unfold tailWord_1940512
  simp only [CollatzResearch.WordTrace]
  refine ⟨35388143572931955954783895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47184191430575941273045193 35388143572931955954783895)
  ·
    refine ⟨53082215359397933932175843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35388143572931955954783895 53082215359397933932175843)
    ·
      refine ⟨79623323039096900898263765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53082215359397933932175843 79623323039096900898263765)
      ·
        refine ⟨1866171633728833614803057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79623323039096900898263765 1866171633728833614803057)
        ·
          refine ⟨1399628725296625211102293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866171633728833614803057 1399628725296625211102293)
          ·
            refine ⟨16401899124569826692605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1399628725296625211102293 16401899124569826692605)
            ·
              rfl

theorem cell21_1940512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 8].length) (baseStart_1940512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940512 prefixEnd_1940512 := by exact prefixLift 1940512
  have htrace : WordTrace (prefixWord ++ tailWord_1940512) baseStart_1940512 baseEnd_1940512 := by
    simpa [prefixWord, tailWord_1940512, baseEnd_1940512] using wordTrace_append hprefix tailTrace_1940512
  have hstable : (prefixWord ++ tailWord_1940512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940512).length < 2 ^ (prefixWord ++ tailWord_1940512).sum := by decide
  have hdescent : baseEnd_1940512 < baseStart_1940512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940526 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1940526 : Nat := 118140960795 + 1940526 * 2 ^ 59
def prefixEnd_1940526 : Nat := 4983230072969 + 3 ^ 40 * 1940526 * 2
def baseEnd_1940526 : Nat := 442854471354124407466973

theorem tailTrace_1940526 : CollatzResearch.WordTrace tailWord_1940526 prefixEnd_1940526 442854471354124407466973 := by
  unfold tailWord_1940526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847099720976649037572179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47184531845208794867051621 8847099720976649037572179)
  ·
    refine ⟨13270649581464973556358269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847099720976649037572179 13270649581464973556358269)
    ·
      refine ⟨4976493593049365083634351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13270649581464973556358269 4976493593049365083634351)
      ·
        refine ⟨7464740389574047625451527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976493593049365083634351 7464740389574047625451527)
        ·
          refine ⟨11197110584361071438177291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7464740389574047625451527 11197110584361071438177291)
          ·
            refine ⟨16795665876541607157265937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197110584361071438177291 16795665876541607157265937)
            ·
              refine ⟨12596749407406205367949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16795665876541607157265937 12596749407406205367949453)
              ·
                refine ⟨4723781027777327012981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12596749407406205367949453 4723781027777327012981045)
                ·
                  refine ⟨442854471354124407466973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723781027777327012981045 442854471354124407466973)
                  ·
                    rfl

theorem cell21_1940526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1940526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940526 prefixEnd_1940526 := by exact prefixLift 1940526
  have htrace : WordTrace (prefixWord ++ tailWord_1940526) baseStart_1940526 baseEnd_1940526 := by
    simpa [prefixWord, tailWord_1940526, baseEnd_1940526] using wordTrace_append hprefix tailTrace_1940526
  have hstable : (prefixWord ++ tailWord_1940526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940526).length < 2 ^ (prefixWord ++ tailWord_1940526).sum := by decide
  have hdescent : baseEnd_1940526 < baseStart_1940526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940554 : List Nat := [3, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1940554 : Nat := 118140960795 + 1940554 * 2 ^ 59
def prefixEnd_1940554 : Nat := 4983230072969 + 3 ^ 40 * 1940554 * 2
def baseEnd_1940554 : Nat := 147620287111867527000083

theorem tailTrace_1940554 : CollatzResearch.WordTrace tailWord_1940554 prefixEnd_1940554 147620287111867527000083 := by
  unfold tailWord_1940554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694454752927938270649179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47185212674474502055064477 17694454752927938270649179)
  ·
    refine ⟨26541682129391907405973769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694454752927938270649179 26541682129391907405973769)
    ·
      refine ⟨19906261597043930554480327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26541682129391907405973769 19906261597043930554480327)
      ·
        refine ⟨29859392395565895831720491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19906261597043930554480327 29859392395565895831720491)
        ·
          refine ⟨44789088593348843747580737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29859392395565895831720491 44789088593348843747580737)
          ·
            refine ⟨33591816445011632810685553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44789088593348843747580737 33591816445011632810685553)
            ·
              refine ⟨25193862333758724608014165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33591816445011632810685553 25193862333758724608014165)
              ·
                refine ⟨147620287111867527000083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25193862333758724608014165 147620287111867527000083)
                ·
                  rfl

theorem cell21_1940554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1940554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940554 prefixEnd_1940554 := by exact prefixLift 1940554
  have htrace : WordTrace (prefixWord ++ tailWord_1940554) baseStart_1940554 baseEnd_1940554 := by
    simpa [prefixWord, tailWord_1940554, baseEnd_1940554] using wordTrace_append hprefix tailTrace_1940554
  have hstable : (prefixWord ++ tailWord_1940554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940554).length < 2 ^ (prefixWord ++ tailWord_1940554).sum := by decide
  have hdescent : baseEnd_1940554 < baseStart_1940554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940585 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_1940585 : Nat := 118140960795 + 1940585 * 2 ^ 59
def prefixEnd_1940585 : Nat := 4983230072969 + 3 ^ 40 * 1940585 * 2
def baseEnd_1940585 : Nat := 442867935957953415983519

theorem tailTrace_1940585 : CollatzResearch.WordTrace tailWord_1940585 prefixEnd_1940585 442867935957953415983519 := by
  unfold tailWord_1940585
  simp only [CollatzResearch.WordTrace]
  refine ⟨70778949674599445376975209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47185966449732963584650139 70778949674599445376975209)
  ·
    refine ⟨53084212255949584032731407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70778949674599445376975209 53084212255949584032731407)
    ·
      refine ⟨79626318383924376049097111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53084212255949584032731407 79626318383924376049097111)
      ·
        refine ⟨119439477575886564073645667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79626318383924376049097111 119439477575886564073645667)
        ·
          refine ⟨179159216363829846110468501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119439477575886564073645667 179159216363829846110468501)
          ·
            refine ⟨8398088267054524036428211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179159216363829846110468501 8398088267054524036428211)
            ·
              refine ⟨12597132400581786054642317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398088267054524036428211 12597132400581786054642317)
              ·
                refine ⟨4723924650218169770490869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12597132400581786054642317 4723924650218169770490869)
                ·
                  refine ⟨442867935957953415983519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723924650218169770490869 442867935957953415983519)
                  ·
                    rfl

theorem cell21_1940585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_1940585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940585 prefixEnd_1940585 := by exact prefixLift 1940585
  have htrace : WordTrace (prefixWord ++ tailWord_1940585) baseStart_1940585 baseEnd_1940585 := by
    simpa [prefixWord, tailWord_1940585, baseEnd_1940585] using wordTrace_append hprefix tailTrace_1940585
  have hstable : (prefixWord ++ tailWord_1940585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940585).length < 2 ^ (prefixWord ++ tailWord_1940585).sum := by decide
  have hdescent : baseEnd_1940585 < baseStart_1940585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940636 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_1940636 : Nat := 118140960795 + 1940636 * 2 ^ 59
def prefixEnd_1940636 : Nat := 4983230072969 + 3 ^ 40 * 1940636 * 2
def baseEnd_1940636 : Nat := 442879574852788660633415

theorem tailTrace_1940636 : CollatzResearch.WordTrace tailWord_1940636 prefixEnd_1940636 442879574852788660633415 := by
  unfold tailWord_1940636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390404898707340543540881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47187206531609787391387841 35390404898707340543540881)
  ·
    refine ⟨26542803674030505407655661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35390404898707340543540881 26542803674030505407655661)
    ·
      refine ⟨9953551377761439527870873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26542803674030505407655661 9953551377761439527870873)
      ·
        refine ⟨7465163533321079645903155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9953551377761439527870873 7465163533321079645903155)
        ·
          refine ⟨11197745299981619468854733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465163533321079645903155 11197745299981619468854733)
          ·
            refine ⟨4199154487493107300820525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11197745299981619468854733 4199154487493107300820525)
            ·
              refine ⟨1574682932809915237807697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4199154487493107300820525 1574682932809915237807697)
              ·
                refine ⟨1181012199607436428355773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574682932809915237807697 1181012199607436428355773)
                ·
                  refine ⟨442879574852788660633415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181012199607436428355773 442879574852788660633415)
                  ·
                    rfl

theorem cell21_1940636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_1940636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940636 prefixEnd_1940636 := by exact prefixLift 1940636
  have htrace : WordTrace (prefixWord ++ tailWord_1940636) baseStart_1940636 baseEnd_1940636 := by
    simpa [prefixWord, tailWord_1940636, baseEnd_1940636] using wordTrace_append hprefix tailTrace_1940636
  have hstable : (prefixWord ++ tailWord_1940636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940636).length < 2 ^ (prefixWord ++ tailWord_1940636).sum := by decide
  have hdescent : baseEnd_1940636 < baseStart_1940636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940647 : List Nat := [1, 1, 6, 2, 1, 1, 1, 8]
def baseStart_1940647 : Nat := 118140960795 + 1940647 * 2 ^ 59
def prefixEnd_1940647 : Nat := 4983230072969 + 3 ^ 40 * 1940647 * 2
def baseEnd_1940647 : Nat := 147627361734218361983353

theorem tailTrace_1940647 : CollatzResearch.WordTrace tailWord_1940647 prefixEnd_1940647 147627361734218361983353 := by
  unfold tailWord_1940647
  simp only [CollatzResearch.WordTrace]
  refine ⟨70781211000374829965732195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47187474000249886643821463 70781211000374829965732195)
  ·
    refine ⟨106171816500562244948598293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70781211000374829965732195 106171816500562244948598293)
    ·
      refine ⟨4976803898463855231965545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106171816500562244948598293 4976803898463855231965545)
      ·
        refine ⟨3732602923847891423974159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4976803898463855231965545 3732602923847891423974159)
        ·
          refine ⟨5598904385771837135961239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732602923847891423974159 5598904385771837135961239)
          ·
            refine ⟨8398356578657755703941859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598904385771837135961239 8398356578657755703941859)
            ·
              refine ⟨12597534867986633555912789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398356578657755703941859 12597534867986633555912789)
              ·
                refine ⟨147627361734218361983353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12597534867986633555912789 147627361734218361983353)
                ·
                  rfl

theorem cell21_1940647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_1940647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940647 prefixEnd_1940647 := by exact prefixLift 1940647
  have htrace : WordTrace (prefixWord ++ tailWord_1940647) baseStart_1940647 baseEnd_1940647 := by
    simpa [prefixWord, tailWord_1940647, baseEnd_1940647] using wordTrace_append hprefix tailTrace_1940647
  have hstable : (prefixWord ++ tailWord_1940647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940647).length < 2 ^ (prefixWord ++ tailWord_1940647).sum := by decide
  have hdescent : baseEnd_1940647 < baseStart_1940647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940650 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_1940650 : Nat := 118140960795 + 1940650 * 2 ^ 59
def prefixEnd_1940650 : Nat := 4983230072969 + 3 ^ 40 * 1940650 * 2
def baseEnd_1940650 : Nat := 442882769843527747400053

theorem tailTrace_1940650 : CollatzResearch.WordTrace tailWord_1940650 prefixEnd_1940650 442882769843527747400053 := by
  unfold tailWord_1940650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695330104840990369522851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47187546946242640985394269 17695330104840990369522851)
  ·
    refine ⟨26542995157261485554284277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695330104840990369522851 26542995157261485554284277)
    ·
      refine ⟨2488405795993264270714151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26542995157261485554284277 2488405795993264270714151)
      ·
        refine ⟨3732608693989896406071227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488405795993264270714151 3732608693989896406071227)
        ·
          refine ⟨5598913040984844609106841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732608693989896406071227 5598913040984844609106841)
          ·
            refine ⟨4199184780738633456830131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598913040984844609106841 4199184780738633456830131)
            ·
              refine ⟨6298777171107950185245197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199184780738633456830131 6298777171107950185245197)
              ·
                refine ⟨2362041439165481319466949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298777171107950185245197 2362041439165481319466949)
                ·
                  refine ⟨442882769843527747400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362041439165481319466949 442882769843527747400053)
                  ·
                    rfl

theorem cell21_1940650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_1940650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940650 prefixEnd_1940650 := by exact prefixLift 1940650
  have htrace : WordTrace (prefixWord ++ tailWord_1940650) baseStart_1940650 baseEnd_1940650 := by
    simpa [prefixWord, tailWord_1940650, baseEnd_1940650] using wordTrace_append hprefix tailTrace_1940650
  have hstable : (prefixWord ++ tailWord_1940650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940650).length < 2 ^ (prefixWord ++ tailWord_1940650).sum := by decide
  have hdescent : baseEnd_1940650 < baseStart_1940650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940675 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_1940675 : Nat := 118140960795 + 1940675 * 2 ^ 59
def prefixEnd_1940675 : Nat := 4983230072969 + 3 ^ 40 * 1940675 * 2
def baseEnd_1940675 : Nat := 442888475184133259483335

theorem tailTrace_1940675 : CollatzResearch.WordTrace tailWord_1940675 prefixEnd_1940675 442888475184133259483335 := by
  unfold tailWord_1940675
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782232244273390747751479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47188154829515593831834319 70782232244273390747751479)
  ·
    refine ⟨106173348366410086121627219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70782232244273390747751479 106173348366410086121627219)
    ·
      refine ⟨159260022549615129182440829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106173348366410086121627219 159260022549615129182440829)
      ·
        refine ⟨59722508456105673443415311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159260022549615129182440829 59722508456105673443415311)
        ·
          refine ⟨89583762684158510165122967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59722508456105673443415311 89583762684158510165122967)
          ·
            refine ⟨134375644026237765247684451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89583762684158510165122967 134375644026237765247684451)
            ·
              refine ⟨201563466039356647871526677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134375644026237765247684451 201563466039356647871526677)
              ·
                refine ⟨9448287470594842868977813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201563466039356647871526677 9448287470594842868977813)
                ·
                  refine ⟨442888475184133259483335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448287470594842868977813 442888475184133259483335)
                  ·
                    rfl

theorem cell21_1940675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_1940675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940675 prefixEnd_1940675 := by exact prefixLift 1940675
  have htrace : WordTrace (prefixWord ++ tailWord_1940675) baseStart_1940675 baseEnd_1940675 := by
    simpa [prefixWord, tailWord_1940675, baseEnd_1940675] using wordTrace_append hprefix tailTrace_1940675
  have hstable : (prefixWord ++ tailWord_1940675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940675).length < 2 ^ (prefixWord ++ tailWord_1940675).sum := by decide
  have hdescent : baseEnd_1940675 < baseStart_1940675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940695 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 3]
def baseStart_1940695 : Nat := 118140960795 + 1940695 * 2 ^ 59
def prefixEnd_1940695 : Nat := 4983230072969 + 3 ^ 40 * 1940695 * 2
def baseEnd_1940695 : Nat := 442893039456617669149961

theorem tailTrace_1940695 : CollatzResearch.WordTrace tailWord_1940695 prefixEnd_1940695 442893039456617669149961 := by
  unfold tailWord_1940695
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782961704200934163479539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47188641136133956108986359 70782961704200934163479539)
  ·
    refine ⟨106174442556301401245219309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70782961704200934163479539 106174442556301401245219309)
    ·
      refine ⟨39815415958613025466957241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106174442556301401245219309 39815415958613025466957241)
      ·
        refine ⟨29861561968959769100217931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39815415958613025466957241 29861561968959769100217931)
        ·
          refine ⟨44792342953439653650326897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29861561968959769100217931 44792342953439653650326897)
          ·
            refine ⟨33594257215079740237745173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44792342953439653650326897 33594257215079740237745173)
            ·
              refine ⟨1574730806956862823644305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33594257215079740237745173 1574730806956862823644305)
              ·
                refine ⟨1181048105217647117733229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574730806956862823644305 1181048105217647117733229)
                ·
                  refine ⟨442893039456617669149961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181048105217647117733229 442893039456617669149961)
                  ·
                    rfl

theorem cell21_1940695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].length) (baseStart_1940695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940695 prefixEnd_1940695 := by exact prefixLift 1940695
  have htrace : WordTrace (prefixWord ++ tailWord_1940695) baseStart_1940695 baseEnd_1940695 := by
    simpa [prefixWord, tailWord_1940695, baseEnd_1940695] using wordTrace_append hprefix tailTrace_1940695
  have hstable : (prefixWord ++ tailWord_1940695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940695).length < 2 ^ (prefixWord ++ tailWord_1940695).sum := by decide
  have hdescent : baseEnd_1940695 < baseStart_1940695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940723 : List Nat := [1, 1, 1, 2, 2, 6, 3, 5]
def baseStart_1940723 : Nat := 118140960795 + 1940723 * 2 ^ 59
def prefixEnd_1940723 : Nat := 4983230072969 + 3 ^ 40 * 1940723 * 2
def baseEnd_1940723 : Nat := 147633143146031947561079

theorem tailTrace_1940723 : CollatzResearch.WordTrace tailWord_1940723 prefixEnd_1940723 147633143146031947561079 := by
  unfold tailWord_1940723
  simp only [CollatzResearch.WordTrace]
  refine ⟨70783982948099494945498823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47189321965399663296999215 70783982948099494945498823)
  ·
    refine ⟨106175974422149242418248235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70783982948099494945498823 106175974422149242418248235)
    ·
      refine ⟨159263961633223863627372353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106175974422149242418248235 159263961633223863627372353)
      ·
        refine ⟨119447971224917897720529265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159263961633223863627372353 119447971224917897720529265)
        ·
          refine ⟨89585978418688423290396949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119447971224917897720529265 89585978418688423290396949)
          ·
            refine ⟨4199342738376019841737357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89585978418688423290396949 4199342738376019841737357)
            ·
              refine ⟨1574753526891007440651509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4199342738376019841737357 1574753526891007440651509)
              ·
                refine ⟨147633143146031947561079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574753526891007440651509 147633143146031947561079)
                ·
                  rfl

theorem cell21_1940723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].length) (baseStart_1940723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940723 prefixEnd_1940723 := by exact prefixLift 1940723
  have htrace : WordTrace (prefixWord ++ tailWord_1940723) baseStart_1940723 baseEnd_1940723 := by
    simpa [prefixWord, tailWord_1940723, baseEnd_1940723] using wordTrace_append hprefix tailTrace_1940723
  have hstable : (prefixWord ++ tailWord_1940723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940723).length < 2 ^ (prefixWord ++ tailWord_1940723).sum := by decide
  have hdescent : baseEnd_1940723 < baseStart_1940723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940889 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 5]
def baseStart_1940889 : Nat := 118140960795 + 1940889 * 2 ^ 59
def prefixEnd_1940889 : Nat := 4983230072969 + 3 ^ 40 * 1940889 * 2
def baseEnd_1940889 : Nat := 442937312899716442916231

theorem tailTrace_1940889 : CollatzResearch.WordTrace tailWord_1940889 prefixEnd_1940889 442937312899716442916231 := by
  unfold tailWord_1940889
  simp only [CollatzResearch.WordTrace]
  refine ⟨70790037465498105296041721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47193358310332070197361147 70790037465498105296041721)
  ·
    refine ⟨53092528099123578972031291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70790037465498105296041721 53092528099123578972031291)
    ·
      refine ⟨79638792148685368458046937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53092528099123578972031291 79638792148685368458046937)
      ·
        refine ⟨59729094111514026343535203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79638792148685368458046937 59729094111514026343535203)
        ·
          refine ⟨89593641167271039515302805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59729094111514026343535203 89593641167271039515302805)
          ·
            refine ⟨4199701929715829977279819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89593641167271039515302805 4199701929715829977279819)
            ·
              refine ⟨6299552894573744965919729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199701929715829977279819 6299552894573744965919729)
              ·
                refine ⟨4724664670930308724439797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299552894573744965919729 4724664670930308724439797)
                ·
                  refine ⟨442937312899716442916231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724664670930308724439797 442937312899716442916231)
                  ·
                    rfl

theorem cell21_1940889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_1940889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940889 prefixEnd_1940889 := by exact prefixLift 1940889
  have htrace : WordTrace (prefixWord ++ tailWord_1940889) baseStart_1940889 baseEnd_1940889 := by
    simpa [prefixWord, tailWord_1940889, baseEnd_1940889] using wordTrace_append hprefix tailTrace_1940889
  have hstable : (prefixWord ++ tailWord_1940889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940889).length < 2 ^ (prefixWord ++ tailWord_1940889).sum := by decide
  have hdescent : baseEnd_1940889 < baseStart_1940889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940920 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_1940920 : Nat := 118140960795 + 1940920 * 2 ^ 59
def prefixEnd_1940920 : Nat := 4983230072969 + 3 ^ 40 * 1940920 * 2
def baseEnd_1940920 : Nat := 442944387522067277899501

theorem tailTrace_1940920 : CollatzResearch.WordTrace tailWord_1940920 prefixEnd_1940920 442944387522067277899501 := by
  unfold tailWord_1940920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35395584064192898795210107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47194112085590531726946809 35395584064192898795210107)
  ·
    refine ⟨53093376096289348192815161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35395584064192898795210107 53093376096289348192815161)
    ·
      refine ⟨39820032072217011144611371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53093376096289348192815161 39820032072217011144611371)
      ·
        refine ⟨59730048108325516716917057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39820032072217011144611371 59730048108325516716917057)
        ·
          refine ⟨44797536081244137537687793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59730048108325516716917057 44797536081244137537687793)
          ·
            refine ⟨33598152060933103153265845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44797536081244137537687793 33598152060933103153265845)
            ·
              refine ⟨3149826755712478420618673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33598152060933103153265845 3149826755712478420618673)
              ·
                refine ⟨2362370066784358815464005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149826755712478420618673 2362370066784358815464005)
                ·
                  refine ⟨442944387522067277899501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362370066784358815464005 442944387522067277899501)
                  ·
                    rfl

theorem cell21_1940920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_1940920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940920 prefixEnd_1940920 := by exact prefixLift 1940920
  have htrace : WordTrace (prefixWord ++ tailWord_1940920) baseStart_1940920 baseEnd_1940920 := by
    simpa [prefixWord, tailWord_1940920, baseEnd_1940920] using wordTrace_append hprefix tailTrace_1940920
  have hstable : (prefixWord ++ tailWord_1940920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940920).length < 2 ^ (prefixWord ++ tailWord_1940920).sum := by decide
  have hdescent : baseEnd_1940920 < baseStart_1940920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940982 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1940982 : Nat := 118140960795 + 1940982 * 2 ^ 59
def prefixEnd_1940982 : Nat := 4983230072969 + 3 ^ 40 * 1940982 * 2
def baseEnd_1940982 : Nat := 442958536766768947866041

theorem tailTrace_1940982 : CollatzResearch.WordTrace tailWord_1940982 prefixEnd_1940982 442958536766768947866041 := by
  unfold tailWord_1940982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424589340885073886198575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47195619636107454786118133 4424589340885073886198575)
  ·
    refine ⟨6636884011327610829297863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424589340885073886198575 6636884011327610829297863)
    ·
      refine ⟨9955326016991416243946795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636884011327610829297863 9955326016991416243946795)
      ·
        refine ⟨14932989025487124365920193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955326016991416243946795 14932989025487124365920193)
        ·
          refine ⟨11199741769115343274440145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932989025487124365920193 11199741769115343274440145)
          ·
            refine ⟨8399806326836507455830109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199741769115343274440145 8399806326836507455830109)
            ·
              refine ⟨3149927372563690295936291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399806326836507455830109 3149927372563690295936291)
              ·
                refine ⟨4724891058845535443904437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149927372563690295936291 4724891058845535443904437)
                ·
                  refine ⟨442958536766768947866041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724891058845535443904437 442958536766768947866041)
                  ·
                    rfl

theorem cell21_1940982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1940982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1940982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1940982 prefixEnd_1940982 := by exact prefixLift 1940982
  have htrace : WordTrace (prefixWord ++ tailWord_1940982) baseStart_1940982 baseEnd_1940982 := by
    simpa [prefixWord, tailWord_1940982, baseEnd_1940982] using wordTrace_append hprefix tailTrace_1940982
  have hstable : (prefixWord ++ tailWord_1940982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940982).length < 2 ^ (prefixWord ++ tailWord_1940982).sum := by decide
  have hdescent : baseEnd_1940982 < baseStart_1940982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941117 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1941117 : Nat := 118140960795 + 1941117 * 2 ^ 59
def prefixEnd_1941117 : Nat := 4983230072969 + 3 ^ 40 * 1941117 * 2
def baseEnd_1941117 : Nat := 442989345606038713115765

theorem tailTrace_1941117 : CollatzResearch.WordTrace tailWord_1941117 prefixEnd_1941117 442989345606038713115765 := by
  unfold tailWord_1941117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70798353308672100235341605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47198902205781400156894403 70798353308672100235341605)
  ·
    refine ⟨13274691245376018794126551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70798353308672100235341605 13274691245376018794126551)
    ·
      refine ⟨19912036868064028191189827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274691245376018794126551 19912036868064028191189827)
      ·
        refine ⟨29868055302096042286784741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19912036868064028191189827 29868055302096042286784741)
        ·
          refine ⟨5600260369143007928772139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29868055302096042286784741 5600260369143007928772139)
          ·
            refine ⟨8400390553714511893158209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600260369143007928772139 8400390553714511893158209)
            ·
              refine ⟨6300292915285883919868657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400390553714511893158209 6300292915285883919868657)
              ·
                refine ⟨4725219686464412939901493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300292915285883919868657 4725219686464412939901493)
                ·
                  refine ⟨442989345606038713115765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725219686464412939901493 442989345606038713115765)
                  ·
                    rfl

theorem cell21_1941117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1941117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941117 prefixEnd_1941117 := by exact prefixLift 1941117
  have htrace : WordTrace (prefixWord ++ tailWord_1941117) baseStart_1941117 baseEnd_1941117 := by
    simpa [prefixWord, tailWord_1941117, baseEnd_1941117] using wordTrace_append hprefix tailTrace_1941117
  have hstable : (prefixWord ++ tailWord_1941117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941117).length < 2 ^ (prefixWord ++ tailWord_1941117).sum := by decide
  have hdescent : baseEnd_1941117 < baseStart_1941117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941151 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_1941151 : Nat := 118140960795 + 1941151 * 2 ^ 59
def prefixEnd_1941151 : Nat := 4983230072969 + 3 ^ 40 * 1941151 * 2
def baseEnd_1941151 : Nat := 442997104869262209549029

theorem tailTrace_1941151 : CollatzResearch.WordTrace tailWord_1941151 prefixEnd_1941151 442997104869262209549029 := by
  unfold tailWord_1941151
  simp only [CollatzResearch.WordTrace]
  refine ⟨70799593390548924042079307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47199728927032616028052871 70799593390548924042079307)
  ·
    refine ⟨106199390085823386063118961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70799593390548924042079307 106199390085823386063118961)
    ·
      refine ⟨79649542564367539547339221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106199390085823386063118961 79649542564367539547339221)
      ·
        refine ⟨1866786153852364208140763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79649542564367539547339221 1866786153852364208140763)
        ·
          refine ⟨2800179230778546312211145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866786153852364208140763 2800179230778546312211145)
          ·
            refine ⟨2100134423083909734158359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800179230778546312211145 2100134423083909734158359)
            ·
              refine ⟨3150201634625864601237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100134423083909734158359 3150201634625864601237539)
              ·
                refine ⟨4725302451938796901856309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150201634625864601237539 4725302451938796901856309)
                ·
                  refine ⟨442997104869262209549029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725302451938796901856309 442997104869262209549029)
                  ·
                    rfl

theorem cell21_1941151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_1941151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941151 prefixEnd_1941151 := by exact prefixLift 1941151
  have htrace : WordTrace (prefixWord ++ tailWord_1941151) baseStart_1941151 baseEnd_1941151 := by
    simpa [prefixWord, tailWord_1941151, baseEnd_1941151] using wordTrace_append hprefix tailTrace_1941151
  have hstable : (prefixWord ++ tailWord_1941151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941151).length < 2 ^ (prefixWord ++ tailWord_1941151).sum := by decide
  have hdescent : baseEnd_1941151 < baseStart_1941151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941176 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1941176 : Nat := 118140960795 + 1941176 * 2 ^ 59
def prefixEnd_1941176 : Nat := 4983230072969 + 3 ^ 40 * 1941176 * 2
def baseEnd_1941176 : Nat := 443002810209867721632311

theorem tailTrace_1941176 : CollatzResearch.WordTrace tailWord_1941176 prefixEnd_1941176 443002810209867721632311 := by
  unfold tailWord_1941176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400252607729176655869691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47200336810305568874492921 35400252607729176655869691)
  ·
    refine ⟨53100378911593764983804537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35400252607729176655869691 53100378911593764983804537)
    ·
      refine ⟨39825284183695323737853403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53100378911593764983804537 39825284183695323737853403)
      ·
        refine ⟨59737926275542985606780105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39825284183695323737853403 59737926275542985606780105)
        ·
          refine ⟨44803444706657239205085079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59737926275542985606780105 44803444706657239205085079)
          ·
            refine ⟨67205167059985858807627619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44803444706657239205085079 67205167059985858807627619)
            ·
              refine ⟨100807750589978788211441429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67205167059985858807627619 100807750589978788211441429)
              ·
                refine ⟨4725363308905255697411317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100807750589978788211441429 4725363308905255697411317)
                ·
                  refine ⟨443002810209867721632311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725363308905255697411317 443002810209867721632311)
                  ·
                    rfl

theorem cell21_1941176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1941176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941176 prefixEnd_1941176 := by exact prefixLift 1941176
  have htrace : WordTrace (prefixWord ++ tailWord_1941176) baseStart_1941176 baseEnd_1941176 := by
    simpa [prefixWord, tailWord_1941176, baseEnd_1941176] using wordTrace_append hprefix tailTrace_1941176
  have hstable : (prefixWord ++ tailWord_1941176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941176).length < 2 ^ (prefixWord ++ tailWord_1941176).sum := by decide
  have hdescent : baseEnd_1941176 < baseStart_1941176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941210 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_1941210 : Nat := 118140960795 + 1941210 * 2 ^ 59
def prefixEnd_1941210 : Nat := 4983230072969 + 3 ^ 40 * 1941210 * 2
def baseEnd_1941210 : Nat := 443010569473091218065575

theorem tailTrace_1941210 : CollatzResearch.WordTrace tailWord_1941210 prefixEnd_1941210 443010569473091218065575 := by
  unfold tailWord_1941210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700436324333794279619271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47201163531556784745651389 17700436324333794279619271)
  ·
    refine ⟨26550654486500691419428907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17700436324333794279619271 26550654486500691419428907)
    ·
      refine ⟨39825981729751037129143361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26550654486500691419428907 39825981729751037129143361)
      ·
        refine ⟨29869486297313277846857521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39825981729751037129143361 29869486297313277846857521)
        ·
          refine ⟨22402114722984958385143141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29869486297313277846857521 22402114722984958385143141)
          ·
            refine ⟨4200396510559679697214339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22402114722984958385143141 4200396510559679697214339)
            ·
              refine ⟨6300594765839519545821509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200396510559679697214339 6300594765839519545821509)
              ·
                refine ⟨1181361518594909914841533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6300594765839519545821509 1181361518594909914841533)
                ·
                  refine ⟨443010569473091218065575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181361518594909914841533 443010569473091218065575)
                  ·
                    rfl

theorem cell21_1941210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_1941210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941210 prefixEnd_1941210 := by exact prefixLift 1941210
  have htrace : WordTrace (prefixWord ++ tailWord_1941210) baseStart_1941210 baseEnd_1941210 := by
    simpa [prefixWord, tailWord_1941210, baseEnd_1941210] using wordTrace_append hprefix tailTrace_1941210
  have hstable : (prefixWord ++ tailWord_1941210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941210).length < 2 ^ (prefixWord ++ tailWord_1941210).sum := by decide
  have hdescent : baseEnd_1941210 < baseStart_1941210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941213 : List Nat := [1, 4, 3, 3, 2, 1, 1, 6]
def baseStart_1941213 : Nat := 118140960795 + 1941213 * 2 ^ 59
def prefixEnd_1941213 : Nat := 4983230072969 + 3 ^ 40 * 1941213 * 2
def baseEnd_1941213 : Nat := 147670418037987959838523

theorem tailTrace_1941213 : CollatzResearch.WordTrace tailWord_1941213 prefixEnd_1941213 147670418037987959838523 := by
  unfold tailWord_1941213
  simp only [CollatzResearch.WordTrace]
  refine ⟨70801854716324308630836293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47201236477549539087224195 70801854716324308630836293)
  ·
    refine ⟨13275347759310807868281805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70801854716324308630836293 13275347759310807868281805)
    ·
      refine ⟨4978255409741552950605677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13275347759310807868281805 4978255409741552950605677)
      ·
        refine ⟨1866845778653082356477129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4978255409741552950605677 1866845778653082356477129)
        ·
          refine ⟨1400134333989811767357847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866845778653082356477129 1400134333989811767357847)
          ·
            refine ⟨2100201500984717651036771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400134333989811767357847 2100201500984717651036771)
            ·
              refine ⟨3150302251477076476555157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100201500984717651036771 3150302251477076476555157)
              ·
                refine ⟨147670418037987959838523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3150302251477076476555157 147670418037987959838523)
                ·
                  rfl

theorem cell21_1941213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 6].length) (baseStart_1941213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941213 prefixEnd_1941213 := by exact prefixLift 1941213
  have htrace : WordTrace (prefixWord ++ tailWord_1941213) baseStart_1941213 baseEnd_1941213 := by
    simpa [prefixWord, tailWord_1941213, baseEnd_1941213] using wordTrace_append hprefix tailTrace_1941213
  have hstable : (prefixWord ++ tailWord_1941213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941213).length < 2 ^ (prefixWord ++ tailWord_1941213).sum := by decide
  have hdescent : baseEnd_1941213 < baseStart_1941213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941224 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_1941224 : Nat := 118140960795 + 1941224 * 2 ^ 59
def prefixEnd_1941224 : Nat := 4983230072969 + 3 ^ 40 * 1941224 * 2
def baseEnd_1941224 : Nat := 443013764463830304832213

theorem tailTrace_1941224 : CollatzResearch.WordTrace tailWord_1941224 prefixEnd_1941224 443013764463830304832213 := by
  unfold tailWord_1941224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35401127959642228754743363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47201503946189638339657817 35401127959642228754743363)
  ·
    refine ⟨53101691939463343132115045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35401127959642228754743363 53101691939463343132115045)
    ·
      refine ⟨9956567238649376837271571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53101691939463343132115045 9956567238649376837271571)
      ·
        refine ⟨14934850857974065255907357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956567238649376837271571 14934850857974065255907357)
        ·
          refine ⟨5600569071740274470965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14934850857974065255907357 5600569071740274470965259)
          ·
            refine ⟨8400853607610411706447889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600569071740274470965259 8400853607610411706447889)
            ·
              refine ⟨6300640205707808779835917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400853607610411706447889 6300640205707808779835917)
              ·
                refine ⟨2362740077140428292438469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6300640205707808779835917 2362740077140428292438469)
                ·
                  refine ⟨443013764463830304832213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362740077140428292438469 443013764463830304832213)
                  ·
                    rfl

theorem cell21_1941224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_1941224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941224 prefixEnd_1941224 := by exact prefixLift 1941224
  have htrace : WordTrace (prefixWord ++ tailWord_1941224) baseStart_1941224 baseEnd_1941224 := by
    simpa [prefixWord, tailWord_1941224, baseEnd_1941224] using wordTrace_append hprefix tailTrace_1941224
  have hstable : (prefixWord ++ tailWord_1941224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941224).length < 2 ^ (prefixWord ++ tailWord_1941224).sum := by decide
  have hdescent : baseEnd_1941224 < baseStart_1941224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941261 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1941261 : Nat := 118140960795 + 1941261 * 2 ^ 59
def prefixEnd_1941261 : Nat := 4983230072969 + 3 ^ 40 * 1941261 * 2
def baseEnd_1941261 : Nat := 443022208367926462715471

theorem tailTrace_1941261 : CollatzResearch.WordTrace tailWord_1941261 prefixEnd_1941261 443022208367926462715471 := by
  unfold tailWord_1941261
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803605420150412828583637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47202403613433608552389091 70803605420150412828583637)
  ·
    refine ⟨1659459502034775300669929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70803605420150412828583637 1659459502034775300669929)
    ·
      refine ⟨1244594626526081475502447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1659459502034775300669929 1244594626526081475502447)
      ·
        refine ⟨1866891939789122213253671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244594626526081475502447 1866891939789122213253671)
        ·
          refine ⟨2800337909683683319880507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866891939789122213253671 2800337909683683319880507)
          ·
            refine ⟨4200506864525524979820761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800337909683683319880507 4200506864525524979820761)
            ·
              refine ⟨3150380148394143734865571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200506864525524979820761 3150380148394143734865571)
              ·
                refine ⟨4725570222591215602298357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150380148394143734865571 4725570222591215602298357)
                ·
                  refine ⟨443022208367926462715471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725570222591215602298357 443022208367926462715471)
                  ·
                    rfl

theorem cell21_1941261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1941261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941261 prefixEnd_1941261 := by exact prefixLift 1941261
  have htrace : WordTrace (prefixWord ++ tailWord_1941261) baseStart_1941261 baseEnd_1941261 := by
    simpa [prefixWord, tailWord_1941261, baseEnd_1941261] using wordTrace_append hprefix tailTrace_1941261
  have hstable : (prefixWord ++ tailWord_1941261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941261).length < 2 ^ (prefixWord ++ tailWord_1941261).sum := by decide
  have hdescent : baseEnd_1941261 < baseStart_1941261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941269 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1941269 : Nat := 118140960795 + 1941269 * 2 ^ 59
def prefixEnd_1941269 : Nat := 4983230072969 + 3 ^ 40 * 1941269 * 2
def baseEnd_1941269 : Nat := 443024034076920226582121

theorem tailTrace_1941269 : CollatzResearch.WordTrace tailWord_1941269 prefixEnd_1941269 443024034076920226582121 := by
  unfold tailWord_1941269
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803897204121430194874861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47202598136080953463249907 70803897204121430194874861)
  ·
    refine ⟨26551461451545536323078073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70803897204121430194874861 26551461451545536323078073)
    ·
      refine ⟨19913596088659152242308555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26551461451545536323078073 19913596088659152242308555)
      ·
        refine ⟨29870394132988728363462833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19913596088659152242308555 29870394132988728363462833)
        ·
          refine ⟨22402795599741546272597125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29870394132988728363462833 22402795599741546272597125)
          ·
            refine ⟨4200524174951539926111961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22402795599741546272597125 4200524174951539926111961)
            ·
              refine ⟨3150393131213654944583971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200524174951539926111961 3150393131213654944583971)
              ·
                refine ⟨4725589696820482416875957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150393131213654944583971 4725589696820482416875957)
                ·
                  refine ⟨443024034076920226582121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725589696820482416875957 443024034076920226582121)
                  ·
                    rfl

theorem cell21_1941269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1941269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941269 prefixEnd_1941269 := by exact prefixLift 1941269
  have htrace : WordTrace (prefixWord ++ tailWord_1941269) baseStart_1941269 baseEnd_1941269 := by
    simpa [prefixWord, tailWord_1941269, baseEnd_1941269] using wordTrace_append hprefix tailTrace_1941269
  have hstable : (prefixWord ++ tailWord_1941269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941269).length < 2 ^ (prefixWord ++ tailWord_1941269).sum := by decide
  have hdescent : baseEnd_1941269 < baseStart_1941269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941283 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_1941283 : Nat := 118140960795 + 1941283 * 2 ^ 59
def prefixEnd_1941283 : Nat := 4983230072969 + 3 ^ 40 * 1941283 * 2
def baseEnd_1941283 : Nat := 443027229067659313348759

theorem tailTrace_1941283 : CollatzResearch.WordTrace tailWord_1941283 prefixEnd_1941283 443027229067659313348759 := by
  unfold tailWord_1941283
  simp only [CollatzResearch.WordTrace]
  refine ⟨70804407826070710585884503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47202938550713807057256335 70804407826070710585884503)
  ·
    refine ⟨106206611739106065878826755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70804407826070710585884503 106206611739106065878826755)
    ·
      refine ⟨159309917608659098818240133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106206611739106065878826755 159309917608659098818240133)
      ·
        refine ⟨29870609551623581028420025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159309917608659098818240133 29870609551623581028420025)
        ·
          refine ⟨22402957163717685771315019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29870609551623581028420025 22402957163717685771315019)
          ·
            refine ⟨33604435745576528656972529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402957163717685771315019 33604435745576528656972529)
            ·
              refine ⟨25203326809182396492729397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33604435745576528656972529 25203326809182396492729397)
              ·
                refine ⟨2362811888360849671193381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25203326809182396492729397 2362811888360849671193381)
                ·
                  refine ⟨443027229067659313348759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362811888360849671193381 443027229067659313348759)
                  ·
                    rfl

theorem cell21_1941283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_1941283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941283 prefixEnd_1941283 := by exact prefixLift 1941283
  have htrace : WordTrace (prefixWord ++ tailWord_1941283) baseStart_1941283 baseEnd_1941283 := by
    simpa [prefixWord, tailWord_1941283, baseEnd_1941283] using wordTrace_append hprefix tailTrace_1941283
  have hstable : (prefixWord ++ tailWord_1941283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941283).length < 2 ^ (prefixWord ++ tailWord_1941283).sum := by decide
  have hdescent : baseEnd_1941283 < baseStart_1941283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941300 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1941300 : Nat := 118140960795 + 1941300 * 2 ^ 59
def prefixEnd_1941300 : Nat := 4983230072969 + 3 ^ 40 * 1941300 * 2
def baseEnd_1941300 : Nat := 443031108699271061565391

theorem tailTrace_1941300 : CollatzResearch.WordTrace tailWord_1941300 prefixEnd_1941300 443031108699271061565391 := by
  unfold tailWord_1941300
  simp only [CollatzResearch.WordTrace]
  refine ⟨35402513933504561244626677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47203351911339414992835569 35402513933504561244626677)
  ·
    refine ⟨3318985681266052616683751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35402513933504561244626677 3318985681266052616683751)
    ·
      refine ⟨4978478521899078925025627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318985681266052616683751 4978478521899078925025627)
      ·
        refine ⟨7467717782848618387538441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978478521899078925025627 7467717782848618387538441)
        ·
          refine ⟨5600788337136463790653831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7467717782848618387538441 5600788337136463790653831)
          ·
            refine ⟨8401182505704695685980747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600788337136463790653831 8401182505704695685980747)
            ·
              refine ⟨12601773758557043528971121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401182505704695685980747 12601773758557043528971121)
              ·
                refine ⟨9451330318917782646728341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12601773758557043528971121 9451330318917782646728341)
                ·
                  refine ⟨443031108699271061565391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9451330318917782646728341 443031108699271061565391)
                  ·
                    rfl

theorem cell21_1941300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1941300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941300 prefixEnd_1941300 := by exact prefixLift 1941300
  have htrace : WordTrace (prefixWord ++ tailWord_1941300) baseStart_1941300 baseEnd_1941300 := by
    simpa [prefixWord, tailWord_1941300, baseEnd_1941300] using wordTrace_append hprefix tailTrace_1941300
  have hstable : (prefixWord ++ tailWord_1941300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941300).length < 2 ^ (prefixWord ++ tailWord_1941300).sum := by decide
  have hdescent : baseEnd_1941300 < baseStart_1941300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941379 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 3]
def baseStart_1941379 : Nat := 118140960795 + 1941379 * 2 ^ 59
def prefixEnd_1941379 : Nat := 4983230072969 + 3 ^ 40 * 1941379 * 2
def baseEnd_1941379 : Nat := 443049137575584479748563

theorem tailTrace_1941379 : CollatzResearch.WordTrace tailWord_1941379 prefixEnd_1941379 443049137575584479748563 := by
  unfold tailWord_1941379
  simp only [CollatzResearch.WordTrace]
  refine ⟨70807909233722918981379191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47205272822481945987586127 70807909233722918981379191)
  ·
    refine ⟨106211863850584378472068787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70807909233722918981379191 106211863850584378472068787)
    ·
      refine ⟨159317795775876567708103181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106211863850584378472068787 159317795775876567708103181)
      ·
        refine ⟨59744173415953712890538693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159317795775876567708103181 59744173415953712890538693)
        ·
          refine ⟨11202032515491321166976005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59744173415953712890538693 11202032515491321166976005)
          ·
            refine ⟨2100381096654622718808001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11202032515491321166976005 2100381096654622718808001)
            ·
              refine ⟨1575285822490967039106001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100381096654622718808001 1575285822490967039106001)
              ·
                refine ⟨1181464366868225279329501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575285822490967039106001 1181464366868225279329501)
                ·
                  refine ⟨443049137575584479748563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181464366868225279329501 443049137575584479748563)
                  ·
                    rfl

theorem cell21_1941379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].length) (baseStart_1941379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941379 prefixEnd_1941379 := by exact prefixLift 1941379
  have htrace : WordTrace (prefixWord ++ tailWord_1941379) baseStart_1941379 baseEnd_1941379 := by
    simpa [prefixWord, tailWord_1941379, baseEnd_1941379] using wordTrace_append hprefix tailTrace_1941379
  have hstable : (prefixWord ++ tailWord_1941379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941379).length < 2 ^ (prefixWord ++ tailWord_1941379).sum := by decide
  have hdescent : baseEnd_1941379 < baseStart_1941379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941407 : List Nat := [1, 1, 2, 5, 3, 1, 3, 5]
def baseStart_1941407 : Nat := 118140960795 + 1941407 * 2 ^ 59
def prefixEnd_1941407 : Nat := 4983230072969 + 3 ^ 40 * 1941407 * 2
def baseEnd_1941407 : Nat := 147685175852354217760613

theorem tailTrace_1941407 : CollatzResearch.WordTrace tailWord_1941407 prefixEnd_1941407 147685175852354217760613 := by
  unfold tailWord_1941407
  simp only [CollatzResearch.WordTrace]
  refine ⟨70808930477621479763398475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47205953651747653175598983 70808930477621479763398475)
  ·
    refine ⟨106213395716432219645097713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70808930477621479763398475 106213395716432219645097713)
    ·
      refine ⟨79660046787324164733823285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106213395716432219645097713 79660046787324164733823285)
      ·
        refine ⟨7468129386311640443795933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79660046787324164733823285 7468129386311640443795933)
        ·
          refine ⟨2800548519866865166423475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7468129386311640443795933 2800548519866865166423475)
          ·
            refine ⟨4200822779800297749635213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800548519866865166423475 4200822779800297749635213)
            ·
              refine ⟨1575308542425111656113205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4200822779800297749635213 1575308542425111656113205)
              ·
                refine ⟨147685175852354217760613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1575308542425111656113205 147685175852354217760613)
                ·
                  rfl

theorem cell21_1941407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].length) (baseStart_1941407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941407 prefixEnd_1941407 := by exact prefixLift 1941407
  have htrace : WordTrace (prefixWord ++ tailWord_1941407) baseStart_1941407 baseEnd_1941407 := by
    simpa [prefixWord, tailWord_1941407, baseEnd_1941407] using wordTrace_append hprefix tailTrace_1941407
  have hstable : (prefixWord ++ tailWord_1941407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941407).length < 2 ^ (prefixWord ++ tailWord_1941407).sum := by decide
  have hdescent : baseEnd_1941407 < baseStart_1941407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941438 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1941438 : Nat := 118140960795 + 1941438 * 2 ^ 59
def prefixEnd_1941438 : Nat := 4983230072969 + 3 ^ 40 * 1941438 * 2
def baseEnd_1941438 : Nat := 443062602179413488265109

theorem tailTrace_1941438 : CollatzResearch.WordTrace tailWord_1941438 prefixEnd_1941438 443062602179413488265109 := by
  unfold tailWord_1941438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851257642563646507222121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47206707427006114705184645 8851257642563646507222121)
  ·
    refine ⟨6638443231922734880416591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8851257642563646507222121 6638443231922734880416591)
    ·
      refine ⟨9957664847884102320624887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638443231922734880416591 9957664847884102320624887)
      ·
        refine ⟨14936497271826153480937331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957664847884102320624887 14936497271826153480937331)
        ·
          refine ⟨22404745907739230221405997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936497271826153480937331 22404745907739230221405997)
          ·
            refine ⟨8401779715402211333027249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22404745907739230221405997 8401779715402211333027249)
            ·
              refine ⟨6301334786551658499770437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401779715402211333027249 6301334786551658499770437)
              ·
                refine ⟨1181500272478435968706957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6301334786551658499770437 1181500272478435968706957)
                ·
                  refine ⟨443062602179413488265109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181500272478435968706957 443062602179413488265109)
                  ·
                    rfl

theorem cell21_1941438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1941438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941438 prefixEnd_1941438 := by exact prefixLift 1941438
  have htrace : WordTrace (prefixWord ++ tailWord_1941438) baseStart_1941438 baseEnd_1941438 := by
    simpa [prefixWord, tailWord_1941438, baseEnd_1941438] using wordTrace_append hprefix tailTrace_1941438
  have hstable : (prefixWord ++ tailWord_1941438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941438).length < 2 ^ (prefixWord ++ tailWord_1941438).sum := by decide
  have hdescent : baseEnd_1941438 < baseStart_1941438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941466 : List Nat := [3, 1, 1, 2, 5, 1, 1, 7]
def baseStart_1941466 : Nat := 118140960795 + 1941466 * 2 ^ 59
def prefixEnd_1941466 : Nat := 4983230072969 + 3 ^ 40 * 1941466 * 2
def baseEnd_1941466 : Nat := 147689664053630553932795

theorem tailTrace_1941466 : CollatzResearch.WordTrace tailWord_1941466 prefixEnd_1941466 147689664053630553932795 := by
  unfold tailWord_1941466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702770596101933209949063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47207388256271821893197501 17702770596101933209949063)
  ·
    refine ⟨26554155894152899814923595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702770596101933209949063 26554155894152899814923595)
    ·
      refine ⟨39831233841229349722385393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26554155894152899814923595 39831233841229349722385393)
      ·
        refine ⟨29873425380922012291789045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39831233841229349722385393 29873425380922012291789045)
        ·
          refine ⟨2800633629461438652355223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29873425380922012291789045 2800633629461438652355223)
          ·
            refine ⟨4200950444192157978532835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800633629461438652355223 4200950444192157978532835)
            ·
              refine ⟨6301425666288236967799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200950444192157978532835 6301425666288236967799253)
              ·
                refine ⟨147689664053630553932795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6301425666288236967799253 147689664053630553932795)
                ·
                  rfl

theorem cell21_1941466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_1941466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941466 prefixEnd_1941466 := by exact prefixLift 1941466
  have htrace : WordTrace (prefixWord ++ tailWord_1941466) baseStart_1941466 baseEnd_1941466 := by
    simpa [prefixWord, tailWord_1941466, baseEnd_1941466] using wordTrace_append hprefix tailTrace_1941466
  have hstable : (prefixWord ++ tailWord_1941466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941466).length < 2 ^ (prefixWord ++ tailWord_1941466).sum := by decide
  have hdescent : baseEnd_1941466 < baseStart_1941466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941497 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_1941497 : Nat := 118140960795 + 1941497 * 2 ^ 59
def prefixEnd_1941497 : Nat := 4983230072969 + 3 ^ 40 * 1941497 * 2
def baseEnd_1941497 : Nat := 443076066783242496781655

theorem tailTrace_1941497 : CollatzResearch.WordTrace tailWord_1941497 prefixEnd_1941497 443076066783242496781655 := by
  unfold tailWord_1941497
  simp only [CollatzResearch.WordTrace]
  refine ⟨70812213047295425134174745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47208142031530283422783163 70812213047295425134174745)
  ·
    refine ⟨53109159785471568850631059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70812213047295425134174745 53109159785471568850631059)
    ·
      refine ⟨79663739678207353275946589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53109159785471568850631059 79663739678207353275946589)
      ·
        refine ⟨29873902379327757478479971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79663739678207353275946589 29873902379327757478479971)
        ·
          refine ⟨44810853568991636217719957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29873902379327757478479971 44810853568991636217719957)
          ·
            refine ⟨2100508761046482947705623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44810853568991636217719957 2100508761046482947705623)
            ·
              refine ⟨3150763141569724421558435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100508761046482947705623 3150763141569724421558435)
              ·
                refine ⟨4726144712354586632337653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150763141569724421558435 4726144712354586632337653)
                ·
                  refine ⟨443076066783242496781655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726144712354586632337653 443076066783242496781655)
                  ·
                    rfl

theorem cell21_1941497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_1941497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941497 prefixEnd_1941497 := by exact prefixLift 1941497
  have htrace : WordTrace (prefixWord ++ tailWord_1941497) baseStart_1941497 baseEnd_1941497 := by
    simpa [prefixWord, tailWord_1941497, baseEnd_1941497] using wordTrace_append hprefix tailTrace_1941497
  have hstable : (prefixWord ++ tailWord_1941497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941497).length < 2 ^ (prefixWord ++ tailWord_1941497).sum := by decide
  have hdescent : baseEnd_1941497 < baseStart_1941497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941652 : List Nat := [2, 4, 2, 3, 2, 1, 7]
def baseStart_1941652 : Nat := 118140960795 + 1941652 * 2 ^ 59
def prefixEnd_1941652 : Nat := 4983230072969 + 3 ^ 40 * 1941652 * 2
def baseEnd_1941652 : Nat := 49234604432777407966445

theorem tailTrace_1941652 : CollatzResearch.WordTrace tailWord_1941652 prefixEnd_1941652 49234604432777407966445 := by
  unfold tailWord_1941652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35408933180866943303033605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47211910907822591070711473 35408933180866943303033605)
  ·
    refine ⟨6639174971412551869318801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35408933180866943303033605 6639174971412551869318801)
    ·
      refine ⟨4979381228559413901989101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6639174971412551869318801 4979381228559413901989101)
      ·
        refine ⟨1867267960709780213245913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4979381228559413901989101 1867267960709780213245913)
        ·
          refine ⟨1400450970532335159934435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867267960709780213245913 1400450970532335159934435)
          ·
            refine ⟨2100676455798502739901653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400450970532335159934435 2100676455798502739901653)
            ·
              refine ⟨49234604432777407966445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2100676455798502739901653 49234604432777407966445)
              ·
                rfl

theorem cell21_1941652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 7].length) (baseStart_1941652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941652 prefixEnd_1941652 := by exact prefixLift 1941652
  have htrace : WordTrace (prefixWord ++ tailWord_1941652) baseStart_1941652 baseEnd_1941652 := by
    simpa [prefixWord, tailWord_1941652, baseEnd_1941652] using wordTrace_append hprefix tailTrace_1941652
  have hstable : (prefixWord ++ tailWord_1941652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941652).length < 2 ^ (prefixWord ++ tailWord_1941652).sum := by decide
  have hdescent : baseEnd_1941652 < baseStart_1941652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941663 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_1941663 : Nat := 118140960795 + 1941663 * 2 ^ 59
def prefixEnd_1941663 : Nat := 4983230072969 + 3 ^ 40 * 1941663 * 2
def baseEnd_1941663 : Nat := 443113950244863097014649

theorem tailTrace_1941663 : CollatzResearch.WordTrace tailWord_1941663 prefixEnd_1941663 443113950244863097014649 := by
  unfold tailWord_1941663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818267564694035484717643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47212178376462690323145095 70818267564694035484717643)
  ·
    refine ⟨106227401347041053227076465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70818267564694035484717643 106227401347041053227076465)
    ·
      refine ⟨79670551010280789920307349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106227401347041053227076465 79670551010280789920307349)
      ·
        refine ⟨3734557078606912027514407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79670551010280789920307349 3734557078606912027514407)
        ·
          refine ⟨5601835617910368041271611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734557078606912027514407 5601835617910368041271611)
          ·
            refine ⟨8402753426865552061907417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601835617910368041271611 8402753426865552061907417)
            ·
              refine ⟨6302065070149164046430563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8402753426865552061907417 6302065070149164046430563)
              ·
                refine ⟨9453097605223746069645845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302065070149164046430563 9453097605223746069645845)
                ·
                  refine ⟨443113950244863097014649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9453097605223746069645845 443113950244863097014649)
                  ·
                    rfl

theorem cell21_1941663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_1941663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941663 prefixEnd_1941663 := by exact prefixLift 1941663
  have htrace : WordTrace (prefixWord ++ tailWord_1941663) baseStart_1941663 baseEnd_1941663 := by
    simpa [prefixWord, tailWord_1941663, baseEnd_1941663] using wordTrace_append hprefix tailTrace_1941663
  have hstable : (prefixWord ++ tailWord_1941663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941663).length < 2 ^ (prefixWord ++ tailWord_1941663).sum := by decide
  have hdescent : baseEnd_1941663 < baseStart_1941663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941666 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1941666 : Nat := 118140960795 + 1941666 * 2 ^ 59
def prefixEnd_1941666 : Nat := 4983230072969 + 3 ^ 40 * 1941666 * 2
def baseEnd_1941666 : Nat := 443114634885735758464643

theorem tailTrace_1941666 : CollatzResearch.WordTrace tailWord_1941666 prefixEnd_1941666 443114634885735758464643 := by
  unfold tailWord_1941666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704594245920791749269213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47212251322455444664717901 17704594245920791749269213)
  ·
    refine ⟨6639222842220296905975955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17704594245920791749269213 6639222842220296905975955)
    ·
      refine ⟨9958834263330445358963933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639222842220296905975955 9958834263330445358963933)
      ·
        refine ⟨3734562848748917009611475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9958834263330445358963933 3734562848748917009611475)
        ·
          refine ⟨5601844273123375514417213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734562848748917009611475 5601844273123375514417213)
          ·
            refine ⟨2100691602421265817906455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5601844273123375514417213 2100691602421265817906455)
            ·
              refine ⟨3151037403631898726859683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100691602421265817906455 3151037403631898726859683)
              ·
                refine ⟨4726556105447848090289525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151037403631898726859683 4726556105447848090289525)
                ·
                  refine ⟨443114634885735758464643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726556105447848090289525 443114634885735758464643)
                  ·
                    rfl

theorem cell21_1941666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1941666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941666 prefixEnd_1941666 := by exact prefixLift 1941666
  have htrace : WordTrace (prefixWord ++ tailWord_1941666) baseStart_1941666 baseEnd_1941666 := by
    simpa [prefixWord, tailWord_1941666, baseEnd_1941666] using wordTrace_append hprefix tailTrace_1941666
  have hstable : (prefixWord ++ tailWord_1941666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941666).length < 2 ^ (prefixWord ++ tailWord_1941666).sum := by decide
  have hdescent : baseEnd_1941666 < baseStart_1941666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941691 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_1941691 : Nat := 118140960795 + 1941691 * 2 ^ 59
def prefixEnd_1941691 : Nat := 4983230072969 + 3 ^ 40 * 1941691 * 2
def baseEnd_1941691 : Nat := 443120340226341270547925

theorem tailTrace_1941691 : CollatzResearch.WordTrace tailWord_1941691 prefixEnd_1941691 443120340226341270547925 := by
  unfold tailWord_1941691
  simp only [CollatzResearch.WordTrace]
  refine ⟨70819288808592596266736927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47212859205728397511157951 70819288808592596266736927)
  ·
    refine ⟨106228933212888894400105391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70819288808592596266736927 106228933212888894400105391)
    ·
      refine ⟨159343399819333341600158087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106228933212888894400105391 159343399819333341600158087)
      ·
        refine ⟨239015099729000012400237131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159343399819333341600158087 239015099729000012400237131)
        ·
          refine ⟨358522649593500018600355697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239015099729000012400237131 358522649593500018600355697)
          ·
            refine ⟨268891987195125013950266773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358522649593500018600355697 268891987195125013950266773)
            ·
              refine ⟨12604311899771485028918755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268891987195125013950266773 12604311899771485028918755)
              ·
                refine ⟨18906467849657227543378133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604311899771485028918755 18906467849657227543378133)
                ·
                  refine ⟨443120340226341270547925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18906467849657227543378133 443120340226341270547925)
                  ·
                    rfl

theorem cell21_1941691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_1941691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941691 prefixEnd_1941691 := by exact prefixLift 1941691
  have htrace : WordTrace (prefixWord ++ tailWord_1941691) baseStart_1941691 baseEnd_1941691 := by
    simpa [prefixWord, tailWord_1941691, baseEnd_1941691] using wordTrace_append hprefix tailTrace_1941691
  have hstable : (prefixWord ++ tailWord_1941691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941691).length < 2 ^ (prefixWord ++ tailWord_1941691).sum := by decide
  have hdescent : baseEnd_1941691 < baseStart_1941691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941722 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1941722 : Nat := 118140960795 + 1941722 * 2 ^ 59
def prefixEnd_1941722 : Nat := 4983230072969 + 3 ^ 40 * 1941722 * 2
def baseEnd_1941722 : Nat := 443127414848692105531195

theorem tailTrace_1941722 : CollatzResearch.WordTrace tailWord_1941722 prefixEnd_1941722 443127414848692105531195 := by
  unfold tailWord_1941722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705104867870072140278855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47213612980986859040743613 17705104867870072140278855)
  ·
    refine ⟨26557657301805108210418283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17705104867870072140278855 26557657301805108210418283)
    ·
      refine ⟨39836485952707662315627425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26557657301805108210418283 39836485952707662315627425)
      ·
        refine ⟨29877364464530746736720569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39836485952707662315627425 29877364464530746736720569)
        ·
          refine ⟨22408023348398060052540427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29877364464530746736720569 22408023348398060052540427)
          ·
            refine ⟨33612035022597090078810641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22408023348398060052540427 33612035022597090078810641)
            ·
              refine ⟨25209026266947817559107981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33612035022597090078810641 25209026266947817559107981)
              ·
                refine ⟨9453384850105431584665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25209026266947817559107981 9453384850105431584665493)
                ·
                  refine ⟨443127414848692105531195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9453384850105431584665493 443127414848692105531195)
                  ·
                    rfl

theorem cell21_1941722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1941722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941722 prefixEnd_1941722 := by exact prefixLift 1941722
  have htrace : WordTrace (prefixWord ++ tailWord_1941722) baseStart_1941722 baseEnd_1941722 := by
    simpa [prefixWord, tailWord_1941722, baseEnd_1941722] using wordTrace_append hprefix tailTrace_1941722
  have hstable : (prefixWord ++ tailWord_1941722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941722).length < 2 ^ (prefixWord ++ tailWord_1941722).sum := by decide
  have hdescent : baseEnd_1941722 < baseStart_1941722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941784 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_1941784 : Nat := 118140960795 + 1941784 * 2 ^ 59
def prefixEnd_1941784 : Nat := 4983230072969 + 3 ^ 40 * 1941784 * 2
def baseEnd_1941784 : Nat := 443141564093393775497735

theorem tailTrace_1941784 : CollatzResearch.WordTrace tailWord_1941784 prefixEnd_1941784 443141564093393775497735 := by
  unfold tailWord_1941784
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411340398627836574936203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47215120531503782099914937 35411340398627836574936203)
  ·
    refine ⟨53117010597941754862404305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35411340398627836574936203 53117010597941754862404305)
    ·
      refine ⟨39837757948456316146803229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53117010597941754862404305 39837757948456316146803229)
      ·
        refine ⟨14939159230671118555051211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39837757948456316146803229 14939159230671118555051211)
        ·
          refine ⟨22408738846006677832576817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939159230671118555051211 22408738846006677832576817)
          ·
            refine ⟨16806554134505008374432613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408738846006677832576817 16806554134505008374432613)
            ·
              refine ⟨3151228900219689070206115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16806554134505008374432613 3151228900219689070206115)
              ·
                refine ⟨4726843350329533605309173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151228900219689070206115 4726843350329533605309173)
                ·
                  refine ⟨443141564093393775497735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726843350329533605309173 443141564093393775497735)
                  ·
                    rfl

theorem cell21_1941784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_1941784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941784 prefixEnd_1941784 := by exact prefixLift 1941784
  have htrace : WordTrace (prefixWord ++ tailWord_1941784) baseStart_1941784 baseEnd_1941784 := by
    simpa [prefixWord, tailWord_1941784, baseEnd_1941784] using wordTrace_append hprefix tailTrace_1941784
  have hstable : (prefixWord ++ tailWord_1941784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941784).length < 2 ^ (prefixWord ++ tailWord_1941784).sum := by decide
  have hdescent : baseEnd_1941784 < baseStart_1941784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941790 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1941790 : Nat := 118140960795 + 1941790 * 2 ^ 59
def prefixEnd_1941790 : Nat := 4983230072969 + 3 ^ 40 * 1941790 * 2
def baseEnd_1941790 : Nat := 443142933375139098397723

theorem tailTrace_1941790 : CollatzResearch.WordTrace tailWord_1941790 prefixEnd_1941790 443142933375139098397723 := by
  unfold tailWord_1941790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852862454404242021823853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47215266423489290783060549 8852862454404242021823853)
  ·
    refine ⟨3319823420401590758183945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8852862454404242021823853 3319823420401590758183945)
    ·
      refine ⟨2489867565301193068637959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319823420401590758183945 2489867565301193068637959)
      ·
        refine ⟨3734801347951789602956939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489867565301193068637959 3734801347951789602956939)
        ·
          refine ⟨5602202021927684404435409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734801347951789602956939 5602202021927684404435409)
          ·
            refine ⟨4201651516445763303326557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602202021927684404435409 4201651516445763303326557)
            ·
              refine ⟨1575619318667161238747459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4201651516445763303326557 1575619318667161238747459)
              ·
                refine ⟨2363428978000741858121189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575619318667161238747459 2363428978000741858121189)
                ·
                  refine ⟨443142933375139098397723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363428978000741858121189 443142933375139098397723)
                  ·
                    rfl

theorem cell21_1941790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1941790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941790 prefixEnd_1941790 := by exact prefixLift 1941790
  have htrace : WordTrace (prefixWord ++ tailWord_1941790) baseStart_1941790 baseEnd_1941790 := by
    simpa [prefixWord, tailWord_1941790, baseEnd_1941790] using wordTrace_append hprefix tailTrace_1941790
  have hstable : (prefixWord ++ tailWord_1941790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941790).length < 2 ^ (prefixWord ++ tailWord_1941790).sum := by decide
  have hdescent : baseEnd_1941790 < baseStart_1941790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941818 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1941818 : Nat := 118140960795 + 1941818 * 2 ^ 59
def prefixEnd_1941818 : Nat := 4983230072969 + 3 ^ 40 * 1941818 * 2
def baseEnd_1941818 : Nat := 443149323356617271930999

theorem tailTrace_1941818 : CollatzResearch.WordTrace tailWord_1941818 prefixEnd_1941818 443149323356617271930999 := by
  unfold tailWord_1941818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705980219783124239152527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47215947252754997971073405 17705980219783124239152527)
  ·
    refine ⟨26558970329674686358728791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17705980219783124239152527 26558970329674686358728791)
    ·
      refine ⟨39838455494512029538093187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558970329674686358728791 39838455494512029538093187)
      ·
        refine ⟨59757683241768044307139781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39838455494512029538093187 59757683241768044307139781)
        ·
          refine ⟨11204565607831508307588709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59757683241768044307139781 11204565607831508307588709)
          ·
            refine ⟨2100856051468407807672883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11204565607831508307588709 2100856051468407807672883)
            ·
              refine ⟨3151284077202611711509325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100856051468407807672883 3151284077202611711509325)
              ·
                refine ⟨1181731528950979391815997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3151284077202611711509325 1181731528950979391815997)
                ·
                  refine ⟨443149323356617271930999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181731528950979391815997 443149323356617271930999)
                  ·
                    rfl

theorem cell21_1941818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1941818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941818 prefixEnd_1941818 := by exact prefixLift 1941818
  have htrace : WordTrace (prefixWord ++ tailWord_1941818) baseStart_1941818 baseEnd_1941818 := by
    simpa [prefixWord, tailWord_1941818, baseEnd_1941818] using wordTrace_append hprefix tailTrace_1941818
  have hstable : (prefixWord ++ tailWord_1941818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941818).length < 2 ^ (prefixWord ++ tailWord_1941818).sum := by decide
  have hdescent : baseEnd_1941818 < baseStart_1941818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941843 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_1941843 : Nat := 118140960795 + 1941843 * 2 ^ 59
def prefixEnd_1941843 : Nat := 4983230072969 + 3 ^ 40 * 1941843 * 2
def baseEnd_1941843 : Nat := 443155028697222784014281

theorem tailTrace_1941843 : CollatzResearch.WordTrace tailWord_1941843 prefixEnd_1941843 443155028697222784014281 := by
  unfold tailWord_1941843
  simp only [CollatzResearch.WordTrace]
  refine ⟨70824832704041926226270183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47216555136027950817513455 70824832704041926226270183)
  ·
    refine ⟨106237249056062889339405275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70824832704041926226270183 106237249056062889339405275)
    ·
      refine ⟨159355873584094334009107913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106237249056062889339405275 159355873584094334009107913)
      ·
        refine ⟨119516905188070750506830935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159355873584094334009107913 119516905188070750506830935)
        ·
          refine ⟨179275357782106125760246403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119516905188070750506830935 179275357782106125760246403)
          ·
            refine ⟨268913036673159188640369605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179275357782106125760246403 268913036673159188640369605)
            ·
              refine ⟨50421194376217347870069301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268913036673159188640369605 50421194376217347870069301)
              ·
                refine ⟨4726986972770376362818997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50421194376217347870069301 4726986972770376362818997)
                ·
                  refine ⟨443155028697222784014281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4726986972770376362818997 443155028697222784014281)
                  ·
                    rfl

theorem cell21_1941843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_1941843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941843 prefixEnd_1941843 := by exact prefixLift 1941843
  have htrace : WordTrace (prefixWord ++ tailWord_1941843) baseStart_1941843 baseEnd_1941843 := by
    simpa [prefixWord, tailWord_1941843, baseEnd_1941843] using wordTrace_append hprefix tailTrace_1941843
  have hstable : (prefixWord ++ tailWord_1941843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941843).length < 2 ^ (prefixWord ++ tailWord_1941843).sum := by decide
  have hdescent : baseEnd_1941843 < baseStart_1941843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941922 : List Nat := [3, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1941922 : Nat := 118140960795 + 1941922 * 2 ^ 59
def prefixEnd_1941922 : Nat := 4983230072969 + 3 ^ 40 * 1941922 * 2
def baseEnd_1941922 : Nat := 147724352524512067399151

theorem tailTrace_1941922 : CollatzResearch.WordTrace tailWord_1941922 prefixEnd_1941922 147724352524512067399151 := by
  unfold tailWord_1941922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706928517688930679599005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47218476047170481812264013 17706928517688930679599005)
  ·
    refine ⟨6640098194133349004849627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17706928517688930679599005 6640098194133349004849627)
    ·
      refine ⟨9960147291200023507274441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640098194133349004849627 9960147291200023507274441)
      ·
        refine ⟨7470110468400017630455831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9960147291200023507274441 7470110468400017630455831)
        ·
          refine ⟨11205165702600026445683747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470110468400017630455831 11205165702600026445683747)
          ·
            refine ⟨16807748553900039668525621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205165702600026445683747 16807748553900039668525621)
            ·
              refine ⟨1575726426928128718924277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16807748553900039668525621 1575726426928128718924277)
              ·
                refine ⟨147724352524512067399151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1575726426928128718924277 147724352524512067399151)
                ·
                  rfl

theorem cell21_1941922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1941922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941922 prefixEnd_1941922 := by exact prefixLift 1941922
  have htrace : WordTrace (prefixWord ++ tailWord_1941922) baseStart_1941922 baseEnd_1941922 := by
    simpa [prefixWord, tailWord_1941922, baseEnd_1941922] using wordTrace_append hprefix tailTrace_1941922
  have hstable : (prefixWord ++ tailWord_1941922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941922).length < 2 ^ (prefixWord ++ tailWord_1941922).sum := by decide
  have hdescent : baseEnd_1941922 < baseStart_1941922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941981 : List Nat := [1, 4, 3, 1, 1, 1, 3, 7]
def baseStart_1941981 : Nat := 118140960795 + 1941981 * 2 ^ 59
def prefixEnd_1941981 : Nat := 4983230072969 + 3 ^ 40 * 1941981 * 2
def baseEnd_1941981 : Nat := 147728840725788403571333

theorem tailTrace_1941981 : CollatzResearch.WordTrace tailWord_1941981 prefixEnd_1941981 147728840725788403571333 := by
  unfold tailWord_1941981
  simp only [CollatzResearch.WordTrace]
  refine ⟨70829865977541975794793797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47219910651694650529862531 70829865977541975794793797)
  ·
    refine ⟨13280599870789120461523837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70829865977541975794793797 13280599870789120461523837)
    ·
      refine ⟨4980224951545920173071439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13280599870789120461523837 4980224951545920173071439)
      ·
        refine ⟨7470337427318880259607159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980224951545920173071439 7470337427318880259607159)
        ·
          refine ⟨11205506140978320389410739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470337427318880259607159 11205506140978320389410739)
          ·
            refine ⟨16808259211467480584116109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205506140978320389410739 16808259211467480584116109)
            ·
              refine ⟨6303097204300305219043541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16808259211467480584116109 6303097204300305219043541)
              ·
                refine ⟨147728840725788403571333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6303097204300305219043541 147728840725788403571333)
                ·
                  rfl

theorem cell21_1941981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_1941981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941981 prefixEnd_1941981 := by exact prefixLift 1941981
  have htrace : WordTrace (prefixWord ++ tailWord_1941981) baseStart_1941981 baseEnd_1941981 := by
    simpa [prefixWord, tailWord_1941981, baseEnd_1941981] using wordTrace_append hprefix tailTrace_1941981
  have hstable : (prefixWord ++ tailWord_1941981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941981).length < 2 ^ (prefixWord ++ tailWord_1941981).sum := by decide
  have hdescent : baseEnd_1941981 < baseStart_1941981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941987 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 3]
def baseStart_1941987 : Nat := 118140960795 + 1941987 * 2 ^ 59
def prefixEnd_1941987 : Nat := 4983230072969 + 3 ^ 40 * 1941987 * 2
def baseEnd_1941987 : Nat := 443187891459110533613987

theorem tailTrace_1941987 : CollatzResearch.WordTrace tailWord_1941987 prefixEnd_1941987 443187891459110533613987 := by
  unfold tailWord_1941987
  simp only [CollatzResearch.WordTrace]
  refine ⟨70830084815520238819512215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47220056543680159213008143 70830084815520238819512215)
  ·
    refine ⟨106245127223280358229268323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70830084815520238819512215 106245127223280358229268323)
    ·
      refine ⟨159367690834920537343902485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106245127223280358229268323 159367690834920537343902485)
      ·
        refine ⟨7470360507886900187995429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159367690834920537343902485 7470360507886900187995429)
        ·
          refine ⟨1400692595228793785249143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7470360507886900187995429 1400692595228793785249143)
          ·
            refine ⟨2101038892843190677873715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400692595228793785249143 2101038892843190677873715)
            ·
              refine ⟨3151558339264786016810573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101038892843190677873715 3151558339264786016810573)
              ·
                refine ⟨1181834377224294756303965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3151558339264786016810573 1181834377224294756303965)
                ·
                  refine ⟨443187891459110533613987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181834377224294756303965 443187891459110533613987)
                  ·
                    rfl

theorem cell21_1941987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 3].length) (baseStart_1941987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1941987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1941987 prefixEnd_1941987 := by exact prefixLift 1941987
  have htrace : WordTrace (prefixWord ++ tailWord_1941987) baseStart_1941987 baseEnd_1941987 := by
    simpa [prefixWord, tailWord_1941987, baseEnd_1941987] using wordTrace_append hprefix tailTrace_1941987
  have hstable : (prefixWord ++ tailWord_1941987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941987).length < 2 ^ (prefixWord ++ tailWord_1941987).sum := by decide
  have hdescent : baseEnd_1941987 < baseStart_1941987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942018 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1942018 : Nat := 118140960795 + 1942018 * 2 ^ 59
def prefixEnd_1942018 : Nat := 4983230072969 + 3 ^ 40 * 1942018 * 2
def baseEnd_1942018 : Nat := 443194966081461368597257

theorem tailTrace_1942018 : CollatzResearch.WordTrace tailWord_1942018 prefixEnd_1942018 443194966081461368597257 := by
  unfold tailWord_1942018
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707803869601982778472677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47220810318938620742593805 17707803869601982778472677)
  ·
    refine ⟨3320213225550371770963627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17707803869601982778472677 3320213225550371770963627)
    ·
      refine ⟨4980319838325557656445441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320213225550371770963627 4980319838325557656445441)
      ·
        refine ⟨3735239878744168242334081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4980319838325557656445441 3735239878744168242334081)
        ·
          refine ⟨2801429909058126181750561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3735239878744168242334081 2801429909058126181750561)
          ·
            refine ⟨2101072431793594636312921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801429909058126181750561 2101072431793594636312921)
            ·
              refine ⟨1575804323845195977234691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101072431793594636312921 1575804323845195977234691)
              ·
                refine ⟨2363706485767793965852037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575804323845195977234691 2363706485767793965852037)
                ·
                  refine ⟨443194966081461368597257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363706485767793965852037 443194966081461368597257)
                  ·
                    rfl

theorem cell21_1942018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1942018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942018 prefixEnd_1942018 := by exact prefixLift 1942018
  have htrace : WordTrace (prefixWord ++ tailWord_1942018) baseStart_1942018 baseEnd_1942018 := by
    simpa [prefixWord, tailWord_1942018, baseEnd_1942018] using wordTrace_append hprefix tailTrace_1942018
  have hstable : (prefixWord ++ tailWord_1942018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942018).length < 2 ^ (prefixWord ++ tailWord_1942018).sum := by decide
  have hdescent : baseEnd_1942018 < baseStart_1942018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942071 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_1942071 : Nat := 118140960795 + 1942071 * 2 ^ 59
def prefixEnd_1942071 : Nat := 4983230072969 + 3 ^ 40 * 1942071 * 2
def baseEnd_1942071 : Nat := 443207061403545054213815

theorem tailTrace_1942071 : CollatzResearch.WordTrace tailWord_1942071 prefixEnd_1942071 443207061403545054213815 := by
  unfold tailWord_1942071
  simp only [CollatzResearch.WordTrace]
  refine ⟨70833148547215921165570067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47222099031477280777046711 70833148547215921165570067)
  ·
    refine ⟨106249722820823881748355101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70833148547215921165570067 106249722820823881748355101)
    ·
      refine ⟨39843646057808955655633163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106249722820823881748355101 39843646057808955655633163)
      ·
        refine ⟨59765469086713433483449745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39843646057808955655633163 59765469086713433483449745)
        ·
          refine ⟨44824101815035075112587309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59765469086713433483449745 44824101815035075112587309)
          ·
            refine ⟨16809038180638153167220241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44824101815035075112587309 16809038180638153167220241)
            ·
              refine ⟨12606778635478614875415181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809038180638153167220241 12606778635478614875415181)
              ·
                refine ⟨4727541988304480578280693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606778635478614875415181 4727541988304480578280693)
                ·
                  refine ⟨443207061403545054213815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727541988304480578280693 443207061403545054213815)
                  ·
                    rfl

theorem cell21_1942071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_1942071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942071 prefixEnd_1942071 := by exact prefixLift 1942071
  have htrace : WordTrace (prefixWord ++ tailWord_1942071) baseStart_1942071 baseEnd_1942071 := by
    simpa [prefixWord, tailWord_1942071, baseEnd_1942071] using wordTrace_append hprefix tailTrace_1942071
  have hstable : (prefixWord ++ tailWord_1942071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942071).length < 2 ^ (prefixWord ++ tailWord_1942071).sum := by decide
  have hdescent : baseEnd_1942071 < baseStart_1942071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942116 : List Nat := [2, 3, 1, 1, 2, 2, 10]
def baseStart_1942116 : Nat := 118140960795 + 1942116 * 2 ^ 59
def prefixEnd_1942116 : Nat := 4983230072969 + 3 ^ 40 * 1942116 * 2
def baseEnd_1942116 : Nat := 49246370112959441773747

theorem tailTrace_1942116 : CollatzResearch.WordTrace tailWord_1942116 prefixEnd_1942116 49246370112959441773747 := by
  unfold tailWord_1942116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35417394916026446925479101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47223193221368595900638801 35417394916026446925479101)
  ·
    refine ⟨13281523093509917597054663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35417394916026446925479101 13281523093509917597054663)
    ·
      refine ⟨19922284640264876395581995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13281523093509917597054663 19922284640264876395581995)
      ·
        refine ⟨29883426960397314593372993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19922284640264876395581995 29883426960397314593372993)
        ·
          refine ⟨22412570220297985945029745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29883426960397314593372993 22412570220297985945029745)
          ·
            refine ⟨16809427665223489458772309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412570220297985945029745 16809427665223489458772309)
            ·
              refine ⟨49246370112959441773747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16809427665223489458772309 49246370112959441773747)
              ·
                rfl

theorem cell21_1942116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 10].length) (baseStart_1942116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942116 prefixEnd_1942116 := by exact prefixLift 1942116
  have htrace : WordTrace (prefixWord ++ tailWord_1942116) baseStart_1942116 baseEnd_1942116 := by
    simpa [prefixWord, tailWord_1942116, baseEnd_1942116] using wordTrace_append hprefix tailTrace_1942116
  have hstable : (prefixWord ++ tailWord_1942116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942116).length < 2 ^ (prefixWord ++ tailWord_1942116).sum := by decide
  have hdescent : baseEnd_1942116 < baseStart_1942116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942147 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_1942147 : Nat := 118140960795 + 1942147 * 2 ^ 59
def prefixEnd_1942147 : Nat := 4983230072969 + 3 ^ 40 * 1942147 * 2
def baseEnd_1942147 : Nat := 443224405638985810946993

theorem tailTrace_1942147 : CollatzResearch.WordTrace tailWord_1942147 prefixEnd_1942147 443224405638985810946993 := by
  unfold tailWord_1942147
  simp only [CollatzResearch.WordTrace]
  refine ⟨70835920494940586145336695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47223946996627057430224463 70835920494940586145336695)
  ·
    refine ⟨106253880742410879218005043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70835920494940586145336695 106253880742410879218005043)
    ·
      refine ⟨159380821113616318827007565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106253880742410879218005043 159380821113616318827007565)
      ·
        refine ⟨59767807917606119560127837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159380821113616318827007565 59767807917606119560127837)
        ·
          refine ⟨22412927969102294835047939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59767807917606119560127837 22412927969102294835047939)
          ·
            refine ⟨33619391953653442252571909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22412927969102294835047939 33619391953653442252571909)
            ·
              refine ⟨6303635991310020422357233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33619391953653442252571909 6303635991310020422357233)
              ·
                refine ⟨4727726993482515316767925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303635991310020422357233 4727726993482515316767925)
                ·
                  refine ⟨443224405638985810946993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727726993482515316767925 443224405638985810946993)
                  ·
                    rfl

theorem cell21_1942147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_1942147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942147 prefixEnd_1942147 := by exact prefixLift 1942147
  have htrace : WordTrace (prefixWord ++ tailWord_1942147) baseStart_1942147 baseEnd_1942147 := by
    simpa [prefixWord, tailWord_1942147, baseEnd_1942147] using wordTrace_append hprefix tailTrace_1942147
  have hstable : (prefixWord ++ tailWord_1942147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942147).length < 2 ^ (prefixWord ++ tailWord_1942147).sum := by decide
  have hdescent : baseEnd_1942147 < baseStart_1942147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942195 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 4]
def baseStart_1942195 : Nat := 118140960795 + 1942195 * 2 ^ 59
def prefixEnd_1942195 : Nat := 4983230072969 + 3 ^ 40 * 1942195 * 2
def baseEnd_1942195 : Nat := 443235359892948394146895

theorem tailTrace_1942195 : CollatzResearch.WordTrace tailWord_1942195 prefixEnd_1942195 443235359892948394146895 := by
  unfold tailWord_1942195
  simp only [CollatzResearch.WordTrace]
  refine ⟨70837671198766690343084039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47225114132511126895389359 70837671198766690343084039)
  ·
    refine ⟨106256506798150035514626059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70837671198766690343084039 106256506798150035514626059)
    ·
      refine ⟨159384760197225053271939089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106256506798150035514626059 159384760197225053271939089)
      ·
        refine ⟨119538570147918789953954317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159384760197225053271939089 119538570147918789953954317)
        ·
          refine ⟨44826963805469546232732869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119538570147918789953954317 44826963805469546232732869)
          ·
            refine ⟨8405055713525539918637413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44826963805469546232732869 8405055713525539918637413)
            ·
              refine ⟨1575947946286038734744515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8405055713525539918637413 1575947946286038734744515)
              ·
                refine ⟨2363921919429058102116773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575947946286038734744515 2363921919429058102116773)
                ·
                  refine ⟨443235359892948394146895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363921919429058102116773 443235359892948394146895)
                  ·
                    rfl

theorem cell21_1942195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_1942195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942195 prefixEnd_1942195 := by exact prefixLift 1942195
  have htrace : WordTrace (prefixWord ++ tailWord_1942195) baseStart_1942195 baseEnd_1942195 := by
    simpa [prefixWord, tailWord_1942195, baseEnd_1942195] using wordTrace_append hprefix tailTrace_1942195
  have hstable : (prefixWord ++ tailWord_1942195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942195).length < 2 ^ (prefixWord ++ tailWord_1942195).sum := by decide
  have hdescent : baseEnd_1942195 < baseStart_1942195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942260 : List Nat := [2, 6, 1, 1, 2, 1, 3, 5]
def baseStart_1942260 : Nat := 118140960795 + 1942260 * 2 ^ 59
def prefixEnd_1942260 : Nat := 4983230072969 + 3 ^ 40 * 1942260 * 2
def baseEnd_1942260 : Nat := 147750064592840908521143

theorem tailTrace_1942260 : CollatzResearch.WordTrace tailWord_1942260 prefixEnd_1942260 147750064592840908521143 := by
  unfold tailWord_1942260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35420020971765603222100117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47226694629020804296133489 35420020971765603222100117)
  ·
    refine ⟨1660313483051512651035943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35420020971765603222100117 1660313483051512651035943)
    ·
      refine ⟨2490470224577268976553915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660313483051512651035943 2490470224577268976553915)
      ·
        refine ⟨3735705336865903464830873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490470224577268976553915 3735705336865903464830873)
        ·
          refine ⟨2801779002649427598623155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3735705336865903464830873 2801779002649427598623155)
          ·
            refine ⟨4202668503974141397934733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801779002649427598623155 4202668503974141397934733)
            ·
              refine ⟨1576000688990303024225525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4202668503974141397934733 1576000688990303024225525)
              ·
                refine ⟨147750064592840908521143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576000688990303024225525 147750064592840908521143)
                ·
                  rfl

theorem cell21_1942260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_1942260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942260 prefixEnd_1942260 := by exact prefixLift 1942260
  have htrace : WordTrace (prefixWord ++ tailWord_1942260) baseStart_1942260 baseEnd_1942260 := by
    simpa [prefixWord, tailWord_1942260, baseEnd_1942260] using wordTrace_append hprefix tailTrace_1942260
  have hstable : (prefixWord ++ tailWord_1942260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942260).length < 2 ^ (prefixWord ++ tailWord_1942260).sum := by decide
  have hdescent : baseEnd_1942260 < baseStart_1942260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942274 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1942274 : Nat := 118140960795 + 1942274 * 2 ^ 59
def prefixEnd_1942274 : Nat := 4983230072969 + 3 ^ 40 * 1942274 * 2
def baseEnd_1942274 : Nat := 443253388769261812330067

theorem tailTrace_1942274 : CollatzResearch.WordTrace tailWord_1942274 prefixEnd_1942274 443253388769261812330067 := by
  unfold tailWord_1942274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710138141370121708802469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47227035043653657890139917 17710138141370121708802469)
  ·
    refine ⟨3320650901506897820400463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17710138141370121708802469 3320650901506897820400463)
    ·
      refine ⟨4980976352260346730600695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320650901506897820400463 4980976352260346730600695)
      ·
        refine ⟨7471464528390520095901043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980976352260346730600695 7471464528390520095901043)
        ·
          refine ⟨11207196792585780143851565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471464528390520095901043 11207196792585780143851565)
          ·
            refine ⟨4202698797219667553944337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11207196792585780143851565 4202698797219667553944337)
            ·
              refine ⟨3152024097914750665458253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4202698797219667553944337 3152024097914750665458253)
              ·
                refine ⟨1182009036718031499546845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3152024097914750665458253 1182009036718031499546845)
                ·
                  refine ⟨443253388769261812330067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182009036718031499546845 443253388769261812330067)
                  ·
                    rfl

theorem cell21_1942274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1942274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942274 prefixEnd_1942274 := by exact prefixLift 1942274
  have htrace : WordTrace (prefixWord ++ tailWord_1942274) baseStart_1942274 baseEnd_1942274 := by
    simpa [prefixWord, tailWord_1942274, baseEnd_1942274] using wordTrace_append hprefix tailTrace_1942274
  have hstable : (prefixWord ++ tailWord_1942274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942274).length < 2 ^ (prefixWord ++ tailWord_1942274).sum := by decide
  have hdescent : baseEnd_1942274 < baseStart_1942274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942364 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1942364 : Nat := 118140960795 + 1942364 * 2 ^ 59
def prefixEnd_1942364 : Nat := 4983230072969 + 3 ^ 40 * 1942364 * 2
def baseEnd_1942364 : Nat := 443273927995441655829883

theorem tailTrace_1942364 : CollatzResearch.WordTrace tailWord_1942364 prefixEnd_1942364 443273927995441655829883 := by
  unfold tailWord_1942364
  simp only [CollatzResearch.WordTrace]
  refine ⟨35421917567577216102993073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47229223423436288137324097 35421917567577216102993073)
  ·
    refine ⟨26566438175682912077244805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35421917567577216102993073 26566438175682912077244805)
    ·
      refine ⟨4981207157940546014483401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26566438175682912077244805 4981207157940546014483401)
      ·
        refine ⟨3735905368455409510862551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4981207157940546014483401 3735905368455409510862551)
        ·
          refine ⟨5603858052683114266293827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735905368455409510862551 5603858052683114266293827)
          ·
            refine ⟨8405787079024671399440741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603858052683114266293827 8405787079024671399440741)
            ·
              refine ⟨1576085077317125887395139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8405787079024671399440741 1576085077317125887395139)
              ·
                refine ⟨2364127615975688831092709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576085077317125887395139 2364127615975688831092709)
                ·
                  refine ⟨443273927995441655829883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364127615975688831092709 443273927995441655829883)
                  ·
                    rfl

theorem cell21_1942364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1942364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942364 prefixEnd_1942364 := by exact prefixLift 1942364
  have htrace : WordTrace (prefixWord ++ tailWord_1942364) baseStart_1942364 baseEnd_1942364 := by
    simpa [prefixWord, tailWord_1942364, baseEnd_1942364] using wordTrace_append hprefix tailTrace_1942364
  have hstable : (prefixWord ++ tailWord_1942364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942364).length < 2 ^ (prefixWord ++ tailWord_1942364).sum := by decide
  have hdescent : baseEnd_1942364 < baseStart_1942364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942409 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 3]
def baseStart_1942409 : Nat := 118140960795 + 1942409 * 2 ^ 59
def prefixEnd_1942409 : Nat := 4983230072969 + 3 ^ 40 * 1942409 * 2
def baseEnd_1942409 : Nat := 443284197608531577579791

theorem tailTrace_1942409 : CollatzResearch.WordTrace tailWord_1942409 prefixEnd_1942409 443284197608531577579791 := by
  unfold tailWord_1942409
  simp only [CollatzResearch.WordTrace]
  refine ⟨70845476419991404891374281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47230317613327603260916187 70845476419991404891374281)
  ·
    refine ⟨53134107314993553668530711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70845476419991404891374281 53134107314993553668530711)
    ·
      refine ⟨79701160972490330502796067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53134107314993553668530711 79701160972490330502796067)
      ·
        refine ⟨119551741458735495754194101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79701160972490330502796067 119551741458735495754194101)
        ·
          refine ⟨11207975761756452726955697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119551741458735495754194101 11207975761756452726955697)
          ·
            refine ⟨8405981821317339545216773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207975761756452726955697 8405981821317339545216773)
            ·
              refine ⟨1576121591497001164728145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8405981821317339545216773 1576121591497001164728145)
              ·
                refine ⟨1182091193622750873546109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576121591497001164728145 1182091193622750873546109)
                ·
                  refine ⟨443284197608531577579791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182091193622750873546109 443284197608531577579791)
                  ·
                    rfl

theorem cell21_1942409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_1942409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942409 prefixEnd_1942409 := by exact prefixLift 1942409
  have htrace : WordTrace (prefixWord ++ tailWord_1942409) baseStart_1942409 baseEnd_1942409 := by
    simpa [prefixWord, tailWord_1942409, baseEnd_1942409] using wordTrace_append hprefix tailTrace_1942409
  have hstable : (prefixWord ++ tailWord_1942409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942409).length < 2 ^ (prefixWord ++ tailWord_1942409).sum := by decide
  have hdescent : baseEnd_1942409 < baseStart_1942409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942589 : List Nat := [1, 4, 1, 3, 1, 4, 1, 6]
def baseStart_1942589 : Nat := 118140960795 + 1942589 * 2 ^ 59
def prefixEnd_1942589 : Nat := 4983230072969 + 3 ^ 40 * 1942589 * 2
def baseEnd_1942589 : Nat := 147775092020297088193141

theorem tailTrace_1942589 : CollatzResearch.WordTrace tailWord_1942589 prefixEnd_1942589 147775092020297088193141 := by
  unfold tailWord_1942589
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852041559339295632926821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47234694372892863755284547 70852041559339295632926821)
  ·
    refine ⟨13284757792376117931173779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70852041559339295632926821 13284757792376117931173779)
    ·
      refine ⟨19927136688564176896760669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284757792376117931173779 19927136688564176896760669)
      ·
        refine ⟨7472676258211566336285251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19927136688564176896760669 7472676258211566336285251)
        ·
          refine ⟨11209014387317349504427877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472676258211566336285251 11209014387317349504427877)
          ·
            refine ⟨2101690197622003032080227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11209014387317349504427877 2101690197622003032080227)
            ·
              refine ⟨3152535296433004548120341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101690197622003032080227 3152535296433004548120341)
              ·
                refine ⟨147775092020297088193141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3152535296433004548120341 147775092020297088193141)
                ·
                  rfl

theorem cell21_1942589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_1942589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942589 prefixEnd_1942589 := by exact prefixLift 1942589
  have htrace : WordTrace (prefixWord ++ tailWord_1942589) baseStart_1942589 baseEnd_1942589 := by
    simpa [prefixWord, tailWord_1942589, baseEnd_1942589] using wordTrace_append hprefix tailTrace_1942589
  have hstable : (prefixWord ++ tailWord_1942589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942589).length < 2 ^ (prefixWord ++ tailWord_1942589).sum := by decide
  have hdescent : baseEnd_1942589 < baseStart_1942589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942634 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1942634 : Nat := 118140960795 + 1942634 * 2 ^ 59
def prefixEnd_1942634 : Nat := 4983230072969 + 3 ^ 40 * 1942634 * 2
def baseEnd_1942634 : Nat := 443335545673981186329331

theorem tailTrace_1942634 : CollatzResearch.WordTrace tailWord_1942634 prefixEnd_1942634 443335545673981186329331 := by
  unfold tailWord_1942634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713420711044067079578739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47235788562784178878876637 17713420711044067079578739)
  ·
    refine ⟨26570131066566100619368109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17713420711044067079578739 26570131066566100619368109)
    ·
      refine ⟨9963799149962287732263041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26570131066566100619368109 9963799149962287732263041)
      ·
        refine ⟨7472849362471715799197281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963799149962287732263041 7472849362471715799197281)
        ·
          refine ⟨5604637021853786849397961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472849362471715799197281 5604637021853786849397961)
          ·
            refine ⟨4203477766390340137048471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604637021853786849397961 4203477766390340137048471)
            ·
              refine ⟨6305216649585510205572707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203477766390340137048471 6305216649585510205572707)
              ·
                refine ⟨9457824974378265308359061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305216649585510205572707 9457824974378265308359061)
                ·
                  refine ⟨443335545673981186329331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9457824974378265308359061 443335545673981186329331)
                  ·
                    rfl

theorem cell21_1942634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1942634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942634 prefixEnd_1942634 := by exact prefixLift 1942634
  have htrace : WordTrace (prefixWord ++ tailWord_1942634) baseStart_1942634 baseEnd_1942634 := by
    simpa [prefixWord, tailWord_1942634, baseEnd_1942634] using wordTrace_append hprefix tailTrace_1942634
  have hstable : (prefixWord ++ tailWord_1942634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942634).length < 2 ^ (prefixWord ++ tailWord_1942634).sum := by decide
  have hdescent : baseEnd_1942634 < baseStart_1942634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942665 : List Nat := [1, 2, 1, 1, 4, 5, 2, 5]
def baseStart_1942665 : Nat := 118140960795 + 1942665 * 2 ^ 59
def prefixEnd_1942665 : Nat := 4983230072969 + 3 ^ 40 * 1942665 * 2
def baseEnd_1942665 : Nat := 147780873432110673770867

theorem tailTrace_1942665 : CollatzResearch.WordTrace tailWord_1942665 prefixEnd_1942665 147780873432110673770867 := by
  unfold tailWord_1942665
  simp only [CollatzResearch.WordTrace]
  refine ⟨70854813507063960612693449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47236542338042640408462299 70854813507063960612693449)
  ·
    refine ⟨53141110130297970459520087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70854813507063960612693449 53141110130297970459520087)
    ·
      refine ⟨79711665195446955689280131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53141110130297970459520087 79711665195446955689280131)
      ·
        refine ⟨119567497793170433533920197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79711665195446955689280131 119567497793170433533920197)
        ·
          refine ⟨22418905836219456287610037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119567497793170433533920197 22418905836219456287610037)
          ·
            refine ⟨2101772422145574026963441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22418905836219456287610037 2101772422145574026963441)
            ·
              refine ⟨1576329316609180520222581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101772422145574026963441 1576329316609180520222581)
              ·
                refine ⟨147780873432110673770867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576329316609180520222581 147780873432110673770867)
                ·
                  rfl

theorem cell21_1942665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].length) (baseStart_1942665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942665 prefixEnd_1942665 := by exact prefixLift 1942665
  have htrace : WordTrace (prefixWord ++ tailWord_1942665) baseStart_1942665 baseEnd_1942665 := by
    simpa [prefixWord, tailWord_1942665, baseEnd_1942665] using wordTrace_append hprefix tailTrace_1942665
  have hstable : (prefixWord ++ tailWord_1942665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942665).length < 2 ^ (prefixWord ++ tailWord_1942665).sum := by decide
  have hdescent : baseEnd_1942665 < baseStart_1942665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942693 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_1942693 : Nat := 118140960795 + 1942693 * 2 ^ 59
def prefixEnd_1942693 : Nat := 4983230072969 + 3 ^ 40 * 1942693 * 2
def baseEnd_1942693 : Nat := 443349010277810194845877

theorem tailTrace_1942693 : CollatzResearch.WordTrace tailWord_1942693 prefixEnd_1942693 443349010277810194845877 := by
  unfold tailWord_1942693
  simp only [CollatzResearch.WordTrace]
  refine ⟨70855834750962521394712733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47237223167308347596475155 70855834750962521394712733)
  ·
    refine ⟨26570938031610945523017275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70855834750962521394712733 26570938031610945523017275)
    ·
      refine ⟨39856407047416418284525913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26570938031610945523017275 39856407047416418284525913)
      ·
        refine ⟨29892305285562313713394435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39856407047416418284525913 29892305285562313713394435)
        ·
          refine ⟨44838457928343470570091653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29892305285562313713394435 44838457928343470570091653)
          ·
            refine ⟨8407210861564400731892185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44838457928343470570091653 8407210861564400731892185)
            ·
              refine ⟨6305408146173300548919139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8407210861564400731892185 6305408146173300548919139)
              ·
                refine ⟨9458112219259950823378709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305408146173300548919139 9458112219259950823378709)
                ·
                  refine ⟨443349010277810194845877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9458112219259950823378709 443349010277810194845877)
                  ·
                    rfl

theorem cell21_1942693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_1942693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942693 prefixEnd_1942693 := by exact prefixLift 1942693
  have htrace : WordTrace (prefixWord ++ tailWord_1942693) baseStart_1942693 baseEnd_1942693 := by
    simpa [prefixWord, tailWord_1942693, baseEnd_1942693] using wordTrace_append hprefix tailTrace_1942693
  have hstable : (prefixWord ++ tailWord_1942693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942693).length < 2 ^ (prefixWord ++ tailWord_1942693).sum := by decide
  have hdescent : baseEnd_1942693 < baseStart_1942693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942707 : List Nat := [1, 1, 1, 2, 3, 2, 3, 8]
def baseStart_1942707 : Nat := 118140960795 + 1942707 * 2 ^ 59
def prefixEnd_1942707 : Nat := 4983230072969 + 3 ^ 40 * 1942707 * 2
def baseEnd_1942707 : Nat := 147784068422849760537505

theorem tailTrace_1942707 : CollatzResearch.WordTrace tailWord_1942707 prefixEnd_1942707 147784068422849760537505 := by
  unfold tailWord_1942707
  simp only [CollatzResearch.WordTrace]
  refine ⟨70856345372911801785722375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47237563581941201190481583 70856345372911801785722375)
  ·
    refine ⟨106284518059367702678583563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70856345372911801785722375 106284518059367702678583563)
    ·
      refine ⟨159426777089051554017875345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106284518059367702678583563 159426777089051554017875345)
      ·
        refine ⟨119570082816788665513406509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159426777089051554017875345 119570082816788665513406509)
        ·
          refine ⟨44838781056295749567527441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119570082816788665513406509 44838781056295749567527441)
          ·
            refine ⟨33629085792221812175645581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44838781056295749567527441 33629085792221812175645581)
            ·
              refine ⟨12610907172083179565867093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33629085792221812175645581 12610907172083179565867093)
              ·
                refine ⟨147784068422849760537505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12610907172083179565867093 147784068422849760537505)
                ·
                  rfl

theorem cell21_1942707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_1942707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942707 prefixEnd_1942707 := by exact prefixLift 1942707
  have htrace : WordTrace (prefixWord ++ tailWord_1942707) baseStart_1942707 baseEnd_1942707 := by
    simpa [prefixWord, tailWord_1942707, baseEnd_1942707] using wordTrace_append hprefix tailTrace_1942707
  have hstable : (prefixWord ++ tailWord_1942707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942707).length < 2 ^ (prefixWord ++ tailWord_1942707).sum := by decide
  have hdescent : baseEnd_1942707 < baseStart_1942707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942907 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 3]
def baseStart_1942907 : Nat := 118140960795 + 1942907 * 2 ^ 59
def prefixEnd_1942907 : Nat := 4983230072969 + 3 ^ 40 * 1942907 * 2
def baseEnd_1942907 : Nat := 443397847993393378278773

theorem tailTrace_1942907 : CollatzResearch.WordTrace tailWord_1942907 prefixEnd_1942907 443397847993393378278773 := by
  unfold tailWord_1942907
  simp only [CollatzResearch.WordTrace]
  refine ⟨70863639972187235943002975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47242426648124823962001983 70863639972187235943002975)
  ·
    refine ⟨106295459958280853914504463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70863639972187235943002975 106295459958280853914504463)
    ·
      refine ⟨159443189937421280871756695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106295459958280853914504463 159443189937421280871756695)
      ·
        refine ⟨239164784906131921307635043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159443189937421280871756695 239164784906131921307635043)
        ·
          refine ⟨358747177359197881961452565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239164784906131921307635043 358747177359197881961452565)
          ·
            refine ⟨16816273938712400716943089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358747177359197881961452565 16816273938712400716943089)
            ·
              refine ⟨12612205454034300537707317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16816273938712400716943089 12612205454034300537707317)
              ·
                refine ⟨1182394261315715675410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12612205454034300537707317 1182394261315715675410061)
                ·
                  refine ⟨443397847993393378278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182394261315715675410061 443397847993393378278773)
                  ·
                    rfl

theorem cell21_1942907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].length) (baseStart_1942907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942907 prefixEnd_1942907 := by exact prefixLift 1942907
  have htrace : WordTrace (prefixWord ++ tailWord_1942907) baseStart_1942907 baseEnd_1942907 := by
    simpa [prefixWord, tailWord_1942907, baseEnd_1942907] using wordTrace_append hprefix tailTrace_1942907
  have hstable : (prefixWord ++ tailWord_1942907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942907).length < 2 ^ (prefixWord ++ tailWord_1942907).sum := by decide
  have hdescent : baseEnd_1942907 < baseStart_1942907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942910 : List Nat := [4, 2, 3, 2, 2, 8]
def baseStart_1942910 : Nat := 118140960795 + 1942910 * 2 ^ 59
def prefixEnd_1942910 : Nat := 4983230072969 + 3 ^ 40 * 1942910 * 2
def baseEnd_1942910 : Nat := 16422167875343186656621

theorem tailTrace_1942910 : CollatzResearch.WordTrace tailWord_1942910 prefixEnd_1942910 16422167875343186656621 := by
  unfold tailWord_1942910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857968673897045931920273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47242499594117578303574789 8857968673897045931920273)
  ·
    refine ⟨6643476505422784448940205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8857968673897045931920273 6643476505422784448940205)
    ·
      refine ⟨2491303689533544168352577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6643476505422784448940205 2491303689533544168352577)
      ·
        refine ⟨1868477767150158126264433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491303689533544168352577 1868477767150158126264433)
        ·
          refine ⟨1401358325362618594698325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868477767150158126264433 1401358325362618594698325)
          ·
            refine ⟨16422167875343186656621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1401358325362618594698325 16422167875343186656621)
            ·
              rfl

theorem cell21_1942910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 8].length) (baseStart_1942910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942910 prefixEnd_1942910 := by exact prefixLift 1942910
  have htrace : WordTrace (prefixWord ++ tailWord_1942910) baseStart_1942910 baseEnd_1942910 := by
    simpa [prefixWord, tailWord_1942910, baseEnd_1942910] using wordTrace_append hprefix tailTrace_1942910
  have hstable : (prefixWord ++ tailWord_1942910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942910).length < 2 ^ (prefixWord ++ tailWord_1942910).sum := by decide
  have hdescent : baseEnd_1942910 < baseStart_1942910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942972 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_1942972 : Nat := 118140960795 + 1942972 * 2 ^ 59
def prefixEnd_1942972 : Nat := 4983230072969 + 3 ^ 40 * 1942972 * 2
def baseEnd_1942972 : Nat := 443412681878967709695307

theorem tailTrace_1942972 : CollatzResearch.WordTrace tailWord_1942972 prefixEnd_1942972 443412681878967709695307 := by
  unfold tailWord_1942972
  simp only [CollatzResearch.WordTrace]
  refine ⟨35433005358475876022059585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47244007144634501362746113 35433005358475876022059585)
  ·
    refine ⟨26574754018856907016544689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35433005358475876022059585 26574754018856907016544689)
    ·
      refine ⟨19931065514142680262408517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26574754018856907016544689 19931065514142680262408517)
      ·
        refine ⟨3737074783901752549201597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19931065514142680262408517 3737074783901752549201597)
        ·
          refine ⟨1401403043963157205950599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3737074783901752549201597 1401403043963157205950599)
          ·
            refine ⟨2102104565944735808925899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401403043963157205950599 2102104565944735808925899)
            ·
              refine ⟨3153156848917103713388849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102104565944735808925899 3153156848917103713388849)
              ·
                refine ⟨2364867636687827785041637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153156848917103713388849 2364867636687827785041637)
                ·
                  refine ⟨443412681878967709695307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364867636687827785041637 443412681878967709695307)
                  ·
                    rfl

theorem cell21_1942972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_1942972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942972 prefixEnd_1942972 := by exact prefixLift 1942972
  have htrace : WordTrace (prefixWord ++ tailWord_1942972) baseStart_1942972 baseEnd_1942972 := by
    simpa [prefixWord, tailWord_1942972, baseEnd_1942972] using wordTrace_append hprefix tailTrace_1942972
  have hstable : (prefixWord ++ tailWord_1942972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942972).length < 2 ^ (prefixWord ++ tailWord_1942972).sum := by decide
  have hdescent : baseEnd_1942972 < baseStart_1942972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942983 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 3]
def baseStart_1942983 : Nat := 118140960795 + 1942983 * 2 ^ 59
def prefixEnd_1942983 : Nat := 4983230072969 + 3 ^ 40 * 1942983 * 2
def baseEnd_1942983 : Nat := 443415192228834135011951

theorem tailTrace_1942983 : CollatzResearch.WordTrace tailWord_1942983 prefixEnd_1942983 443415192228834135011951 := by
  unfold tailWord_1942983
  simp only [CollatzResearch.WordTrace]
  refine ⟨70866411919911900922769603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47244274613274600615179735 70866411919911900922769603)
  ·
    refine ⟨106299617879867851384154405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70866411919911900922769603 106299617879867851384154405)
    ·
      refine ⟨19931178352475222134528951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106299617879867851384154405 19931178352475222134528951)
      ·
        refine ⟨29896767528712833201793427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931178352475222134528951 29896767528712833201793427)
        ·
          refine ⟨44845151293069249802690141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29896767528712833201793427 44845151293069249802690141)
          ·
            refine ⟨16816931734900968676008803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44845151293069249802690141 16816931734900968676008803)
            ·
              refine ⟨25225397602351453014013205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816931734900968676008803 25225397602351453014013205)
              ·
                refine ⟨1182440512610224360031869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25225397602351453014013205 1182440512610224360031869)
                ·
                  refine ⟨443415192228834135011951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182440512610224360031869 443415192228834135011951)
                  ·
                    rfl

theorem cell21_1942983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].length) (baseStart_1942983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1942983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1942983 prefixEnd_1942983 := by exact prefixLift 1942983
  have htrace : WordTrace (prefixWord ++ tailWord_1942983) baseStart_1942983 baseEnd_1942983 := by
    simpa [prefixWord, tailWord_1942983, baseEnd_1942983] using wordTrace_append hprefix tailTrace_1942983
  have hstable : (prefixWord ++ tailWord_1942983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942983).length < 2 ^ (prefixWord ++ tailWord_1942983).sum := by decide
  have hdescent : baseEnd_1942983 < baseStart_1942983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943093 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 3]
def baseStart_1943093 : Nat := 118140960795 + 1943093 * 2 ^ 59
def prefixEnd_1943093 : Nat := 4983230072969 + 3 ^ 40 * 1943093 * 2
def baseEnd_1943093 : Nat := 443440295727498388178393

theorem tailTrace_1943093 : CollatzResearch.WordTrace tailWord_1943093 prefixEnd_1943093 443440295727498388178393 := by
  unfold tailWord_1943093
  simp only [CollatzResearch.WordTrace]
  refine ⟨70870423949513389709273933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47246949299675593139515955 70870423949513389709273933)
  ·
    refine ⟨26576408981067521140977725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70870423949513389709273933 26576408981067521140977725)
    ·
      refine ⟨9966153367900320427866647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26576408981067521140977725 9966153367900320427866647)
      ·
        refine ⟨14949230051850480641799971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9966153367900320427866647 14949230051850480641799971)
        ·
          refine ⟨22423845077775720962699957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14949230051850480641799971 22423845077775720962699957)
          ·
            refine ⟨2102235476041473840253121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22423845077775720962699957 2102235476041473840253121)
            ·
              refine ⟨1576676607031105380189841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102235476041473840253121 1576676607031105380189841)
              ·
                refine ⟨1182507455273329035142381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576676607031105380189841 1182507455273329035142381)
                ·
                  refine ⟨443440295727498388178393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182507455273329035142381 443440295727498388178393)
                  ·
                    rfl

theorem cell21_1943093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_1943093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943093 prefixEnd_1943093 := by exact prefixLift 1943093
  have htrace : WordTrace (prefixWord ++ tailWord_1943093) baseStart_1943093 baseEnd_1943093 := by
    simpa [prefixWord, tailWord_1943093, baseEnd_1943093] using wordTrace_append hprefix tailTrace_1943093
  have hstable : (prefixWord ++ tailWord_1943093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943093).length < 2 ^ (prefixWord ++ tailWord_1943093).sum := by decide
  have hdescent : baseEnd_1943093 < baseStart_1943093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943186 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1943186 : Nat := 118140960795 + 1943186 * 2 ^ 59
def prefixEnd_1943186 : Nat := 4983230072969 + 3 ^ 40 * 1943186 * 2
def baseEnd_1943186 : Nat := 443461519594550893128203

theorem tailTrace_1943186 : CollatzResearch.WordTrace tailWord_1943186 prefixEnd_1943186 443461519594550893128203 := by
  unfold tailWord_1943186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718453984544116648102353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47249210625450977728272941 17718453984544116648102353)
  ·
    refine ⟨13288840488408087486076765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17718453984544116648102353 13288840488408087486076765)
    ·
      refine ⟨4983315183153032807278787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13288840488408087486076765 4983315183153032807278787)
      ·
        refine ⟨7474972774729549210918181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983315183153032807278787 7474972774729549210918181)
        ·
          refine ⟨1401557395261790477047159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7474972774729549210918181 1401557395261790477047159)
          ·
            refine ⟨2102336092892685715570739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401557395261790477047159 2102336092892685715570739)
            ·
              refine ⟨3153504139339028573356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102336092892685715570739 3153504139339028573356109)
              ·
                refine ⟨1182564052252135715008541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153504139339028573356109 1182564052252135715008541)
                ·
                  refine ⟨443461519594550893128203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182564052252135715008541 443461519594550893128203)
                  ·
                    rfl

theorem cell21_1943186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1943186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943186 prefixEnd_1943186 := by exact prefixLift 1943186
  have htrace : WordTrace (prefixWord ++ tailWord_1943186) baseStart_1943186 baseEnd_1943186 := by
    simpa [prefixWord, tailWord_1943186, baseEnd_1943186] using wordTrace_append hprefix tailTrace_1943186
  have hstable : (prefixWord ++ tailWord_1943186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943186).length < 2 ^ (prefixWord ++ tailWord_1943186).sum := by decide
  have hdescent : baseEnd_1943186 < baseStart_1943186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943346 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1943346 : Nat := 118140960795 + 1943346 * 2 ^ 59
def prefixEnd_1943346 : Nat := 4983230072969 + 3 ^ 40 * 1943346 * 2
def baseEnd_1943346 : Nat := 443498033774426170461209

theorem tailTrace_1943346 : CollatzResearch.WordTrace tailWord_1943346 prefixEnd_1943346 443498033774426170461209 := by
  unfold tailWord_1943346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17719912904399203479558473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47253101078397875945489261 17719912904399203479558473)
  ·
    refine ⟨13289934678299402609668855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17719912904399203479558473 13289934678299402609668855)
    ·
      refine ⟨19934902017449103914503283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13289934678299402609668855 19934902017449103914503283)
      ·
        refine ⟨29902353026173655871754925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19934902017449103914503283 29902353026173655871754925)
        ·
          refine ⟨11213382384815120951908097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29902353026173655871754925 11213382384815120951908097)
          ·
            refine ⟨8410036788611340713931073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11213382384815120951908097 8410036788611340713931073)
            ·
              refine ⟨6307527591458505535448305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410036788611340713931073 6307527591458505535448305)
              ·
                refine ⟨4730645693593879151586229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6307527591458505535448305 4730645693593879151586229)
                ·
                  refine ⟨443498033774426170461209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4730645693593879151586229 443498033774426170461209)
                  ·
                    rfl

theorem cell21_1943346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1943346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943346 prefixEnd_1943346 := by exact prefixLift 1943346
  have htrace : WordTrace (prefixWord ++ tailWord_1943346) baseStart_1943346 baseEnd_1943346 := by
    simpa [prefixWord, tailWord_1943346, baseEnd_1943346] using wordTrace_append hprefix tailTrace_1943346
  have hstable : (prefixWord ++ tailWord_1943346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943346).length < 2 ^ (prefixWord ++ tailWord_1943346).sum := by decide
  have hdescent : baseEnd_1943346 < baseStart_1943346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943349 : List Nat := [1, 3, 3, 1, 4, 2, 2, 5]
def baseStart_1943349 : Nat := 118140960795 + 1943349 * 2 ^ 59
def prefixEnd_1943349 : Nat := 4983230072969 + 3 ^ 40 * 1943349 * 2
def baseEnd_1943349 : Nat := 147832906138432943970401

theorem tailTrace_1943349 : CollatzResearch.WordTrace tailWord_1943349 prefixEnd_1943349 147832906138432943970401 := by
  unfold tailWord_1943349
  simp only [CollatzResearch.WordTrace]
  refine ⟨70879761036585945430593101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47253174024390630287062067 70879761036585945430593101)
  ·
    refine ⟨26579910388719729536472413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70879761036585945430593101 26579910388719729536472413)
    ·
      refine ⟨9967466395769898576177155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26579910388719729536472413 9967466395769898576177155)
      ·
        refine ⟨14951199593654847864265733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967466395769898576177155 14951199593654847864265733)
        ·
          refine ⟨2803349923810283974549825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14951199593654847864265733 2803349923810283974549825)
          ·
            refine ⟨2102512442857712980912369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803349923810283974549825 2102512442857712980912369)
            ·
              refine ⟨1576884332143284735684277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102512442857712980912369 1576884332143284735684277)
              ·
                refine ⟨147832906138432943970401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576884332143284735684277 147832906138432943970401)
                ·
                  rfl

theorem cell21_1943349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].length) (baseStart_1943349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943349 prefixEnd_1943349 := by exact prefixLift 1943349
  have htrace : WordTrace (prefixWord ++ tailWord_1943349) baseStart_1943349 baseEnd_1943349 := by
    simpa [prefixWord, tailWord_1943349, baseEnd_1943349] using wordTrace_append hprefix tailTrace_1943349
  have hstable : (prefixWord ++ tailWord_1943349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943349).length < 2 ^ (prefixWord ++ tailWord_1943349).sum := by decide
  have hdescent : baseEnd_1943349 < baseStart_1943349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943363 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 3]
def baseStart_1943363 : Nat := 118140960795 + 1943363 * 2 ^ 59
def prefixEnd_1943363 : Nat := 4983230072969 + 3 ^ 40 * 1943363 * 2
def baseEnd_1943363 : Nat := 443501913406037918677841

theorem tailTrace_1943363 : CollatzResearch.WordTrace tailWord_1943363 prefixEnd_1943363 443501913406037918677841 := by
  unfold tailWord_1943363
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880271658535225821602743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47253514439023483881068495 70880271658535225821602743)
  ·
    refine ⟨106320407487802838732404115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70880271658535225821602743 106320407487802838732404115)
    ·
      refine ⟨159480611231704258098606173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106320407487802838732404115 159480611231704258098606173)
      ·
        refine ⟨59805229211889096786977315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159480611231704258098606173 59805229211889096786977315)
        ·
          refine ⟨89707843817833645180465973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59805229211889096786977315 89707843817833645180465973)
          ·
            refine ⟨8410110357921904235668685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89707843817833645180465973 8410110357921904235668685)
            ·
              refine ⟨3153791384220714088375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8410110357921904235668685 3153791384220714088375757)
              ·
                refine ⟨1182671769082767783140909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153791384220714088375757 1182671769082767783140909)
                ·
                  refine ⟨443501913406037918677841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182671769082767783140909 443501913406037918677841)
                  ·
                    rfl

theorem cell21_1943363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].length) (baseStart_1943363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943363 prefixEnd_1943363 := by exact prefixLift 1943363
  have htrace : WordTrace (prefixWord ++ tailWord_1943363) baseStart_1943363 baseEnd_1943363 := by
    simpa [prefixWord, tailWord_1943363, baseEnd_1943363] using wordTrace_append hprefix tailTrace_1943363
  have hstable : (prefixWord ++ tailWord_1943363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943363).length < 2 ^ (prefixWord ++ tailWord_1943363).sum := by decide
  have hdescent : baseEnd_1943363 < baseStart_1943363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943391 : List Nat := [1, 1, 2, 3, 1, 5, 2, 6]
def baseStart_1943391 : Nat := 118140960795 + 1943391 * 2 ^ 59
def prefixEnd_1943391 : Nat := 4983230072969 + 3 ^ 40 * 1943391 * 2
def baseEnd_1943391 : Nat := 147836101129172030737039

theorem tailTrace_1943391 : CollatzResearch.WordTrace tailWord_1943391 prefixEnd_1943391 147836101129172030737039 := by
  unfold tailWord_1943391
  simp only [CollatzResearch.WordTrace]
  refine ⟨70881292902433786603622027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47254195268289191069081351 70881292902433786603622027)
  ·
    refine ⟨106321939353650679905433041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70881292902433786603622027 106321939353650679905433041)
    ·
      refine ⟨79741454515238009929074781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106321939353650679905433041 79741454515238009929074781)
      ·
        refine ⟨29903045443214253723403043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79741454515238009929074781 29903045443214253723403043)
        ·
          refine ⟨44854568164821380585104565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29903045443214253723403043 44854568164821380585104565)
          ·
            refine ⟨4205115765452004429853553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44854568164821380585104565 4205115765452004429853553)
            ·
              refine ⟨3153836824089003322390165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205115765452004429853553 3153836824089003322390165)
              ·
                refine ⟨147836101129172030737039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153836824089003322390165 147836101129172030737039)
                ·
                  rfl

theorem cell21_1943391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_1943391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943391 prefixEnd_1943391 := by exact prefixLift 1943391
  have htrace : WordTrace (prefixWord ++ tailWord_1943391) baseStart_1943391 baseEnd_1943391 := by
    simpa [prefixWord, tailWord_1943391, baseEnd_1943391] using wordTrace_append hprefix tailTrace_1943391
  have hstable : (prefixWord ++ tailWord_1943391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943391).length < 2 ^ (prefixWord ++ tailWord_1943391).sum := by decide
  have hdescent : baseEnd_1943391 < baseStart_1943391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943394 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1943394 : Nat := 118140960795 + 1943394 * 2 ^ 59
def prefixEnd_1943394 : Nat := 4983230072969 + 3 ^ 40 * 1943394 * 2
def baseEnd_1943394 : Nat := 443508988028388753661111

theorem tailTrace_1943394 : CollatzResearch.WordTrace tailWord_1943394 prefixEnd_1943394 443508988028388753661111 := by
  unfold tailWord_1943394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720350580355729528995309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47254268214281945410654157 17720350580355729528995309)
  ·
    refine ⟨6645131467633398573373241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17720350580355729528995309 6645131467633398573373241)
    ·
      refine ⟨4983848600725048930029931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645131467633398573373241 4983848600725048930029931)
      ·
        refine ⟨7475772901087573395044897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983848600725048930029931 7475772901087573395044897)
        ·
          refine ⟨5606829675815680046283673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475772901087573395044897 5606829675815680046283673)
          ·
            refine ⟨4205122256861760034712755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5606829675815680046283673 4205122256861760034712755)
            ·
              refine ⟨6307683385292640052069133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205122256861760034712755 6307683385292640052069133)
              ·
                refine ⟨2365381269484740019525925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6307683385292640052069133 2365381269484740019525925)
                ·
                  refine ⟨443508988028388753661111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365381269484740019525925 443508988028388753661111)
                  ·
                    rfl

theorem cell21_1943394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1943394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943394 prefixEnd_1943394 := by exact prefixLift 1943394
  have htrace : WordTrace (prefixWord ++ tailWord_1943394) baseStart_1943394 baseEnd_1943394 := by
    simpa [prefixWord, tailWord_1943394, baseEnd_1943394] using wordTrace_append hprefix tailTrace_1943394
  have hstable : (prefixWord ++ tailWord_1943394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943394).length < 2 ^ (prefixWord ++ tailWord_1943394).sum := by decide
  have hdescent : baseEnd_1943394 < baseStart_1943394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943453 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1943453 : Nat := 118140960795 + 1943453 * 2 ^ 59
def prefixEnd_1943453 : Nat := 4983230072969 + 3 ^ 40 * 1943453 * 2
def baseEnd_1943453 : Nat := 443522452632217762177657

theorem tailTrace_1943453 : CollatzResearch.WordTrace tailWord_1943453 prefixEnd_1943453 443522452632217762177657 := by
  unfold tailWord_1943453
  simp only [CollatzResearch.WordTrace]
  refine ⟨70883554228209171192379013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47255702818806114128252675 70883554228209171192379013)
  ·
    refine ⟨13290666417789219598571065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70883554228209171192379013 13290666417789219598571065)
    ·
      refine ⟨9967999813341914698928299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13290666417789219598571065 9967999813341914698928299)
      ·
        refine ⟨14951999720012872048392449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967999813341914698928299 14951999720012872048392449)
        ·
          refine ⟨11213999790009654036294337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14951999720012872048392449 11213999790009654036294337)
          ·
            refine ⟨8410499842507240527220753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11213999790009654036294337 8410499842507240527220753)
            ·
              refine ⟨6307874881880430395415565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410499842507240527220753 6307874881880430395415565)
              ·
                refine ⟨2365453080705161398280837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6307874881880430395415565 2365453080705161398280837)
                ·
                  refine ⟨443522452632217762177657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365453080705161398280837 443522452632217762177657)
                  ·
                    rfl

theorem cell21_1943453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1943453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943453 prefixEnd_1943453 := by exact prefixLift 1943453
  have htrace : WordTrace (prefixWord ++ tailWord_1943453) baseStart_1943453 baseEnd_1943453 := by
    simpa [prefixWord, tailWord_1943453, baseEnd_1943453] using wordTrace_append hprefix tailTrace_1943453
  have hstable : (prefixWord ++ tailWord_1943453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943453).length < 2 ^ (prefixWord ++ tailWord_1943453).sum := by decide
  have hdescent : baseEnd_1943453 < baseStart_1943453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943481 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_1943481 : Nat := 118140960795 + 1943481 * 2 ^ 59
def prefixEnd_1943481 : Nat := 4983230072969 + 3 ^ 40 * 1943481 * 2
def baseEnd_1943481 : Nat := 443528842613695935710933

theorem tailTrace_1943481 : CollatzResearch.WordTrace tailWord_1943481 prefixEnd_1943481 443528842613695935710933 := by
  unfold tailWord_1943481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70884575472107731974398297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47256383648071821316265531 70884575472107731974398297)
  ·
    refine ⟨53163431604080798980798723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70884575472107731974398297 53163431604080798980798723)
    ·
      refine ⟨79745147406121198471198085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53163431604080798980798723 79745147406121198471198085)
      ·
        refine ⟨14952215138647724713349641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79745147406121198471198085 14952215138647724713349641)
        ·
          refine ⟨11214161353985793535012231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952215138647724713349641 11214161353985793535012231)
          ·
            refine ⟨16821242030978690302518347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214161353985793535012231 16821242030978690302518347)
            ·
              refine ⟨25231863046468035453777521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16821242030978690302518347 25231863046468035453777521)
              ·
                refine ⟨18923897284851026590333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25231863046468035453777521 18923897284851026590333141)
                ·
                  refine ⟨443528842613695935710933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18923897284851026590333141 443528842613695935710933)
                  ·
                    rfl

theorem cell21_1943481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_1943481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943481 prefixEnd_1943481 := by exact prefixLift 1943481
  have htrace : WordTrace (prefixWord ++ tailWord_1943481) baseStart_1943481 baseEnd_1943481 := by
    simpa [prefixWord, tailWord_1943481, baseEnd_1943481] using wordTrace_append hprefix tailTrace_1943481
  have hstable : (prefixWord ++ tailWord_1943481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943481).length < 2 ^ (prefixWord ++ tailWord_1943481).sum := by decide
  have hdescent : baseEnd_1943481 < baseStart_1943481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943484 : List Nat := [2, 2, 2, 5, 1, 1, 8]
def baseStart_1943484 : Nat := 118140960795 + 1943484 * 2 ^ 59
def prefixEnd_1943484 : Nat := 4983230072969 + 3 ^ 40 * 1943484 * 2
def baseEnd_1943484 : Nat := 49281058583840955240103

theorem tailTrace_1943484 : CollatzResearch.WordTrace tailWord_1943484 prefixEnd_1943484 49281058583840955240103 := by
  unfold tailWord_1943484
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442342445548431743378753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47256456594064575657838337 35442342445548431743378753)
  ·
    refine ⟨26581756834161323807534065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35442342445548431743378753 26581756834161323807534065)
    ·
      refine ⟨19936317625620992855650549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26581756834161323807534065 19936317625620992855650549)
      ·
        refine ⟨1869029777401968080217239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19936317625620992855650549 1869029777401968080217239)
        ·
          refine ⟨2803544666102952120325859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869029777401968080217239 2803544666102952120325859)
          ·
            refine ⟨4205316999154428180488789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803544666102952120325859 4205316999154428180488789)
            ·
              refine ⟨49281058583840955240103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4205316999154428180488789 49281058583840955240103)
              ·
                rfl

theorem cell21_1943484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 8].length) (baseStart_1943484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943484 prefixEnd_1943484 := by exact prefixLift 1943484
  have htrace : WordTrace (prefixWord ++ tailWord_1943484) baseStart_1943484 baseEnd_1943484 := by
    simpa [prefixWord, tailWord_1943484, baseEnd_1943484] using wordTrace_append hprefix tailTrace_1943484
  have hstable : (prefixWord ++ tailWord_1943484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943484).length < 2 ^ (prefixWord ++ tailWord_1943484).sum := by decide
  have hdescent : baseEnd_1943484 < baseStart_1943484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943602 : List Nat := [3, 2, 1, 1, 2, 12]
def baseStart_1943602 : Nat := 118140960795 + 1943602 * 2 ^ 59
def prefixEnd_1943602 : Nat := 4983230072969 + 3 ^ 40 * 1943602 * 2
def baseEnd_1943602 : Nat := 16428016906008393118297

theorem tailTrace_1943602 : CollatzResearch.WordTrace tailWord_1943602 prefixEnd_1943602 16428016906008393118297 := by
  unfold tailWord_1943602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722247176167342409888265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47259325803112913093035373 17722247176167342409888265)
  ·
    refine ⟨13291685382125506807416199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17722247176167342409888265 13291685382125506807416199)
    ·
      refine ⟨19937528073188260211124299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291685382125506807416199 19937528073188260211124299)
      ·
        refine ⟨29906292109782390316686449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19937528073188260211124299 29906292109782390316686449)
        ·
          refine ⟨22429719082336792737514837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29906292109782390316686449 22429719082336792737514837)
          ·
            refine ⟨16428016906008393118297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22429719082336792737514837 16428016906008393118297)
            ·
              rfl

theorem cell21_1943602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 12].length) (baseStart_1943602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943602 prefixEnd_1943602 := by exact prefixLift 1943602
  have htrace : WordTrace (prefixWord ++ tailWord_1943602) baseStart_1943602 baseEnd_1943602 := by
    simpa [prefixWord, tailWord_1943602, baseEnd_1943602] using wordTrace_append hprefix tailTrace_1943602
  have hstable : (prefixWord ++ tailWord_1943602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943602).length < 2 ^ (prefixWord ++ tailWord_1943602).sum := by decide
  have hdescent : baseEnd_1943602 < baseStart_1943602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943622 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1943622 : Nat := 118140960795 + 1943622 * 2 ^ 59
def prefixEnd_1943622 : Nat := 4983230072969 + 3 ^ 40 * 1943622 * 2
def baseEnd_1943622 : Nat := 443561020734711023860645

theorem tailTrace_1943622 : CollatzResearch.WordTrace tailWord_1943622 prefixEnd_1943622 443561020734711023860645 := by
  unfold tailWord_1943622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215303692643653532977535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47259812109731275370187413 2215303692643653532977535)
  ·
    refine ⟨3322955538965480299466303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215303692643653532977535 3322955538965480299466303)
    ·
      refine ⟨4984433308448220449199455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322955538965480299466303 4984433308448220449199455)
      ·
        refine ⟨7476649962672330673799183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984433308448220449199455 7476649962672330673799183)
        ·
          refine ⟨11214974944008496010698775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476649962672330673799183 11214974944008496010698775)
          ·
            refine ⟨16822462416012744016048163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214974944008496010698775 16822462416012744016048163)
            ·
              refine ⟨25233693624019116024072245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822462416012744016048163 25233693624019116024072245)
              ·
                refine ⟨2365658777251792127256773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25233693624019116024072245 2365658777251792127256773)
                ·
                  refine ⟨443561020734711023860645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365658777251792127256773 443561020734711023860645)
                  ·
                    rfl

theorem cell21_1943622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1943622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943622 prefixEnd_1943622 := by exact prefixLift 1943622
  have htrace : WordTrace (prefixWord ++ tailWord_1943622) baseStart_1943622 baseEnd_1943622 := by
    simpa [prefixWord, tailWord_1943622, baseEnd_1943622] using wordTrace_append hprefix tailTrace_1943622
  have hstable : (prefixWord ++ tailWord_1943622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943622).length < 2 ^ (prefixWord ++ tailWord_1943622).sum := by decide
  have hdescent : baseEnd_1943622 < baseStart_1943622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943664 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_1943664 : Nat := 118140960795 + 1943664 * 2 ^ 59
def prefixEnd_1943664 : Nat := 4983230072969 + 3 ^ 40 * 1943664 * 2
def baseEnd_1943664 : Nat := 443570605706928284160559

theorem tailTrace_1943664 : CollatzResearch.WordTrace tailWord_1943664 prefixEnd_1943664 443570605706928284160559 := by
  unfold tailWord_1943664
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445625015222377114155023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47260833353629836152206697 35445625015222377114155023)
  ·
    refine ⟨53168437522833565671232535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35445625015222377114155023 53168437522833565671232535)
    ·
      refine ⟨79752656284250348506848803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53168437522833565671232535 79752656284250348506848803)
      ·
        refine ⟨119628984426375522760273205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79752656284250348506848803 119628984426375522760273205)
        ·
          refine ⟨11215217289972705258775613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119628984426375522760273205 11215217289972705258775613)
          ·
            refine ⟨4205706483739764472040855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11215217289972705258775613 4205706483739764472040855)
            ·
              refine ⟨6308559725609646708061283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205706483739764472040855 6308559725609646708061283)
              ·
                refine ⟨9462839588414470062091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308559725609646708061283 9462839588414470062091925)
                ·
                  refine ⟨443570605706928284160559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9462839588414470062091925 443570605706928284160559)
                  ·
                    rfl

theorem cell21_1943664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_1943664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943664 prefixEnd_1943664 := by exact prefixLift 1943664
  have htrace : WordTrace (prefixWord ++ tailWord_1943664) baseStart_1943664 baseEnd_1943664 := by
    simpa [prefixWord, tailWord_1943664, baseEnd_1943664] using wordTrace_append hprefix tailTrace_1943664
  have hstable : (prefixWord ++ tailWord_1943664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943664).length < 2 ^ (prefixWord ++ tailWord_1943664).sum := by decide
  have hdescent : baseEnd_1943664 < baseStart_1943664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943732 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1943732 : Nat := 118140960795 + 1943732 * 2 ^ 59
def prefixEnd_1943732 : Nat := 4983230072969 + 3 ^ 40 * 1943732 * 2
def baseEnd_1943732 : Nat := 443586124233375277027087

theorem tailTrace_1943732 : CollatzResearch.WordTrace tailWord_1943732 prefixEnd_1943732 443586124233375277027087 := by
  unfold tailWord_1943732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35446865097099200920892725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47262486796132267894523633 35446865097099200920892725)
  ·
    refine ⟨3323143602853050086333693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35446865097099200920892725 3323143602853050086333693)
    ·
      refine ⟨1246178851069893782375135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3323143602853050086333693 1246178851069893782375135)
      ·
        refine ⟨1869268276604840673562703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246178851069893782375135 1869268276604840673562703)
        ·
          refine ⟨2803902414907261010344055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869268276604840673562703 2803902414907261010344055)
          ·
            refine ⟨4205853622360891515516083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803902414907261010344055 4205853622360891515516083)
            ·
              refine ⟨6308780433541337273274125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205853622360891515516083 6308780433541337273274125)
              ·
                refine ⟨2365792662578001477477797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6308780433541337273274125 2365792662578001477477797)
                ·
                  refine ⟨443586124233375277027087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365792662578001477477797 443586124233375277027087)
                  ·
                    rfl

theorem cell21_1943732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1943732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943732 prefixEnd_1943732 := by exact prefixLift 1943732
  have htrace : WordTrace (prefixWord ++ tailWord_1943732) baseStart_1943732 baseEnd_1943732 := by
    simpa [prefixWord, tailWord_1943732, baseEnd_1943732] using wordTrace_append hprefix tailTrace_1943732
  have hstable : (prefixWord ++ tailWord_1943732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943732).length < 2 ^ (prefixWord ++ tailWord_1943732).sum := by decide
  have hdescent : baseEnd_1943732 < baseStart_1943732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943754 : List Nat := [3, 1, 2, 1, 3, 1, 1, 9]
def baseStart_1943754 : Nat := 118140960795 + 1943754 * 2 ^ 59
def prefixEnd_1943754 : Nat := 4983230072969 + 3 ^ 40 * 1943754 * 2
def baseEnd_1943754 : Nat := 147863714977702709220125

theorem tailTrace_1943754 : CollatzResearch.WordTrace tailWord_1943754 prefixEnd_1943754 147863714977702709220125 := by
  unfold tailWord_1943754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723633150029674899771579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47263021733412466399390877 17723633150029674899771579)
  ·
    refine ⟨26585449725044512349657369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723633150029674899771579 26585449725044512349657369)
    ·
      refine ⟨19939087293783384262243027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26585449725044512349657369 19939087293783384262243027)
      ·
        refine ⟨29908630940675076393364541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19939087293783384262243027 29908630940675076393364541)
        ·
          refine ⟨11215736602753153647511703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29908630940675076393364541 11215736602753153647511703)
          ·
            refine ⟨16823604904129730471267555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215736602753153647511703 16823604904129730471267555)
            ·
              refine ⟨25235407356194595706901333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16823604904129730471267555 25235407356194595706901333)
              ·
                refine ⟨147863714977702709220125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25235407356194595706901333 147863714977702709220125)
                ·
                  rfl

theorem cell21_1943754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_1943754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943754 prefixEnd_1943754 := by exact prefixLift 1943754
  have htrace : WordTrace (prefixWord ++ tailWord_1943754) baseStart_1943754 baseEnd_1943754 := by
    simpa [prefixWord, tailWord_1943754, baseEnd_1943754] using wordTrace_append hprefix tailTrace_1943754
  have hstable : (prefixWord ++ tailWord_1943754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943754).length < 2 ^ (prefixWord ++ tailWord_1943754).sum := by decide
  have hdescent : baseEnd_1943754 < baseStart_1943754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943861 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1943861 : Nat := 118140960795 + 1943861 * 2 ^ 59
def prefixEnd_1943861 : Nat := 4983230072969 + 3 ^ 40 * 1943861 * 2
def baseEnd_1943861 : Nat := 443615563790899719376823

theorem tailTrace_1943861 : CollatzResearch.WordTrace tailWord_1943861 prefixEnd_1943861 443615563790899719376823 := by
  unfold tailWord_1943861
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898435210731056873231437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47265623473820704582154291 70898435210731056873231437)
  ·
    refine ⟨26586913204024146327461789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70898435210731056873231437 26586913204024146327461789)
    ·
      refine ⟨9970092451509054872798171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26586913204024146327461789 9970092451509054872798171)
      ·
        refine ⟨14955138677263582309197257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970092451509054872798171 14955138677263582309197257)
        ·
          refine ⟨11216354007947686731897943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14955138677263582309197257 11216354007947686731897943)
          ·
            refine ⟨16824531011921530097846915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216354007947686731897943 16824531011921530097846915)
            ·
              refine ⟨25236796517882295146770373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824531011921530097846915 25236796517882295146770373)
              ·
                refine ⟨4731899347102930340019445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25236796517882295146770373 4731899347102930340019445)
                ·
                  refine ⟨443615563790899719376823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731899347102930340019445 443615563790899719376823)
                  ·
                    rfl

theorem cell21_1943861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1943861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943861 prefixEnd_1943861 := by exact prefixLift 1943861
  have htrace : WordTrace (prefixWord ++ tailWord_1943861) baseStart_1943861 baseEnd_1943861 := by
    simpa [prefixWord, tailWord_1943861, baseEnd_1943861] using wordTrace_append hprefix tailTrace_1943861
  have hstable : (prefixWord ++ tailWord_1943861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943861).length < 2 ^ (prefixWord ++ tailWord_1943861).sum := by decide
  have hdescent : baseEnd_1943861 < baseStart_1943861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943875 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_1943875 : Nat := 118140960795 + 1943875 * 2 ^ 59
def prefixEnd_1943875 : Nat := 4983230072969 + 3 ^ 40 * 1943875 * 2
def baseEnd_1943875 : Nat := 443618758781638806143461

theorem tailTrace_1943875 : CollatzResearch.WordTrace tailWord_1943875 prefixEnd_1943875 443618758781638806143461 := by
  unfold tailWord_1943875
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898945832680337264241079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47265963888453558176160719 70898945832680337264241079)
  ·
    refine ⟨106348418749020505896361619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70898945832680337264241079 106348418749020505896361619)
    ·
      refine ⟨159522628123530758844542429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106348418749020505896361619 159522628123530758844542429)
      ·
        refine ⟨59820985546324034566703411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159522628123530758844542429 59820985546324034566703411)
        ·
          refine ⟨89731478319486051850055117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59820985546324034566703411 89731478319486051850055117)
          ·
            refine ⟨33649304369807269443770669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89731478319486051850055117 33649304369807269443770669)
            ·
              refine ⟨12618489138677726041414001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33649304369807269443770669 12618489138677726041414001)
              ·
                refine ⟨9463866854008294531060501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12618489138677726041414001 9463866854008294531060501)
                ·
                  refine ⟨443618758781638806143461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9463866854008294531060501 443618758781638806143461)
                  ·
                    rfl

theorem cell21_1943875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_1943875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943875 prefixEnd_1943875 := by exact prefixLift 1943875
  have htrace : WordTrace (prefixWord ++ tailWord_1943875) baseStart_1943875 baseEnd_1943875 := by
    simpa [prefixWord, tailWord_1943875, baseEnd_1943875] using wordTrace_append hprefix tailTrace_1943875
  have hstable : (prefixWord ++ tailWord_1943875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943875).length < 2 ^ (prefixWord ++ tailWord_1943875).sum := by decide
  have hdescent : baseEnd_1943875 < baseStart_1943875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943892 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1943892 : Nat := 118140960795 + 1943892 * 2 ^ 59
def prefixEnd_1943892 : Nat := 4983230072969 + 3 ^ 40 * 1943892 * 2
def baseEnd_1943892 : Nat := 443622638413250554360093

theorem tailTrace_1943892 : CollatzResearch.WordTrace tailWord_1943892 prefixEnd_1943892 443622638413250554360093 := by
  unfold tailWord_1943892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449782936809374583804965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47266377249079166111739953 35449782936809374583804965)
  ·
    refine ⟨6646834300651757734463431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35449782936809374583804965 6646834300651757734463431)
    ·
      refine ⟨9970251450977636601695147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646834300651757734463431 9970251450977636601695147)
      ·
        refine ⟨14955377176466454902542721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9970251450977636601695147 14955377176466454902542721)
        ·
          refine ⟨11216532882349841176907041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14955377176466454902542721 11216532882349841176907041)
          ·
            refine ⟨8412399661762380882680281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11216532882349841176907041 8412399661762380882680281)
            ·
              refine ⟨6309299746321785662010211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412399661762380882680281 6309299746321785662010211)
              ·
                refine ⟨9463949619482678493015317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309299746321785662010211 9463949619482678493015317)
                ·
                  refine ⟨443622638413250554360093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9463949619482678493015317 443622638413250554360093)
                  ·
                    rfl

theorem cell21_1943892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1943892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943892 prefixEnd_1943892 := by exact prefixLift 1943892
  have htrace : WordTrace (prefixWord ++ tailWord_1943892) baseStart_1943892 baseEnd_1943892 := by
    simpa [prefixWord, tailWord_1943892, baseEnd_1943892] using wordTrace_append hprefix tailTrace_1943892
  have hstable : (prefixWord ++ tailWord_1943892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943892).length < 2 ^ (prefixWord ++ tailWord_1943892).sum := by decide
  have hdescent : baseEnd_1943892 < baseStart_1943892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943895 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 3]
def baseStart_1943895 : Nat := 118140960795 + 1943895 * 2 ^ 59
def prefixEnd_1943895 : Nat := 4983230072969 + 3 ^ 40 * 1943895 * 2
def baseEnd_1943895 : Nat := 443623323054123215810087

theorem tailTrace_1943895 : CollatzResearch.WordTrace tailWord_1943895 prefixEnd_1943895 443623323054123215810087 := by
  unfold tailWord_1943895
  simp only [CollatzResearch.WordTrace]
  refine ⟨70899675292607880679969139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47266450195071920453312759 70899675292607880679969139)
  ·
    refine ⟨106349512938911821019953709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70899675292607880679969139 106349512938911821019953709)
    ·
      refine ⟨39881067352091932882482641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106349512938911821019953709 39881067352091932882482641)
      ·
        refine ⟨29910800514068949661861981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39881067352091932882482641 29910800514068949661861981)
        ·
          refine ⟨11216550192775856123198243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29910800514068949661861981 11216550192775856123198243)
          ·
            refine ⟨16824825289163784184797365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216550192775856123198243 16824825289163784184797365)
            ·
              refine ⟨1577327370859104767324753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16824825289163784184797365 1577327370859104767324753)
              ·
                refine ⟨1182995528144328575493565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577327370859104767324753 1182995528144328575493565)
                ·
                  refine ⟨443623323054123215810087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182995528144328575493565 443623323054123215810087)
                  ·
                    rfl

theorem cell21_1943895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].length) (baseStart_1943895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943895 prefixEnd_1943895 := by exact prefixLift 1943895
  have htrace : WordTrace (prefixWord ++ tailWord_1943895) baseStart_1943895 baseEnd_1943895 := by
    simpa [prefixWord, tailWord_1943895, baseEnd_1943895] using wordTrace_append hprefix tailTrace_1943895
  have hstable : (prefixWord ++ tailWord_1943895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943895).length < 2 ^ (prefixWord ++ tailWord_1943895).sum := by decide
  have hdescent : baseEnd_1943895 < baseStart_1943895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943909 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 4]
def baseStart_1943909 : Nat := 118140960795 + 1943909 * 2 ^ 59
def prefixEnd_1943909 : Nat := 4983230072969 + 3 ^ 40 * 1943909 * 2
def baseEnd_1943909 : Nat := 443626518044862302576725

theorem tailTrace_1943909 : CollatzResearch.WordTrace tailWord_1943909 prefixEnd_1943909 443626518044862302576725 := by
  unfold tailWord_1943909
  simp only [CollatzResearch.WordTrace]
  refine ⟨70900185914557161070978781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47266790609704774047319187 70900185914557161070978781)
  ·
    refine ⟨26587569717958935401617043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70900185914557161070978781 26587569717958935401617043)
    ·
      refine ⟨39881354576938403102425565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26587569717958935401617043 39881354576938403102425565)
      ·
        refine ⟨14955507966351901163409587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39881354576938403102425565 14955507966351901163409587)
        ·
          refine ⟨22433261949527851745114381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955507966351901163409587 22433261949527851745114381)
          ·
            refine ⟨8412473231072944404417893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22433261949527851745114381 8412473231072944404417893)
            ·
              refine ⟨1577338730826177075828355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8412473231072944404417893 1577338730826177075828355)
              ·
                refine ⟨2366008096239265613742533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577338730826177075828355 2366008096239265613742533)
                ·
                  refine ⟨443626518044862302576725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366008096239265613742533 443626518044862302576725)
                  ·
                    rfl

theorem cell21_1943909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_1943909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943909 prefixEnd_1943909 := by exact prefixLift 1943909
  have htrace : WordTrace (prefixWord ++ tailWord_1943909) baseStart_1943909 baseEnd_1943909 := by
    simpa [prefixWord, tailWord_1943909, baseEnd_1943909] using wordTrace_append hprefix tailTrace_1943909
  have hstable : (prefixWord ++ tailWord_1943909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943909).length < 2 ^ (prefixWord ++ tailWord_1943909).sum := by decide
  have hdescent : baseEnd_1943909 < baseStart_1943909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943946 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_1943946 : Nat := 118140960795 + 1943946 * 2 ^ 59
def prefixEnd_1943946 : Nat := 4983230072969 + 3 ^ 40 * 1943946 * 2
def baseEnd_1943946 : Nat := 443634961948958460459983

theorem tailTrace_1943946 : CollatzResearch.WordTrace tailWord_1943946 prefixEnd_1943946 443634961948958460459983 := by
  unfold tailWord_1943946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725383853855779097518923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47267690276948744260050461 17725383853855779097518923)
  ·
    refine ⟨26588075780783668646278385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17725383853855779097518923 26588075780783668646278385)
    ·
      refine ⟨19941056835587751484708789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26588075780783668646278385 19941056835587751484708789)
      ·
        refine ⟨1869474078336351701691449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19941056835587751484708789 1869474078336351701691449)
        ·
          refine ⟨1402105558752263776268587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869474078336351701691449 1402105558752263776268587)
          ·
            refine ⟨2103158338128395664402881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402105558752263776268587 2103158338128395664402881)
            ·
              refine ⟨1577368753596296748302161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103158338128395664402881 1577368753596296748302161)
              ·
                refine ⟨1183026565197222561226621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577368753596296748302161 1183026565197222561226621)
                ·
                  refine ⟨443634961948958460459983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183026565197222561226621 443634961948958460459983)
                  ·
                    rfl

theorem cell21_1943946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_1943946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943946 prefixEnd_1943946 := by exact prefixLift 1943946
  have htrace : WordTrace (prefixWord ++ tailWord_1943946) baseStart_1943946 baseEnd_1943946 := by
    simpa [prefixWord, tailWord_1943946, baseEnd_1943946] using wordTrace_append hprefix tailTrace_1943946
  have hstable : (prefixWord ++ tailWord_1943946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943946).length < 2 ^ (prefixWord ++ tailWord_1943946).sum := by decide
  have hdescent : baseEnd_1943946 < baseStart_1943946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943968 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_1943968 : Nat := 118140960795 + 1943968 * 2 ^ 59
def prefixEnd_1943968 : Nat := 4983230072969 + 3 ^ 40 * 1943968 * 2
def baseEnd_1943968 : Nat := 443639982648691311093271

theorem tailTrace_1943968 : CollatzResearch.WordTrace tailWord_1943968 prefixEnd_1943968 443639982648691311093271 := by
  unfold tailWord_1943968
  simp only [CollatzResearch.WordTrace]
  refine ⟨35451168910671707073688279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47268225214228942764917705 35451168910671707073688279)
  ·
    refine ⟨53176753366007560610532419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35451168910671707073688279 53176753366007560610532419)
    ·
      refine ⟨79765130049011340915798629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53176753366007560610532419 79765130049011340915798629)
      ·
        refine ⟨14955961884189626421712243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79765130049011340915798629 14955961884189626421712243)
        ·
          refine ⟨22433942826284439632568365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14955961884189626421712243 22433942826284439632568365)
          ·
            refine ⟨8412728559856664862213137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22433942826284439632568365 8412728559856664862213137)
            ·
              refine ⟨6309546419892498646659853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412728559856664862213137 6309546419892498646659853)
              ·
                refine ⟨2366079907459686992497445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309546419892498646659853 2366079907459686992497445)
                ·
                  refine ⟨443639982648691311093271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366079907459686992497445 443639982648691311093271)
                  ·
                    rfl

theorem cell21_1943968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_1943968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1943968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1943968 prefixEnd_1943968 := by exact prefixLift 1943968
  have htrace : WordTrace (prefixWord ++ tailWord_1943968) baseStart_1943968 baseEnd_1943968 := by
    simpa [prefixWord, tailWord_1943968, baseEnd_1943968] using wordTrace_append hprefix tailTrace_1943968
  have hstable : (prefixWord ++ tailWord_1943968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943968).length < 2 ^ (prefixWord ++ tailWord_1943968).sum := by decide
  have hdescent : baseEnd_1943968 < baseStart_1943968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944078 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1944078 : Nat := 118140960795 + 1944078 * 2 ^ 59
def prefixEnd_1944078 : Nat := 4983230072969 + 3 ^ 40 * 1944078 * 2
def baseEnd_1944078 : Nat := 443665086147355564259713

theorem tailTrace_1944078 : CollatzResearch.WordTrace tailWord_1944078 prefixEnd_1944078 443665086147355564259713 := by
  unfold tailWord_1944078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863293731368112866735111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47270899900629935289253925 8863293731368112866735111)
  ·
    refine ⟨13294940597052169300102667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863293731368112866735111 13294940597052169300102667)
    ·
      refine ⟨19942410895578253950154001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294940597052169300102667 19942410895578253950154001)
      ·
        refine ⟨14956808171683690462615501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19942410895578253950154001 14956808171683690462615501)
        ·
          refine ⟨5608803064381383923480813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14956808171683690462615501 5608803064381383923480813)
          ·
            refine ⟨2103301149143018971305305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5608803064381383923480813 2103301149143018971305305)
            ·
              refine ⟨1577475861857264228478979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103301149143018971305305 1577475861857264228478979)
              ·
                refine ⟨2366213792785896342718469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577475861857264228478979 2366213792785896342718469)
                ·
                  refine ⟨443665086147355564259713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366213792785896342718469 443665086147355564259713)
                  ·
                    rfl

theorem cell21_1944078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1944078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944078 prefixEnd_1944078 := by exact prefixLift 1944078
  have htrace : WordTrace (prefixWord ++ tailWord_1944078) baseStart_1944078 baseEnd_1944078 := by
    simpa [prefixWord, tailWord_1944078, baseEnd_1944078] using wordTrace_append hprefix tailTrace_1944078
  have hstable : (prefixWord ++ tailWord_1944078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944078).length < 2 ^ (prefixWord ++ tailWord_1944078).sum := by decide
  have hdescent : baseEnd_1944078 < baseStart_1944078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944109 : List Nat := [1, 5, 4, 1, 2, 8]
def baseStart_1944109 : Nat := 118140960795 + 1944109 * 2 ^ 59
def prefixEnd_1944109 : Nat := 4983230072969 + 3 ^ 40 * 1944109 * 2
def baseEnd_1944109 : Nat := 16432302250729866638629

theorem tailTrace_1944109 : CollatzResearch.WordTrace tailWord_1944109 prefixEnd_1944109 16432302250729866638629 := by
  unfold tailWord_1944109
  simp only [CollatzResearch.WordTrace]
  refine ⟨70907480513832595228259381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47271653675888396818839587 70907480513832595228259381)
  ·
    refine ⟨6647576298171805802649317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70907480513832595228259381 6647576298171805802649317)
    ·
      refine ⟨1246420555907213587996747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6647576298171805802649317 1246420555907213587996747)
      ·
        refine ⟨1869630833860820381995121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246420555907213587996747 1869630833860820381995121)
        ·
          refine ⟨1402223125395615286496341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869630833860820381995121 1402223125395615286496341)
          ·
            refine ⟨16432302250729866638629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1402223125395615286496341 16432302250729866638629)
            ·
              rfl

theorem cell21_1944109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 8].length) (baseStart_1944109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944109 prefixEnd_1944109 := by exact prefixLift 1944109
  have htrace : WordTrace (prefixWord ++ tailWord_1944109) baseStart_1944109 baseEnd_1944109 := by
    simpa [prefixWord, tailWord_1944109, baseEnd_1944109] using wordTrace_append hprefix tailTrace_1944109
  have hstable : (prefixWord ++ tailWord_1944109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944109).length < 2 ^ (prefixWord ++ tailWord_1944109).sum := by decide
  have hdescent : baseEnd_1944109 < baseStart_1944109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944120 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_1944120 : Nat := 118140960795 + 1944120 * 2 ^ 59
def prefixEnd_1944120 : Nat := 4983230072969 + 3 ^ 40 * 1944120 * 2
def baseEnd_1944120 : Nat := 443674671119572824559627

theorem tailTrace_1944120 : CollatzResearch.WordTrace tailWord_1944120 prefixEnd_1944120 443674671119572824559627 := by
  unfold tailWord_1944120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35453940858396372053454907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47271921144528496071273209 35453940858396372053454907)
  ·
    refine ⟨53180911287594558080182361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35453940858396372053454907 53180911287594558080182361)
    ·
      refine ⟨39885683465695918560136771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53180911287594558080182361 39885683465695918560136771)
      ·
        refine ⟨59828525198543877840205157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39885683465695918560136771 59828525198543877840205157)
        ·
          refine ⟨11217848474726977095038467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59828525198543877840205157 11217848474726977095038467)
          ·
            refine ⟨16826772712090465642557701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217848474726977095038467 16826772712090465642557701)
            ·
              refine ⟨3155019883516962307979569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16826772712090465642557701 3155019883516962307979569)
              ·
                refine ⟨2366264912637721730984677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155019883516962307979569 2366264912637721730984677)
                ·
                  refine ⟨443674671119572824559627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366264912637721730984677 443674671119572824559627)
                  ·
                    rfl

theorem cell21_1944120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_1944120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944120 prefixEnd_1944120 := by exact prefixLift 1944120
  have htrace : WordTrace (prefixWord ++ tailWord_1944120) baseStart_1944120 baseEnd_1944120 := by
    simpa [prefixWord, tailWord_1944120, baseEnd_1944120] using wordTrace_append hprefix tailTrace_1944120
  have hstable : (prefixWord ++ tailWord_1944120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944120).length < 2 ^ (prefixWord ++ tailWord_1944120).sum := by decide
  have hdescent : baseEnd_1944120 < baseStart_1944120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944179 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_1944179 : Nat := 118140960795 + 1944179 * 2 ^ 59
def prefixEnd_1944179 : Nat := 4983230072969 + 3 ^ 40 * 1944179 * 2
def baseEnd_1944179 : Nat := 443688135723401833076173

theorem tailTrace_1944179 : CollatzResearch.WordTrace tailWord_1944179 prefixEnd_1944179 443688135723401833076173 := by
  unfold tailWord_1944179
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910033623578997183307591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47273355749052664788871727 70910033623578997183307591)
  ·
    refine ⟨106365050435368495774961387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70910033623578997183307591 106365050435368495774961387)
    ·
      refine ⟨159547575653052743662442081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106365050435368495774961387 159547575653052743662442081)
      ·
        refine ⟨119660681739789557746831561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159547575653052743662442081 119660681739789557746831561)
        ·
          refine ⟨89745511304842168310123671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119660681739789557746831561 89745511304842168310123671)
          ·
            refine ⟨134618266957263252465185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89745511304842168310123671 134618266957263252465185507)
            ·
              refine ⟨201927400435894878697778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134618266957263252465185507 201927400435894878697778261)
              ·
                refine ⟨2366336723858143109739589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 201927400435894878697778261 2366336723858143109739589)
                ·
                  refine ⟨443688135723401833076173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366336723858143109739589 443688135723401833076173)
                  ·
                    rfl

theorem cell21_1944179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_1944179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944179 prefixEnd_1944179 := by exact prefixLift 1944179
  have htrace : WordTrace (prefixWord ++ tailWord_1944179) baseStart_1944179 baseEnd_1944179 := by
    simpa [prefixWord, tailWord_1944179, baseEnd_1944179] using wordTrace_append hprefix tailTrace_1944179
  have hstable : (prefixWord ++ tailWord_1944179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944179).length < 2 ^ (prefixWord ++ tailWord_1944179).sum := by decide
  have hdescent : baseEnd_1944179 < baseStart_1944179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944300 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1944300 : Nat := 118140960795 + 1944300 * 2 ^ 59
def prefixEnd_1944300 : Nat := 4983230072969 + 3 ^ 40 * 1944300 * 2
def baseEnd_1944300 : Nat := 443715749571932511559259

theorem tailTrace_1944300 : CollatzResearch.WordTrace tailWord_1944300 prefixEnd_1944300 443715749571932511559259 := by
  unfold tailWord_1944300
  simp only [CollatzResearch.WordTrace]
  refine ⟨35457223428070317424231177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47276297904093756565641569 35457223428070317424231177)
  ·
    refine ⟨26592917571052738068173383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35457223428070317424231177 26592917571052738068173383)
    ·
      refine ⟨39889376356579107102260075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592917571052738068173383 39889376356579107102260075)
      ·
        refine ⟨59834064534868660653390113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39889376356579107102260075 59834064534868660653390113)
        ·
          refine ⟨44875548401151495490042585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59834064534868660653390113 44875548401151495490042585)
          ·
            refine ⟨33656661300863621617531939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44875548401151495490042585 33656661300863621617531939)
            ·
              refine ⟨50484991951295432426297909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33656661300863621617531939 50484991951295432426297909)
              ·
                refine ⟨4732967995433946789965429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50484991951295432426297909 4732967995433946789965429)
                ·
                  refine ⟨443715749571932511559259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732967995433946789965429 443715749571932511559259)
                  ·
                    rfl

theorem cell21_1944300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1944300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944300 prefixEnd_1944300 := by exact prefixLift 1944300
  have htrace : WordTrace (prefixWord ++ tailWord_1944300) baseStart_1944300 baseEnd_1944300 := by
    simpa [prefixWord, tailWord_1944300, baseEnd_1944300] using wordTrace_append hprefix tailTrace_1944300
  have hstable : (prefixWord ++ tailWord_1944300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944300).length < 2 ^ (prefixWord ++ tailWord_1944300).sum := by decide
  have hdescent : baseEnd_1944300 < baseStart_1944300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944348 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1944348 : Nat := 118140960795 + 1944348 * 2 ^ 59
def prefixEnd_1944348 : Nat := 4983230072969 + 3 ^ 40 * 1944348 * 2
def baseEnd_1944348 : Nat := 443726703825895094759161

theorem tailTrace_1944348 : CollatzResearch.WordTrace tailWord_1944348 prefixEnd_1944348 443726703825895094759161 := by
  unfold tailWord_1944348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458098779983369523104849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47277465039977826030806465 35458098779983369523104849)
  ·
    refine ⟨26593574084987527142328637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35458098779983369523104849 26593574084987527142328637)
    ·
      refine ⟨9972590281870322678373239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26593574084987527142328637 9972590281870322678373239)
      ·
        refine ⟨14958885422805484017559859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972590281870322678373239 14958885422805484017559859)
        ·
          refine ⟨22438328134208226026339789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958885422805484017559859 22438328134208226026339789)
          ·
            refine ⟨8414373050328084759877421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22438328134208226026339789 8414373050328084759877421)
            ·
              refine ⟨3155389893873031784954033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8414373050328084759877421 3155389893873031784954033)
              ·
                refine ⟨2366542420404773838715525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155389893873031784954033 2366542420404773838715525)
                ·
                  refine ⟨443726703825895094759161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366542420404773838715525 443726703825895094759161)
                  ·
                    rfl

theorem cell21_1944348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1944348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944348 prefixEnd_1944348 := by exact prefixLift 1944348
  have htrace : WordTrace (prefixWord ++ tailWord_1944348) baseStart_1944348 baseEnd_1944348 := by
    simpa [prefixWord, tailWord_1944348, baseEnd_1944348] using wordTrace_append hprefix tailTrace_1944348
  have hstable : (prefixWord ++ tailWord_1944348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944348).length < 2 ^ (prefixWord ++ tailWord_1944348).sum := by decide
  have hdescent : baseEnd_1944348 < baseStart_1944348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944376 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_1944376 : Nat := 118140960795 + 1944376 * 2 ^ 59
def prefixEnd_1944376 : Nat := 4983230072969 + 3 ^ 40 * 1944376 * 2
def baseEnd_1944376 : Nat := 443733093807373268292437

theorem tailTrace_1944376 : CollatzResearch.WordTrace tailWord_1944376 prefixEnd_1944376 443733093807373268292437 := by
  unfold tailWord_1944376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458609401932649914114491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47278145869243533218819321 35458609401932649914114491)
  ·
    refine ⟨53187914102898974871171737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35458609401932649914114491 53187914102898974871171737)
    ·
      refine ⟨39890935577174231153378803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53187914102898974871171737 39890935577174231153378803)
      ·
        refine ⟨59836403365761346730068205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39890935577174231153378803 59836403365761346730068205)
        ·
          refine ⟨22438651262160505023775577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59836403365761346730068205 22438651262160505023775577)
          ·
            refine ⟨16828988446620378767831683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22438651262160505023775577 16828988446620378767831683)
            ·
              refine ⟨25243482669930568151747525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828988446620378767831683 25243482669930568151747525)
              ·
                refine ⟨4733153000611981528452661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25243482669930568151747525 4733153000611981528452661)
                ·
                  refine ⟨443733093807373268292437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4733153000611981528452661 443733093807373268292437)
                  ·
                    rfl

theorem cell21_1944376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_1944376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944376 prefixEnd_1944376 := by exact prefixLift 1944376
  have htrace : WordTrace (prefixWord ++ tailWord_1944376) baseStart_1944376 baseEnd_1944376 := by
    simpa [prefixWord, tailWord_1944376, baseEnd_1944376] using wordTrace_append hprefix tailTrace_1944376
  have hstable : (prefixWord ++ tailWord_1944376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944376).length < 2 ^ (prefixWord ++ tailWord_1944376).sum := by decide
  have hdescent : baseEnd_1944376 < baseStart_1944376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944385 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 3]
def baseStart_1944385 : Nat := 118140960795 + 1944385 * 2 ^ 59
def prefixEnd_1944385 : Nat := 4983230072969 + 3 ^ 40 * 1944385 * 2
def baseEnd_1944385 : Nat := 443735147729991252642419

theorem tailTrace_1944385 : CollatzResearch.WordTrace tailWord_1944385 prefixEnd_1944385 443735147729991252642419 := by
  unfold tailWord_1944385
  simp only [CollatzResearch.WordTrace]
  refine ⟨70917547060832694365306609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47278364707221796243537739 70917547060832694365306609)
  ·
    refine ⟨53188160295624520773979957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70917547060832694365306609 53188160295624520773979957)
    ·
      refine ⟨4986390027714798822560621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53188160295624520773979957 4986390027714798822560621)
      ·
        refine ⟨1869896260393049558460233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4986390027714798822560621 1869896260393049558460233)
        ·
          refine ⟨1402422195294787168845175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869896260393049558460233 1402422195294787168845175)
          ·
            refine ⟨2103633292942180753267763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402422195294787168845175 2103633292942180753267763)
            ·
              refine ⟨3155449939413271129901645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103633292942180753267763 3155449939413271129901645)
              ·
                refine ⟨1183293727279976673713117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3155449939413271129901645 1183293727279976673713117)
                ·
                  refine ⟨443735147729991252642419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183293727279976673713117 443735147729991252642419)
                  ·
                    rfl

theorem cell21_1944385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_1944385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944385 prefixEnd_1944385 := by exact prefixLift 1944385
  have htrace : WordTrace (prefixWord ++ tailWord_1944385) baseStart_1944385 baseEnd_1944385 := by
    simpa [prefixWord, tailWord_1944385, baseEnd_1944385] using wordTrace_append hprefix tailTrace_1944385
  have hstable : (prefixWord ++ tailWord_1944385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944385).length < 2 ^ (prefixWord ++ tailWord_1944385).sum := by decide
  have hdescent : baseEnd_1944385 < baseStart_1944385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944407 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_1944407 : Nat := 118140960795 + 1944407 * 2 ^ 59
def prefixEnd_1944407 : Nat := 4983230072969 + 3 ^ 40 * 1944407 * 2
def baseEnd_1944407 : Nat := 443740168429724103275707

theorem tailTrace_1944407 : CollatzResearch.WordTrace tailWord_1944407 prefixEnd_1944407 443740168429724103275707 := by
  unfold tailWord_1944407
  simp only [CollatzResearch.WordTrace]
  refine ⟨70918349466752992122607475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47278899644501994748404983 70918349466752992122607475)
  ·
    refine ⟨106377524200129488183911213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70918349466752992122607475 106377524200129488183911213)
    ·
      refine ⟨39891571575048558068966705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106377524200129488183911213 39891571575048558068966705)
      ·
        refine ⟨29918678681286418551725029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39891571575048558068966705 29918678681286418551725029)
        ·
          refine ⟨5609752252741203478448443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29918678681286418551725029 5609752252741203478448443)
          ·
            refine ⟨8414628379111805217672665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609752252741203478448443 8414628379111805217672665)
            ·
              refine ⟨6310971284333853913254499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8414628379111805217672665 6310971284333853913254499)
              ·
                refine ⟨9466456926500780869881749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310971284333853913254499 9466456926500780869881749)
                ·
                  refine ⟨443740168429724103275707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9466456926500780869881749 443740168429724103275707)
                  ·
                    rfl

theorem cell21_1944407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_1944407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944407 prefixEnd_1944407 := by exact prefixLift 1944407
  have htrace : WordTrace (prefixWord ++ tailWord_1944407) baseStart_1944407 baseEnd_1944407 := by
    simpa [prefixWord, tailWord_1944407, baseEnd_1944407] using wordTrace_append hprefix tailTrace_1944407
  have hstable : (prefixWord ++ tailWord_1944407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944407).length < 2 ^ (prefixWord ++ tailWord_1944407).sum := by decide
  have hdescent : baseEnd_1944407 < baseStart_1944407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944421 : List Nat := [1, 3, 1, 3, 1, 1, 3, 8]
def baseStart_1944421 : Nat := 118140960795 + 1944421 * 2 ^ 59
def prefixEnd_1944421 : Nat := 4983230072969 + 3 ^ 40 * 1944421 * 2
def baseEnd_1944421 : Nat := 147914454473487730014115

theorem tailTrace_1944421 : CollatzResearch.WordTrace tailWord_1944421 prefixEnd_1944421 147914454473487730014115 := by
  unfold tailWord_1944421
  simp only [CollatzResearch.WordTrace]
  refine ⟨70918860088702272513617117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47279240059134848342411411 70918860088702272513617117)
  ·
    refine ⟨26594572533263352192606419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70918860088702272513617117 26594572533263352192606419)
    ·
      refine ⟨39891858799895028288909629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26594572533263352192606419 39891858799895028288909629)
      ·
        refine ⟨14959447049960635608341111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39891858799895028288909629 14959447049960635608341111)
        ·
          refine ⟨22439170574940953412511667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959447049960635608341111 22439170574940953412511667)
          ·
            refine ⟨33658755862411430118767501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22439170574940953412511667 33658755862411430118767501)
            ·
              refine ⟨12622033448404286294537813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33658755862411430118767501 12622033448404286294537813)
              ·
                refine ⟨147914454473487730014115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12622033448404286294537813 147914454473487730014115)
                ·
                  rfl

theorem cell21_1944421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_1944421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944421 prefixEnd_1944421 := by exact prefixLift 1944421
  have htrace : WordTrace (prefixWord ++ tailWord_1944421) baseStart_1944421 baseEnd_1944421 := by
    simpa [prefixWord, tailWord_1944421, baseEnd_1944421] using wordTrace_append hprefix tailTrace_1944421
  have hstable : (prefixWord ++ tailWord_1944421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944421).length < 2 ^ (prefixWord ++ tailWord_1944421).sum := by decide
  have hdescent : baseEnd_1944421 < baseStart_1944421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944424 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_1944424 : Nat := 118140960795 + 1944424 * 2 ^ 59
def prefixEnd_1944424 : Nat := 4983230072969 + 3 ^ 40 * 1944424 * 2
def baseEnd_1944424 : Nat := 443744048061335851492339

theorem tailTrace_1944424 : CollatzResearch.WordTrace tailWord_1944424 prefixEnd_1944424 443744048061335851492339 := by
  unfold tailWord_1944424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459484753845702012988163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47279313005127602683984217 35459484753845702012988163)
  ·
    refine ⟨53189227130768553019482245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35459484753845702012988163 53189227130768553019482245)
    ·
      refine ⟨9972980087019103691152921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53189227130768553019482245 9972980087019103691152921)
      ·
        refine ⟨7479735065264327768364691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9972980087019103691152921 7479735065264327768364691)
        ·
          refine ⟨11219602597896491652547037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479735065264327768364691 11219602597896491652547037)
          ·
            refine ⟨4207350974211184369705139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11219602597896491652547037 4207350974211184369705139)
            ·
              refine ⟨6311026461316776554557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207350974211184369705139 6311026461316776554557709)
              ·
                refine ⟨2366634922993791207959141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6311026461316776554557709 2366634922993791207959141)
                ·
                  refine ⟨443744048061335851492339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366634922993791207959141 443744048061335851492339)
                  ·
                    rfl

theorem cell21_1944424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_1944424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944424 prefixEnd_1944424 := by exact prefixLift 1944424
  have htrace : WordTrace (prefixWord ++ tailWord_1944424) baseStart_1944424 baseEnd_1944424 := by
    simpa [prefixWord, tailWord_1944424, baseEnd_1944424] using wordTrace_append hprefix tailTrace_1944424
  have hstable : (prefixWord ++ tailWord_1944424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944424).length < 2 ^ (prefixWord ++ tailWord_1944424).sum := by decide
  have hdescent : baseEnd_1944424 < baseStart_1944424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944483 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_1944483 : Nat := 118140960795 + 1944483 * 2 ^ 59
def prefixEnd_1944483 : Nat := 4983230072969 + 3 ^ 40 * 1944483 * 2
def baseEnd_1944483 : Nat := 443757512665164860008885

theorem tailTrace_1944483 : CollatzResearch.WordTrace tailWord_1944483 prefixEnd_1944483 443757512665164860008885 := by
  unfold tailWord_1944483
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921121414477657102374103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47280747609651771401582735 70921121414477657102374103)
  ·
    refine ⟨106381682121716485653561155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70921121414477657102374103 106381682121716485653561155)
    ·
      refine ⟨159572523182574728480341733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106381682121716485653561155 159572523182574728480341733)
      ·
        refine ⟨29919848096732761590064075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159572523182574728480341733 29919848096732761590064075)
        ·
          refine ⟨44879772145099142385096113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919848096732761590064075 44879772145099142385096113)
          ·
            refine ⟨33659829108824356788822085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44879772145099142385096113 33659829108824356788822085)
            ·
              refine ⟨6311217957904566897904141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33659829108824356788822085 6311217957904566897904141)
              ·
                refine ⟨2366706734214212586714053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6311217957904566897904141 2366706734214212586714053)
                ·
                  refine ⟨443757512665164860008885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366706734214212586714053 443757512665164860008885)
                  ·
                    rfl

theorem cell21_1944483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_1944483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944483 prefixEnd_1944483 := by exact prefixLift 1944483
  have htrace : WordTrace (prefixWord ++ tailWord_1944483) baseStart_1944483 baseEnd_1944483 := by
    simpa [prefixWord, tailWord_1944483, baseEnd_1944483] using wordTrace_append hprefix tailTrace_1944483
  have hstable : (prefixWord ++ tailWord_1944483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944483).length < 2 ^ (prefixWord ++ tailWord_1944483).sum := by decide
  have hdescent : baseEnd_1944483 < baseStart_1944483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944534 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1944534 : Nat := 118140960795 + 1944534 * 2 ^ 59
def prefixEnd_1944534 : Nat := 4983230072969 + 3 ^ 40 * 1944534 * 2
def baseEnd_1944534 : Nat := 443769151560000104658781

theorem tailTrace_1944534 : CollatzResearch.WordTrace tailWord_1944534 prefixEnd_1944534 443769151560000104658781 := by
  unfold tailWord_1944534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432686346080805800780041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47281987691528595208320437 4432686346080805800780041)
  ·
    refine ⟨3324514759560604350585031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4432686346080805800780041 3324514759560604350585031)
    ·
      refine ⟨4986772139340906525877547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324514759560604350585031 4986772139340906525877547)
      ·
        refine ⟨7480158209011359788816321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986772139340906525877547 7480158209011359788816321)
        ·
          refine ⟨5610118656758519841612241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7480158209011359788816321 5610118656758519841612241)
          ·
            refine ⟨4207588992568889881209181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5610118656758519841612241 4207588992568889881209181)
            ·
              refine ⟨1577845872213333705453443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4207588992568889881209181 1577845872213333705453443)
              ·
                refine ⟨2366768808320000558180165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577845872213333705453443 2366768808320000558180165)
                ·
                  refine ⟨443769151560000104658781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366768808320000558180165 443769151560000104658781)
                  ·
                    rfl

theorem cell21_1944534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1944534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944534 prefixEnd_1944534 := by exact prefixLift 1944534
  have htrace : WordTrace (prefixWord ++ tailWord_1944534) baseStart_1944534 baseEnd_1944534 := by
    simpa [prefixWord, tailWord_1944534, baseEnd_1944534] using wordTrace_append hprefix tailTrace_1944534
  have hstable : (prefixWord ++ tailWord_1944534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944534).length < 2 ^ (prefixWord ++ tailWord_1944534).sum := by decide
  have hdescent : baseEnd_1944534 < baseStart_1944534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944590 : List Nat := [4, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1944590 : Nat := 118140960795 + 1944590 * 2 ^ 59
def prefixEnd_1944590 : Nat := 4983230072969 + 3 ^ 40 * 1944590 * 2
def baseEnd_1944590 : Nat := 147927310507652150575111

theorem tailTrace_1944590 : CollatzResearch.WordTrace tailWord_1944590 prefixEnd_1944590 147927310507652150575111 := by
  unfold tailWord_1944590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865628003136251797064903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47283349350060009584346149 8865628003136251797064903)
  ·
    refine ⟨13298442004704377695597355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865628003136251797064903 13298442004704377695597355)
    ·
      refine ⟨19947663007056566543396033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298442004704377695597355 19947663007056566543396033)
      ·
        refine ⟨14960747255292424907547025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19947663007056566543396033 14960747255292424907547025)
        ·
          refine ⟨11220560441469318680660269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14960747255292424907547025 11220560441469318680660269)
          ·
            refine ⟨4207710165550994505247601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11220560441469318680660269 4207710165550994505247601)
            ·
              refine ⟨3155782624163245878935701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207710165550994505247601 3155782624163245878935701)
              ·
                refine ⟨147927310507652150575111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3155782624163245878935701 147927310507652150575111)
                ·
                  rfl

theorem cell21_1944590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1944590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944590 prefixEnd_1944590 := by exact prefixLift 1944590
  have htrace : WordTrace (prefixWord ++ tailWord_1944590) baseStart_1944590 baseEnd_1944590 := by
    simpa [prefixWord, tailWord_1944590, baseEnd_1944590] using wordTrace_append hprefix tailTrace_1944590
  have hstable : (prefixWord ++ tailWord_1944590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944590).length < 2 ^ (prefixWord ++ tailWord_1944590).sum := by decide
  have hdescent : baseEnd_1944590 < baseStart_1944590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944697 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_1944697 : Nat := 118140960795 + 1944697 * 2 ^ 59
def prefixEnd_1944697 : Nat := 4983230072969 + 3 ^ 40 * 1944697 * 2
def baseEnd_1944697 : Nat := 443806350380748043441781

theorem tailTrace_1944697 : CollatzResearch.WordTrace tailWord_1944697 prefixEnd_1944697 443806350380748043441781 := by
  unfold tailWord_1944697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70928926635702371650664345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47285951090468247767109563 70928926635702371650664345)
  ·
    refine ⟨53196694976776778737998259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70928926635702371650664345 53196694976776778737998259)
    ·
      refine ⟨79795042465165168106997389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53196694976776778737998259 79795042465165168106997389)
      ·
        refine ⟨29923140924436938040124021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79795042465165168106997389 29923140924436938040124021)
        ·
          refine ⟨2805294461665962941261627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29923140924436938040124021 2805294461665962941261627)
          ·
            refine ⟨4207941692498944411892441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805294461665962941261627 4207941692498944411892441)
            ·
              refine ⟨3155956269374208308919331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207941692498944411892441 3155956269374208308919331)
              ·
                refine ⟨4733934404061312463378997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155956269374208308919331 4733934404061312463378997)
                ·
                  refine ⟨443806350380748043441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4733934404061312463378997 443806350380748043441781)
                  ·
                    rfl

theorem cell21_1944697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_1944697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944697 prefixEnd_1944697 := by exact prefixLift 1944697
  have htrace : WordTrace (prefixWord ++ tailWord_1944697) baseStart_1944697 baseEnd_1944697 := by
    simpa [prefixWord, tailWord_1944697, baseEnd_1944697] using wordTrace_append hprefix tailTrace_1944697
  have hstable : (prefixWord ++ tailWord_1944697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944697).length < 2 ^ (prefixWord ++ tailWord_1944697).sum := by decide
  have hdescent : baseEnd_1944697 < baseStart_1944697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944739 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_1944739 : Nat := 118140960795 + 1944739 * 2 ^ 59
def prefixEnd_1944739 : Nat := 4983230072969 + 3 ^ 40 * 1944739 * 2
def baseEnd_1944739 : Nat := 443815935352965303741695

theorem tailTrace_1944739 : CollatzResearch.WordTrace tailWord_1944739 prefixEnd_1944739 443815935352965303741695 := by
  unfold tailWord_1944739
  simp only [CollatzResearch.WordTrace]
  refine ⟨70930458501550212823693271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47286972334366808549128847 70930458501550212823693271)
  ·
    refine ⟨106395687752325319235539907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70930458501550212823693271 106395687752325319235539907)
    ·
      refine ⟨159593531628487978853309861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106395687752325319235539907 159593531628487978853309861)
      ·
        refine ⟨29923787180341496034995599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159593531628487978853309861 29923787180341496034995599)
        ·
          refine ⟨44885680770512244052493399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29923787180341496034995599 44885680770512244052493399)
          ·
            refine ⟨67328521155768366078740099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44885680770512244052493399 67328521155768366078740099)
            ·
              refine ⟨100992781733652549118110149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67328521155768366078740099 100992781733652549118110149)
              ·
                refine ⟨18936146575059852959645653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100992781733652549118110149 18936146575059852959645653)
                ·
                  refine ⟨443815935352965303741695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18936146575059852959645653 443815935352965303741695)
                  ·
                    rfl

theorem cell21_1944739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_1944739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944739 prefixEnd_1944739 := by exact prefixLift 1944739
  have htrace : WordTrace (prefixWord ++ tailWord_1944739) baseStart_1944739 baseEnd_1944739 := by
    simpa [prefixWord, tailWord_1944739, baseEnd_1944739] using wordTrace_append hprefix tailTrace_1944739
  have hstable : (prefixWord ++ tailWord_1944739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944739).length < 2 ^ (prefixWord ++ tailWord_1944739).sum := by decide
  have hdescent : baseEnd_1944739 < baseStart_1944739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944849 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 3]
def baseStart_1944849 : Nat := 118140960795 + 1944849 * 2 ^ 59
def prefixEnd_1944849 : Nat := 4983230072969 + 3 ^ 40 * 1944849 * 2
def baseEnd_1944849 : Nat := 443841038851629556908137

theorem tailTrace_1944849 : CollatzResearch.WordTrace tailWord_1944849 prefixEnd_1944849 443841038851629556908137 := by
  unfold tailWord_1944849
  simp only [CollatzResearch.WordTrace]
  refine ⟨70934470531151701610197601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47289647020767801073465067 70934470531151701610197601)
  ·
    refine ⟨53200852898363776207648201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70934470531151701610197601 53200852898363776207648201)
    ·
      refine ⟨39900639673772832155736151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53200852898363776207648201 39900639673772832155736151)
      ·
        refine ⟨59850959510659248233604227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39900639673772832155736151 59850959510659248233604227)
        ·
          refine ⟨89776439265988872350406341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59850959510659248233604227 89776439265988872350406341)
          ·
            refine ⟨16833082362372913565701189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89776439265988872350406341 16833082362372913565701189)
            ·
              refine ⟨3156202942944921293568973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16833082362372913565701189 3156202942944921293568973)
              ·
                refine ⟨1183576103604345485088365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3156202942944921293568973 1183576103604345485088365)
                ·
                  refine ⟨443841038851629556908137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183576103604345485088365 443841038851629556908137)
                  ·
                    rfl

theorem cell21_1944849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_1944849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944849 prefixEnd_1944849 := by exact prefixLift 1944849
  have htrace : WordTrace (prefixWord ++ tailWord_1944849) baseStart_1944849 baseEnd_1944849 := by
    simpa [prefixWord, tailWord_1944849, baseEnd_1944849] using wordTrace_append hprefix tailTrace_1944849
  have hstable : (prefixWord ++ tailWord_1944849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944849).length < 2 ^ (prefixWord ++ tailWord_1944849).sum := by decide
  have hdescent : baseEnd_1944849 < baseStart_1944849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944863 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_1944863 : Nat := 118140960795 + 1944863 * 2 ^ 59
def prefixEnd_1944863 : Nat := 4983230072969 + 3 ^ 40 * 1944863 * 2
def baseEnd_1944863 : Nat := 443844233842368643674775

theorem tailTrace_1944863 : CollatzResearch.WordTrace tailWord_1944863 prefixEnd_1944863 443844233842368643674775 := by
  unfold tailWord_1944863
  simp only [CollatzResearch.WordTrace]
  refine ⟨70934981153100982001207243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47289987435400654667471495 70934981153100982001207243)
  ·
    refine ⟨106402471729651473001810865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70934981153100982001207243 106402471729651473001810865)
    ·
      refine ⟨79801853797238604751358149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106402471729651473001810865 79801853797238604751358149)
      ·
        refine ⟨14962847586982238390879653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79801853797238604751358149 14962847586982238390879653)
        ·
          refine ⟨2805533922559169698289935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14962847586982238390879653 2805533922559169698289935)
          ·
            refine ⟨4208300883838754547434903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805533922559169698289935 4208300883838754547434903)
            ·
              refine ⟨6312451325758131821152355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208300883838754547434903 6312451325758131821152355)
              ·
                refine ⟨9468676988637197731728533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312451325758131821152355 9468676988637197731728533)
                ·
                  refine ⟨443844233842368643674775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9468676988637197731728533 443844233842368643674775)
                  ·
                    rfl

theorem cell21_1944863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_1944863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944863 prefixEnd_1944863 := by exact prefixLift 1944863
  have htrace : WordTrace (prefixWord ++ tailWord_1944863) baseStart_1944863 baseEnd_1944863 := by
    simpa [prefixWord, tailWord_1944863, baseEnd_1944863] using wordTrace_append hprefix tailTrace_1944863
  have hstable : (prefixWord ++ tailWord_1944863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944863).length < 2 ^ (prefixWord ++ tailWord_1944863).sum := by decide
  have hdescent : baseEnd_1944863 < baseStart_1944863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944922 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1944922 : Nat := 118140960795 + 1944922 * 2 ^ 59
def prefixEnd_1944922 : Nat := 4983230072969 + 3 ^ 40 * 1944922 * 2
def baseEnd_1944922 : Nat := 443857698446197652191321

theorem tailTrace_1944922 : CollatzResearch.WordTrace tailWord_1944922 prefixEnd_1944922 443857698446197652191321 := by
  unfold tailWord_1944922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734283264971808769401255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47291422039924823385070013 17734283264971808769401255)
  ·
    refine ⟨26601424897457713154101883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17734283264971808769401255 26601424897457713154101883)
    ·
      refine ⟨39902137346186569731152825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26601424897457713154101883 39902137346186569731152825)
      ·
        refine ⟨29926603009639927298364619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39902137346186569731152825 29926603009639927298364619)
        ·
          refine ⟨44889904514459890947546929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29926603009639927298364619 44889904514459890947546929)
          ·
            refine ⟨33667428385844918210660197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44889904514459890947546929 33667428385844918210660197)
            ·
              refine ⟨6312642822345922164498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33667428385844918210660197 6312642822345922164498787)
              ·
                refine ⟨9468964233518883246748181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312642822345922164498787 9468964233518883246748181)
                ·
                  refine ⟨443857698446197652191321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9468964233518883246748181 443857698446197652191321)
                  ·
                    rfl

theorem cell21_1944922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1944922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1944922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1944922 prefixEnd_1944922 := by exact prefixLift 1944922
  have htrace : WordTrace (prefixWord ++ tailWord_1944922) baseStart_1944922 baseEnd_1944922 := by
    simpa [prefixWord, tailWord_1944922, baseEnd_1944922] using wordTrace_append hprefix tailTrace_1944922
  have hstable : (prefixWord ++ tailWord_1944922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944922).length < 2 ^ (prefixWord ++ tailWord_1944922).sum := by decide
  have hdescent : baseEnd_1944922 < baseStart_1944922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945119 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_1945119 : Nat := 118140960795 + 1945119 * 2 ^ 59
def prefixEnd_1945119 : Nat := 4983230072969 + 3 ^ 40 * 1945119 * 2
def baseEnd_1945119 : Nat := 443902656530169087407585

theorem tailTrace_1945119 : CollatzResearch.WordTrace tailWord_1945119 prefixEnd_1945119 443902656530169087407585 := by
  unfold tailWord_1945119
  simp only [CollatzResearch.WordTrace]
  refine ⟨70944318240173537722526411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47296212160115691815017607 70944318240173537722526411)
  ·
    refine ⟨106416477360260306583789617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70944318240173537722526411 106416477360260306583789617)
    ·
      refine ⟨79812358020195229937842213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106416477360260306583789617 79812358020195229937842213)
      ·
        refine ⟨14964817128786605613345415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79812358020195229937842213 14964817128786605613345415)
        ·
          refine ⟨22447225693179908420018123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14964817128786605613345415 22447225693179908420018123)
          ·
            refine ⟨33670838539769862630027185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22447225693179908420018123 33670838539769862630027185)
            ·
              refine ⟨25253128904827396972520389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33670838539769862630027185 25253128904827396972520389)
              ·
                refine ⟨4734961669655136932347573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25253128904827396972520389 4734961669655136932347573)
                ·
                  refine ⟨443902656530169087407585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4734961669655136932347573 443902656530169087407585)
                  ·
                    rfl

theorem cell21_1945119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_1945119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945119 prefixEnd_1945119 := by exact prefixLift 1945119
  have htrace : WordTrace (prefixWord ++ tailWord_1945119) baseStart_1945119 baseEnd_1945119 := by
    simpa [prefixWord, tailWord_1945119, baseEnd_1945119] using wordTrace_append hprefix tailTrace_1945119
  have hstable : (prefixWord ++ tailWord_1945119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945119).length < 2 ^ (prefixWord ++ tailWord_1945119).sum := by decide
  have hdescent : baseEnd_1945119 < baseStart_1945119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945136 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_1945136 : Nat := 118140960795 + 1945136 * 2 ^ 59
def prefixEnd_1945136 : Nat := 4983230072969 + 3 ^ 40 * 1945136 * 2
def baseEnd_1945136 : Nat := 443906536161780835624217

theorem tailTrace_1945136 : CollatzResearch.WordTrace tailWord_1945136 prefixEnd_1945136 443906536161780835624217 := by
  unfold tailWord_1945136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35472469140555974812947631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47296625520741299750596841 35472469140555974812947631)
  ·
    refine ⟨53208703710833962219421447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35472469140555974812947631 53208703710833962219421447)
    ·
      refine ⟨79813055566250943329132171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53208703710833962219421447 79813055566250943329132171)
      ·
        refine ⟨119719583349376414993698257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79813055566250943329132171 119719583349376414993698257)
        ·
          refine ⟨89789687512032311245273693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119719583349376414993698257 89789687512032311245273693)
          ·
            refine ⟨33671132817012116716977635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89789687512032311245273693 33671132817012116716977635)
            ·
              refine ⟨50506699225518175075466453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33671132817012116716977635 50506699225518175075466453)
              ·
                refine ⟨1183750763098082228331245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50506699225518175075466453 1183750763098082228331245)
                ·
                  refine ⟨443906536161780835624217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183750763098082228331245 443906536161780835624217)
                  ·
                    rfl

theorem cell21_1945136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_1945136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945136 prefixEnd_1945136 := by exact prefixLift 1945136
  have htrace : WordTrace (prefixWord ++ tailWord_1945136) baseStart_1945136 baseEnd_1945136 := by
    simpa [prefixWord, tailWord_1945136, baseEnd_1945136] using wordTrace_append hprefix tailTrace_1945136
  have hstable : (prefixWord ++ tailWord_1945136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945136).length < 2 ^ (prefixWord ++ tailWord_1945136).sum := by decide
  have hdescent : baseEnd_1945136 < baseStart_1945136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945153 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 3]
def baseStart_1945153 : Nat := 118140960795 + 1945153 * 2 ^ 59
def prefixEnd_1945153 : Nat := 4983230072969 + 3 ^ 40 * 1945153 * 2
def baseEnd_1945153 : Nat := 443910415793392583840849

theorem tailTrace_1945153 : CollatzResearch.WordTrace tailWord_1945153 prefixEnd_1945153 443910415793392583840849 := by
  unfold tailWord_1945153
  simp only [CollatzResearch.WordTrace]
  refine ⟨70945558322050361529264113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47297038881366907686176075 70945558322050361529264113)
  ·
    refine ⟨53209168741537771146948085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70945558322050361529264113 53209168741537771146948085)
    ·
      refine ⟨4988359569519166045026383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53209168741537771146948085 4988359569519166045026383)
      ·
        refine ⟨7482539354278749067539575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988359569519166045026383 7482539354278749067539575)
        ·
          refine ⟨11223809031418123601309363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482539354278749067539575 11223809031418123601309363)
          ·
            refine ⟨16835713547127185401964045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223809031418123601309363 16835713547127185401964045)
            ·
              refine ⟨6313392580172694525736517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16835713547127185401964045 6313392580172694525736517)
              ·
                refine ⟨1183761108782380223575597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6313392580172694525736517 1183761108782380223575597)
                ·
                  refine ⟨443910415793392583840849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183761108782380223575597 443910415793392583840849)
                  ·
                    rfl

theorem cell21_1945153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_1945153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945153 prefixEnd_1945153 := by exact prefixLift 1945153
  have htrace : WordTrace (prefixWord ++ tailWord_1945153) baseStart_1945153 baseEnd_1945153 := by
    simpa [prefixWord, tailWord_1945153, baseEnd_1945153] using wordTrace_append hprefix tailTrace_1945153
  have hstable : (prefixWord ++ tailWord_1945153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945153).length < 2 ^ (prefixWord ++ tailWord_1945153).sum := by decide
  have hdescent : baseEnd_1945153 < baseStart_1945153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945246 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1945246 : Nat := 118140960795 + 1945246 * 2 ^ 59
def prefixEnd_1945246 : Nat := 4983230072969 + 3 ^ 40 * 1945246 * 2
def baseEnd_1945246 : Nat := 443931639660445088790659

theorem tailTrace_1945246 : CollatzResearch.WordTrace tailWord_1945246 prefixEnd_1945246 443931639660445088790659 := by
  unfold tailWord_1945246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868618788839179801549949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47299300207142292274933061 8868618788839179801549949)
  ·
    refine ⟨3325732045814692425581231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8868618788839179801549949 3325732045814692425581231)
    ·
      refine ⟨4988598068722038638371847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325732045814692425581231 4988598068722038638371847)
      ·
        refine ⟨7482897103083057957557771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988598068722038638371847 7482897103083057957557771)
        ·
          refine ⟨11224345654624586936336657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482897103083057957557771 11224345654624586936336657)
          ·
            refine ⟨8418259240968440202252493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11224345654624586936336657 8418259240968440202252493)
            ·
              refine ⟨3156847215363165075844685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8418259240968440202252493 3156847215363165075844685)
              ·
                refine ⟨1183817705761186903441757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3156847215363165075844685 1183817705761186903441757)
                ·
                  refine ⟨443931639660445088790659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183817705761186903441757 443931639660445088790659)
                  ·
                    rfl

theorem cell21_1945246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1945246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945246 prefixEnd_1945246 := by exact prefixLift 1945246
  have htrace : WordTrace (prefixWord ++ tailWord_1945246) baseStart_1945246 baseEnd_1945246 := by
    simpa [prefixWord, tailWord_1945246, baseEnd_1945246] using wordTrace_append hprefix tailTrace_1945246
  have hstable : (prefixWord ++ tailWord_1945246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945246).length < 2 ^ (prefixWord ++ tailWord_1945246).sum := by decide
  have hdescent : baseEnd_1945246 < baseStart_1945246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945361 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_1945361 : Nat := 118140960795 + 1945361 * 2 ^ 59
def prefixEnd_1945361 : Nat := 4983230072969 + 3 ^ 40 * 1945361 * 2
def baseEnd_1945361 : Nat := 443957884227230444373757

theorem tailTrace_1945361 : CollatzResearch.WordTrace tailWord_1945361 prefixEnd_1945361 443957884227230444373757 := by
  unfold tailWord_1945361
  simp only [CollatzResearch.WordTrace]
  refine ⟨70953144705296813052835937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47302096470197875368557291 70953144705296813052835937)
  ·
    refine ⟨53214858528972609789626953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70953144705296813052835937 53214858528972609789626953)
    ·
      refine ⟨39911143896729457342220215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53214858528972609789626953 39911143896729457342220215)
      ·
        refine ⟨59866715845094186013330323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39911143896729457342220215 59866715845094186013330323)
        ·
          refine ⟨89800073767641279019995485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59866715845094186013330323 89800073767641279019995485)
          ·
            refine ⟨33675027662865479632498307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89800073767641279019995485 33675027662865479632498307)
            ·
              refine ⟨50512541494298219448747461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33675027662865479632498307 50512541494298219448747461)
              ·
                refine ⟨9471101530180916146640149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50512541494298219448747461 9471101530180916146640149)
                ·
                  refine ⟨443957884227230444373757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9471101530180916146640149 443957884227230444373757)
                  ·
                    rfl

theorem cell21_1945361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_1945361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945361 prefixEnd_1945361 := by exact prefixLift 1945361
  have htrace : WordTrace (prefixWord ++ tailWord_1945361) baseStart_1945361 baseEnd_1945361 := by
    simpa [prefixWord, tailWord_1945361, baseEnd_1945361] using wordTrace_append hprefix tailTrace_1945361
  have hstable : (prefixWord ++ tailWord_1945361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945361).length < 2 ^ (prefixWord ++ tailWord_1945361).sum := by decide
  have hdescent : baseEnd_1945361 < baseStart_1945361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945378 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1945378 : Nat := 118140960795 + 1945378 * 2 ^ 59
def prefixEnd_1945378 : Nat := 4983230072969 + 3 ^ 40 * 1945378 * 2
def baseEnd_1945378 : Nat := 443961763858842192590389

theorem tailTrace_1945378 : CollatzResearch.WordTrace tailWord_1945378 prefixEnd_1945378 443961763858842192590389 := by
  unfold tailWord_1945378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738441186558806239051197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47302509830823483304136525 17738441186558806239051197)
  ·
    refine ⟨6651915444959552339644199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17738441186558806239051197 6651915444959552339644199)
    ·
      refine ⟨9977873167439328509466299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651915444959552339644199 9977873167439328509466299)
      ·
        refine ⟨14966809751158992764199449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977873167439328509466299 14966809751158992764199449)
        ·
          refine ⟨11225107313369244573149587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14966809751158992764199449 11225107313369244573149587)
          ·
            refine ⟨16837660970053866859724381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225107313369244573149587 16837660970053866859724381)
            ·
              refine ⟨6314122863770200072396643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16837660970053866859724381 6314122863770200072396643)
              ·
                refine ⟨9471184295655300108594965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314122863770200072396643 9471184295655300108594965)
                ·
                  refine ⟨443961763858842192590389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9471184295655300108594965 443961763858842192590389)
                  ·
                    rfl

theorem cell21_1945378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1945378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945378 prefixEnd_1945378 := by exact prefixLift 1945378
  have htrace : WordTrace (prefixWord ++ tailWord_1945378) baseStart_1945378 baseEnd_1945378 := by
    simpa [prefixWord, tailWord_1945378, baseEnd_1945378] using wordTrace_append hprefix tailTrace_1945378
  have hstable : (prefixWord ++ tailWord_1945378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945378).length < 2 ^ (prefixWord ++ tailWord_1945378).sum := by decide
  have hdescent : baseEnd_1945378 < baseStart_1945378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945440 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_1945440 : Nat := 118140960795 + 1945440 * 2 ^ 59
def prefixEnd_1945440 : Nat := 4983230072969 + 3 ^ 40 * 1945440 * 2
def baseEnd_1945440 : Nat := 443975913103543862556929

theorem tailTrace_1945440 : CollatzResearch.WordTrace tailWord_1945440 prefixEnd_1945440 443975913103543862556929 := by
  unfold tailWord_1945440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478013036005304772480887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47304017381340406363307849 35478013036005304772480887)
  ·
    refine ⟨53217019554007957158721331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35478013036005304772480887 53217019554007957158721331)
    ·
      refine ⟨79825529331011935738081997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53217019554007957158721331 79825529331011935738081997)
      ·
        refine ⟨29934573499129475901780749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79825529331011935738081997 29934573499129475901780749)
        ·
          refine ⟨11225465062173553463167781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29934573499129475901780749 11225465062173553463167781)
          ·
            refine ⟨2104774699157541274343959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11225465062173553463167781 2104774699157541274343959)
            ·
              refine ⟨3157162048736311911515939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104774699157541274343959 3157162048736311911515939)
              ·
                refine ⟨4735743073104467867273909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157162048736311911515939 4735743073104467867273909)
                ·
                  refine ⟨443975913103543862556929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735743073104467867273909 443975913103543862556929)
                  ·
                    rfl

theorem cell21_1945440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_1945440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945440 prefixEnd_1945440 := by exact prefixLift 1945440
  have htrace : WordTrace (prefixWord ++ tailWord_1945440) baseStart_1945440 baseEnd_1945440 := by
    simpa [prefixWord, tailWord_1945440, baseEnd_1945440] using wordTrace_append hprefix tailTrace_1945440
  have hstable : (prefixWord ++ tailWord_1945440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945440).length < 2 ^ (prefixWord ++ tailWord_1945440).sum := by decide
  have hdescent : baseEnd_1945440 < baseStart_1945440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945533 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1945533 : Nat := 118140960795 + 1945533 * 2 ^ 59
def prefixEnd_1945533 : Nat := 4983230072969 + 3 ^ 40 * 1945533 * 2
def baseEnd_1945533 : Nat := 443997136970596367506739

theorem tailTrace_1945533 : CollatzResearch.WordTrace tailWord_1945533 prefixEnd_1945533 443997136970596367506739 := by
  unfold tailWord_1945533
  simp only [CollatzResearch.WordTrace]
  refine ⟨70959418060673686428097253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47306278707115790952064835 70959418060673686428097253)
  ·
    refine ⟨13304890886376316205268235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70959418060673686428097253 13304890886376316205268235)
    ·
      refine ⟨19957336329564474307902353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304890886376316205268235 19957336329564474307902353)
      ·
        refine ⟨14968002247173355730926765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19957336329564474307902353 14968002247173355730926765)
        ·
          refine ⟨5613000842690008399097537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14968002247173355730926765 5613000842690008399097537)
          ·
            refine ⟨4209750632017506299323153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613000842690008399097537 4209750632017506299323153)
            ·
              refine ⟨3157312974013129724492365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209750632017506299323153 3157312974013129724492365)
              ·
                refine ⟨1183992365254923646684637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3157312974013129724492365 1183992365254923646684637)
                ·
                  refine ⟨443997136970596367506739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183992365254923646684637 443997136970596367506739)
                  ·
                    rfl

theorem cell21_1945533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1945533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945533 prefixEnd_1945533 := by exact prefixLift 1945533
  have htrace : WordTrace (prefixWord ++ tailWord_1945533) baseStart_1945533 baseEnd_1945533 := by
    simpa [prefixWord, tailWord_1945533, baseEnd_1945533] using wordTrace_append hprefix tailTrace_1945533
  have hstable : (prefixWord ++ tailWord_1945533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945533).length < 2 ^ (prefixWord ++ tailWord_1945533).sum := by decide
  have hdescent : baseEnd_1945533 < baseStart_1945533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945544 : List Nat := [2, 1, 3, 1, 4, 2, 8]
def baseStart_1945544 : Nat := 118140960795 + 1945544 * 2 ^ 59
def prefixEnd_1945544 : Nat := 4983230072969 + 3 ^ 40 * 1945544 * 2
def baseEnd_1945544 : Nat := 49333294146718088091487

theorem tailTrace_1945544 : CollatzResearch.WordTrace tailWord_1945544 prefixEnd_1945544 49333294146718088091487 := by
  unfold tailWord_1945544
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479909631816917653373843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47306546175755890204498457 35479909631816917653373843)
  ·
    refine ⟨53219864447725376480060765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479909631816917653373843 53219864447725376480060765)
    ·
      refine ⟨19957449167897016180022787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53219864447725376480060765 19957449167897016180022787)
      ·
        refine ⟨29936173751845524270034181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19957449167897016180022787 29936173751845524270034181)
        ·
          refine ⟨5613032578471035800631409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29936173751845524270034181 5613032578471035800631409)
          ·
            refine ⟨4209774433853276850473557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613032578471035800631409 4209774433853276850473557)
            ·
              refine ⟨49333294146718088091487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4209774433853276850473557 49333294146718088091487)
              ·
                rfl

theorem cell21_1945544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 8].length) (baseStart_1945544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945544 prefixEnd_1945544 := by exact prefixLift 1945544
  have htrace : WordTrace (prefixWord ++ tailWord_1945544) baseStart_1945544 baseEnd_1945544 := by
    simpa [prefixWord, tailWord_1945544, baseEnd_1945544] using wordTrace_append hprefix tailTrace_1945544
  have hstable : (prefixWord ++ tailWord_1945544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945544).length < 2 ^ (prefixWord ++ tailWord_1945544).sum := by decide
  have hdescent : baseEnd_1945544 < baseStart_1945544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945592 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_1945592 : Nat := 118140960795 + 1945592 * 2 ^ 59
def prefixEnd_1945592 : Nat := 4983230072969 + 3 ^ 40 * 1945592 * 2
def baseEnd_1945592 : Nat := 444010601574425376023285

theorem tailTrace_1945592 : CollatzResearch.WordTrace tailWord_1945592 prefixEnd_1945592 444010601574425376023285 := by
  unfold tailWord_1945592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35480784983729969752247515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47307713311639959669663353 35480784983729969752247515)
  ·
    refine ⟨53221177475594954628371273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35480784983729969752247515 53221177475594954628371273)
    ·
      refine ⟨39915883106696215971278455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53221177475594954628371273 39915883106696215971278455)
      ·
        refine ⟨59873824660044323956917683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39915883106696215971278455 59873824660044323956917683)
        ·
          refine ⟨89810736990066485935376525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59873824660044323956917683 89810736990066485935376525)
          ·
            refine ⟨33679026371274932225766197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89810736990066485935376525 33679026371274932225766197)
            ·
              refine ⟨3157408722307024896165581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33679026371274932225766197 3157408722307024896165581)
              ·
                refine ⟨1184028270865134336062093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3157408722307024896165581 1184028270865134336062093)
                ·
                  refine ⟨444010601574425376023285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184028270865134336062093 444010601574425376023285)
                  ·
                    rfl

theorem cell21_1945592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_1945592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945592 prefixEnd_1945592 := by exact prefixLift 1945592
  have htrace : WordTrace (prefixWord ++ tailWord_1945592) baseStart_1945592 baseEnd_1945592 := by
    simpa [prefixWord, tailWord_1945592, baseEnd_1945592] using wordTrace_append hprefix tailTrace_1945592
  have hstable : (prefixWord ++ tailWord_1945592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945592).length < 2 ^ (prefixWord ++ tailWord_1945592).sum := by decide
  have hdescent : baseEnd_1945592 < baseStart_1945592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945623 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_1945623 : Nat := 118140960795 + 1945623 * 2 ^ 59
def prefixEnd_1945623 : Nat := 4983230072969 + 3 ^ 40 * 1945623 * 2
def baseEnd_1945623 : Nat := 444017676196776211006555

theorem tailTrace_1945623 : CollatzResearch.WordTrace tailWord_1945623 prefixEnd_1945623 444017676196776211006555 := by
  unfold tailWord_1945623
  simp only [CollatzResearch.WordTrace]
  refine ⟨70962700630347631798873523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47308467086898421199249015 70962700630347631798873523)
  ·
    refine ⟨106444050945521447698310285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70962700630347631798873523 106444050945521447698310285)
    ·
      refine ⟨39916519104570542886866357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106444050945521447698310285 39916519104570542886866357)
      ·
        refine ⟨3742173666053488395643721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39916519104570542886866357 3742173666053488395643721)
        ·
          refine ⟨2806630249540116296732791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742173666053488395643721 2806630249540116296732791)
          ·
            refine ⟨4209945374310174445099187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806630249540116296732791 4209945374310174445099187)
            ·
              refine ⟨6314918061465261667648781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209945374310174445099187 6314918061465261667648781)
              ·
                refine ⟨2368094273049473125368293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314918061465261667648781 2368094273049473125368293)
                ·
                  refine ⟨444017676196776211006555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368094273049473125368293 444017676196776211006555)
                  ·
                    rfl

theorem cell21_1945623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_1945623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945623 prefixEnd_1945623 := by exact prefixLift 1945623
  have htrace : WordTrace (prefixWord ++ tailWord_1945623) baseStart_1945623 baseEnd_1945623 := by
    simpa [prefixWord, tailWord_1945623, baseEnd_1945623] using wordTrace_append hprefix tailTrace_1945623
  have hstable : (prefixWord ++ tailWord_1945623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945623).length < 2 ^ (prefixWord ++ tailWord_1945623).sum := by decide
  have hdescent : baseEnd_1945623 < baseStart_1945623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945761 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 3]
def baseStart_1945761 : Nat := 118140960795 + 1945761 * 2 ^ 59
def prefixEnd_1945761 : Nat := 4983230072969 + 3 ^ 40 * 1945761 * 2
def baseEnd_1945761 : Nat := 444049169676918637706273

theorem tailTrace_1945761 : CollatzResearch.WordTrace tailWord_1945761 prefixEnd_1945761 444049169676918637706273 := by
  unfold tailWord_1945761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70967733903847681367397137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47311822602565120911598091 70967733903847681367397137)
  ·
    refine ⟨53225800427885761025547853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70967733903847681367397137 53225800427885761025547853)
    ·
      refine ⟨19959675160457160384580445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53225800427885761025547853 19959675160457160384580445)
      ·
        refine ⟨7484878185171435144217667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19959675160457160384580445 7484878185171435144217667)
        ·
          refine ⟨11227317277757152716326501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484878185171435144217667 11227317277757152716326501)
          ·
            refine ⟨2105121989579466134311219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11227317277757152716326501 2105121989579466134311219)
            ·
              refine ⟨3157682984369199201466829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105121989579466134311219 3157682984369199201466829)
              ·
                refine ⟨1184131119138449700550061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3157682984369199201466829 1184131119138449700550061)
                ·
                  refine ⟨444049169676918637706273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184131119138449700550061 444049169676918637706273)
                  ·
                    rfl

theorem cell21_1945761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_1945761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945761 prefixEnd_1945761 := by exact prefixLift 1945761
  have htrace : WordTrace (prefixWord ++ tailWord_1945761) baseStart_1945761 baseEnd_1945761 := by
    simpa [prefixWord, tailWord_1945761, baseEnd_1945761] using wordTrace_append hprefix tailTrace_1945761
  have hstable : (prefixWord ++ tailWord_1945761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945761).length < 2 ^ (prefixWord ++ tailWord_1945761).sum := by decide
  have hdescent : baseEnd_1945761 < baseStart_1945761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945834 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_1945834 : Nat := 118140960795 + 1945834 * 2 ^ 59
def prefixEnd_1945834 : Nat := 4983230072969 + 3 ^ 40 * 1945834 * 2
def baseEnd_1945834 : Nat := 444065829271486732989457

theorem tailTrace_1945834 : CollatzResearch.WordTrace tailWord_1945834 prefixEnd_1945834 444065829271486732989457 := by
  unfold tailWord_1945834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742599108145803708701139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47313597621722143223203037 17742599108145803708701139)
  ·
    refine ⟨26613898662218705563051709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17742599108145803708701139 26613898662218705563051709)
    ·
      refine ⟨9980211998332014586144391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26613898662218705563051709 9980211998332014586144391)
      ·
        refine ⟨14970317997498021879216587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980211998332014586144391 14970317997498021879216587)
        ·
          refine ⟨22455476996247032818824881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14970317997498021879216587 22455476996247032818824881)
          ·
            refine ⟨16841607747185274614118661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22455476996247032818824881 16841607747185274614118661)
            ·
              refine ⟨3157801452597238990147249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16841607747185274614118661 3157801452597238990147249)
              ·
                refine ⟨2368351089447929242610437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157801452597238990147249 2368351089447929242610437)
                ·
                  refine ⟨444065829271486732989457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368351089447929242610437 444065829271486732989457)
                  ·
                    rfl

theorem cell21_1945834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_1945834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945834 prefixEnd_1945834 := by exact prefixLift 1945834
  have htrace : WordTrace (prefixWord ++ tailWord_1945834) baseStart_1945834 baseEnd_1945834 := by
    simpa [prefixWord, tailWord_1945834, baseEnd_1945834] using wordTrace_append hprefix tailTrace_1945834
  have hstable : (prefixWord ++ tailWord_1945834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945834).length < 2 ^ (prefixWord ++ tailWord_1945834).sum := by decide
  have hdescent : baseEnd_1945834 < baseStart_1945834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945837 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 3]
def baseStart_1945837 : Nat := 118140960795 + 1945837 * 2 ^ 59
def prefixEnd_1945837 : Nat := 4983230072969 + 3 ^ 40 * 1945837 * 2
def baseEnd_1945837 : Nat := 444066513912359394439451

theorem tailTrace_1945837 : CollatzResearch.WordTrace tailWord_1945837 prefixEnd_1945837 444066513912359394439451 := by
  unfold tailWord_1945837
  simp only [CollatzResearch.WordTrace]
  refine ⟨70970505851572346347163765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47313670567714897564775843 70970505851572346347163765)
  ·
    refine ⟨6653484923584907470046603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70970505851572346347163765 6653484923584907470046603)
    ·
      refine ⟨9980227385377361205069905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653484923584907470046603 9980227385377361205069905)
      ·
        refine ⟨7485170539033020903802429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9980227385377361205069905 7485170539033020903802429)
        ·
          refine ⟨2806938952137382838925911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7485170539033020903802429 2806938952137382838925911)
          ·
            refine ⟨4210408428206074258388867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806938952137382838925911 4210408428206074258388867)
            ·
              refine ⟨6315612642309111387583301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210408428206074258388867 6315612642309111387583301)
              ·
                refine ⟨1184177370432958385171869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6315612642309111387583301 1184177370432958385171869)
                ·
                  refine ⟨444066513912359394439451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184177370432958385171869 444066513912359394439451)
                  ·
                    rfl

theorem cell21_1945837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_1945837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945837 prefixEnd_1945837 := by exact prefixLift 1945837
  have htrace : WordTrace (prefixWord ++ tailWord_1945837) baseStart_1945837 baseEnd_1945837 := by
    simpa [prefixWord, tailWord_1945837, baseEnd_1945837] using wordTrace_append hprefix tailTrace_1945837
  have hstable : (prefixWord ++ tailWord_1945837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945837).length < 2 ^ (prefixWord ++ tailWord_1945837).sum := by decide
  have hdescent : baseEnd_1945837 < baseStart_1945837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945896 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_1945896 : Nat := 118140960795 + 1945896 * 2 ^ 59
def prefixEnd_1945896 : Nat := 4983230072969 + 3 ^ 40 * 1945896 * 2
def baseEnd_1945896 : Nat := 444079978516188402955997

theorem tailTrace_1945896 : CollatzResearch.WordTrace tailWord_1945896 prefixEnd_1945896 444079978516188402955997 := by
  unfold tailWord_1945896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35486328879179299711780771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47315105172239066282374361 35486328879179299711780771)
  ·
    refine ⟨53229493318768949567671157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35486328879179299711780771 53229493318768949567671157)
    ·
      refine ⟨4990264998634589021969171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53229493318768949567671157 4990264998634589021969171)
      ·
        refine ⟨7485397497951883532953757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990264998634589021969171 7485397497951883532953757)
        ·
          refine ⟨2807024061731956324857659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7485397497951883532953757 2807024061731956324857659)
          ·
            refine ⟨4210536092597934487286489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807024061731956324857659 4210536092597934487286489)
            ·
              refine ⟨3157902069448450865464867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4210536092597934487286489 3157902069448450865464867)
              ·
                refine ⟨4736853104172676298197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157902069448450865464867 4736853104172676298197301)
                ·
                  refine ⟨444079978516188402955997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736853104172676298197301 444079978516188402955997)
                  ·
                    rfl

theorem cell21_1945896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_1945896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945896 prefixEnd_1945896 := by exact prefixLift 1945896
  have htrace : WordTrace (prefixWord ++ tailWord_1945896) baseStart_1945896 baseEnd_1945896 := by
    simpa [prefixWord, tailWord_1945896, baseEnd_1945896] using wordTrace_append hprefix tailTrace_1945896
  have hstable : (prefixWord ++ tailWord_1945896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945896).length < 2 ^ (prefixWord ++ tailWord_1945896).sum := by decide
  have hdescent : baseEnd_1945896 < baseStart_1945896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945907 : List Nat := [1, 1, 1, 2, 5, 1, 2, 8]
def baseStart_1945907 : Nat := 118140960795 + 1945907 * 2 ^ 59
def prefixEnd_1945907 : Nat := 4983230072969 + 3 ^ 40 * 1945907 * 2
def baseEnd_1945907 : Nat := 148027496288684942757547

theorem tailTrace_1945907 : CollatzResearch.WordTrace tailWord_1945907 prefixEnd_1945907 148027496288684942757547 := by
  unfold tailWord_1945907
  simp only [CollatzResearch.WordTrace]
  refine ⟨70973058961318748302211975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47315372640879165534807983 70973058961318748302211975)
  ·
    refine ⟨106459588441978122453317963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70973058961318748302211975 106459588441978122453317963)
    ·
      refine ⟨159689382662967183679976945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106459588441978122453317963 159689382662967183679976945)
      ·
        refine ⟨119767036997225387759982709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159689382662967183679976945 119767036997225387759982709)
        ·
          refine ⟨11228159718489880102498379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119767036997225387759982709 11228159718489880102498379)
          ·
            refine ⟨16842239577734820153747569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228159718489880102498379 16842239577734820153747569)
            ·
              refine ⟨12631679683301115115310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16842239577734820153747569 12631679683301115115310677)
              ·
                refine ⟨148027496288684942757547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12631679683301115115310677 148027496288684942757547)
                ·
                  rfl

theorem cell21_1945907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_1945907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945907 prefixEnd_1945907 := by exact prefixLift 1945907
  have htrace : WordTrace (prefixWord ++ tailWord_1945907) baseStart_1945907 baseEnd_1945907 := by
    simpa [prefixWord, tailWord_1945907, baseEnd_1945907] using wordTrace_append hprefix tailTrace_1945907
  have hstable : (prefixWord ++ tailWord_1945907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945907).length < 2 ^ (prefixWord ++ tailWord_1945907).sum := by decide
  have hdescent : baseEnd_1945907 < baseStart_1945907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945938 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1945938 : Nat := 118140960795 + 1945938 * 2 ^ 59
def prefixEnd_1945938 : Nat := 4983230072969 + 3 ^ 40 * 1945938 * 2
def baseEnd_1945938 : Nat := 444089563488405663255911

theorem tailTrace_1945938 : CollatzResearch.WordTrace tailWord_1945938 prefixEnd_1945938 444089563488405663255911 := by
  unfold tailWord_1945938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743547406051610149147617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47316126416137627064393645 17743547406051610149147617)
  ·
    refine ⟨13307660554538707611860713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17743547406051610149147617 13307660554538707611860713)
    ·
      refine ⟨9980745415904030708895535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13307660554538707611860713 9980745415904030708895535)
      ·
        refine ⟨14971118123856046063343303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980745415904030708895535 14971118123856046063343303)
        ·
          refine ⟨22456677185784069095014955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971118123856046063343303 22456677185784069095014955)
          ·
            refine ⟨33685015778676103642522433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22456677185784069095014955 33685015778676103642522433)
            ·
              refine ⟨25263761834007077731891825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33685015778676103642522433 25263761834007077731891825)
              ·
                refine ⟨18947821375505308298918869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25263761834007077731891825 18947821375505308298918869)
                ·
                  refine ⟨444089563488405663255911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18947821375505308298918869 444089563488405663255911)
                  ·
                    rfl

theorem cell21_1945938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1945938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945938 prefixEnd_1945938 := by exact prefixLift 1945938
  have htrace : WordTrace (prefixWord ++ tailWord_1945938) baseStart_1945938 baseEnd_1945938 := by
    simpa [prefixWord, tailWord_1945938, baseEnd_1945938] using wordTrace_append hprefix tailTrace_1945938
  have hstable : (prefixWord ++ tailWord_1945938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945938).length < 2 ^ (prefixWord ++ tailWord_1945938).sum := by decide
  have hdescent : baseEnd_1945938 < baseStart_1945938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1945941 : List Nat := [1, 3, 2, 2, 5, 1, 7]
def baseStart_1945941 : Nat := 118140960795 + 1945941 * 2 ^ 59
def prefixEnd_1945941 : Nat := 4983230072969 + 3 ^ 40 * 1945941 * 2
def baseEnd_1945941 : Nat := 49343360903253147189545

theorem tailTrace_1945941 : CollatzResearch.WordTrace tailWord_1945941 prefixEnd_1945941 49343360903253147189545 := by
  unfold tailWord_1945941
  simp only [CollatzResearch.WordTrace]
  refine ⟨70974299043195572108949677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47316199362130381405966451 70974299043195572108949677)
  ·
    refine ⟨26615362141198339540856129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70974299043195572108949677 26615362141198339540856129)
    ·
      refine ⟨19961521605898754655642097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26615362141198339540856129 19961521605898754655642097)
      ·
        refine ⟨14971141204424065991731573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19961521605898754655642097 14971141204424065991731573)
        ·
          refine ⟨1403544487914756186724835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14971141204424065991731573 1403544487914756186724835)
          ·
            refine ⟨2105316731872134280087253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403544487914756186724835 2105316731872134280087253)
            ·
              refine ⟨49343360903253147189545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2105316731872134280087253 49343360903253147189545)
              ·
                rfl

theorem cell21_1945941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 7].length) (baseStart_1945941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1945941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1945941 prefixEnd_1945941 := by exact prefixLift 1945941
  have htrace : WordTrace (prefixWord ++ tailWord_1945941) baseStart_1945941 baseEnd_1945941 := by
    simpa [prefixWord, tailWord_1945941, baseEnd_1945941] using wordTrace_append hprefix tailTrace_1945941
  have hstable : (prefixWord ++ tailWord_1945941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1945941).length < 2 ^ (prefixWord ++ tailWord_1945941).sum := by decide
  have hdescent : baseEnd_1945941 < baseStart_1945941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1945941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946028 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1946028 : Nat := 118140960795 + 1946028 * 2 ^ 59
def prefixEnd_1946028 : Nat := 4983230072969 + 3 ^ 40 * 1946028 * 2
def baseEnd_1946028 : Nat := 444110102714585506755727

theorem tailTrace_1946028 : CollatzResearch.WordTrace tailWord_1946028 prefixEnd_1946028 444110102714585506755727 := by
  unfold tailWord_1946028
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488736096940192983683369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47318314795920257311577825 35488736096940192983683369)
  ·
    refine ⟨26616552072705144737762527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35488736096940192983683369 26616552072705144737762527)
    ·
      refine ⟨39924828109057717106643791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26616552072705144737762527 39924828109057717106643791)
      ·
        refine ⟨59887242163586575659965687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39924828109057717106643791 59887242163586575659965687)
        ·
          refine ⟨89830863245379863489948531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59887242163586575659965687 89830863245379863489948531)
          ·
            refine ⟨134746294868069795234922797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89830863245379863489948531 134746294868069795234922797)
            ·
              refine ⟨50529860575526173213096049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134746294868069795234922797 50529860575526173213096049)
              ·
                refine ⟨37897395431644629909822037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50529860575526173213096049 37897395431644629909822037)
                ·
                  refine ⟨444110102714585506755727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37897395431644629909822037 444110102714585506755727)
                  ·
                    rfl

theorem cell21_1946028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1946028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946028 prefixEnd_1946028 := by exact prefixLift 1946028
  have htrace : WordTrace (prefixWord ++ tailWord_1946028) baseStart_1946028 baseEnd_1946028 := by
    simpa [prefixWord, tailWord_1946028, baseEnd_1946028] using wordTrace_append hprefix tailTrace_1946028
  have hstable : (prefixWord ++ tailWord_1946028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946028).length < 2 ^ (prefixWord ++ tailWord_1946028).sum := by decide
  have hdescent : baseEnd_1946028 < baseStart_1946028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946093 : List Nat := [1, 5, 1, 3, 1, 1, 4, 5]
def baseStart_1946093 : Nat := 118140960795 + 1946093 * 2 ^ 59
def prefixEnd_1946093 : Nat := 4983230072969 + 3 ^ 40 * 1946093 * 2
def baseEnd_1946093 : Nat := 148041645533386612724087

theorem tailTrace_1946093 : CollatzResearch.WordTrace tailWord_1946093 prefixEnd_1946093 148041645533386612724087 := by
  unfold tailWord_1946093
  simp only [CollatzResearch.WordTrace]
  refine ⟨70979842938644902068482933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47319895292429934712321955 70979842938644902068482933)
  ·
    refine ⟨6654360275497959568920275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70979842938644902068482933 6654360275497959568920275)
    ·
      refine ⟨9981540413246939353380413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6654360275497959568920275 9981540413246939353380413)
      ·
        refine ⟨3743077654967602257517655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9981540413246939353380413 3743077654967602257517655)
        ·
          refine ⟨5614616482451403386276483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743077654967602257517655 5614616482451403386276483)
          ·
            refine ⟨8421924723677105079414725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614616482451403386276483 8421924723677105079414725)
            ·
              refine ⟨1579110885689457202390261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8421924723677105079414725 1579110885689457202390261)
              ·
                refine ⟨148041645533386612724087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579110885689457202390261 148041645533386612724087)
                ·
                  rfl

theorem cell21_1946093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].length) (baseStart_1946093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946093 prefixEnd_1946093 := by exact prefixLift 1946093
  have htrace : WordTrace (prefixWord ++ tailWord_1946093) baseStart_1946093 baseEnd_1946093 := by
    simpa [prefixWord, tailWord_1946093, baseEnd_1946093] using wordTrace_append hprefix tailTrace_1946093
  have hstable : (prefixWord ++ tailWord_1946093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946093).length < 2 ^ (prefixWord ++ tailWord_1946093).sum := by decide
  have hdescent : baseEnd_1946093 < baseStart_1946093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946104 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_1946104 : Nat := 118140960795 + 1946104 * 2 ^ 59
def prefixEnd_1946104 : Nat := 4983230072969 + 3 ^ 40 * 1946104 * 2
def baseEnd_1946104 : Nat := 444127446950026263488905

theorem tailTrace_1946104 : CollatzResearch.WordTrace tailWord_1946104 prefixEnd_1946104 444127446950026263488905 := by
  unfold tailWord_1946104
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490122070802525473566683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47320162761070033964755577 35490122070802525473566683)
  ·
    refine ⟨53235183106203788210350025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35490122070802525473566683 53235183106203788210350025)
    ·
      refine ⟨39926387329652841157762519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53235183106203788210350025 39926387329652841157762519)
      ·
        refine ⟨59889580994479261736643779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39926387329652841157762519 59889580994479261736643779)
        ·
          refine ⟨89834371491718892604965669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59889580994479261736643779 89834371491718892604965669)
          ·
            refine ⟨16843944654697292363431063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89834371491718892604965669 16843944654697292363431063)
            ·
              refine ⟨25265916982045938545146595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16843944654697292363431063 25265916982045938545146595)
              ·
                refine ⟨37898875473068907817719893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25265916982045938545146595 37898875473068907817719893)
                ·
                  refine ⟨444127446950026263488905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37898875473068907817719893 444127446950026263488905)
                  ·
                    rfl

theorem cell21_1946104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_1946104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946104 prefixEnd_1946104 := by exact prefixLift 1946104
  have htrace : WordTrace (prefixWord ++ tailWord_1946104) baseStart_1946104 baseEnd_1946104 := by
    simpa [prefixWord, tailWord_1946104, baseEnd_1946104] using wordTrace_append hprefix tailTrace_1946104
  have hstable : (prefixWord ++ tailWord_1946104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946104).length < 2 ^ (prefixWord ++ tailWord_1946104).sum := by decide
  have hdescent : baseEnd_1946104 < baseStart_1946104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946138 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1946138 : Nat := 118140960795 + 1946138 * 2 ^ 59
def prefixEnd_1946138 : Nat := 4983230072969 + 3 ^ 40 * 1946138 * 2
def baseEnd_1946138 : Nat := 444135206213249759922169

theorem tailTrace_1946138 : CollatzResearch.WordTrace tailWord_1946138 prefixEnd_1946138 444135206213249759922169 := by
  unfold tailWord_1946138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745371055870468688467767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47320989482321249835914045 17745371055870468688467767)
  ·
    refine ⟨26618056583805703032701651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17745371055870468688467767 26618056583805703032701651)
    ·
      refine ⟨39927084875708554549052477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26618056583805703032701651 39927084875708554549052477)
      ·
        refine ⟨14972656828390707955894679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39927084875708554549052477 14972656828390707955894679)
        ·
          refine ⟨22458985242586061933842019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14972656828390707955894679 22458985242586061933842019)
          ·
            refine ⟨33688477863879092900763029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22458985242586061933842019 33688477863879092900763029)
            ·
              refine ⟨1579147399869332479723267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33688477863879092900763029 1579147399869332479723267)
              ·
                refine ⟨2368721099803998719584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579147399869332479723267 2368721099803998719584901)
                ·
                  refine ⟨444135206213249759922169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368721099803998719584901 444135206213249759922169)
                  ·
                    rfl

theorem cell21_1946138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1946138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946138 prefixEnd_1946138 := by exact prefixLift 1946138
  have htrace : WordTrace (prefixWord ++ tailWord_1946138) baseStart_1946138 baseEnd_1946138 := by
    simpa [prefixWord, tailWord_1946138, baseEnd_1946138] using wordTrace_append hprefix tailTrace_1946138
  have hstable : (prefixWord ++ tailWord_1946138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946138).length < 2 ^ (prefixWord ++ tailWord_1946138).sum := by decide
  have hdescent : baseEnd_1946138 < baseStart_1946138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946152 : List Nat := [2, 1, 5, 2, 1, 1, 2, 7]
def baseStart_1946152 : Nat := 118140960795 + 1946152 * 2 ^ 59
def prefixEnd_1946152 : Nat := 4983230072969 + 3 ^ 40 * 1946152 * 2
def baseEnd_1946152 : Nat := 148046133734662948896269

theorem tailTrace_1946152 : CollatzResearch.WordTrace tailWord_1946152 prefixEnd_1946152 148046133734662948896269 := by
  unfold tailWord_1946152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490997422715577572440355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47321329896954103429920473 35490997422715577572440355)
  ·
    refine ⟨53236496134073366358660533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35490997422715577572440355 53236496134073366358660533)
    ·
      refine ⟨4990921512569378096124425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53236496134073366358660533 4990921512569378096124425)
      ·
        refine ⟨3743191134427033572093319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990921512569378096124425 3743191134427033572093319)
        ·
          refine ⟨5614786701640550358139979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743191134427033572093319 5614786701640550358139979)
          ·
            refine ⟨8422180052460825537209969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614786701640550358139979 8422180052460825537209969)
            ·
              refine ⟨6316635039345619152907477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8422180052460825537209969 6316635039345619152907477)
              ·
                refine ⟨148046133734662948896269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6316635039345619152907477 148046133734662948896269)
                ·
                  rfl

theorem cell21_1946152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_1946152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946152 prefixEnd_1946152 := by exact prefixLift 1946152
  have htrace : WordTrace (prefixWord ++ tailWord_1946152) baseStart_1946152 baseEnd_1946152 := by
    simpa [prefixWord, tailWord_1946152, baseEnd_1946152] using wordTrace_append hprefix tailTrace_1946152
  have hstable : (prefixWord ++ tailWord_1946152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946152).length < 2 ^ (prefixWord ++ tailWord_1946152).sum := by decide
  have hdescent : baseEnd_1946152 < baseStart_1946152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946197 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_1946197 : Nat := 118140960795 + 1946197 * 2 ^ 59
def prefixEnd_1946197 : Nat := 4983230072969 + 3 ^ 40 * 1946197 * 2
def baseEnd_1946197 : Nat := 444148670817078768438715

theorem tailTrace_1946197 : CollatzResearch.WordTrace tailWord_1946197 prefixEnd_1946197 444148670817078768438715 := by
  unfold tailWord_1946197
  simp only [CollatzResearch.WordTrace]
  refine ⟨70983636130268127830268845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47322424086845418553512563 70983636130268127830268845)
  ·
    refine ⟨26618863548850547936350817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70983636130268127830268845 26618863548850547936350817)
    ·
      refine ⟨19964147661637910952263113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26618863548850547936350817 19964147661637910952263113)
      ·
        refine ⟨14973110746228433214197335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19964147661637910952263113 14973110746228433214197335)
        ·
          refine ⟨22459666119342649821296003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14973110746228433214197335 22459666119342649821296003)
          ·
            refine ⟨33689499179013974731944005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22459666119342649821296003 33689499179013974731944005)
            ·
              refine ⟨6316781096065120262239501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33689499179013974731944005 6316781096065120262239501)
              ·
                refine ⟨2368792911024420098339813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6316781096065120262239501 2368792911024420098339813)
                ·
                  refine ⟨444148670817078768438715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368792911024420098339813 444148670817078768438715)
                  ·
                    rfl

theorem cell21_1946197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_1946197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946197 prefixEnd_1946197 := by exact prefixLift 1946197
  have htrace : WordTrace (prefixWord ++ tailWord_1946197) baseStart_1946197 baseEnd_1946197 := by
    simpa [prefixWord, tailWord_1946197, baseEnd_1946197] using wordTrace_append hprefix tailTrace_1946197
  have hstable : (prefixWord ++ tailWord_1946197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946197).length < 2 ^ (prefixWord ++ tailWord_1946197).sum := by decide
  have hdescent : baseEnd_1946197 < baseStart_1946197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946287 : List Nat := [1, 1, 2, 1, 2, 7, 7]
def baseStart_1946287 : Nat := 118140960795 + 1946287 * 2 ^ 59
def prefixEnd_1946287 : Nat := 4983230072969 + 3 ^ 40 * 1946287 * 2
def baseEnd_1946287 : Nat := 49352134449250956882059

theorem tailTrace_1946287 : CollatzResearch.WordTrace tailWord_1946287 prefixEnd_1946287 49352134449250956882059 := by
  unfold tailWord_1946287
  simp only [CollatzResearch.WordTrace]
  refine ⟨70986918699942073201045115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47324612466628048800696743 70986918699942073201045115)
  ·
    refine ⟨106480378049913109801567673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70986918699942073201045115 106480378049913109801567673)
    ·
      refine ⟨79860283537434832351175755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106480378049913109801567673 79860283537434832351175755)
      ·
        refine ⟨119790425306152248526763633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79860283537434832351175755 119790425306152248526763633)
        ·
          refine ⟨89842818979614186395072725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119790425306152248526763633 89842818979614186395072725)
          ·
            refine ⟨2105691069834707493634517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89842818979614186395072725 2105691069834707493634517)
            ·
              refine ⟨49352134449250956882059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2105691069834707493634517 49352134449250956882059)
              ·
                rfl

theorem cell21_1946287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 7].length) (baseStart_1946287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946287 prefixEnd_1946287 := by exact prefixLift 1946287
  have htrace : WordTrace (prefixWord ++ tailWord_1946287) baseStart_1946287 baseEnd_1946287 := by
    simpa [prefixWord, tailWord_1946287, baseEnd_1946287] using wordTrace_append hprefix tailTrace_1946287
  have hstable : (prefixWord ++ tailWord_1946287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946287).length < 2 ^ (prefixWord ++ tailWord_1946287).sum := by decide
  have hdescent : baseEnd_1946287 < baseStart_1946287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946293 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 3]
def baseStart_1946293 : Nat := 118140960795 + 1946293 * 2 ^ 59
def prefixEnd_1946293 : Nat := 4983230072969 + 3 ^ 40 * 1946293 * 2
def baseEnd_1946293 : Nat := 444170579325003934838519

theorem tailTrace_1946293 : CollatzResearch.WordTrace tailWord_1946293 prefixEnd_1946293 444170579325003934838519 := by
  unfold tailWord_1946293
  simp only [CollatzResearch.WordTrace]
  refine ⟨70987137537920336225763533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47324758358613557483842355 70987137537920336225763533)
  ·
    refine ⟨26620176576720126084661325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70987137537920336225763533 26620176576720126084661325)
    ·
      refine ⟨9982566216270047281747997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26620176576720126084661325 9982566216270047281747997)
      ·
        refine ⟨3743462331101267730655499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9982566216270047281747997 3743462331101267730655499)
        ·
          refine ⟨5615193496651901595983249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743462331101267730655499 5615193496651901595983249)
          ·
            refine ⟨4211395122488926196987437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5615193496651901595983249 4211395122488926196987437)
            ·
              refine ⟨1579273170933347323870289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4211395122488926196987437 1579273170933347323870289)
              ·
                refine ⟨1184454878200010492902717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579273170933347323870289 1184454878200010492902717)
                ·
                  refine ⟨444170579325003934838519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184454878200010492902717 444170579325003934838519)
                  ·
                    rfl

theorem cell21_1946293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_1946293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946293 prefixEnd_1946293 := by exact prefixLift 1946293
  have htrace : WordTrace (prefixWord ++ tailWord_1946293) baseStart_1946293 baseEnd_1946293 := by
    simpa [prefixWord, tailWord_1946293, baseEnd_1946293] using wordTrace_append hprefix tailTrace_1946293
  have hstable : (prefixWord ++ tailWord_1946293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946293).length < 2 ^ (prefixWord ++ tailWord_1946293).sum := by decide
  have hdescent : baseEnd_1946293 < baseStart_1946293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946366 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1946366 : Nat := 118140960795 + 1946366 * 2 ^ 59
def prefixEnd_1946366 : Nat := 4983230072969 + 3 ^ 40 * 1946366 * 2
def baseEnd_1946366 : Nat := 444187238919572030121703

theorem tailTrace_1946366 : CollatzResearch.WordTrace tailWord_1946366 prefixEnd_1946366 444187238919572030121703 := by
  unfold tailWord_1946366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873725008331983711646369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47326533377770579795447301 8873725008331983711646369)
  ·
    refine ⟨6655293756248987783734777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873725008331983711646369 6655293756248987783734777)
    ·
      refine ⟨4991470317186740837801083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6655293756248987783734777 4991470317186740837801083)
      ·
        refine ⟨7487205475780111256701625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991470317186740837801083 7487205475780111256701625)
        ·
          refine ⟨5615404106835083442526219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487205475780111256701625 5615404106835083442526219)
          ·
            refine ⟨8423106160252625163789329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615404106835083442526219 8423106160252625163789329)
            ·
              refine ⟨6317329620189468872841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8423106160252625163789329 6317329620189468872841997)
              ·
                refine ⟨2368998607571050827315749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6317329620189468872841997 2368998607571050827315749)
                ·
                  refine ⟨444187238919572030121703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368998607571050827315749 444187238919572030121703)
                  ·
                    rfl

theorem cell21_1946366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1946366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946366 prefixEnd_1946366 := by exact prefixLift 1946366
  have htrace : WordTrace (prefixWord ++ tailWord_1946366) baseStart_1946366 baseEnd_1946366 := by
    simpa [prefixWord, tailWord_1946366, baseEnd_1946366] using wordTrace_append hprefix tailTrace_1946366
  have hstable : (prefixWord ++ tailWord_1946366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946366).length < 2 ^ (prefixWord ++ tailWord_1946366).sum := by decide
  have hdescent : baseEnd_1946366 < baseStart_1946366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946377 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_1946377 : Nat := 118140960795 + 1946377 * 2 ^ 59
def prefixEnd_1946377 : Nat := 4983230072969 + 3 ^ 40 * 1946377 * 2
def baseEnd_1946377 : Nat := 444189749269438455438347

theorem tailTrace_1946377 : CollatzResearch.WordTrace tailWord_1946377 prefixEnd_1946377 444189749269438455438347 := by
  unfold tailWord_1946377
  simp only [CollatzResearch.WordTrace]
  refine ⟨70990201269616018571821385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47326800846410679047880923 70990201269616018571821385)
  ·
    refine ⟨53242650952212013928866039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70990201269616018571821385 53242650952212013928866039)
    ·
      refine ⟨79863976428318020893299059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53242650952212013928866039 79863976428318020893299059)
      ·
        refine ⟨119795964642477031339948589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79863976428318020893299059 119795964642477031339948589)
        ·
          refine ⟨44923486740928886752480721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119795964642477031339948589 44923486740928886752480721)
          ·
            refine ⟨33692615055696665064360541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44923486740928886752480721 33692615055696665064360541)
            ·
              refine ⟨12634730645886249399135203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33692615055696665064360541 12634730645886249399135203)
              ·
                refine ⟨18952095968829374098702805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634730645886249399135203 18952095968829374098702805)
                ·
                  refine ⟨444189749269438455438347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18952095968829374098702805 444189749269438455438347)
                  ·
                    rfl

theorem cell21_1946377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_1946377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946377 prefixEnd_1946377 := by exact prefixLift 1946377
  have htrace : WordTrace (prefixWord ++ tailWord_1946377) baseStart_1946377 baseEnd_1946377 := by
    simpa [prefixWord, tailWord_1946377, baseEnd_1946377] using wordTrace_append hprefix tailTrace_1946377
  have hstable : (prefixWord ++ tailWord_1946377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946377).length < 2 ^ (prefixWord ++ tailWord_1946377).sum := by decide
  have hdescent : baseEnd_1946377 < baseStart_1946377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946636 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1946636 : Nat := 118140960795 + 1946636 * 2 ^ 59
def prefixEnd_1946636 : Nat := 4983230072969 + 3 ^ 40 * 1946636 * 2
def baseEnd_1946636 : Nat := 444248856598111560621151

theorem tailTrace_1946636 : CollatzResearch.WordTrace tailWord_1946636 prefixEnd_1946636 444248856598111560621151 := by
  unfold tailWord_1946636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35499823887838852902749881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47333098517118470536999841 35499823887838852902749881)
  ·
    refine ⟨26624867915879139677062411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35499823887838852902749881 26624867915879139677062411)
    ·
      refine ⟨39937301873818709515593617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26624867915879139677062411 39937301873818709515593617)
      ·
        refine ⟨29952976405364032136695213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39937301873818709515593617 29952976405364032136695213)
        ·
          refine ⟨11232366152011512051260705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29952976405364032136695213 11232366152011512051260705)
          ·
            refine ⟨8424274614008634038445529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232366152011512051260705 8424274614008634038445529)
            ·
              refine ⟨6318205960506475528834147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8424274614008634038445529 6318205960506475528834147)
              ·
                refine ⟨9477308940759713293251221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318205960506475528834147 9477308940759713293251221)
                ·
                  refine ⟨444248856598111560621151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9477308940759713293251221 444248856598111560621151)
                  ·
                    rfl

theorem cell21_1946636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1946636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946636 prefixEnd_1946636 := by exact prefixLift 1946636
  have htrace : WordTrace (prefixWord ++ tailWord_1946636) baseStart_1946636 baseEnd_1946636 := by
    simpa [prefixWord, tailWord_1946636, baseEnd_1946636] using wordTrace_append hprefix tailTrace_1946636
  have hstable : (prefixWord ++ tailWord_1946636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946636).length < 2 ^ (prefixWord ++ tailWord_1946636).sum := by decide
  have hdescent : baseEnd_1946636 < baseStart_1946636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946642 : List Nat := [3, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1946642 : Nat := 118140960795 + 1946642 * 2 ^ 59
def prefixEnd_1946642 : Nat := 4983230072969 + 3 ^ 40 * 1946642 * 2
def baseEnd_1946642 : Nat := 148083408626618961173713

theorem tailTrace_1946642 : CollatzResearch.WordTrace tailWord_1946642 prefixEnd_1946642 148083408626618961173713 := by
  unfold tailWord_1946642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749966653413992207554545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47333244409103979220145453 17749966653413992207554545)
  ·
    refine ⟨13312474990060494155665909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17749966653413992207554545 13312474990060494155665909)
    ·
      refine ⟨1248044530318171327093679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13312474990060494155665909 1248044530318171327093679)
      ·
        refine ⟨1872066795477256990640519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248044530318171327093679 1872066795477256990640519)
        ·
          refine ⟨2808100193215885485960779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872066795477256990640519 2808100193215885485960779)
          ·
            refine ⟨4212150289823828228941169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808100193215885485960779 4212150289823828228941169)
            ·
              refine ⟨3159112717367871171705877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212150289823828228941169 3159112717367871171705877)
              ·
                refine ⟨148083408626618961173713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3159112717367871171705877 148083408626618961173713)
                ·
                  rfl

theorem cell21_1946642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1946642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946642 prefixEnd_1946642 := by exact prefixLift 1946642
  have htrace : WordTrace (prefixWord ++ tailWord_1946642) baseStart_1946642 baseEnd_1946642 := by
    simpa [prefixWord, tailWord_1946642, baseEnd_1946642] using wordTrace_append hprefix tailTrace_1946642
  have hstable : (prefixWord ++ tailWord_1946642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946642).length < 2 ^ (prefixWord ++ tailWord_1946642).sum := by decide
  have hdescent : baseEnd_1946642 < baseStart_1946642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946712 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_1946712 : Nat := 118140960795 + 1946712 * 2 ^ 59
def prefixEnd_1946712 : Nat := 4983230072969 + 3 ^ 40 * 1946712 * 2
def baseEnd_1946712 : Nat := 444266200833552317354329

theorem tailTrace_1946712 : CollatzResearch.WordTrace tailWord_1946712 prefixEnd_1946712 444266200833552317354329 := by
  unfold tailWord_1946712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35501209861701185392633195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47334946482268247190177593 35501209861701185392633195)
  ·
    refine ⟨53251814792551778088949793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35501209861701185392633195 53251814792551778088949793)
    ·
      refine ⟨39938861094413833566712345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53251814792551778088949793 39938861094413833566712345)
      ·
        refine ⟨29954145820810375175034259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39938861094413833566712345 29954145820810375175034259)
        ·
          refine ⟨44931218731215562762551389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954145820810375175034259 44931218731215562762551389)
          ·
            refine ⟨16849207024205836035956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44931218731215562762551389 16849207024205836035956771)
            ·
              refine ⟨25273810536308754053935157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16849207024205836035956771 25273810536308754053935157)
              ·
                refine ⟨2369419737778945692556421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25273810536308754053935157 2369419737778945692556421)
                ·
                  refine ⟨444266200833552317354329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369419737778945692556421 444266200833552317354329)
                  ·
                    rfl

theorem cell21_1946712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_1946712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946712 prefixEnd_1946712 := by exact prefixLift 1946712
  have htrace : WordTrace (prefixWord ++ tailWord_1946712) baseStart_1946712 baseEnd_1946712 := by
    simpa [prefixWord, tailWord_1946712, baseEnd_1946712] using wordTrace_append hprefix tailTrace_1946712
  have hstable : (prefixWord ++ tailWord_1946712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946712).length < 2 ^ (prefixWord ++ tailWord_1946712).sum := by decide
  have hdescent : baseEnd_1946712 < baseStart_1946712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946718 : List Nat := [4, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1946718 : Nat := 118140960795 + 1946718 * 2 ^ 59
def prefixEnd_1946718 : Nat := 4983230072969 + 3 ^ 40 * 1946718 * 2
def baseEnd_1946718 : Nat := 148089190038432546751439

theorem tailTrace_1946718 : CollatzResearch.WordTrace tailWord_1946718 prefixEnd_1946718 148089190038432546751439 := by
  unfold tailWord_1946718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875329820172579226248101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47335092374253755873323205 8875329820172579226248101)
  ·
    refine ⟨1664124341282358604921519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8875329820172579226248101 1664124341282358604921519)
    ·
      refine ⟨2496186511923537907382279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664124341282358604921519 2496186511923537907382279)
      ·
        refine ⟨3744279767885306861073419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496186511923537907382279 3744279767885306861073419)
        ·
          refine ⟨5616419651827960291610129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744279767885306861073419 5616419651827960291610129)
          ·
            refine ⟨4212314738870970218707597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5616419651827960291610129 4212314738870970218707597)
            ·
              refine ⟨1579618027076613832015349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4212314738870970218707597 1579618027076613832015349)
              ·
                refine ⟨148089190038432546751439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579618027076613832015349 148089190038432546751439)
                ·
                  rfl

theorem cell21_1946718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1946718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946718 prefixEnd_1946718 := by exact prefixLift 1946718
  have htrace : WordTrace (prefixWord ++ tailWord_1946718) baseStart_1946718 baseEnd_1946718 := by
    simpa [prefixWord, tailWord_1946718, baseEnd_1946718] using wordTrace_append hprefix tailTrace_1946718
  have hstable : (prefixWord ++ tailWord_1946718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946718).length < 2 ^ (prefixWord ++ tailWord_1946718).sum := by decide
  have hdescent : baseEnd_1946718 < baseStart_1946718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946788 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1946788 : Nat := 118140960795 + 1946788 * 2 ^ 59
def prefixEnd_1946788 : Nat := 4983230072969 + 3 ^ 40 * 1946788 * 2
def baseEnd_1946788 : Nat := 444283545068993074087507

theorem tailTrace_1946788 : CollatzResearch.WordTrace tailWord_1946788 prefixEnd_1946788 444283545068993074087507 := by
  unfold tailWord_1946788
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502595835563517882516509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47336794447418023843355345 35502595835563517882516509)
  ·
    refine ⟨13313473438336319205943691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35502595835563517882516509 13313473438336319205943691)
    ·
      refine ⟨19970210157504478808915537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313473438336319205943691 19970210157504478808915537)
      ·
        refine ⟨14977657618128359106686653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19970210157504478808915537 14977657618128359106686653)
        ·
          refine ⟨5616621606798134665007495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14977657618128359106686653 5616621606798134665007495)
          ·
            refine ⟨8424932410197201997511243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616621606798134665007495 8424932410197201997511243)
            ·
              refine ⟨12637398615295802996266865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424932410197201997511243 12637398615295802996266865)
              ·
                refine ⟨9478048961471852247200149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12637398615295802996266865 9478048961471852247200149)
                ·
                  refine ⟨444283545068993074087507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9478048961471852247200149 444283545068993074087507)
                  ·
                    rfl

theorem cell21_1946788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1946788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946788 prefixEnd_1946788 := by exact prefixLift 1946788
  have htrace : WordTrace (prefixWord ++ tailWord_1946788) baseStart_1946788 baseEnd_1946788 := by
    simpa [prefixWord, tailWord_1946788, baseEnd_1946788] using wordTrace_append hprefix tailTrace_1946788
  have hstable : (prefixWord ++ tailWord_1946788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946788).length < 2 ^ (prefixWord ++ tailWord_1946788).sum := by decide
  have hdescent : baseEnd_1946788 < baseStart_1946788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946802 : List Nat := [3, 2, 1, 1, 1, 4, 9]
def baseStart_1946802 : Nat := 118140960795 + 1946802 * 2 ^ 59
def prefixEnd_1946802 : Nat := 4983230072969 + 3 ^ 40 * 1946802 * 2
def baseEnd_1946802 : Nat := 49365193339970240094905

theorem tailTrace_1946802 : CollatzResearch.WordTrace tailWord_1946802 prefixEnd_1946802 49365193339970240094905 := by
  unfold tailWord_1946802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751425573269079039010665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47337134862050877437361773 17751425573269079039010665)
  ·
    refine ⟨13313569179951809279257999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17751425573269079039010665 13313569179951809279257999)
    ·
      refine ⟨19970353769927713918886999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313569179951809279257999 19970353769927713918886999)
      ·
        refine ⟨29955530654891570878330499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970353769927713918886999 29955530654891570878330499)
        ·
          refine ⟨44933295982337356317495749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29955530654891570878330499 44933295982337356317495749)
          ·
            refine ⟨8424992996688254309530453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44933295982337356317495749 8424992996688254309530453)
            ·
              refine ⟨49365193339970240094905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8424992996688254309530453 49365193339970240094905)
              ·
                rfl

theorem cell21_1946802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 9].length) (baseStart_1946802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946802 prefixEnd_1946802 := by exact prefixLift 1946802
  have htrace : WordTrace (prefixWord ++ tailWord_1946802) baseStart_1946802 baseEnd_1946802 := by
    simpa [prefixWord, tailWord_1946802, baseEnd_1946802] using wordTrace_append hprefix tailTrace_1946802
  have hstable : (prefixWord ++ tailWord_1946802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946802).length < 2 ^ (prefixWord ++ tailWord_1946802).sum := by decide
  have hdescent : baseEnd_1946802 < baseStart_1946802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946847 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_1946847 : Nat := 118140960795 + 1946847 * 2 ^ 59
def prefixEnd_1946847 : Nat := 4983230072969 + 3 ^ 40 * 1946847 * 2
def baseEnd_1946847 : Nat := 444297009672822082604053

theorem tailTrace_1946847 : CollatzResearch.WordTrace tailWord_1946847 prefixEnd_1946847 444297009672822082604053 := by
  unfold tailWord_1946847
  simp only [CollatzResearch.WordTrace]
  refine ⟨71007343577913288841430795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47338229051942192560953863 71007343577913288841430795)
  ·
    refine ⟨106511015366869933262146193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71007343577913288841430795 106511015366869933262146193)
    ·
      refine ⟨79883261525152449946609645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106511015366869933262146193 79883261525152449946609645)
      ·
        refine ⟨29956223071932168729978617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79883261525152449946609645 29956223071932168729978617)
        ·
          refine ⟨22467167303949126547483963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29956223071932168729978617 22467167303949126547483963)
          ·
            refine ⟨33700750955923689821225945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22467167303949126547483963 33700750955923689821225945)
            ·
              refine ⟨25275563216942767365919459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33700750955923689821225945 25275563216942767365919459)
              ·
                refine ⟨37913344825414151048879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25275563216942767365919459 37913344825414151048879189)
                ·
                  refine ⟨444297009672822082604053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37913344825414151048879189 444297009672822082604053)
                  ·
                    rfl

theorem cell21_1946847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_1946847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946847 prefixEnd_1946847 := by exact prefixLift 1946847
  have htrace : WordTrace (prefixWord ++ tailWord_1946847) baseStart_1946847 baseEnd_1946847 := by
    simpa [prefixWord, tailWord_1946847, baseEnd_1946847] using wordTrace_append hprefix tailTrace_1946847
  have hstable : (prefixWord ++ tailWord_1946847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946847).length < 2 ^ (prefixWord ++ tailWord_1946847).sum := by decide
  have hdescent : baseEnd_1946847 < baseStart_1946847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1946867 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 3]
def baseStart_1946867 : Nat := 118140960795 + 1946867 * 2 ^ 59
def prefixEnd_1946867 : Nat := 4983230072969 + 3 ^ 40 * 1946867 * 2
def baseEnd_1946867 : Nat := 444301573945306492270679

theorem tailTrace_1946867 : CollatzResearch.WordTrace tailWord_1946867 prefixEnd_1946867 444301573945306492270679 := by
  unfold tailWord_1946867
  simp only [CollatzResearch.WordTrace]
  refine ⟨71008073037840832257158855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47338715358560554838105903 71008073037840832257158855)
  ·
    refine ⟨106512109556761248385738283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71008073037840832257158855 106512109556761248385738283)
    ·
      refine ⟨159768164335141872578607425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106512109556761248385738283 159768164335141872578607425)
      ·
        refine ⟨119826123251356404433955569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159768164335141872578607425 119826123251356404433955569)
        ·
          refine ⟨89869592438517303325466677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119826123251356404433955569 89869592438517303325466677)
          ·
            refine ⟨8425274291110997186762501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89869592438517303325466677 8425274291110997186762501)
            ·
              refine ⟨1579738929583311972517969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8425274291110997186762501 1579738929583311972517969)
              ·
                refine ⟨1184804197187483979388477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579738929583311972517969 1184804197187483979388477)
                ·
                  refine ⟨444301573945306492270679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184804197187483979388477 444301573945306492270679)
                  ·
                    rfl

theorem cell21_1946867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].length) (baseStart_1946867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1946867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1946867 prefixEnd_1946867 := by exact prefixLift 1946867
  have htrace : WordTrace (prefixWord ++ tailWord_1946867) baseStart_1946867 baseEnd_1946867 := by
    simpa [prefixWord, tailWord_1946867, baseEnd_1946867] using wordTrace_append hprefix tailTrace_1946867
  have hstable : (prefixWord ++ tailWord_1946867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1946867).length < 2 ^ (prefixWord ++ tailWord_1946867).sum := by decide
  have hdescent : baseEnd_1946867 < baseStart_1946867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1946867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947036 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_1947036 : Nat := 118140960795 + 1947036 * 2 ^ 59
def prefixEnd_1947036 : Nat := 4983230072969 + 3 ^ 40 * 1947036 * 2
def baseEnd_1947036 : Nat := 444340142047799753953667

theorem tailTrace_1947036 : CollatzResearch.WordTrace tailWord_1947036 prefixEnd_1947036 444340142047799753953667 := by
  unfold tailWord_1947036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35507118487114287060030481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47342824649485716080040641 35507118487114287060030481)
  ·
    refine ⟨26630338865335715295022861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35507118487114287060030481 26630338865335715295022861)
    ·
      refine ⟨9986377074500893235633573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26630338865335715295022861 9986377074500893235633573)
      ·
        refine ⟨1872445701468917481681295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9986377074500893235633573 1872445701468917481681295)
        ·
          refine ⟨2808668552203376222521943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872445701468917481681295 2808668552203376222521943)
          ·
            refine ⟨4213002828305064333782915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808668552203376222521943 4213002828305064333782915)
            ·
              refine ⟨6319504242457596500674373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213002828305064333782915 6319504242457596500674373)
              ·
                refine ⟨1184907045460799343876445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6319504242457596500674373 1184907045460799343876445)
                ·
                  refine ⟨444340142047799753953667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184907045460799343876445 444340142047799753953667)
                  ·
                    rfl

theorem cell21_1947036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_1947036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947036 prefixEnd_1947036 := by exact prefixLift 1947036
  have htrace : WordTrace (prefixWord ++ tailWord_1947036) baseStart_1947036 baseEnd_1947036 := by
    simpa [prefixWord, tailWord_1947036, baseEnd_1947036] using wordTrace_append hprefix tailTrace_1947036
  have hstable : (prefixWord ++ tailWord_1947036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947036).length < 2 ^ (prefixWord ++ tailWord_1947036).sum := by decide
  have hdescent : baseEnd_1947036 < baseStart_1947036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947061 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_1947061 : Nat := 118140960795 + 1947061 * 2 ^ 59
def prefixEnd_1947061 : Nat := 4983230072969 + 3 ^ 40 * 1947061 * 2
def baseEnd_1947061 : Nat := 444345847388405266036949

theorem tailTrace_1947061 : CollatzResearch.WordTrace tailWord_1947061 prefixEnd_1947061 444345847388405266036949 := by
  unfold tailWord_1947061
  simp only [CollatzResearch.WordTrace]
  refine ⟨71015148799138003389721037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47343432532758668926480691 71015148799138003389721037)
  ·
    refine ⟨26630680799676751271145389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71015148799138003389721037 26630680799676751271145389)
    ·
      refine ⟨9986505299878781726679521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26630680799676751271145389 9986505299878781726679521)
      ·
        refine ⟨7489878974909086295009641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9986505299878781726679521 7489878974909086295009641)
        ·
          refine ⟨5617409231181814721257231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7489878974909086295009641 5617409231181814721257231)
          ·
            refine ⟨8426113846772722081885847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617409231181814721257231 8426113846772722081885847)
            ·
              refine ⟨12639170770159083122828771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426113846772722081885847 12639170770159083122828771)
              ·
                refine ⟨18958756155238624684243157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12639170770159083122828771 18958756155238624684243157)
                ·
                  refine ⟨444345847388405266036949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18958756155238624684243157 444345847388405266036949)
                  ·
                    rfl

theorem cell21_1947061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_1947061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947061 prefixEnd_1947061 := by exact prefixLift 1947061
  have htrace : WordTrace (prefixWord ++ tailWord_1947061) baseStart_1947061 baseEnd_1947061 := by
    simpa [prefixWord, tailWord_1947061, baseEnd_1947061] using wordTrace_append hprefix tailTrace_1947061
  have hstable : (prefixWord ++ tailWord_1947061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947061).length < 2 ^ (prefixWord ++ tailWord_1947061).sum := by decide
  have hdescent : baseEnd_1947061 < baseStart_1947061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947140 : List Nat := [2, 3, 2, 3, 3, 1, 7]
def baseStart_1947140 : Nat := 118140960795 + 1947140 * 2 ^ 59
def prefixEnd_1947140 : Nat := 4983230072969 + 3 ^ 40 * 1947140 * 2
def baseEnd_1947140 : Nat := 49373764029413187135569

theorem tailTrace_1947140 : CollatzResearch.WordTrace tailWord_1947140 prefixEnd_1947140 49373764029413187135569 := by
  unfold tailWord_1947140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35509015082925899940923437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47345353443901199921231249 35509015082925899940923437)
  ·
    refine ⟨13315880656097212477846289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35509015082925899940923437 13315880656097212477846289)
    ·
      refine ⟨9986910492072909358384717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13315880656097212477846289 9986910492072909358384717)
      ·
        refine ⟨3745091434527341009394269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9986910492072909358384717 3745091434527341009394269)
        ·
          refine ⟨1404409287947752878522851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3745091434527341009394269 1404409287947752878522851)
          ·
            refine ⟨2106613931921629317784277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404409287947752878522851 2106613931921629317784277)
            ·
              refine ⟨49373764029413187135569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2106613931921629317784277 49373764029413187135569)
              ·
                rfl

theorem cell21_1947140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 7].length) (baseStart_1947140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947140 prefixEnd_1947140 := by exact prefixLift 1947140
  have htrace : WordTrace (prefixWord ++ tailWord_1947140) baseStart_1947140 baseEnd_1947140 := by
    simpa [prefixWord, tailWord_1947140, baseEnd_1947140] using wordTrace_append hprefix tailTrace_1947140
  have hstable : (prefixWord ++ tailWord_1947140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947140).length < 2 ^ (prefixWord ++ tailWord_1947140).sum := by decide
  have hdescent : baseEnd_1947140 < baseStart_1947140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947241 : List Nat := [1, 2, 1, 1, 1, 4, 2, 9]
def baseStart_1947241 : Nat := 118140960795 + 1947241 * 2 ^ 59
def prefixEnd_1947241 : Nat := 4983230072969 + 3 ^ 40 * 1947241 * 2
def baseEnd_1947241 : Nat := 148128975280254984345527

theorem tailTrace_1947241 : CollatzResearch.WordTrace tailWord_1947241 prefixEnd_1947241 148128975280254984345527 := by
  unfold tailWord_1947241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021713938485894131273577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47347809292323929420849051 71021713938485894131273577)
  ·
    refine ⟨53266285453864420598455183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71021713938485894131273577 53266285453864420598455183)
    ·
      refine ⟨79899428180796630897682775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53266285453864420598455183 79899428180796630897682775)
      ·
        refine ⟨119849142271194946346524163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79899428180796630897682775 119849142271194946346524163)
        ·
          refine ⟨179773713406792419519786245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119849142271194946346524163 179773713406792419519786245)
          ·
            refine ⟨33707571263773578659959921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179773713406792419519786245 33707571263773578659959921)
            ·
              refine ⟨25280678447830183994969941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33707571263773578659959921 25280678447830183994969941)
              ·
                refine ⟨148128975280254984345527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25280678447830183994969941 148128975280254984345527)
                ·
                  rfl

theorem cell21_1947241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_1947241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947241 prefixEnd_1947241 := by exact prefixLift 1947241
  have htrace : WordTrace (prefixWord ++ tailWord_1947241) baseStart_1947241 baseEnd_1947241 := by
    simpa [prefixWord, tailWord_1947241, baseEnd_1947241] using wordTrace_append hprefix tailTrace_1947241
  have hstable : (prefixWord ++ tailWord_1947241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947241).length < 2 ^ (prefixWord ++ tailWord_1947241).sum := by decide
  have hdescent : baseEnd_1947241 < baseStart_1947241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947261 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1947261 : Nat := 118140960795 + 1947261 * 2 ^ 59
def prefixEnd_1947261 : Nat := 4983230072969 + 3 ^ 40 * 1947261 * 2
def baseEnd_1947261 : Nat := 444391490113249362703207

theorem tailTrace_1947261 : CollatzResearch.WordTrace tailWord_1947261 prefixEnd_1947261 444391490113249362703207 := by
  unfold tailWord_1947261
  simp only [CollatzResearch.WordTrace]
  refine ⟨71022443398413437547001637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47348295598942291698001091 71022443398413437547001637)
  ·
    refine ⟨13316708137202519540062807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71022443398413437547001637 13316708137202519540062807)
    ·
      refine ⟨19975062205803779310094211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316708137202519540062807 19975062205803779310094211)
      ·
        refine ⟨29962593308705668965141317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19975062205803779310094211 29962593308705668965141317)
        ·
          refine ⟨5617986245382312930963997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29962593308705668965141317 5617986245382312930963997)
          ·
            refine ⟨2106744842018367349111499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5617986245382312930963997 2106744842018367349111499)
            ·
              refine ⟨3160117263027551023667249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106744842018367349111499 3160117263027551023667249)
              ·
                refine ⟨2370087947270663267750437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3160117263027551023667249 2370087947270663267750437)
                ·
                  refine ⟨444391490113249362703207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370087947270663267750437 444391490113249362703207)
                  ·
                    rfl

theorem cell21_1947261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1947261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947261 prefixEnd_1947261 := by exact prefixLift 1947261
  have htrace : WordTrace (prefixWord ++ tailWord_1947261) baseStart_1947261 baseEnd_1947261 := by
    simpa [prefixWord, tailWord_1947261, baseEnd_1947261] using wordTrace_append hprefix tailTrace_1947261
  have hstable : (prefixWord ++ tailWord_1947261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947261).length < 2 ^ (prefixWord ++ tailWord_1947261).sum := by decide
  have hdescent : baseEnd_1947261 < baseStart_1947261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947292 : List Nat := [2, 2, 3, 2, 3, 2, 2, 5]
def baseStart_1947292 : Nat := 118140960795 + 1947292 * 2 ^ 59
def prefixEnd_1947292 : Nat := 4983230072969 + 3 ^ 40 * 1947292 * 2
def baseEnd_1947292 : Nat := 148132854911866732562159

theorem tailTrace_1947292 : CollatzResearch.WordTrace tailWord_1947292 prefixEnd_1947292 148132854911866732562159 := by
  unfold tailWord_1947292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511787030650564920690065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47349049374200753227586753 35511787030650564920690065)
  ·
    refine ⟨26633840272987923690517549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35511787030650564920690065 26633840272987923690517549)
    ·
      refine ⟨9987690102370471383944081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26633840272987923690517549 9987690102370471383944081)
      ·
        refine ⟨7490767576777853537958061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9987690102370471383944081 7490767576777853537958061)
        ·
          refine ⟨2809037841291695076734273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7490767576777853537958061 2809037841291695076734273)
          ·
            refine ⟨2106778380968771307550705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809037841291695076734273 2106778380968771307550705)
            ·
              refine ⟨1580083785726578480663029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106778380968771307550705 1580083785726578480663029)
              ·
                refine ⟨148132854911866732562159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580083785726578480663029 148132854911866732562159)
                ·
                  rfl

theorem cell21_1947292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_1947292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947292 prefixEnd_1947292 := by exact prefixLift 1947292
  have htrace : WordTrace (prefixWord ++ tailWord_1947292) baseStart_1947292 baseEnd_1947292 := by
    simpa [prefixWord, tailWord_1947292, baseEnd_1947292] using wordTrace_append hprefix tailTrace_1947292
  have hstable : (prefixWord ++ tailWord_1947292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947292).length < 2 ^ (prefixWord ++ tailWord_1947292).sum := by decide
  have hdescent : baseEnd_1947292 < baseStart_1947292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947379 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_1947379 : Nat := 118140960795 + 1947379 * 2 ^ 59
def prefixEnd_1947379 : Nat := 4983230072969 + 3 ^ 40 * 1947379 * 2
def baseEnd_1947379 : Nat := 444418419320907379736299

theorem tailTrace_1947379 : CollatzResearch.WordTrace tailWord_1947379 prefixEnd_1947379 444418419320907379736299 := by
  unfold tailWord_1947379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71026747211985943699797191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47351164807990629133198127 71026747211985943699797191)
  ·
    refine ⟨106540120817978915549695787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71026747211985943699797191 106540120817978915549695787)
    ·
      refine ⟨159810181226968373324543681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106540120817978915549695787 159810181226968373324543681)
      ·
        refine ⟨119857635920226279993407761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159810181226968373324543681 119857635920226279993407761)
        ·
          refine ⟨89893226940169709995055821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119857635920226279993407761 89893226940169709995055821)
          ·
            refine ⟨33709960102563641248145933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89893226940169709995055821 33709960102563641248145933)
            ·
              refine ⟨12641235038461365468054725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33709960102563641248145933 12641235038461365468054725)
              ·
                refine ⟨2370231569711506025260261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12641235038461365468054725 2370231569711506025260261)
                ·
                  refine ⟨444418419320907379736299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370231569711506025260261 444418419320907379736299)
                  ·
                    rfl

theorem cell21_1947379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_1947379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947379 prefixEnd_1947379 := by exact prefixLift 1947379
  have htrace : WordTrace (prefixWord ++ tailWord_1947379) baseStart_1947379 baseEnd_1947379 := by
    simpa [prefixWord, tailWord_1947379, baseEnd_1947379] using wordTrace_append hprefix tailTrace_1947379
  have hstable : (prefixWord ++ tailWord_1947379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947379).length < 2 ^ (prefixWord ++ tailWord_1947379).sum := by decide
  have hdescent : baseEnd_1947379 < baseStart_1947379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947396 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1947396 : Nat := 118140960795 + 1947396 * 2 ^ 59
def prefixEnd_1947396 : Nat := 4983230072969 + 3 ^ 40 * 1947396 * 2
def baseEnd_1947396 : Nat := 444422298952519127952931

theorem tailTrace_1947396 : CollatzResearch.WordTrace tailWord_1947396 prefixEnd_1947396 444422298952519127952931 := by
  unfold tailWord_1947396
  simp only [CollatzResearch.WordTrace]
  refine ⟨35513683626462177801583021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47351578168616237068777361 35513683626462177801583021)
  ·
    refine ⟨13317631359923316675593633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35513683626462177801583021 13317631359923316675593633)
    ·
      refine ⟨9988223519942487506695225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13317631359923316675593633 9988223519942487506695225)
      ·
        refine ⟨7491167639956865630021419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9988223519942487506695225 7491167639956865630021419)
        ·
          refine ⟨11236751459935298445032129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491167639956865630021419 11236751459935298445032129)
          ·
            refine ⟨8427563594951473833774097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236751459935298445032129 8427563594951473833774097)
            ·
              refine ⟨6320672696213605375330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8427563594951473833774097 6320672696213605375330573)
              ·
                refine ⟨2370252261080102015748965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320672696213605375330573 2370252261080102015748965)
                ·
                  refine ⟨444422298952519127952931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370252261080102015748965 444422298952519127952931)
                  ·
                    rfl

theorem cell21_1947396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1947396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947396 prefixEnd_1947396 := by exact prefixLift 1947396
  have htrace : WordTrace (prefixWord ++ tailWord_1947396) baseStart_1947396 baseEnd_1947396 := by
    simpa [prefixWord, tailWord_1947396, baseEnd_1947396] using wordTrace_append hprefix tailTrace_1947396
  have hstable : (prefixWord ++ tailWord_1947396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947396).length < 2 ^ (prefixWord ++ tailWord_1947396).sum := by decide
  have hdescent : baseEnd_1947396 < baseStart_1947396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947424 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_1947424 : Nat := 118140960795 + 1947424 * 2 ^ 59
def prefixEnd_1947424 : Nat := 4983230072969 + 3 ^ 40 * 1947424 * 2
def baseEnd_1947424 : Nat := 444428688933997301486207

theorem tailTrace_1947424 : CollatzResearch.WordTrace tailWord_1947424 prefixEnd_1947424 444428688933997301486207 := by
  unfold tailWord_1947424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35514194248411458192592663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47352258997881944256790217 35514194248411458192592663)
  ·
    refine ⟨53271291372617187288888995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35514194248411458192592663 53271291372617187288888995)
    ·
      refine ⟨79906937058925780933333493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53271291372617187288888995 79906937058925780933333493)
      ·
        refine ⟨7491275349274291962500015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79906937058925780933333493 7491275349274291962500015)
        ·
          refine ⟨11236913023911437943750023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491275349274291962500015 11236913023911437943750023)
          ·
            refine ⟨16855369535867156915625035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236913023911437943750023 16855369535867156915625035)
            ·
              refine ⟨25283054303800735373437553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16855369535867156915625035 25283054303800735373437553)
              ·
                refine ⟨18962290727850551530078165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25283054303800735373437553 18962290727850551530078165)
                ·
                  refine ⟨444428688933997301486207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18962290727850551530078165 444428688933997301486207)
                  ·
                    rfl

theorem cell21_1947424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_1947424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947424 prefixEnd_1947424 := by exact prefixLift 1947424
  have htrace : WordTrace (prefixWord ++ tailWord_1947424) baseStart_1947424 baseEnd_1947424 := by
    simpa [prefixWord, tailWord_1947424, baseEnd_1947424] using wordTrace_append hprefix tailTrace_1947424
  have hstable : (prefixWord ++ tailWord_1947424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947424).length < 2 ^ (prefixWord ++ tailWord_1947424).sum := by decide
  have hdescent : baseEnd_1947424 < baseStart_1947424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947441 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_1947441 : Nat := 118140960795 + 1947441 * 2 ^ 59
def prefixEnd_1947441 : Nat := 4983230072969 + 3 ^ 40 * 1947441 * 2
def baseEnd_1947441 : Nat := 444432568565609049702839

theorem tailTrace_1947441 : CollatzResearch.WordTrace tailWord_1947441 prefixEnd_1947441 444432568565609049702839 := by
  unfold tailWord_1947441
  simp only [CollatzResearch.WordTrace]
  refine ⟨71029008537761328288554177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47352672358507552192369451 71029008537761328288554177)
  ·
    refine ⟨53271756403320996216415633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71029008537761328288554177 53271756403320996216415633)
    ·
      refine ⟨39953817302490747162311725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53271756403320996216415633 39953817302490747162311725)
      ·
        refine ⟨14982681488434030185866897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39953817302490747162311725 14982681488434030185866897)
        ·
          refine ⟨11237011116325522639400173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14982681488434030185866897 11237011116325522639400173)
          ·
            refine ⟨4213879168622070989775065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11237011116325522639400173 4213879168622070989775065)
            ·
              refine ⟨3160409376466553242331299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213879168622070989775065 3160409376466553242331299)
              ·
                refine ⟨4740614064699829863496949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160409376466553242331299 4740614064699829863496949)
                ·
                  refine ⟨444432568565609049702839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740614064699829863496949 444432568565609049702839)
                  ·
                    rfl

theorem cell21_1947441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_1947441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947441 prefixEnd_1947441 := by exact prefixLift 1947441
  have htrace : WordTrace (prefixWord ++ tailWord_1947441) baseStart_1947441 baseEnd_1947441 := by
    simpa [prefixWord, tailWord_1947441, baseEnd_1947441] using wordTrace_append hprefix tailTrace_1947441
  have hstable : (prefixWord ++ tailWord_1947441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947441).length < 2 ^ (prefixWord ++ tailWord_1947441).sum := by decide
  have hdescent : baseEnd_1947441 < baseStart_1947441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947548 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1947548 : Nat := 118140960795 + 1947548 * 2 ^ 59
def prefixEnd_1947548 : Nat := 4983230072969 + 3 ^ 40 * 1947548 * 2
def baseEnd_1947548 : Nat := 444456987423400641419287

theorem tailTrace_1947548 : CollatzResearch.WordTrace tailWord_1947548 prefixEnd_1947548 444456987423400641419287 := by
  unfold tailWord_1947548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516455574186842781349649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47355274098915790375132865 35516455574186842781349649)
  ·
    refine ⟨26637341680640132086012237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35516455574186842781349649 26637341680640132086012237)
    ·
      refine ⟨9989003130240049532254589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26637341680640132086012237 9989003130240049532254589)
      ·
        refine ⟨3745876173840018574595471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9989003130240049532254589 3745876173840018574595471)
        ·
          refine ⟨5618814260760027861893207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745876173840018574595471 5618814260760027861893207)
          ·
            refine ⟨8428221391140041792839811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618814260760027861893207 8428221391140041792839811)
            ·
              refine ⟨12642332086710062689259717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428221391140041792839811 12642332086710062689259717)
              ·
                refine ⟨2370437266258136754236197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12642332086710062689259717 2370437266258136754236197)
                ·
                  refine ⟨444456987423400641419287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370437266258136754236197 444456987423400641419287)
                  ·
                    rfl

theorem cell21_1947548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1947548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947548 prefixEnd_1947548 := by exact prefixLift 1947548
  have htrace : WordTrace (prefixWord ++ tailWord_1947548) baseStart_1947548 baseEnd_1947548 := by
    simpa [prefixWord, tailWord_1947548, baseEnd_1947548] using wordTrace_append hprefix tailTrace_1947548
  have hstable : (prefixWord ++ tailWord_1947548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947548).length < 2 ^ (prefixWord ++ tailWord_1947548).sum := by decide
  have hdescent : baseEnd_1947548 < baseStart_1947548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947576 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1947576 : Nat := 118140960795 + 1947576 * 2 ^ 59
def prefixEnd_1947576 : Nat := 4983230072969 + 3 ^ 40 * 1947576 * 2
def baseEnd_1947576 : Nat := 444463377404878814952563

theorem tailTrace_1947576 : CollatzResearch.WordTrace tailWord_1947576 prefixEnd_1947576 444463377404878814952563 := by
  unfold tailWord_1947576
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516966196136123172359291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47355954928181497563145721 35516966196136123172359291)
  ·
    refine ⟨53275449294204184758538937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35516966196136123172359291 53275449294204184758538937)
    ·
      refine ⟨39956586970653138568904203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53275449294204184758538937 39956586970653138568904203)
      ·
        refine ⟨59934880455979707853356305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39956586970653138568904203 59934880455979707853356305)
        ·
          refine ⟨44951160341984780890017229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59934880455979707853356305 44951160341984780890017229)
          ·
            refine ⟨16856685128244292833756461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44951160341984780890017229 16856685128244292833756461)
            ·
              refine ⟨6321256923091609812658673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16856685128244292833756461 6321256923091609812658673)
              ·
                refine ⟨4740942692318707359494005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6321256923091609812658673 4740942692318707359494005)
                ·
                  refine ⟨444463377404878814952563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740942692318707359494005 444463377404878814952563)
                  ·
                    rfl

theorem cell21_1947576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1947576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947576 prefixEnd_1947576 := by exact prefixLift 1947576
  have htrace : WordTrace (prefixWord ++ tailWord_1947576) baseStart_1947576 baseEnd_1947576 := by
    simpa [prefixWord, tailWord_1947576, baseEnd_1947576] using wordTrace_append hprefix tailTrace_1947576
  have hstable : (prefixWord ++ tailWord_1947576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947576).length < 2 ^ (prefixWord ++ tailWord_1947576).sum := by decide
  have hdescent : baseEnd_1947576 < baseStart_1947576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947661 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1947661 : Nat := 118140960795 + 1947661 * 2 ^ 59
def prefixEnd_1947661 : Nat := 4983230072969 + 3 ^ 40 * 1947661 * 2
def baseEnd_1947661 : Nat := 444482775562937556035723

theorem tailTrace_1947661 : CollatzResearch.WordTrace tailWord_1947661 prefixEnd_1947661 444482775562937556035723 := by
  unfold tailWord_1947661
  simp only [CollatzResearch.WordTrace]
  refine ⟨71037032596964305861562837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358021731309537241041891 71037032596964305861562837)
  ·
    refine ⟨1664930451491350918630379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 71037032596964305861562837 1664930451491350918630379)
    ·
      refine ⟨2497395677237026377945569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664930451491350918630379 2497395677237026377945569)
      ·
        refine ⟨1873046757927769783459177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497395677237026377945569 1873046757927769783459177)
        ·
          refine ⟨1404785068445827337594383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873046757927769783459177 1404785068445827337594383)
          ·
            refine ⟨2107177602668741006391575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404785068445827337594383 2107177602668741006391575)
            ·
              refine ⟨3160766404003111509587363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107177602668741006391575 3160766404003111509587363)
              ·
                refine ⟨4741149606004667264381045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160766404003111509587363 4741149606004667264381045)
                ·
                  refine ⟨444482775562937556035723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741149606004667264381045 444482775562937556035723)
                  ·
                    rfl

theorem cell21_1947661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1947661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947661 prefixEnd_1947661 := by exact prefixLift 1947661
  have htrace : WordTrace (prefixWord ++ tailWord_1947661) baseStart_1947661 baseEnd_1947661 := by
    simpa [prefixWord, tailWord_1947661, baseEnd_1947661] using wordTrace_append hprefix tailTrace_1947661
  have hstable : (prefixWord ++ tailWord_1947661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947661).length < 2 ^ (prefixWord ++ tailWord_1947661).sum := by decide
  have hdescent : baseEnd_1947661 < baseStart_1947661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947683 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_1947683 : Nat := 118140960795 + 1947683 * 2 ^ 59
def prefixEnd_1947683 : Nat := 4983230072969 + 3 ^ 40 * 1947683 * 2
def baseEnd_1947683 : Nat := 444487796262670406669011

theorem tailTrace_1947683 : CollatzResearch.WordTrace tailWord_1947683 prefixEnd_1947683 444487796262670406669011 := by
  unfold tailWord_1947683
  simp only [CollatzResearch.WordTrace]
  refine ⟨71037835002884603618863703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358556668589735745909135 71037835002884603618863703)
  ·
    refine ⟨106556752504326905428295555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71037835002884603618863703 106556752504326905428295555)
    ·
      refine ⟨159835128756490358142443333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106556752504326905428295555 159835128756490358142443333)
      ·
        refine ⟨29969086641841942151708125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159835128756490358142443333 29969086641841942151708125)
        ·
          refine ⟨11238407490690728306890547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29969086641841942151708125 11238407490690728306890547)
          ·
            refine ⟨16857611236036092460335821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11238407490690728306890547 16857611236036092460335821)
            ·
              refine ⟨6321604213513534672625933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16857611236036092460335821 6321604213513534672625933)
              ·
                refine ⟨2370601580067575502234725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6321604213513534672625933 2370601580067575502234725)
                ·
                  refine ⟨444487796262670406669011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370601580067575502234725 444487796262670406669011)
                  ·
                    rfl

theorem cell21_1947683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_1947683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947683 prefixEnd_1947683 := by exact prefixLift 1947683
  have htrace : WordTrace (prefixWord ++ tailWord_1947683) baseStart_1947683 baseEnd_1947683 := by
    simpa [prefixWord, tailWord_1947683, baseEnd_1947683] using wordTrace_append hprefix tailTrace_1947683
  have hstable : (prefixWord ++ tailWord_1947683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947683).length < 2 ^ (prefixWord ++ tailWord_1947683).sum := by decide
  have hdescent : baseEnd_1947683 < baseStart_1947683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947697 : List Nat := [1, 2, 2, 3, 1, 3, 2, 7]
def baseStart_1947697 : Nat := 118140960795 + 1947697 * 2 ^ 59
def prefixEnd_1947697 : Nat := 4983230072969 + 3 ^ 40 * 1947697 * 2
def baseEnd_1947697 : Nat := 148163663751136497811883

theorem tailTrace_1947697 : CollatzResearch.WordTrace tailWord_1947697 prefixEnd_1947697 148163663751136497811883 := by
  unfold tailWord_1947697
  simp only [CollatzResearch.WordTrace]
  refine ⟨71038345624833884009873345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47358897083222589339915563 71038345624833884009873345)
  ·
    refine ⟨53278759218625413007405009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71038345624833884009873345 53278759218625413007405009)
    ·
      refine ⟨39959069413969059755553757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53278759218625413007405009 39959069413969059755553757)
      ·
        refine ⟨14984651030238397408332659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39959069413969059755553757 14984651030238397408332659)
        ·
          refine ⟨22476976545357596112498989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14984651030238397408332659 22476976545357596112498989)
          ·
            refine ⟨8428866204509098542187121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22476976545357596112498989 8428866204509098542187121)
            ·
              refine ⟨6321649653381823906640341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428866204509098542187121 6321649653381823906640341)
              ·
                refine ⟨148163663751136497811883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6321649653381823906640341 148163663751136497811883)
                ·
                  rfl

theorem cell21_1947697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_1947697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947697 prefixEnd_1947697 := by exact prefixLift 1947697
  have htrace : WordTrace (prefixWord ++ tailWord_1947697) baseStart_1947697 baseEnd_1947697 := by
    simpa [prefixWord, tailWord_1947697, baseEnd_1947697] using wordTrace_append hprefix tailTrace_1947697
  have hstable : (prefixWord ++ tailWord_1947697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947697).length < 2 ^ (prefixWord ++ tailWord_1947697).sum := by decide
  have hdescent : baseEnd_1947697 < baseStart_1947697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947762 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1947762 : Nat := 118140960795 + 1947762 * 2 ^ 59
def prefixEnd_1947762 : Nat := 4983230072969 + 3 ^ 40 * 1947762 * 2
def baseEnd_1947762 : Nat := 444505825138983824852183

theorem tailTrace_1947762 : CollatzResearch.WordTrace tailWord_1947762 prefixEnd_1947762 444505825138983824852183 := by
  unfold tailWord_1947762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760179092399600027747385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47360477579732266740659693 17760179092399600027747385)
  ·
    refine ⟨13320134319299700020810539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17760179092399600027747385 13320134319299700020810539)
    ·
      refine ⟨19980201478949550031215809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320134319299700020810539 19980201478949550031215809)
      ·
        refine ⟨14985151109212162523411857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19980201478949550031215809 14985151109212162523411857)
        ·
          refine ⟨11238863331909121892558893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14985151109212162523411857 11238863331909121892558893)
          ·
            refine ⟨4214573749465920709709585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11238863331909121892558893 4214573749465920709709585)
            ·
              refine ⟨3160930312099440532282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214573749465920709709585 3160930312099440532282189)
              ·
                refine ⟨1185348867037290199605821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3160930312099440532282189 1185348867037290199605821)
                ·
                  refine ⟨444505825138983824852183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185348867037290199605821 444505825138983824852183)
                  ·
                    rfl

theorem cell21_1947762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1947762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947762 prefixEnd_1947762 := by exact prefixLift 1947762
  have htrace : WordTrace (prefixWord ++ tailWord_1947762) baseStart_1947762 baseEnd_1947762 := by
    simpa [prefixWord, tailWord_1947762, baseEnd_1947762] using wordTrace_append hprefix tailTrace_1947762
  have hstable : (prefixWord ++ tailWord_1947762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947762).length < 2 ^ (prefixWord ++ tailWord_1947762).sum := by decide
  have hdescent : baseEnd_1947762 < baseStart_1947762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947773 : List Nat := [1, 4, 1, 1, 3, 3, 8]
def baseStart_1947773 : Nat := 118140960795 + 1947773 * 2 ^ 59
def prefixEnd_1947773 : Nat := 4983230072969 + 3 ^ 40 * 1947773 * 2
def baseEnd_1947773 : Nat := 49389815054316694463203

theorem tailTrace_1947773 : CollatzResearch.WordTrace tailWord_1947773 prefixEnd_1947773 49389815054316694463203 := by
  unfold tailWord_1947773
  simp only [CollatzResearch.WordTrace]
  refine ⟨71041117572558548989639973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47360745048372365993093315 71041117572558548989639973)
  ·
    refine ⟨13320209544854727935557495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71041117572558548989639973 13320209544854727935557495)
    ·
      refine ⟨19980314317282091903336243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320209544854727935557495 19980314317282091903336243)
      ·
        refine ⟨29970471475923137855004365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19980314317282091903336243 29970471475923137855004365)
        ·
          refine ⟨11238926803471176695626637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29970471475923137855004365 11238926803471176695626637)
          ·
            refine ⟨4214597551301691260859989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11238926803471176695626637 4214597551301691260859989)
            ·
              refine ⟨49389815054316694463203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4214597551301691260859989 49389815054316694463203)
              ·
                rfl

theorem cell21_1947773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 8].length) (baseStart_1947773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947773 prefixEnd_1947773 := by exact prefixLift 1947773
  have htrace : WordTrace (prefixWord ++ tailWord_1947773) baseStart_1947773 baseEnd_1947773 := by
    simpa [prefixWord, tailWord_1947773, baseEnd_1947773] using wordTrace_append hprefix tailTrace_1947773
  have hstable : (prefixWord ++ tailWord_1947773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947773).length < 2 ^ (prefixWord ++ tailWord_1947773).sum := by decide
  have hdescent : baseEnd_1947773 < baseStart_1947773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947804 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1947804 : Nat := 118140960795 + 1947804 * 2 ^ 59
def prefixEnd_1947804 : Nat := 4983230072969 + 3 ^ 40 * 1947804 * 2
def baseEnd_1947804 : Nat := 444515410111201085152097

theorem tailTrace_1947804 : CollatzResearch.WordTrace tailWord_1947804 prefixEnd_1947804 444515410111201085152097 := by
  unfold tailWord_1947804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35521124117723120642009233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47361498823630827522678977 35521124117723120642009233)
  ·
    refine ⟨26640843088292340481506925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35521124117723120642009233 26640843088292340481506925)
    ·
      refine ⟨9990316158109627680565097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26640843088292340481506925 9990316158109627680565097)
      ·
        refine ⟨7492737118582220760423823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9990316158109627680565097 7492737118582220760423823)
        ·
          refine ⟨11239105677873331140635735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492737118582220760423823 11239105677873331140635735)
          ·
            refine ⟨16858658516809996710953603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239105677873331140635735 16858658516809996710953603)
            ·
              refine ⟨25287987775214995066430405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16858658516809996710953603 25287987775214995066430405)
              ·
                refine ⟨4741497707852811574955701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25287987775214995066430405 4741497707852811574955701)
                ·
                  refine ⟨444515410111201085152097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741497707852811574955701 444515410111201085152097)
                  ·
                    rfl

theorem cell21_1947804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1947804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947804 prefixEnd_1947804 := by exact prefixLift 1947804
  have htrace : WordTrace (prefixWord ++ tailWord_1947804) baseStart_1947804 baseEnd_1947804 := by
    simpa [prefixWord, tailWord_1947804, baseEnd_1947804] using wordTrace_append hprefix tailTrace_1947804
  have hstable : (prefixWord ++ tailWord_1947804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947804).length < 2 ^ (prefixWord ++ tailWord_1947804).sum := by decide
  have hdescent : baseEnd_1947804 < baseStart_1947804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947807 : List Nat := [1, 1, 2, 6, 1, 3, 2, 5]
def baseStart_1947807 : Nat := 118140960795 + 1947807 * 2 ^ 59
def prefixEnd_1947807 : Nat := 4983230072969 + 3 ^ 40 * 1947807 * 2
def baseEnd_1947807 : Nat := 148172031584024582200697

theorem tailTrace_1947807 : CollatzResearch.WordTrace tailWord_1947807 prefixEnd_1947807 148172031584024582200697 := by
  unfold tailWord_1947807
  simp only [CollatzResearch.WordTrace]
  refine ⟨71042357654435372796377675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47361571769623581864251783 71042357654435372796377675)
  ·
    refine ⟨106563536481653059194566513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71042357654435372796377675 106563536481653059194566513)
    ·
      refine ⟨79922652361239794395924885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106563536481653059194566513 79922652361239794395924885)
      ·
        refine ⟨3746374329433115362308979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79922652361239794395924885 3746374329433115362308979)
        ·
          refine ⟨5619561494149673043463469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746374329433115362308979 5619561494149673043463469)
          ·
            refine ⟨2107335560306127391298801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5619561494149673043463469 2107335560306127391298801)
            ·
              refine ⟨1580501670229595543474101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107335560306127391298801 1580501670229595543474101)
              ·
                refine ⟨148172031584024582200697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580501670229595543474101 148172031584024582200697)
                ·
                  rfl

theorem cell21_1947807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].length) (baseStart_1947807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947807 prefixEnd_1947807 := by exact prefixLift 1947807
  have htrace : WordTrace (prefixWord ++ tailWord_1947807) baseStart_1947807 baseEnd_1947807 := by
    simpa [prefixWord, tailWord_1947807, baseEnd_1947807] using wordTrace_append hprefix tailTrace_1947807
  have hstable : (prefixWord ++ tailWord_1947807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947807).length < 2 ^ (prefixWord ++ tailWord_1947807).sum := by decide
  have hdescent : baseEnd_1947807 < baseStart_1947807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947838 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1947838 : Nat := 118140960795 + 1947838 * 2 ^ 59
def prefixEnd_1947838 : Nat := 4983230072969 + 3 ^ 40 * 1947838 * 2
def baseEnd_1947838 : Nat := 444523169374424581585361

theorem tailTrace_1947838 : CollatzResearch.WordTrace tailWord_1947838 prefixEnd_1947838 444523169374424581585361 := by
  unfold tailWord_1947838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880436039665383136344521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47362325544882043393837445 8880436039665383136344521)
  ·
    refine ⟨6660327029749037352258391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880436039665383136344521 6660327029749037352258391)
    ·
      refine ⟨9990490544623556028387587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660327029749037352258391 9990490544623556028387587)
      ·
        refine ⟨14985735816935334042581381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990490544623556028387587 14985735816935334042581381)
        ·
          refine ⟨2809825465675375132984009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14985735816935334042581381 2809825465675375132984009)
          ·
            refine ⟨2107369099256531349738007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809825465675375132984009 2107369099256531349738007)
            ·
              refine ⟨3161053648884797024607011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107369099256531349738007 3161053648884797024607011)
              ·
                refine ⟨4741580473327195536910517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161053648884797024607011 4741580473327195536910517)
                ·
                  refine ⟨444523169374424581585361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741580473327195536910517 444523169374424581585361)
                  ·
                    rfl

theorem cell21_1947838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1947838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947838 prefixEnd_1947838 := by exact prefixLift 1947838
  have htrace : WordTrace (prefixWord ++ tailWord_1947838) baseStart_1947838 baseEnd_1947838 := by
    simpa [prefixWord, tailWord_1947838, baseEnd_1947838] using wordTrace_append hprefix tailTrace_1947838
  have hstable : (prefixWord ++ tailWord_1947838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947838).length < 2 ^ (prefixWord ++ tailWord_1947838).sum := by decide
  have hdescent : baseEnd_1947838 < baseStart_1947838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947863 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_1947863 : Nat := 118140960795 + 1947863 * 2 ^ 59
def prefixEnd_1947863 : Nat := 4983230072969 + 3 ^ 40 * 1947863 * 2
def baseEnd_1947863 : Nat := 444528874715030093668643

theorem tailTrace_1947863 : CollatzResearch.WordTrace tailWord_1947863 prefixEnd_1947863 444528874715030093668643 := by
  unfold tailWord_1947863
  simp only [CollatzResearch.WordTrace]
  refine ⟨71044400142232494360416243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47362933428154996240277495 71044400142232494360416243)
  ·
    refine ⟨106566600213348741540624365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71044400142232494360416243 106566600213348741540624365)
    ·
      refine ⟨39962475080005778077734137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106566600213348741540624365 39962475080005778077734137)
      ·
        refine ⟨29971856310004333558300603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39962475080005778077734137 29971856310004333558300603)
        ·
          refine ⟨44957784465006500337450905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29971856310004333558300603 44957784465006500337450905)
          ·
            refine ⟨33718338348754875253088179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44957784465006500337450905 33718338348754875253088179)
            ·
              refine ⟨50577507523132312879632269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33718338348754875253088179 50577507523132312879632269)
              ·
                refine ⟨18966565321174617329862101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50577507523132312879632269 18966565321174617329862101)
                ·
                  refine ⟨444528874715030093668643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18966565321174617329862101 444528874715030093668643)
                  ·
                    rfl

theorem cell21_1947863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_1947863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947863 prefixEnd_1947863 := by exact prefixLift 1947863
  have htrace : WordTrace (prefixWord ++ tailWord_1947863) baseStart_1947863 baseEnd_1947863 := by
    simpa [prefixWord, tailWord_1947863, baseEnd_1947863] using wordTrace_append hprefix tailTrace_1947863
  have hstable : (prefixWord ++ tailWord_1947863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947863).length < 2 ^ (prefixWord ++ tailWord_1947863).sum := by decide
  have hdescent : baseEnd_1947863 < baseStart_1947863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1947939 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_1947939 : Nat := 118140960795 + 1947939 * 2 ^ 59
def prefixEnd_1947939 : Nat := 4983230072969 + 3 ^ 40 * 1947939 * 2
def baseEnd_1947939 : Nat := 444546218950470850401821

theorem tailTrace_1947939 : CollatzResearch.WordTrace tailWord_1947939 prefixEnd_1947939 444546218950470850401821 := by
  unfold tailWord_1947939
  simp only [CollatzResearch.WordTrace]
  refine ⟨71047172089957159340182871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47364781393304772893455247 71047172089957159340182871)
  ·
    refine ⟨106570758134935739010274307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71047172089957159340182871 106570758134935739010274307)
    ·
      refine ⟨159856137202403608515411461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106570758134935739010274307 159856137202403608515411461)
      ·
        refine ⟨29973025725450676596639649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159856137202403608515411461 29973025725450676596639649)
        ·
          refine ⟨22479769294088007447479737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29973025725450676596639649 22479769294088007447479737)
          ·
            refine ⟨16859826970566005585609803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22479769294088007447479737 16859826970566005585609803)
            ·
              refine ⟨25289740455849008378414705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859826970566005585609803 25289740455849008378414705)
              ·
                refine ⟨18967305341886756283811029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25289740455849008378414705 18967305341886756283811029)
                ·
                  refine ⟨444546218950470850401821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18967305341886756283811029 444546218950470850401821)
                  ·
                    rfl

theorem cell21_1947939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_1947939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1947939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1947939 prefixEnd_1947939 := by exact prefixLift 1947939
  have htrace : WordTrace (prefixWord ++ tailWord_1947939) baseStart_1947939 baseEnd_1947939 := by
    simpa [prefixWord, tailWord_1947939, baseEnd_1947939] using wordTrace_append hprefix tailTrace_1947939
  have hstable : (prefixWord ++ tailWord_1947939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1947939).length < 2 ^ (prefixWord ++ tailWord_1947939).sum := by decide
  have hdescent : baseEnd_1947939 < baseStart_1947939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1947939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948015 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_1948015 : Nat := 118140960795 + 1948015 * 2 ^ 59
def prefixEnd_1948015 : Nat := 4983230072969 + 3 ^ 40 * 1948015 * 2
def baseEnd_1948015 : Nat := 444563563185911607134999

theorem tailTrace_1948015 : CollatzResearch.WordTrace tailWord_1948015 prefixEnd_1948015 444563563185911607134999 := by
  unfold tailWord_1948015
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049944037681824319949499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47366629358454549546632999 71049944037681824319949499)
  ·
    refine ⟨106574916056522736479924249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71049944037681824319949499 106574916056522736479924249)
    ·
      refine ⟨79931187042392052359943187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106574916056522736479924249 79931187042392052359943187)
      ·
        refine ⟨119896780563588078539914781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79931187042392052359943187 119896780563588078539914781)
        ·
          refine ⟨44961292711345529452468043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119896780563588078539914781 44961292711345529452468043)
          ·
            refine ⟨67441939067018294178702065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44961292711345529452468043 67441939067018294178702065)
            ·
              refine ⟨50581454300263720634026549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67441939067018294178702065 50581454300263720634026549)
              ·
                refine ⟨4742011340649723809439989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50581454300263720634026549 4742011340649723809439989)
                ·
                  refine ⟨444563563185911607134999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742011340649723809439989 444563563185911607134999)
                  ·
                    rfl

theorem cell21_1948015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_1948015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948015 prefixEnd_1948015 := by exact prefixLift 1948015
  have htrace : WordTrace (prefixWord ++ tailWord_1948015) baseStart_1948015 baseEnd_1948015 := by
    simpa [prefixWord, tailWord_1948015, baseEnd_1948015] using wordTrace_append hprefix tailTrace_1948015
  have hstable : (prefixWord ++ tailWord_1948015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948015).length < 2 ^ (prefixWord ++ tailWord_1948015).sum := by decide
  have hdescent : baseEnd_1948015 < baseStart_1948015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948021 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 4]
def baseStart_1948021 : Nat := 118140960795 + 1948021 * 2 ^ 59
def prefixEnd_1948021 : Nat := 4983230072969 + 3 ^ 40 * 1948021 * 2
def baseEnd_1948021 : Nat := 444564932467656930034987

theorem tailTrace_1948021 : CollatzResearch.WordTrace tailWord_1948021 prefixEnd_1948021 444564932467656930034987 := by
  unfold tailWord_1948021
  simp only [CollatzResearch.WordTrace]
  refine ⟨71050162875660087344667917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47366775250440058229778611 71050162875660087344667917)
  ·
    refine ⟨26643811078372532754250469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71050162875660087344667917 26643811078372532754250469)
    ·
      refine ⟨4995714577194849891421963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26643811078372532754250469 4995714577194849891421963)
      ·
        refine ⟨7493571865792274837132945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995714577194849891421963 7493571865792274837132945)
        ·
          refine ⟨5620178899344206127849709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7493571865792274837132945 5620178899344206127849709)
          ·
            refine ⟨2107567087254077297943641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5620178899344206127849709 2107567087254077297943641)
            ·
              refine ⟨1580675315440557973457731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107567087254077297943641 1580675315440557973457731)
              ·
                refine ⟨2371012973160836960186597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580675315440557973457731 2371012973160836960186597)
                ·
                  refine ⟨444564932467656930034987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371012973160836960186597 444564932467656930034987)
                  ·
                    rfl

theorem cell21_1948021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_1948021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948021 prefixEnd_1948021 := by exact prefixLift 1948021
  have htrace : WordTrace (prefixWord ++ tailWord_1948021) baseStart_1948021 baseEnd_1948021 := by
    simpa [prefixWord, tailWord_1948021, baseEnd_1948021] using wordTrace_append hprefix tailTrace_1948021
  have hstable : (prefixWord ++ tailWord_1948021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948021).length < 2 ^ (prefixWord ++ tailWord_1948021).sum := by decide
  have hdescent : baseEnd_1948021 < baseStart_1948021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948060 : List Nat := [2, 2, 3, 14]
def baseStart_1948060 : Nat := 118140960795 + 1948060 * 2 ^ 59
def prefixEnd_1948060 : Nat := 4983230072969 + 3 ^ 40 * 1948060 * 2
def baseEnd_1948060 : Nat := 1829521945674903411049

theorem tailTrace_1948060 : CollatzResearch.WordTrace tailWord_1948060 prefixEnd_1948060 1829521945674903411049 := by
  unfold tailWord_1948060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35525792661259398502668817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47367723548345864670225089 35525792661259398502668817)
  ·
    refine ⟨26644344495944548877001613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35525792661259398502668817 26644344495944548877001613)
    ·
      refine ⟨9991629185979205828875605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26644344495944548877001613 9991629185979205828875605)
      ·
        refine ⟨1829521945674903411049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9991629185979205828875605 1829521945674903411049)
        ·
          rfl

theorem cell21_1948060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 14].length) (baseStart_1948060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948060 prefixEnd_1948060 := by exact prefixLift 1948060
  have htrace : WordTrace (prefixWord ++ tailWord_1948060) baseStart_1948060 baseEnd_1948060 := by
    simpa [prefixWord, tailWord_1948060, baseEnd_1948060] using wordTrace_append hprefix tailTrace_1948060
  have hstable : (prefixWord ++ tailWord_1948060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948060).length < 2 ^ (prefixWord ++ tailWord_1948060).sum := by decide
  have hdescent : baseEnd_1948060 < baseStart_1948060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948063 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_1948063 : Nat := 118140960795 + 1948063 * 2 ^ 59
def prefixEnd_1948063 : Nat := 4983230072969 + 3 ^ 40 * 1948063 * 2
def baseEnd_1948063 : Nat := 444574517439874190334901

theorem tailTrace_1948063 : CollatzResearch.WordTrace tailWord_1948063 prefixEnd_1948063 444574517439874190334901 := by
  unfold tailWord_1948063
  simp only [CollatzResearch.WordTrace]
  refine ⟨71051694741507928517696843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47367796494338619011797895 71051694741507928517696843)
  ·
    refine ⟨106577542112261892776545265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71051694741507928517696843 106577542112261892776545265)
    ·
      refine ⟨79933156584196419582408949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106577542112261892776545265 79933156584196419582408949)
      ·
        refine ⟨7493733429768414335850839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79933156584196419582408949 7493733429768414335850839)
        ·
          refine ⟨11240600144652621503776259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493733429768414335850839 11240600144652621503776259)
          ·
            refine ⟨16860900216978932255664389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240600144652621503776259 16860900216978932255664389)
            ·
              refine ⟨3161418790683549797937073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16860900216978932255664389 3161418790683549797937073)
              ·
                refine ⟨2371064093012662348452805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161418790683549797937073 2371064093012662348452805)
                ·
                  refine ⟨444574517439874190334901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371064093012662348452805 444574517439874190334901)
                  ·
                    rfl

theorem cell21_1948063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_1948063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948063 prefixEnd_1948063 := by exact prefixLift 1948063
  have htrace : WordTrace (prefixWord ++ tailWord_1948063) baseStart_1948063 baseEnd_1948063 := by
    simpa [prefixWord, tailWord_1948063, baseEnd_1948063] using wordTrace_append hprefix tailTrace_1948063
  have hstable : (prefixWord ++ tailWord_1948063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948063).length < 2 ^ (prefixWord ++ tailWord_1948063).sum := by decide
  have hdescent : baseEnd_1948063 < baseStart_1948063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948114 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1948114 : Nat := 118140960795 + 1948114 * 2 ^ 59
def prefixEnd_1948114 : Nat := 4983230072969 + 3 ^ 40 * 1948114 * 2
def baseEnd_1948114 : Nat := 444586156334709434984797

theorem tailTrace_1948114 : CollatzResearch.WordTrace tailWord_1948114 prefixEnd_1948114 444586156334709434984797 := by
  unfold tailWord_1948114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17763388716080791056950849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47369036576215442818535597 17763388716080791056950849)
  ·
    refine ⟨13322541537060593292713137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17763388716080791056950849 13322541537060593292713137)
    ·
      refine ⟨9991906152795444969534853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13322541537060593292713137 9991906152795444969534853)
      ·
        refine ⟨1873482403649145931787785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9991906152795444969534853 1873482403649145931787785)
        ·
          refine ⟨1405111802736859448840839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873482403649145931787785 1405111802736859448840839)
          ·
            refine ⟨2107667704105289173261259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405111802736859448840839 2107667704105289173261259)
            ·
              refine ⟨3161501556157933759891889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107667704105289173261259 3161501556157933759891889)
              ·
                refine ⟨2371126167118450319918917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161501556157933759891889 2371126167118450319918917)
                ·
                  refine ⟨444586156334709434984797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371126167118450319918917 444586156334709434984797)
                  ·
                    rfl

theorem cell21_1948114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1948114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948114 prefixEnd_1948114 := by exact prefixLift 1948114
  have htrace : WordTrace (prefixWord ++ tailWord_1948114) baseStart_1948114 baseEnd_1948114 := by
    simpa [prefixWord, tailWord_1948114, baseEnd_1948114] using wordTrace_append hprefix tailTrace_1948114
  have hstable : (prefixWord ++ tailWord_1948114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948114).length < 2 ^ (prefixWord ++ tailWord_1948114).sum := by decide
  have hdescent : baseEnd_1948114 < baseStart_1948114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948122 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1948122 : Nat := 118140960795 + 1948122 * 2 ^ 59
def prefixEnd_1948122 : Nat := 4983230072969 + 3 ^ 40 * 1948122 * 2
def baseEnd_1948122 : Nat := 444587982043703198851447

theorem tailTrace_1948122 : CollatzResearch.WordTrace tailWord_1948122 prefixEnd_1948122 444587982043703198851447 := by
  unfold tailWord_1948122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17763461662073545398523655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47369231098862787729396413 17763461662073545398523655)
  ·
    refine ⟨26645192493110318097785483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17763461662073545398523655 26645192493110318097785483)
    ·
      refine ⟨39967788739665477146678225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26645192493110318097785483 39967788739665477146678225)
      ·
        refine ⟨29975841554749107860008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39967788739665477146678225 29975841554749107860008669)
        ·
          refine ⟨11240940583030915447503251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29975841554749107860008669 11240940583030915447503251)
          ·
            refine ⟨16861410874546373171254877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240940583030915447503251 16861410874546373171254877)
            ·
              refine ⟨6323029077954889939220579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16861410874546373171254877 6323029077954889939220579)
              ·
                refine ⟨9484543616932334908830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323029077954889939220579 9484543616932334908830869)
                ·
                  refine ⟨444587982043703198851447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9484543616932334908830869 444587982043703198851447)
                  ·
                    rfl

theorem cell21_1948122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1948122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948122 prefixEnd_1948122 := by exact prefixLift 1948122
  have htrace : WordTrace (prefixWord ++ tailWord_1948122) baseStart_1948122 baseEnd_1948122 := by
    simpa [prefixWord, tailWord_1948122, baseEnd_1948122] using wordTrace_append hprefix tailTrace_1948122
  have hstable : (prefixWord ++ tailWord_1948122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948122).length < 2 ^ (prefixWord ++ tailWord_1948122).sum := by decide
  have hdescent : baseEnd_1948122 < baseStart_1948122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948125 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1948125 : Nat := 118140960795 + 1948125 * 2 ^ 59
def prefixEnd_1948125 : Nat := 4983230072969 + 3 ^ 40 * 1948125 * 2
def baseEnd_1948125 : Nat := 444588666684575860301441

theorem tailTrace_1948125 : CollatzResearch.WordTrace tailWord_1948125 prefixEnd_1948125 444588666684575860301441 := by
  unfold tailWord_1948125
  simp only [CollatzResearch.WordTrace]
  refine ⟨71053956067283313106453829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47369304044855542070969219 71053956067283313106453829)
  ·
    refine ⟨13322616762615621207460093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71053956067283313106453829 13322616762615621207460093)
    ·
      refine ⟨4995981285980857952797535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13322616762615621207460093 4995981285980857952797535)
      ·
        refine ⟨7493971928971286929196303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995981285980857952797535 7493971928971286929196303)
        ·
          refine ⟨11240957893456930393794455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493971928971286929196303 11240957893456930393794455)
          ·
            refine ⟨16861436840185395590691683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240957893456930393794455 16861436840185395590691683)
            ·
              refine ⟨25292155260278093386037525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16861436840185395590691683 25292155260278093386037525)
              ·
                refine ⟨1185569777825535627470509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25292155260278093386037525 1185569777825535627470509)
                ·
                  refine ⟨444588666684575860301441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185569777825535627470509 444588666684575860301441)
                  ·
                    rfl

theorem cell21_1948125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1948125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948125 prefixEnd_1948125 := by exact prefixLift 1948125
  have htrace : WordTrace (prefixWord ++ tailWord_1948125) baseStart_1948125 baseEnd_1948125 := by
    simpa [prefixWord, tailWord_1948125, baseEnd_1948125] using wordTrace_append hprefix tailTrace_1948125
  have hstable : (prefixWord ++ tailWord_1948125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948125).length < 2 ^ (prefixWord ++ tailWord_1948125).sum := by decide
  have hdescent : baseEnd_1948125 < baseStart_1948125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948139 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 4]
def baseStart_1948139 : Nat := 118140960795 + 1948139 * 2 ^ 59
def prefixEnd_1948139 : Nat := 4983230072969 + 3 ^ 40 * 1948139 * 2
def baseEnd_1948139 : Nat := 444591861675314947068079

theorem tailTrace_1948139 : CollatzResearch.WordTrace tailWord_1948139 prefixEnd_1948139 444591861675314947068079 := by
  unfold tailWord_1948139
  simp only [CollatzResearch.WordTrace]
  refine ⟨71054466689232593497463471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47369644459488395664975647 71054466689232593497463471)
  ·
    refine ⟨106581700033848890246195207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71054466689232593497463471 106581700033848890246195207)
    ·
      refine ⟨159872550050773335369292811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106581700033848890246195207 159872550050773335369292811)
      ·
        refine ⟨239808825076160003053939217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159872550050773335369292811 239808825076160003053939217)
        ·
          refine ⟨179856618807120002290454413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239808825076160003053939217 179856618807120002290454413)
          ·
            refine ⟨67446232052670000858920405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179856618807120002290454413 67446232052670000858920405)
            ·
              refine ⟨1580771063734453145130947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67446232052670000858920405 1580771063734453145130947)
              ·
                refine ⟨2371156595601679717696421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580771063734453145130947 2371156595601679717696421)
                ·
                  refine ⟨444591861675314947068079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371156595601679717696421 444591861675314947068079)
                  ·
                    rfl

theorem cell21_1948139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_1948139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948139 prefixEnd_1948139 := by exact prefixLift 1948139
  have htrace : WordTrace (prefixWord ++ tailWord_1948139) baseStart_1948139 baseEnd_1948139 := by
    simpa [prefixWord, tailWord_1948139, baseEnd_1948139] using wordTrace_append hprefix tailTrace_1948139
  have hstable : (prefixWord ++ tailWord_1948139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948139).length < 2 ^ (prefixWord ++ tailWord_1948139).sum := by decide
  have hdescent : baseEnd_1948139 < baseStart_1948139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948153 : List Nat := [1, 2, 1, 3, 1, 2, 6, 5]
def baseStart_1948153 : Nat := 118140960795 + 1948153 * 2 ^ 59
def prefixEnd_1948153 : Nat := 4983230072969 + 3 ^ 40 * 1948153 * 2
def baseEnd_1948153 : Nat := 148198352222018011278239

theorem tailTrace_1948153 : CollatzResearch.WordTrace tailWord_1948153 prefixEnd_1948153 148198352222018011278239 := by
  unfold tailWord_1948153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71054977311181873888473113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47369984874121249258982075 71054977311181873888473113)
  ·
    refine ⟨53291232983386405416354835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71054977311181873888473113 53291232983386405416354835)
    ·
      refine ⟨79936849475079608124532253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53291232983386405416354835 79936849475079608124532253)
      ·
        refine ⟨29976318553154853046699595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79936849475079608124532253 29976318553154853046699595)
        ·
          refine ⟨44964477829732279570049393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29976318553154853046699595 44964477829732279570049393)
          ·
            refine ⟨33723358372299209677537045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44964477829732279570049393 33723358372299209677537045)
            ·
              refine ⟨1580782423701525453634549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33723358372299209677537045 1580782423701525453634549)
              ·
                refine ⟨148198352222018011278239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580782423701525453634549 148198352222018011278239)
                ·
                  rfl

theorem cell21_1948153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].length) (baseStart_1948153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948153 prefixEnd_1948153 := by exact prefixLift 1948153
  have htrace : WordTrace (prefixWord ++ tailWord_1948153) baseStart_1948153 baseEnd_1948153 := by
    simpa [prefixWord, tailWord_1948153, baseEnd_1948153] using wordTrace_append hprefix tailTrace_1948153
  have hstable : (prefixWord ++ tailWord_1948153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948153).length < 2 ^ (prefixWord ++ tailWord_1948153).sum := by decide
  have hdescent : baseEnd_1948153 < baseStart_1948153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948184 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_1948184 : Nat := 118140960795 + 1948184 * 2 ^ 59
def prefixEnd_1948184 : Nat := 4983230072969 + 3 ^ 40 * 1948184 * 2
def baseEnd_1948184 : Nat := 444602131288404868817987

theorem tailTrace_1948184 : CollatzResearch.WordTrace tailWord_1948184 prefixEnd_1948184 444602131288404868817987 := by
  unfold tailWord_1948184
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528053987034783091425803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47370738649379710788567737 35528053987034783091425803)
  ·
    refine ⟨53292080980552174637138705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35528053987034783091425803 53292080980552174637138705)
    ·
      refine ⟨39969060735414130977854029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53292080980552174637138705 39969060735414130977854029)
      ·
        refine ⟨14988397775780299116695261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39969060735414130977854029 14988397775780299116695261)
        ·
          refine ⟨5620649165917612168760723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14988397775780299116695261 5620649165917612168760723)
          ·
            refine ⟨8430973748876418253141085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620649165917612168760723 8430973748876418253141085)
            ·
              refine ⟨3161615155828656844927907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8430973748876418253141085 3161615155828656844927907)
              ·
                refine ⟨4742422733742985267391861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161615155828656844927907 4742422733742985267391861)
                ·
                  refine ⟨444602131288404868817987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4742422733742985267391861 444602131288404868817987)
                  ·
                    rfl

theorem cell21_1948184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_1948184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948184 prefixEnd_1948184 := by exact prefixLift 1948184
  have htrace : WordTrace (prefixWord ++ tailWord_1948184) baseStart_1948184 baseEnd_1948184 := by
    simpa [prefixWord, tailWord_1948184, baseEnd_1948184] using wordTrace_append hprefix tailTrace_1948184
  have hstable : (prefixWord ++ tailWord_1948184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948184).length < 2 ^ (prefixWord ++ tailWord_1948184).sum := by decide
  have hdescent : baseEnd_1948184 < baseStart_1948184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948288 : List Nat := [2, 1, 1, 2, 1, 6, 8]
def baseStart_1948288 : Nat := 118140960795 + 1948288 * 2 ^ 59
def prefixEnd_1948288 : Nat := 4983230072969 + 3 ^ 40 * 1948288 * 2
def baseEnd_1948288 : Nat := 49402873945035977676049

theorem tailTrace_1948288 : CollatzResearch.WordTrace tailWord_1948288 prefixEnd_1948288 49402873945035977676049 := by
  unfold tailWord_1948288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35529950582846395972318759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47373267443795194629758345 35529950582846395972318759)
  ·
    refine ⟨53294925874269593958478139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35529950582846395972318759 53294925874269593958478139)
    ·
      refine ⟨79942388811404390937717209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53294925874269593958478139 79942388811404390937717209)
      ·
        refine ⟨59956791608553293203287907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79942388811404390937717209 59956791608553293203287907)
        ·
          refine ⟨89935187412829939804931861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59956791608553293203287907 89935187412829939804931861)
          ·
            refine ⟨4215711909976403428356181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89935187412829939804931861 4215711909976403428356181)
            ·
              refine ⟨49402873945035977676049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4215711909976403428356181 49402873945035977676049)
              ·
                rfl

theorem cell21_1948288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 8].length) (baseStart_1948288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948288 prefixEnd_1948288 := by exact prefixLift 1948288
  have htrace : WordTrace (prefixWord ++ tailWord_1948288) baseStart_1948288 baseEnd_1948288 := by
    simpa [prefixWord, tailWord_1948288, baseEnd_1948288] using wordTrace_append hprefix tailTrace_1948288
  have hstable : (prefixWord ++ tailWord_1948288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948288).length < 2 ^ (prefixWord ++ tailWord_1948288).sum := by decide
  have hdescent : baseEnd_1948288 < baseStart_1948288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948350 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1948350 : Nat := 118140960795 + 1948350 * 2 ^ 59
def prefixEnd_1948350 : Nat := 4983230072969 + 3 ^ 40 * 1948350 * 2
def baseEnd_1948350 : Nat := 444640014750025469050981

theorem tailTrace_1948350 : CollatzResearch.WordTrace tailWord_1948350 prefixEnd_1948350 444640014750025469050981 := by
  unfold tailWord_1948350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882770311433522066674313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47374774994312117688929669 8882770311433522066674313)
  ·
    refine ⟨6662077733575141550005735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8882770311433522066674313 6662077733575141550005735)
    ·
      refine ⟨9993116600362712325008603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662077733575141550005735 9993116600362712325008603)
      ·
        refine ⟨14989674900544068487512905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9993116600362712325008603 14989674900544068487512905)
        ·
          refine ⟨11242256175408051365634679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14989674900544068487512905 11242256175408051365634679)
          ·
            refine ⟨16863384263112077048452019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11242256175408051365634679 16863384263112077048452019)
            ·
              refine ⟨25295076394668115572678029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863384263112077048452019 25295076394668115572678029)
              ·
                refine ⟨9485653648000543339754261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25295076394668115572678029 9485653648000543339754261)
                ·
                  refine ⟨444640014750025469050981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9485653648000543339754261 444640014750025469050981)
                  ·
                    rfl

theorem cell21_1948350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1948350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948350 prefixEnd_1948350 := by exact prefixLift 1948350
  have htrace : WordTrace (prefixWord ++ tailWord_1948350) baseStart_1948350 baseEnd_1948350 := by
    simpa [prefixWord, tailWord_1948350, baseEnd_1948350] using wordTrace_append hprefix tailTrace_1948350
  have hstable : (prefixWord ++ tailWord_1948350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948350).length < 2 ^ (prefixWord ++ tailWord_1948350).sum := by decide
  have hdescent : baseEnd_1948350 < baseStart_1948350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948409 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_1948409 : Nat := 118140960795 + 1948409 * 2 ^ 59
def prefixEnd_1948409 : Nat := 4983230072969 + 3 ^ 40 * 1948409 * 2
def baseEnd_1948409 : Nat := 444653479353854477567527

theorem tailTrace_1948409 : CollatzResearch.WordTrace tailWord_1948409 prefixEnd_1948409 444653479353854477567527 := by
  unfold tailWord_1948409
  simp only [CollatzResearch.WordTrace]
  refine ⟨71064314398254429609792281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47376209598836286406528187 71064314398254429609792281)
  ·
    refine ⟨53298235798690822207344211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71064314398254429609792281 53298235798690822207344211)
    ·
      refine ⟨79947353698036233311016317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53298235798690822207344211 79947353698036233311016317)
      ·
        refine ⟨29980257636763587491631119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79947353698036233311016317 29980257636763587491631119)
        ·
          refine ⟨44970386455145381237446679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29980257636763587491631119 44970386455145381237446679)
          ·
            refine ⟨67455579682718071856170019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44970386455145381237446679 67455579682718071856170019)
            ·
              refine ⟨101183369524077107784255029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67455579682718071856170019 101183369524077107784255029)
              ·
                refine ⟨9485940892882228854773909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101183369524077107784255029 9485940892882228854773909)
                ·
                  refine ⟨444653479353854477567527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9485940892882228854773909 444653479353854477567527)
                  ·
                    rfl

theorem cell21_1948409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_1948409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948409 prefixEnd_1948409 := by exact prefixLift 1948409
  have htrace : WordTrace (prefixWord ++ tailWord_1948409) baseStart_1948409 baseEnd_1948409 := by
    simpa [prefixWord, tailWord_1948409, baseEnd_1948409] using wordTrace_append hprefix tailTrace_1948409
  have hstable : (prefixWord ++ tailWord_1948409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948409).length < 2 ^ (prefixWord ++ tailWord_1948409).sum := by decide
  have hdescent : baseEnd_1948409 < baseStart_1948409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948426 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_1948426 : Nat := 118140960795 + 1948426 * 2 ^ 59
def prefixEnd_1948426 : Nat := 4983230072969 + 3 ^ 40 * 1948426 * 2
def baseEnd_1948426 : Nat := 444657358985466225784159

theorem tailTrace_1948426 : CollatzResearch.WordTrace tailWord_1948426 prefixEnd_1948426 444657358985466225784159 := by
  unfold tailWord_1948426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17766233609798210378290283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47376622959461894342107421 17766233609798210378290283)
  ·
    refine ⟨26649350414697315567435425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17766233609798210378290283 26649350414697315567435425)
    ·
      refine ⟨19987012811022986675576569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26649350414697315567435425 19987012811022986675576569)
      ·
        refine ⟨14990259608267240006682427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19987012811022986675576569 14990259608267240006682427)
        ·
          refine ⟨22485389412400860010023641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14990259608267240006682427 22485389412400860010023641)
          ·
            refine ⟨16864042059300645007517731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22485389412400860010023641 16864042059300645007517731)
            ·
              refine ⟨25296063088950967511276597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16864042059300645007517731 25296063088950967511276597)
              ·
                refine ⟨2371505914589153204182181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25296063088950967511276597 2371505914589153204182181)
                ·
                  refine ⟨444657358985466225784159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371505914589153204182181 444657358985466225784159)
                  ·
                    rfl

theorem cell21_1948426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_1948426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948426 prefixEnd_1948426 := by exact prefixLift 1948426
  have htrace : WordTrace (prefixWord ++ tailWord_1948426) baseStart_1948426 baseEnd_1948426 := by
    simpa [prefixWord, tailWord_1948426, baseEnd_1948426] using wordTrace_append hprefix tailTrace_1948426
  have hstable : (prefixWord ++ tailWord_1948426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948426).length < 2 ^ (prefixWord ++ tailWord_1948426).sum := by decide
  have hdescent : baseEnd_1948426 < baseStart_1948426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948471 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_1948471 : Nat := 118140960795 + 1948471 * 2 ^ 59
def prefixEnd_1948471 : Nat := 4983230072969 + 3 ^ 40 * 1948471 * 2
def baseEnd_1948471 : Nat := 444667628598556147534067

theorem tailTrace_1948471 : CollatzResearch.WordTrace tailWord_1948471 prefixEnd_1948471 444667628598556147534067 := by
  unfold tailWord_1948471
  simp only [CollatzResearch.WordTrace]
  refine ⟨71066575724029814198549267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47377717149353209465699511 71066575724029814198549267)
  ·
    refine ⟨106599863586044721297823901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71066575724029814198549267 106599863586044721297823901)
    ·
      refine ⟨39974948844766770486683963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106599863586044721297823901 39974948844766770486683963)
      ·
        refine ⟨59962423267150155730025945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39974948844766770486683963 59962423267150155730025945)
        ·
          refine ⟨44971817450362616797519459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59962423267150155730025945 44971817450362616797519459)
          ·
            refine ⟨67457726175543925196279189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44971817450362616797519459 67457726175543925196279189)
            ·
              refine ⟨3162080914478621493575587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67457726175543925196279189 3162080914478621493575587)
              ·
                refine ⟨4743121371717932240363381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162080914478621493575587 4743121371717932240363381)
                ·
                  refine ⟨444667628598556147534067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743121371717932240363381 444667628598556147534067)
                  ·
                    rfl

theorem cell21_1948471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_1948471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948471 prefixEnd_1948471 := by exact prefixLift 1948471
  have htrace : WordTrace (prefixWord ++ tailWord_1948471) baseStart_1948471 baseEnd_1948471 := by
    simpa [prefixWord, tailWord_1948471, baseEnd_1948471] using wordTrace_append hprefix tailTrace_1948471
  have hstable : (prefixWord ++ tailWord_1948471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948471).length < 2 ^ (prefixWord ++ tailWord_1948471).sum := by decide
  have hdescent : baseEnd_1948471 < baseStart_1948471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948505 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 3]
def baseStart_1948505 : Nat := 118140960795 + 1948505 * 2 ^ 59
def prefixEnd_1948505 : Nat := 4983230072969 + 3 ^ 40 * 1948505 * 2
def baseEnd_1948505 : Nat := 444675387861779643967331

theorem tailTrace_1948505 : CollatzResearch.WordTrace tailWord_1948505 prefixEnd_1948505 444675387861779643967331 := by
  unfold tailWord_1948505
  simp only [CollatzResearch.WordTrace]
  refine ⟨71067815805906638005286969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47378543870604425336857979 71067815805906638005286969)
  ·
    refine ⟨53300861854429978503965227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71067815805906638005286969 53300861854429978503965227)
    ·
      refine ⟨79951292781644967755947841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53300861854429978503965227 79951292781644967755947841)
      ·
        refine ⟨59963469586233725816960881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79951292781644967755947841 59963469586233725816960881)
        ·
          refine ⟨44972602189675294362720661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59963469586233725816960881 44972602189675294362720661)
          ·
            refine ⟨2108090727641029423252531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44972602189675294362720661 2108090727641029423252531)
            ·
              refine ⟨3162136091461544134878797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108090727641029423252531 3162136091461544134878797)
              ·
                refine ⟨1185801034298079050579549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3162136091461544134878797 1185801034298079050579549)
                ·
                  refine ⟨444675387861779643967331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185801034298079050579549 444675387861779643967331)
                  ·
                    rfl

theorem cell21_1948505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_1948505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948505 prefixEnd_1948505 := by exact prefixLift 1948505
  have htrace : WordTrace (prefixWord ++ tailWord_1948505) baseStart_1948505 baseEnd_1948505 := by
    simpa [prefixWord, tailWord_1948505, baseEnd_1948505] using wordTrace_append hprefix tailTrace_1948505
  have hstable : (prefixWord ++ tailWord_1948505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948505).length < 2 ^ (prefixWord ++ tailWord_1948505).sum := by decide
  have hdescent : baseEnd_1948505 < baseStart_1948505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948516 : List Nat := [2, 3, 1, 1, 4, 1, 9]
def baseStart_1948516 : Nat := 118140960795 + 1948516 * 2 ^ 59
def prefixEnd_1948516 : Nat := 4983230072969 + 3 ^ 40 * 1948516 * 2
def baseEnd_1948516 : Nat := 49408655356849563253775

theorem tailTrace_1948516 : CollatzResearch.WordTrace tailWord_1948516 prefixEnd_1948516 49408655356849563253775 := by
  unfold tailWord_1948516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35534108504433393441968701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47378811339244524589291601 35534108504433393441968701)
  ·
    refine ⟨13325290689162522540738263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35534108504433393441968701 13325290689162522540738263)
    ·
      refine ⟨19987936033743783811107395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325290689162522540738263 19987936033743783811107395)
      ·
        refine ⟨29981904050615675716661093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19987936033743783811107395 29981904050615675716661093)
        ·
          refine ⟨5621607009490439196873955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29981904050615675716661093 5621607009490439196873955)
          ·
            refine ⟨8432410514235658795310933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621607009490439196873955 8432410514235658795310933)
            ·
              refine ⟨49408655356849563253775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8432410514235658795310933 49408655356849563253775)
              ·
                rfl

theorem cell21_1948516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 9].length) (baseStart_1948516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948516 prefixEnd_1948516 := by exact prefixLift 1948516
  have htrace : WordTrace (prefixWord ++ tailWord_1948516) baseStart_1948516 baseEnd_1948516 := by
    simpa [prefixWord, tailWord_1948516, baseEnd_1948516] using wordTrace_append hprefix tailTrace_1948516
  have hstable : (prefixWord ++ tailWord_1948516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948516).length < 2 ^ (prefixWord ++ tailWord_1948516).sum := by decide
  have hdescent : baseEnd_1948516 < baseStart_1948516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948533 : List Nat := [1, 3, 4, 1, 1, 3, 2, 6]
def baseStart_1948533 : Nat := 118140960795 + 1948533 * 2 ^ 59
def prefixEnd_1948533 : Nat := 4983230072969 + 3 ^ 40 * 1948533 * 2
def baseEnd_1948533 : Nat := 148227259281085939166869

theorem tailTrace_1948533 : CollatzResearch.WordTrace tailWord_1948533 prefixEnd_1948533 148227259281085939166869 := by
  unfold tailWord_1948533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71068837049805198787306253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47379224699870132524870835 71068837049805198787306253)
  ·
    refine ⟨26650813893676949545239845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71068837049805198787306253 26650813893676949545239845)
    ·
      refine ⟨4997027605064428039732471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26650813893676949545239845 4997027605064428039732471)
      ·
        refine ⟨7495541407596642059598707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4997027605064428039732471 7495541407596642059598707)
        ·
          refine ⟨11243312111394963089398061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7495541407596642059598707 11243312111394963089398061)
          ·
            refine ⟨4216242041773111158524273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11243312111394963089398061 4216242041773111158524273)
            ·
              refine ⟨3162181531329833368893205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216242041773111158524273 3162181531329833368893205)
              ·
                refine ⟨148227259281085939166869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162181531329833368893205 148227259281085939166869)
                ·
                  rfl

theorem cell21_1948533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_1948533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948533 prefixEnd_1948533 := by exact prefixLift 1948533
  have htrace : WordTrace (prefixWord ++ tailWord_1948533) baseStart_1948533 baseEnd_1948533 := by
    simpa [prefixWord, tailWord_1948533, baseEnd_1948533] using wordTrace_append hprefix tailTrace_1948533
  have hstable : (prefixWord ++ tailWord_1948533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948533).length < 2 ^ (prefixWord ++ tailWord_1948533).sum := by decide
  have hdescent : baseEnd_1948533 < baseStart_1948533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948660 : List Nat := [2, 6, 2, 1, 1, 1, 1, 7]
def baseStart_1948660 : Nat := 118140960795 + 1948660 * 2 ^ 59
def prefixEnd_1948660 : Nat := 4983230072969 + 3 ^ 40 * 1948660 * 2
def baseEnd_1948660 : Nat := 148236920324511272961227

theorem tailTrace_1948660 : CollatzResearch.WordTrace tailWord_1948660 prefixEnd_1948660 148236920324511272961227 := by
  unfold tailWord_1948660
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536734560172549738589717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47382312746896732984786289 35536734560172549738589717)
  ·
    refine ⟨1665784432508088268996393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35536734560172549738589717 1665784432508088268996393)
    ·
      refine ⟨1249338324381066201747295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1665784432508088268996393 1249338324381066201747295)
      ·
        refine ⟨1874007486571599302620943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249338324381066201747295 1874007486571599302620943)
        ·
          refine ⟨2811011229857398953931415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874007486571599302620943 2811011229857398953931415)
          ·
            refine ⟨4216516844786098430897123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811011229857398953931415 4216516844786098430897123)
            ·
              refine ⟨6324775267179147646345685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216516844786098430897123 6324775267179147646345685)
              ·
                refine ⟨148236920324511272961227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6324775267179147646345685 148236920324511272961227)
                ·
                  rfl

theorem cell21_1948660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_1948660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948660 prefixEnd_1948660 := by exact prefixLift 1948660
  have htrace : WordTrace (prefixWord ++ tailWord_1948660) baseStart_1948660 baseEnd_1948660 := by
    simpa [prefixWord, tailWord_1948660, baseEnd_1948660] using wordTrace_append hprefix tailTrace_1948660
  have hstable : (prefixWord ++ tailWord_1948660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948660).length < 2 ^ (prefixWord ++ tailWord_1948660).sum := by decide
  have hdescent : baseEnd_1948660 < baseStart_1948660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948668 : List Nat := [2, 2, 2, 1, 2, 4, 1, 7]
def baseStart_1948668 : Nat := 118140960795 + 1948668 * 2 ^ 59
def prefixEnd_1948668 : Nat := 4983230072969 + 3 ^ 40 * 1948668 * 2
def baseEnd_1948668 : Nat := 148237528894175860916777

theorem tailTrace_1948668 : CollatzResearch.WordTrace tailWord_1948668 prefixEnd_1948668 148237528894175860916777 := by
  unfold tailWord_1948668
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536880452158058421735329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47382507269544077895647105 35536880452158058421735329)
  ·
    refine ⟨26652660339118543816301497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35536880452158058421735329 26652660339118543816301497)
    ·
      refine ⟨19989495254338907862226123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26652660339118543816301497 19989495254338907862226123)
      ·
        refine ⟨29984242881508361793339185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19989495254338907862226123 29984242881508361793339185)
        ·
          refine ⟨22488182161131271345004389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29984242881508361793339185 22488182161131271345004389)
          ·
            refine ⟨4216534155212113377188323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22488182161131271345004389 4216534155212113377188323)
            ·
              refine ⟨6324801232818170065782485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216534155212113377188323 6324801232818170065782485)
              ·
                refine ⟨148237528894175860916777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6324801232818170065782485 148237528894175860916777)
                ·
                  rfl

theorem cell21_1948668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_1948668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948668 prefixEnd_1948668 := by exact prefixLift 1948668
  have htrace : WordTrace (prefixWord ++ tailWord_1948668) baseStart_1948668 baseEnd_1948668 := by
    simpa [prefixWord, tailWord_1948668, baseEnd_1948668] using wordTrace_append hprefix tailTrace_1948668
  have hstable : (prefixWord ++ tailWord_1948668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948668).length < 2 ^ (prefixWord ++ tailWord_1948668).sum := by decide
  have hdescent : baseEnd_1948668 < baseStart_1948668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948775 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_1948775 : Nat := 118140960795 + 1948775 * 2 ^ 59
def prefixEnd_1948775 : Nat := 4983230072969 + 3 ^ 40 * 1948775 * 2
def baseEnd_1948775 : Nat := 444737005540319174466779

theorem tailTrace_1948775 : CollatzResearch.WordTrace tailWord_1948775 prefixEnd_1948775 444737005540319174466779 := by
  unfold tailWord_1948775
  simp only [CollatzResearch.WordTrace]
  refine ⟨71077663514928474117615779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47385109009952316078410519 71077663514928474117615779)
  ·
    refine ⟨106616495272392711176423669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71077663514928474117615779 106616495272392711176423669)
    ·
      refine ⟨9995296431786816672789719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106616495272392711176423669 9995296431786816672789719)
      ·
        refine ⟨14992944647680225009184579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995296431786816672789719 14992944647680225009184579)
        ·
          refine ⟨22489416971520337513776869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992944647680225009184579 22489416971520337513776869)
          ·
            refine ⟨4216765682160063283833163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22489416971520337513776869 4216765682160063283833163)
            ·
              refine ⟨6325148523240094925749745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216765682160063283833163 6325148523240094925749745)
              ·
                refine ⟨4743861392430071194312309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6325148523240094925749745 4743861392430071194312309)
                ·
                  refine ⟨444737005540319174466779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743861392430071194312309 444737005540319174466779)
                  ·
                    rfl

theorem cell21_1948775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_1948775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948775 prefixEnd_1948775 := by exact prefixLift 1948775
  have htrace : WordTrace (prefixWord ++ tailWord_1948775) baseStart_1948775 baseEnd_1948775 := by
    simpa [prefixWord, tailWord_1948775, baseEnd_1948775] using wordTrace_append hprefix tailTrace_1948775
  have hstable : (prefixWord ++ tailWord_1948775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948775).length < 2 ^ (prefixWord ++ tailWord_1948775).sum := by decide
  have hdescent : baseEnd_1948775 < baseStart_1948775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948798 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1948798 : Nat := 118140960795 + 1948798 * 2 ^ 59
def prefixEnd_1948798 : Nat := 4983230072969 + 3 ^ 40 * 1948798 * 2
def baseEnd_1948798 : Nat := 444742254453676245583399

theorem tailTrace_1948798 : CollatzResearch.WordTrace tailWord_1948798 prefixEnd_1948798 444742254453676245583399 := by
  unfold tailWord_1948798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884812799230643630712881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47385668262563432697135365 8884812799230643630712881)
  ·
    refine ⟨6663609599422982723034661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8884812799230643630712881 6663609599422982723034661)
    ·
      refine ⟨1249426799891809260568999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6663609599422982723034661 1249426799891809260568999)
      ·
        refine ⟨1874140199837713890853499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249426799891809260568999 1874140199837713890853499)
        ·
          refine ⟨2811210299756570836280249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874140199837713890853499 2811210299756570836280249)
          ·
            refine ⟨2108407724817428127210187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811210299756570836280249 2108407724817428127210187)
            ·
              refine ⟨3162611587226142190815281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108407724817428127210187 3162611587226142190815281)
              ·
                refine ⟨2371958690419606643111461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162611587226142190815281 2371958690419606643111461)
                ·
                  refine ⟨444742254453676245583399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371958690419606643111461 444742254453676245583399)
                  ·
                    rfl

theorem cell21_1948798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1948798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948798 prefixEnd_1948798 := by exact prefixLift 1948798
  have htrace : WordTrace (prefixWord ++ tailWord_1948798) baseStart_1948798 baseEnd_1948798 := by
    simpa [prefixWord, tailWord_1948798, baseEnd_1948798] using wordTrace_append hprefix tailTrace_1948798
  have hstable : (prefixWord ++ tailWord_1948798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948798).length < 2 ^ (prefixWord ++ tailWord_1948798).sum := by decide
  have hdescent : baseEnd_1948798 < baseStart_1948798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948803 : List Nat := [1, 1, 1, 3, 3, 2, 10]
def baseStart_1948803 : Nat := 118140960795 + 1948803 * 2 ^ 59
def prefixEnd_1948803 : Nat := 4983230072969 + 3 ^ 40 * 1948803 * 2
def baseEnd_1948803 : Nat := 49415932835755260888895

theorem tailTrace_1948803 : CollatzResearch.WordTrace tailWord_1948803 prefixEnd_1948803 49415932835755260888895 := by
  unfold tailWord_1948803
  simp only [CollatzResearch.WordTrace]
  refine ⟨71078684758827034899635063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47385789839218023266423375 71078684758827034899635063)
  ·
    refine ⟨106618027138240552349452595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71078684758827034899635063 106618027138240552349452595)
    ·
      refine ⟨159927040707360828524178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106618027138240552349452595 159927040707360828524178893)
      ·
        refine ⟨59972640265260310696567085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159927040707360828524178893 59972640265260310696567085)
        ·
          refine ⟨22489740099472616511212657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59972640265260310696567085 22489740099472616511212657)
          ·
            refine ⟨16867305074604462383409493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22489740099472616511212657 16867305074604462383409493)
            ·
              refine ⟨49415932835755260888895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16867305074604462383409493 49415932835755260888895)
              ·
                rfl

theorem cell21_1948803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_1948803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948803 prefixEnd_1948803 := by exact prefixLift 1948803
  have htrace : WordTrace (prefixWord ++ tailWord_1948803) baseStart_1948803 baseEnd_1948803 := by
    simpa [prefixWord, tailWord_1948803, baseEnd_1948803] using wordTrace_append hprefix tailTrace_1948803
  have hstable : (prefixWord ++ tailWord_1948803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948803).length < 2 ^ (prefixWord ++ tailWord_1948803).sum := by decide
  have hdescent : baseEnd_1948803 < baseStart_1948803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948823 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 4]
def baseStart_1948823 : Nat := 118140960795 + 1948823 * 2 ^ 59
def prefixEnd_1948823 : Nat := 4983230072969 + 3 ^ 40 * 1948823 * 2
def baseEnd_1948823 : Nat := 444747959794281757666681

theorem tailTrace_1948823 : CollatzResearch.WordTrace tailWord_1948823 prefixEnd_1948823 444747959794281757666681 := by
  unfold tailWord_1948823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71079414218754578315363123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47386276145836385543575415 71079414218754578315363123)
  ·
    refine ⟨106619121328131867473044685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71079414218754578315363123 106619121328131867473044685)
    ·
      refine ⟨39982170498049450302391757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106619121328131867473044685 39982170498049450302391757)
      ·
        refine ⟨14993313936768543863396909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39982170498049450302391757 14993313936768543863396909)
        ·
          refine ⟨5622492726288203948773841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14993313936768543863396909 5622492726288203948773841)
          ·
            refine ⟨4216869544716152961580381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5622492726288203948773841 4216869544716152961580381)
            ·
              refine ⟨1581326079268557360592643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4216869544716152961580381 1581326079268557360592643)
              ·
                refine ⟨2371989118902836040888965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581326079268557360592643 2371989118902836040888965)
                ·
                  refine ⟨444747959794281757666681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371989118902836040888965 444747959794281757666681)
                  ·
                    rfl

theorem cell21_1948823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_1948823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948823 prefixEnd_1948823 := by exact prefixLift 1948823
  have htrace : WordTrace (prefixWord ++ tailWord_1948823) baseStart_1948823 baseEnd_1948823 := by
    simpa [prefixWord, tailWord_1948823, baseEnd_1948823] using wordTrace_append hprefix tailTrace_1948823
  have hstable : (prefixWord ++ tailWord_1948823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948823).length < 2 ^ (prefixWord ++ tailWord_1948823).sum := by decide
  have hdescent : baseEnd_1948823 < baseStart_1948823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948837 : List Nat := [1, 3, 1, 2, 1, 6, 2, 5]
def baseStart_1948837 : Nat := 118140960795 + 1948837 * 2 ^ 59
def prefixEnd_1948837 : Nat := 4983230072969 + 3 ^ 40 * 1948837 * 2
def baseEnd_1948837 : Nat := 148250384928340281477773

theorem tailTrace_1948837 : CollatzResearch.WordTrace tailWord_1948837 prefixEnd_1948837 148250384928340281477773 := by
  unfold tailWord_1948837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71079924840703858706372765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47386616560469239137581843 71079924840703858706372765)
  ·
    refine ⟨26654971815263947014889787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71079924840703858706372765 26654971815263947014889787)
    ·
      refine ⟨39982457722895920522334681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26654971815263947014889787 39982457722895920522334681)
      ·
        refine ⟨29986843292171940391751011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39982457722895920522334681 29986843292171940391751011)
        ·
          refine ⟨44980264938257910587626517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29986843292171940391751011 44980264938257910587626517)
          ·
            refine ⟨2108449918980839558794993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44980264938257910587626517 2108449918980839558794993)
            ·
              refine ⟨1581337439235629669096245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108449918980839558794993 1581337439235629669096245)
              ·
                refine ⟨148250384928340281477773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1581337439235629669096245 148250384928340281477773)
                ·
                  rfl

theorem cell21_1948837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].length) (baseStart_1948837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948837 prefixEnd_1948837 := by exact prefixLift 1948837
  have htrace : WordTrace (prefixWord ++ tailWord_1948837) baseStart_1948837 baseEnd_1948837 := by
    simpa [prefixWord, tailWord_1948837, baseEnd_1948837] using wordTrace_append hprefix tailTrace_1948837
  have hstable : (prefixWord ++ tailWord_1948837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948837).length < 2 ^ (prefixWord ++ tailWord_1948837).sum := by decide
  have hdescent : baseEnd_1948837 < baseStart_1948837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948882 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1948882 : Nat := 118140960795 + 1948882 * 2 ^ 59
def prefixEnd_1948882 : Nat := 4983230072969 + 3 ^ 40 * 1948882 * 2
def baseEnd_1948882 : Nat := 444761424398110766183227

theorem tailTrace_1948882 : CollatzResearch.WordTrace tailWord_1948882 prefixEnd_1948882 444761424398110766183227 := by
  unfold tailWord_1948882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770391531385207847940225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47387710750360554261173933 17770391531385207847940225)
  ·
    refine ⟨13327793648538905885955169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17770391531385207847940225 13327793648538905885955169)
    ·
      refine ⟨9995845236404179414466377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13327793648538905885955169 9995845236404179414466377)
      ·
        refine ⟨7496883927303134560849783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9995845236404179414466377 7496883927303134560849783)
        ·
          refine ⟨11245325890954701841274675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496883927303134560849783 11245325890954701841274675)
          ·
            refine ⟨16867988836432052761912013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245325890954701841274675 16867988836432052761912013)
            ·
              refine ⟨6325495813662019785717005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16867988836432052761912013 6325495813662019785717005)
              ·
                refine ⟨2372060930123257419643877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6325495813662019785717005 2372060930123257419643877)
                ·
                  refine ⟨444761424398110766183227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372060930123257419643877 444761424398110766183227)
                  ·
                    rfl

theorem cell21_1948882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1948882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948882 prefixEnd_1948882 := by exact prefixLift 1948882
  have htrace : WordTrace (prefixWord ++ tailWord_1948882) baseStart_1948882 baseEnd_1948882 := by
    simpa [prefixWord, tailWord_1948882, baseEnd_1948882] using wordTrace_append hprefix tailTrace_1948882
  have hstable : (prefixWord ++ tailWord_1948882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948882).length < 2 ^ (prefixWord ++ tailWord_1948882).sum := by decide
  have hdescent : baseEnd_1948882 < baseStart_1948882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1948930 : List Nat := [3, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1948930 : Nat := 118140960795 + 1948930 * 2 ^ 59
def prefixEnd_1948930 : Nat := 4983230072969 + 3 ^ 40 * 1948930 * 2
def baseEnd_1948930 : Nat := 148257459550691116461043

theorem tailTrace_1948930 : CollatzResearch.WordTrace tailWord_1948930 prefixEnd_1948930 148257459550691116461043 := by
  unfold tailWord_1948930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770829207341733897377061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47388877886244623726338829 17770829207341733897377061)
  ·
    refine ⟨3332030476376575105758199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17770829207341733897377061 3332030476376575105758199)
    ·
      refine ⟨4998045714564862658637299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332030476376575105758199 4998045714564862658637299)
      ·
        refine ⟨7497068571847293987955949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998045714564862658637299 7497068571847293987955949)
        ·
          refine ⟨2811400714442735245483481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7497068571847293987955949 2811400714442735245483481)
          ·
            refine ⟨2108550535832051434112611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811400714442735245483481 2108550535832051434112611)
            ·
              refine ⟨3162825803748077151168917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108550535832051434112611 3162825803748077151168917)
              ·
                refine ⟨148257459550691116461043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162825803748077151168917 148257459550691116461043)
                ·
                  rfl

theorem cell21_1948930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1948930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1948930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1948930 prefixEnd_1948930 := by exact prefixLift 1948930
  have htrace : WordTrace (prefixWord ++ tailWord_1948930) baseStart_1948930 baseEnd_1948930 := by
    simpa [prefixWord, tailWord_1948930, baseEnd_1948930] using wordTrace_append hprefix tailTrace_1948930
  have hstable : (prefixWord ++ tailWord_1948930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1948930).length < 2 ^ (prefixWord ++ tailWord_1948930).sum := by decide
  have hdescent : baseEnd_1948930 < baseStart_1948930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1948930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949037 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1949037 : Nat := 118140960795 + 1949037 * 2 ^ 59
def prefixEnd_1949037 : Nat := 4983230072969 + 3 ^ 40 * 1949037 * 2
def baseEnd_1949037 : Nat := 444796797509864941099577

theorem tailTrace_1949037 : CollatzResearch.WordTrace tailWord_1949037 prefixEnd_1949037 444796797509864941099577 := by
  unfold tailWord_1949037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71087219439979292863653365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47391479626652861909102243 71087219439979292863653365)
  ·
    refine ⟨6664426822498058705967503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71087219439979292863653365 6664426822498058705967503)
    ·
      refine ⟨9996640233747088058951255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664426822498058705967503 9996640233747088058951255)
      ·
        refine ⟨14994960350620632088426883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996640233747088058951255 14994960350620632088426883)
        ·
          refine ⟨22492440525930948132640325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994960350620632088426883 22492440525930948132640325)
          ·
            refine ⟨4217332598612052774870061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22492440525930948132640325 4217332598612052774870061)
            ·
              refine ⟨1581499724479519790576273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4217332598612052774870061 1581499724479519790576273)
              ·
                refine ⟨1186124793359639842932205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581499724479519790576273 1186124793359639842932205)
                ·
                  refine ⟨444796797509864941099577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186124793359639842932205 444796797509864941099577)
                  ·
                    rfl

theorem cell21_1949037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1949037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949037 prefixEnd_1949037 := by exact prefixLift 1949037
  have htrace : WordTrace (prefixWord ++ tailWord_1949037) baseStart_1949037 baseEnd_1949037 := by
    simpa [prefixWord, tailWord_1949037, baseEnd_1949037] using wordTrace_append hprefix tailTrace_1949037
  have hstable : (prefixWord ++ tailWord_1949037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949037).length < 2 ^ (prefixWord ++ tailWord_1949037).sum := by decide
  have hdescent : baseEnd_1949037 < baseStart_1949037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949079 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 3]
def baseStart_1949079 : Nat := 118140960795 + 1949079 * 2 ^ 59
def prefixEnd_1949079 : Nat := 4983230072969 + 3 ^ 40 * 1949079 * 2
def baseEnd_1949079 : Nat := 444806382482082201399491

theorem tailTrace_1949079 : CollatzResearch.WordTrace tailWord_1949079 prefixEnd_1949079 444806382482082201399491 := by
  unfold tailWord_1949079
  simp only [CollatzResearch.WordTrace]
  refine ⟨71088751305827134036682291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47392500870551422691121527 71088751305827134036682291)
  ·
    refine ⟨106633126958740701055023437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71088751305827134036682291 106633126958740701055023437)
    ·
      refine ⟨39987422609527762895633789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106633126958740701055023437 39987422609527762895633789)
      ·
        refine ⟨14995283478572911085862671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39987422609527762895633789 14995283478572911085862671)
        ·
          refine ⟨22492925217859366628794007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14995283478572911085862671 22492925217859366628794007)
          ·
            refine ⟨33739387826789049943191011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22492925217859366628794007 33739387826789049943191011)
            ·
              refine ⟨50609081740183574914786517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33739387826789049943191011 50609081740183574914786517)
              ·
                refine ⟨1186150353285552537065309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50609081740183574914786517 1186150353285552537065309)
                ·
                  refine ⟨444806382482082201399491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186150353285552537065309 444806382482082201399491)
                  ·
                    rfl

theorem cell21_1949079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].length) (baseStart_1949079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949079 prefixEnd_1949079 := by exact prefixLift 1949079
  have htrace : WordTrace (prefixWord ++ tailWord_1949079) baseStart_1949079 baseEnd_1949079 := by
    simpa [prefixWord, tailWord_1949079, baseEnd_1949079] using wordTrace_append hprefix tailTrace_1949079
  have hstable : (prefixWord ++ tailWord_1949079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949079).length < 2 ^ (prefixWord ++ tailWord_1949079).sum := by decide
  have hdescent : baseEnd_1949079 < baseStart_1949079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949155 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_1949155 : Nat := 118140960795 + 1949155 * 2 ^ 59
def prefixEnd_1949155 : Nat := 4983230072969 + 3 ^ 40 * 1949155 * 2
def baseEnd_1949155 : Nat := 444823726717522958132669

theorem tailTrace_1949155 : CollatzResearch.WordTrace tailWord_1949155 prefixEnd_1949155 444823726717522958132669 := by
  unfold tailWord_1949155
  simp only [CollatzResearch.WordTrace]
  refine ⟨71091523253551799016448919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47394348835701199344299279 71091523253551799016448919)
  ·
    refine ⟨106637284880327698524673379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71091523253551799016448919 106637284880327698524673379)
    ·
      refine ⟨159955927320491547787010069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106637284880327698524673379 159955927320491547787010069)
      ·
        refine ⟨7497934093148041302516097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159955927320491547787010069 7497934093148041302516097)
        ·
          refine ⟨5623450569861030976887073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497934093148041302516097 5623450569861030976887073)
          ·
            refine ⟨4217587927395773232665305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5623450569861030976887073 4217587927395773232665305)
            ·
              refine ⟨3163190945546829924498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217587927395773232665305 3163190945546829924498979)
              ·
                refine ⟨4744786418320244886748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163190945546829924498979 4744786418320244886748469)
                ·
                  refine ⟨444823726717522958132669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744786418320244886748469 444823726717522958132669)
                  ·
                    rfl

theorem cell21_1949155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_1949155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949155 prefixEnd_1949155 := by exact prefixLift 1949155
  have htrace : WordTrace (prefixWord ++ tailWord_1949155) baseStart_1949155 baseEnd_1949155 := by
    simpa [prefixWord, tailWord_1949155, baseEnd_1949155] using wordTrace_append hprefix tailTrace_1949155
  have hstable : (prefixWord ++ tailWord_1949155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949155).length < 2 ^ (prefixWord ++ tailWord_1949155).sum := by decide
  have hdescent : baseEnd_1949155 < baseStart_1949155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949186 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1949186 : Nat := 118140960795 + 1949186 * 2 ^ 59
def prefixEnd_1949186 : Nat := 4983230072969 + 3 ^ 40 * 1949186 * 2
def baseEnd_1949186 : Nat := 444830801339873793115939

theorem tailTrace_1949186 : CollatzResearch.WordTrace tailWord_1949186 prefixEnd_1949186 444830801339873793115939 := by
  unfold tailWord_1949186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773163479109872827706853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47395102610959660873884941 17773163479109872827706853)
  ·
    refine ⟨3332468152333101155195035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17773163479109872827706853 3332468152333101155195035)
    ·
      refine ⟨4998702228499651732792553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332468152333101155195035 4998702228499651732792553)
      ·
        refine ⟨3749026671374738799594415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998702228499651732792553 3749026671374738799594415)
        ·
          refine ⟨5623540007062108199391623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749026671374738799594415 5623540007062108199391623)
          ·
            refine ⟨8435310010593162299087435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623540007062108199391623 8435310010593162299087435)
            ·
              refine ⟨12652965015889743448631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435310010593162299087435 12652965015889743448631153)
              ·
                refine ⟨9489723761917307586473365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652965015889743448631153 9489723761917307586473365)
                ·
                  refine ⟨444830801339873793115939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9489723761917307586473365 444830801339873793115939)
                  ·
                    rfl

theorem cell21_1949186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1949186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949186 prefixEnd_1949186 := by exact prefixLift 1949186
  have htrace : WordTrace (prefixWord ++ tailWord_1949186) baseStart_1949186 baseEnd_1949186 := by
    simpa [prefixWord, tailWord_1949186, baseEnd_1949186] using wordTrace_append hprefix tailTrace_1949186
  have hstable : (prefixWord ++ tailWord_1949186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949186).length < 2 ^ (prefixWord ++ tailWord_1949186).sum := by decide
  have hdescent : baseEnd_1949186 < baseStart_1949186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949273 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_1949273 : Nat := 118140960795 + 1949273 * 2 ^ 59
def prefixEnd_1949273 : Nat := 4983230072969 + 3 ^ 40 * 1949273 * 2
def baseEnd_1949273 : Nat := 444850655925180975165761

theorem tailTrace_1949273 : CollatzResearch.WordTrace tailWord_1949273 prefixEnd_1949273 444850655925180975165761 := by
  unfold tailWord_1949273
  simp only [CollatzResearch.WordTrace]
  refine ⟨71095827067124305169244473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47397218044749536779496315 71095827067124305169244473)
  ·
    refine ⟨53321870300343228876933355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71095827067124305169244473 53321870300343228876933355)
    ·
      refine ⟨79982805450514843315400033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53321870300343228876933355 79982805450514843315400033)
      ·
        refine ⟨59987104087886132486550025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79982805450514843315400033 59987104087886132486550025)
        ·
          refine ⟨44990328065914599364912519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59987104087886132486550025 44990328065914599364912519)
          ·
            refine ⟨67485492098871899047368779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44990328065914599364912519 67485492098871899047368779)
            ·
              refine ⟨101228238148307848571053169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67485492098871899047368779 101228238148307848571053169)
              ·
                refine ⟨75921178611230886428289877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101228238148307848571053169 75921178611230886428289877)
                ·
                  refine ⟨444850655925180975165761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75921178611230886428289877 444850655925180975165761)
                  ·
                    rfl

theorem cell21_1949273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_1949273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949273 prefixEnd_1949273 := by exact prefixLift 1949273
  have htrace : WordTrace (prefixWord ++ tailWord_1949273) baseStart_1949273 baseEnd_1949273 := by
    simpa [prefixWord, tailWord_1949273, baseEnd_1949273] using wordTrace_append hprefix tailTrace_1949273
  have hstable : (prefixWord ++ tailWord_1949273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949273).length < 2 ^ (prefixWord ++ tailWord_1949273).sum := by decide
  have hdescent : baseEnd_1949273 < baseStart_1949273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949276 : List Nat := [2, 2, 4, 1, 2, 1, 3, 6]
def baseStart_1949276 : Nat := 118140960795 + 1949276 * 2 ^ 59
def prefixEnd_1949276 : Nat := 4983230072969 + 3 ^ 40 * 1949276 * 2
def baseEnd_1949276 : Nat := 148283780188684545538585

theorem tailTrace_1949276 : CollatzResearch.WordTrace tailWord_1949276 prefixEnd_1949276 148283780188684545538585 := by
  unfold tailWord_1949276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35547968243056718340801841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47397290990742291121069121 35547968243056718340801841)
  ·
    refine ⟨26660976182292538755601381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35547968243056718340801841 26660976182292538755601381)
    ·
      refine ⟨4998933034179851016675259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26660976182292538755601381 4998933034179851016675259)
      ·
        refine ⟨7498399551269776525012889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998933034179851016675259 7498399551269776525012889)
        ·
          refine ⟨5623799663452332393759667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7498399551269776525012889 5623799663452332393759667)
          ·
            refine ⟨8435699495178498590639501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623799663452332393759667 8435699495178498590639501)
            ·
              refine ⟨3163387310691936971489813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8435699495178498590639501 3163387310691936971489813)
              ·
                refine ⟨148283780188684545538585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3163387310691936971489813 148283780188684545538585)
                ·
                  rfl

theorem cell21_1949276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_1949276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949276 prefixEnd_1949276 := by exact prefixLift 1949276
  have htrace : WordTrace (prefixWord ++ tailWord_1949276) baseStart_1949276 baseEnd_1949276 := by
    simpa [prefixWord, tailWord_1949276, baseEnd_1949276] using wordTrace_append hprefix tailTrace_1949276
  have hstable : (prefixWord ++ tailWord_1949276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949276).length < 2 ^ (prefixWord ++ tailWord_1949276).sum := by decide
  have hdescent : baseEnd_1949276 < baseStart_1949276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949290 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1949290 : Nat := 118140960795 + 1949290 * 2 ^ 59
def prefixEnd_1949290 : Nat := 4983230072969 + 3 ^ 40 * 1949290 * 2
def baseEnd_1949290 : Nat := 444854535556792723382393

theorem tailTrace_1949290 : CollatzResearch.WordTrace tailWord_1949290 prefixEnd_1949290 444854535556792723382393 := by
  unfold tailWord_1949290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17774111777015679268153331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47397631405375144715075549 17774111777015679268153331)
  ·
    refine ⟨26661167665523518902229997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17774111777015679268153331 26661167665523518902229997)
    ·
      refine ⟨9997937874571319588336249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26661167665523518902229997 9997937874571319588336249)
      ·
        refine ⟨7498453405928489691252187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9997937874571319588336249 7498453405928489691252187)
        ·
          refine ⟨11247680108892734536878281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498453405928489691252187 11247680108892734536878281)
          ·
            refine ⟨8435760081669550902658711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11247680108892734536878281 8435760081669550902658711)
            ·
              refine ⟨12653640122504326353988067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435760081669550902658711 12653640122504326353988067)
              ·
                refine ⟨18980460183756489530982101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653640122504326353988067 18980460183756489530982101)
                ·
                  refine ⟨444854535556792723382393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18980460183756489530982101 444854535556792723382393)
                  ·
                    rfl

theorem cell21_1949290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1949290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949290 prefixEnd_1949290 := by exact prefixLift 1949290
  have htrace : WordTrace (prefixWord ++ tailWord_1949290) baseStart_1949290 baseEnd_1949290 := by
    simpa [prefixWord, tailWord_1949290, baseEnd_1949290] using wordTrace_append hprefix tailTrace_1949290
  have hstable : (prefixWord ++ tailWord_1949290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949290).length < 2 ^ (prefixWord ++ tailWord_1949290).sum := by decide
  have hdescent : baseEnd_1949290 < baseStart_1949290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949293 : List Nat := [1, 5, 1, 1, 4, 1, 3, 5]
def baseStart_1949293 : Nat := 118140960795 + 1949293 * 2 ^ 59
def prefixEnd_1949293 : Nat := 4983230072969 + 3 ^ 40 * 1949293 * 2
def baseEnd_1949293 : Nat := 148285073399221794944129

theorem tailTrace_1949293 : CollatzResearch.WordTrace tailWord_1949293 prefixEnd_1949293 148285073399221794944129 := by
  unfold tailWord_1949293
  simp only [CollatzResearch.WordTrace]
  refine ⟨71096556527051848584972533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47397704351367899056648355 71096556527051848584972533)
  ·
    refine ⟨6665302174411110804841175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71096556527051848584972533 6665302174411110804841175)
    ·
      refine ⟨9997953261616666207261763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6665302174411110804841175 9997953261616666207261763)
      ·
        refine ⟨14996929892424999310892645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9997953261616666207261763 14996929892424999310892645)
        ·
          refine ⟨2811924354829687370792371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14996929892424999310892645 2811924354829687370792371)
          ·
            refine ⟨4217886532244531056188557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811924354829687370792371 4217886532244531056188557)
            ·
              refine ⟨1581707449591699146070709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4217886532244531056188557 1581707449591699146070709)
              ·
                refine ⟨148285073399221794944129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1581707449591699146070709 148285073399221794944129)
                ·
                  rfl

theorem cell21_1949293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].length) (baseStart_1949293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949293 prefixEnd_1949293 := by exact prefixLift 1949293
  have htrace : WordTrace (prefixWord ++ tailWord_1949293) baseStart_1949293 baseEnd_1949293 := by
    simpa [prefixWord, tailWord_1949293, baseEnd_1949293] using wordTrace_append hprefix tailTrace_1949293
  have hstable : (prefixWord ++ tailWord_1949293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949293).length < 2 ^ (prefixWord ++ tailWord_1949293).sum := by decide
  have hdescent : baseEnd_1949293 < baseStart_1949293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949307 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 3]
def baseStart_1949307 : Nat := 118140960795 + 1949307 * 2 ^ 59
def prefixEnd_1949307 : Nat := 4983230072969 + 3 ^ 40 * 1949307 * 2
def baseEnd_1949307 : Nat := 444858415188404471599025

theorem tailTrace_1949307 : CollatzResearch.WordTrace tailWord_1949307 prefixEnd_1949307 444858415188404471599025 := by
  unfold tailWord_1949307
  simp only [CollatzResearch.WordTrace]
  refine ⟨71097067149001128975982175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47398044766000752650654783 71097067149001128975982175)
  ·
    refine ⟨106645600723501693463973263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71097067149001128975982175 106645600723501693463973263)
    ·
      refine ⟨159968401085252540195959895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106645600723501693463973263 159968401085252540195959895)
      ·
        refine ⟨239952601627878810293939843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159968401085252540195959895 239952601627878810293939843)
        ·
          refine ⟨359928902441818215440909765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239952601627878810293939843 359928902441818215440909765)
          ·
            refine ⟨67486669207840915395170581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359928902441818215440909765 67486669207840915395170581)
            ·
              refine ⟨3163437619117542909148621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67486669207840915395170581 3163437619117542909148621)
              ·
                refine ⟨1186289107169078590930733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163437619117542909148621 1186289107169078590930733)
                ·
                  refine ⟨444858415188404471599025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186289107169078590930733 444858415188404471599025)
                  ·
                    rfl

theorem cell21_1949307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].length) (baseStart_1949307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949307 prefixEnd_1949307 := by exact prefixLift 1949307
  have htrace : WordTrace (prefixWord ++ tailWord_1949307) baseStart_1949307 baseEnd_1949307 := by
    simpa [prefixWord, tailWord_1949307, baseEnd_1949307] using wordTrace_append hprefix tailTrace_1949307
  have hstable : (prefixWord ++ tailWord_1949307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949307).length < 2 ^ (prefixWord ++ tailWord_1949307).sum := by decide
  have hdescent : baseEnd_1949307 < baseStart_1949307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949321 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_1949321 : Nat := 118140960795 + 1949321 * 2 ^ 59
def prefixEnd_1949321 : Nat := 4983230072969 + 3 ^ 40 * 1949321 * 2
def baseEnd_1949321 : Nat := 444861610179143558365663

theorem tailTrace_1949321 : CollatzResearch.WordTrace tailWord_1949321 prefixEnd_1949321 444861610179143558365663 := by
  unfold tailWord_1949321
  simp only [CollatzResearch.WordTrace]
  refine ⟨71097577770950409366991817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47398385180633606244661211 71097577770950409366991817)
  ·
    refine ⟨53323183328212807025243863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71097577770950409366991817 53323183328212807025243863)
    ·
      refine ⟨79984774992319210537865795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53323183328212807025243863 79984774992319210537865795)
      ·
        refine ⟨119977162488478815806798693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79984774992319210537865795 119977162488478815806798693)
        ·
          refine ⟨22495717966589777963774755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119977162488478815806798693 22495717966589777963774755)
          ·
            refine ⟨33743576949884666945662133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22495717966589777963774755 33743576949884666945662133)
            ·
              refine ⟨3163460339051687526155825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33743576949884666945662133 3163460339051687526155825)
              ·
                refine ⟨2372595254288765644616869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163460339051687526155825 2372595254288765644616869)
                ·
                  refine ⟨444861610179143558365663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372595254288765644616869 444861610179143558365663)
                  ·
                    rfl

theorem cell21_1949321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_1949321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949321 prefixEnd_1949321 := by exact prefixLift 1949321
  have htrace : WordTrace (prefixWord ++ tailWord_1949321) baseStart_1949321 baseEnd_1949321 := by
    simpa [prefixWord, tailWord_1949321, baseEnd_1949321] using wordTrace_append hprefix tailTrace_1949321
  have hstable : (prefixWord ++ tailWord_1949321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949321).length < 2 ^ (prefixWord ++ tailWord_1949321).sum := by decide
  have hdescent : baseEnd_1949321 < baseStart_1949321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949358 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1949358 : Nat := 118140960795 + 1949358 * 2 ^ 59
def prefixEnd_1949358 : Nat := 4983230072969 + 3 ^ 40 * 1949358 * 2
def baseEnd_1949358 : Nat := 444870054083239716248921

theorem tailTrace_1949358 : CollatzResearch.WordTrace tailWord_1949358 prefixEnd_1949358 444870054083239716248921 := by
  unfold tailWord_1949358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887365908977045585761091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47399284847877576457392485 8887365908977045585761091)
  ·
    refine ⟨13331048863465568378641637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887365908977045585761091 13331048863465568378641637)
    ·
      refine ⟨2499571661899794070995307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13331048863465568378641637 2499571661899794070995307)
      ·
        refine ⟨3749357492849691106492961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499571661899794070995307 3749357492849691106492961)
        ·
          refine ⟨2812018119637268329869721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749357492849691106492961 2812018119637268329869721)
          ·
            refine ⟨2109013589727951247402291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2812018119637268329869721 2109013589727951247402291)
            ·
              refine ⟨3163520384591926871103437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109013589727951247402291 3163520384591926871103437)
              ·
                refine ⟨1186320144221972576663789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163520384591926871103437 1186320144221972576663789)
                ·
                  refine ⟨444870054083239716248921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186320144221972576663789 444870054083239716248921)
                  ·
                    rfl

theorem cell21_1949358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1949358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949358 prefixEnd_1949358 := by exact prefixLift 1949358
  have htrace : WordTrace (prefixWord ++ tailWord_1949358) baseStart_1949358 baseEnd_1949358 := by
    simpa [prefixWord, tailWord_1949358, baseEnd_1949358] using wordTrace_append hprefix tailTrace_1949358
  have hstable : (prefixWord ++ tailWord_1949358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949358).length < 2 ^ (prefixWord ++ tailWord_1949358).sum := by decide
  have hdescent : baseEnd_1949358 < baseStart_1949358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949476 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_1949476 : Nat := 118140960795 + 1949476 * 2 ^ 59
def prefixEnd_1949476 : Nat := 4983230072969 + 3 ^ 40 * 1949476 * 2
def baseEnd_1949476 : Nat := 444896983290897733282013

theorem tailTrace_1949476 : CollatzResearch.WordTrace tailWord_1949476 prefixEnd_1949476 444896983290897733282013 := by
  unfold tailWord_1949476
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551615542694435419442141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47402154056925913892589521 35551615542694435419442141)
  ·
    refine ⟨13331855828510413282290803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35551615542694435419442141 13331855828510413282290803)
    ·
      refine ⟨19997783742765619923436205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331855828510413282290803 19997783742765619923436205)
      ·
        refine ⟨7499168903537107471288577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19997783742765619923436205 7499168903537107471288577)
        ·
          refine ⟨5624376677652830603466433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499168903537107471288577 5624376677652830603466433)
          ·
            refine ⟨4218282508239622952599825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5624376677652830603466433 4218282508239622952599825)
            ·
              refine ⟨3163711881179717214449869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218282508239622952599825 3163711881179717214449869)
              ·
                refine ⟨1186391955442393955418701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163711881179717214449869 1186391955442393955418701)
                ·
                  refine ⟨444896983290897733282013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186391955442393955418701 444896983290897733282013)
                  ·
                    rfl

theorem cell21_1949476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_1949476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949476 prefixEnd_1949476 := by exact prefixLift 1949476
  have htrace : WordTrace (prefixWord ++ tailWord_1949476) baseStart_1949476 baseEnd_1949476 := by
    simpa [prefixWord, tailWord_1949476, baseEnd_1949476] using wordTrace_append hprefix tailTrace_1949476
  have hstable : (prefixWord ++ tailWord_1949476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949476).length < 2 ^ (prefixWord ++ tailWord_1949476).sum := by decide
  have hdescent : baseEnd_1949476 < baseStart_1949476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949490 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1949490 : Nat := 118140960795 + 1949490 * 2 ^ 59
def prefixEnd_1949490 : Nat := 4983230072969 + 3 ^ 40 * 1949490 * 2
def baseEnd_1949490 : Nat := 444900178281636820048651

theorem tailTrace_1949490 : CollatzResearch.WordTrace tailWord_1949490 prefixEnd_1949490 444900178281636820048651 := by
  unfold tailWord_1949490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775935426834537807473481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47402494471558767486595949 17775935426834537807473481)
  ·
    refine ⟨13331951570125903355605111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17775935426834537807473481 13331951570125903355605111)
    ·
      refine ⟨19997927355188855033407667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331951570125903355605111 19997927355188855033407667)
      ·
        refine ⟨29996891032783282550111501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19997927355188855033407667 29996891032783282550111501)
        ·
          refine ⟨11248834137293730956291813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29996891032783282550111501 11248834137293730956291813)
          ·
            refine ⟨2109156400742574554304715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11248834137293730956291813 2109156400742574554304715)
            ·
              refine ⟨3163734601113861831457073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109156400742574554304715 3163734601113861831457073)
              ·
                refine ⟨2372800950835396373592805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163734601113861831457073 2372800950835396373592805)
                ·
                  refine ⟨444900178281636820048651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372800950835396373592805 444900178281636820048651)
                  ·
                    rfl

theorem cell21_1949490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1949490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949490 prefixEnd_1949490 := by exact prefixLift 1949490
  have htrace : WordTrace (prefixWord ++ tailWord_1949490) baseStart_1949490 baseEnd_1949490 := by
    simpa [prefixWord, tailWord_1949490, baseEnd_1949490] using wordTrace_append hprefix tailTrace_1949490
  have hstable : (prefixWord ++ tailWord_1949490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949490).length < 2 ^ (prefixWord ++ tailWord_1949490).sum := by decide
  have hdescent : baseEnd_1949490 < baseStart_1949490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949535 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 3]
def baseStart_1949535 : Nat := 118140960795 + 1949535 * 2 ^ 59
def prefixEnd_1949535 : Nat := 4983230072969 + 3 ^ 40 * 1949535 * 2
def baseEnd_1949535 : Nat := 444910447894726741798559

theorem tailTrace_1949535 : CollatzResearch.WordTrace tailWord_1949535 prefixEnd_1949535 444910447894726741798559 := by
  unfold tailWord_1949535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71105382992175123915282059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47403588661450082610188039 71105382992175123915282059)
  ·
    refine ⟨106658074488262685872923089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71105382992175123915282059 106658074488262685872923089)
    ·
      refine ⟨79993555866197014404692317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106658074488262685872923089 79993555866197014404692317)
      ·
        refine ⟨29997583449823880401759619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79993555866197014404692317 29997583449823880401759619)
        ·
          refine ⟨44996375174735820602639429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29997583449823880401759619 44996375174735820602639429)
          ·
            refine ⟨8436820345262966362994893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44996375174735820602639429 8436820345262966362994893)
            ·
              refine ⟨3163807629473612386123085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8436820345262966362994893 3163807629473612386123085)
              ·
                refine ⟨1186427861052604644796157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163807629473612386123085 1186427861052604644796157)
                ·
                  refine ⟨444910447894726741798559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186427861052604644796157 444910447894726741798559)
                  ·
                    rfl

theorem cell21_1949535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].length) (baseStart_1949535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949535 prefixEnd_1949535 := by exact prefixLift 1949535
  have htrace : WordTrace (prefixWord ++ tailWord_1949535) baseStart_1949535 baseEnd_1949535 := by
    simpa [prefixWord, tailWord_1949535, baseEnd_1949535] using wordTrace_append hprefix tailTrace_1949535
  have hstable : (prefixWord ++ tailWord_1949535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949535).length < 2 ^ (prefixWord ++ tailWord_1949535).sum := by decide
  have hdescent : baseEnd_1949535 < baseStart_1949535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949577 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_1949577 : Nat := 118140960795 + 1949577 * 2 ^ 59
def prefixEnd_1949577 : Nat := 4983230072969 + 3 ^ 40 * 1949577 * 2
def baseEnd_1949577 : Nat := 444920032866944002098473

theorem tailTrace_1949577 : CollatzResearch.WordTrace tailWord_1949577 prefixEnd_1949577 444920032866944002098473 := by
  unfold tailWord_1949577
  simp only [CollatzResearch.WordTrace]
  refine ⟨71106914858022965088310985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47404609905348643392207323 71106914858022965088310985)
  ·
    refine ⟨53330186143517223816233239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71106914858022965088310985 53330186143517223816233239)
    ·
      refine ⟨79995279215275835724349859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53330186143517223816233239 79995279215275835724349859)
      ·
        refine ⟨119992918822913753586524789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79995279215275835724349859 119992918822913753586524789)
        ·
          refine ⟨11249336139648164398736699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119992918822913753586524789 11249336139648164398736699)
          ·
            refine ⟨16874004209472246598105049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249336139648164398736699 16874004209472246598105049)
            ·
              refine ⟨12655503157104184948578787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874004209472246598105049 12655503157104184948578787)
              ·
                refine ⟨18983254735656277422868181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12655503157104184948578787 18983254735656277422868181)
                ·
                  refine ⟨444920032866944002098473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18983254735656277422868181 444920032866944002098473)
                  ·
                    rfl

theorem cell21_1949577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_1949577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949577 prefixEnd_1949577 := by exact prefixLift 1949577
  have htrace : WordTrace (prefixWord ++ tailWord_1949577) baseStart_1949577 baseEnd_1949577 := by
    simpa [prefixWord, tailWord_1949577, baseEnd_1949577] using wordTrace_append hprefix tailTrace_1949577
  have hstable : (prefixWord ++ tailWord_1949577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949577).length < 2 ^ (prefixWord ++ tailWord_1949577).sum := by decide
  have hdescent : baseEnd_1949577 < baseStart_1949577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949732 : List Nat := [2, 3, 1, 4, 2, 1, 2, 6]
def baseStart_1949732 : Nat := 118140960795 + 1949732 * 2 ^ 59
def prefixEnd_1949732 : Nat := 4983230072969 + 3 ^ 40 * 1949732 * 2
def baseEnd_1949732 : Nat := 148318468659566059004941

theorem tailTrace_1949732 : CollatzResearch.WordTrace tailWord_1949732 prefixEnd_1949732 148318468659566059004941 := by
  unfold tailWord_1949732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556284086230713280101725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47408378781640951040135633 35556284086230713280101725)
  ·
    refine ⟨13333606532336517480038147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35556284086230713280101725 13333606532336517480038147)
    ·
      refine ⟨20000409798504776220057221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333606532336517480038147 20000409798504776220057221)
      ·
        refine ⟨3750076837219645541260729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20000409798504776220057221 3750076837219645541260729)
        ·
          refine ⟨2812557627914734155945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750076837219645541260729 2812557627914734155945547)
          ·
            refine ⟨4218836441872101233918321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812557627914734155945547 4218836441872101233918321)
            ·
              refine ⟨3164127331404075925438741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218836441872101233918321 3164127331404075925438741)
              ·
                refine ⟨148318468659566059004941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3164127331404075925438741 148318468659566059004941)
                ·
                  rfl

theorem cell21_1949732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_1949732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949732 prefixEnd_1949732 := by exact prefixLift 1949732
  have htrace : WordTrace (prefixWord ++ tailWord_1949732) baseStart_1949732 baseEnd_1949732 := by
    simpa [prefixWord, tailWord_1949732, baseEnd_1949732] using wordTrace_append hprefix tailTrace_1949732
  have hstable : (prefixWord ++ tailWord_1949732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949732).length < 2 ^ (prefixWord ++ tailWord_1949732).sum := by decide
  have hdescent : baseEnd_1949732 < baseStart_1949732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949743 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_1949743 : Nat := 118140960795 + 1949743 * 2 ^ 59
def prefixEnd_1949743 : Nat := 4983230072969 + 3 ^ 40 * 1949743 * 2
def baseEnd_1949743 : Nat := 444957916328564602331467

theorem tailTrace_1949743 : CollatzResearch.WordTrace tailWord_1949743 prefixEnd_1949743 444957916328564602331467 := by
  unfold tailWord_1949743
  simp only [CollatzResearch.WordTrace]
  refine ⟨71112969375421575438853883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47408646250281050292569255 71112969375421575438853883)
  ·
    refine ⟨106669454063132363158280825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71112969375421575438853883 106669454063132363158280825)
    ·
      refine ⟨80002090547349272368710619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106669454063132363158280825 80002090547349272368710619)
      ·
        refine ⟨120003135821023908553065929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80002090547349272368710619 120003135821023908553065929)
        ·
          refine ⟨90002351865767931414799447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120003135821023908553065929 90002351865767931414799447)
          ·
            refine ⟨135003527798651897122199171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90002351865767931414799447 135003527798651897122199171)
            ·
              refine ⟨202505291697977845683298757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135003527798651897122199171 202505291697977845683298757)
              ·
                refine ⟨37969742193370846065618517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202505291697977845683298757 37969742193370846065618517)
                ·
                  refine ⟨444957916328564602331467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37969742193370846065618517 444957916328564602331467)
                  ·
                    rfl

theorem cell21_1949743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_1949743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949743 prefixEnd_1949743 := by exact prefixLift 1949743
  have htrace : WordTrace (prefixWord ++ tailWord_1949743) baseStart_1949743 baseEnd_1949743 := by
    simpa [prefixWord, tailWord_1949743, baseEnd_1949743] using wordTrace_append hprefix tailTrace_1949743
  have hstable : (prefixWord ++ tailWord_1949743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949743).length < 2 ^ (prefixWord ++ tailWord_1949743).sum := by decide
  have hdescent : baseEnd_1949743 < baseStart_1949743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949774 : List Nat := [4, 1, 1, 1, 1, 13]
def baseStart_1949774 : Nat := 118140960795 + 1949774 * 2 ^ 59
def prefixEnd_1949774 : Nat := 4983230072969 + 3 ^ 40 * 1949774 * 2
def baseEnd_1949774 : Nat := 16480184850033905085731

theorem tailTrace_1949774 : CollatzResearch.WordTrace tailWord_1949774 prefixEnd_1949774 16480184850033905085731 := by
  unfold tailWord_1949774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889262504788658466654047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47409400025539511822154917 8889262504788658466654047)
  ·
    refine ⟨13333893757182987699981071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8889262504788658466654047 13333893757182987699981071)
    ·
      refine ⟨20000840635774481549971607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333893757182987699981071 20000840635774481549971607)
      ·
        refine ⟨30001260953661722324957411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000840635774481549971607 30001260953661722324957411)
        ·
          refine ⟨45001891430492583487436117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30001260953661722324957411 45001891430492583487436117)
          ·
            refine ⟨16480184850033905085731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45001891430492583487436117 16480184850033905085731)
            ·
              rfl

theorem cell21_1949774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 13].length) (baseStart_1949774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949774 prefixEnd_1949774 := by exact prefixLift 1949774
  have htrace : WordTrace (prefixWord ++ tailWord_1949774) baseStart_1949774 baseEnd_1949774 := by
    simpa [prefixWord, tailWord_1949774, baseEnd_1949774] using wordTrace_append hprefix tailTrace_1949774
  have hstable : (prefixWord ++ tailWord_1949774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949774).length < 2 ^ (prefixWord ++ tailWord_1949774).sum := by decide
  have hdescent : baseEnd_1949774 < baseStart_1949774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949873 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 3]
def baseStart_1949873 : Nat := 118140960795 + 1949873 * 2 ^ 59
def prefixEnd_1949873 : Nat := 4983230072969 + 3 ^ 40 * 1949873 * 2
def baseEnd_1949873 : Nat := 444987584099713265164535

theorem tailTrace_1949873 : CollatzResearch.WordTrace tailWord_1949873 prefixEnd_1949873 444987584099713265164535 := by
  unfold tailWord_1949873
  simp only [CollatzResearch.WordTrace]
  refine ⟨71117710864950607641086273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47411807243300405094057515 71117710864950607641086273)
  ·
    refine ⟨53338283148712955730814705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71117710864950607641086273 53338283148712955730814705)
    ·
      refine ⟨40003712361534716798111029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53338283148712955730814705 40003712361534716798111029)
      ·
        refine ⟨3750348033893879699822909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40003712361534716798111029 3750348033893879699822909)
        ·
          refine ⟨1406380512710204887433591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3750348033893879699822909 1406380512710204887433591)
          ·
            refine ⟨2109570769065307331150387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406380512710204887433591 2109570769065307331150387)
            ·
              refine ⟨3164356153597960996725581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109570769065307331150387 3164356153597960996725581)
              ·
                refine ⟨1186633557599235373772093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3164356153597960996725581 1186633557599235373772093)
                ·
                  refine ⟨444987584099713265164535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186633557599235373772093 444987584099713265164535)
                  ·
                    rfl

theorem cell21_1949873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_1949873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949873 prefixEnd_1949873 := by exact prefixLift 1949873
  have htrace : WordTrace (prefixWord ++ tailWord_1949873) baseStart_1949873 baseEnd_1949873 := by
    simpa [prefixWord, tailWord_1949873, baseEnd_1949873] using wordTrace_append hprefix tailTrace_1949873
  have hstable : (prefixWord ++ tailWord_1949873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949873).length < 2 ^ (prefixWord ++ tailWord_1949873).sum := by decide
  have hdescent : baseEnd_1949873 < baseStart_1949873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949884 : List Nat := [2, 2, 2, 3, 4, 1, 7]
def baseStart_1949884 : Nat := 118140960795 + 1949884 * 2 ^ 59
def prefixEnd_1949884 : Nat := 4983230072969 + 3 ^ 40 * 1949884 * 2
def baseEnd_1949884 : Nat := 49443343827731076720131

theorem tailTrace_1949884 : CollatzResearch.WordTrace tailWord_1949884 prefixEnd_1949884 49443343827731076720131 := by
  unfold tailWord_1949884
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559056033955378259868353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47412074711940504346491137 35559056033955378259868353)
  ·
    refine ⟨26669292025466533694901265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35559056033955378259868353 26669292025466533694901265)
    ·
      refine ⟨20001969019099900271175949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26669292025466533694901265 20001969019099900271175949)
      ·
        refine ⟨7500738382162462601690981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20001969019099900271175949 7500738382162462601690981)
        ·
          refine ⟨1406388446655461737817059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7500738382162462601690981 1406388446655461737817059)
          ·
            refine ⟨2109582669983192606725589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406388446655461737817059 2109582669983192606725589)
            ·
              refine ⟨49443343827731076720131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2109582669983192606725589 49443343827731076720131)
              ·
                rfl

theorem cell21_1949884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 7].length) (baseStart_1949884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949884 prefixEnd_1949884 := by exact prefixLift 1949884
  have htrace : WordTrace (prefixWord ++ tailWord_1949884) baseStart_1949884 baseEnd_1949884 := by
    simpa [prefixWord, tailWord_1949884, baseEnd_1949884] using wordTrace_append hprefix tailTrace_1949884
  have hstable : (prefixWord ++ tailWord_1949884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949884).length < 2 ^ (prefixWord ++ tailWord_1949884).sum := by decide
  have hdescent : baseEnd_1949884 < baseStart_1949884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1949890 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1949890 : Nat := 118140960795 + 1949890 * 2 ^ 59
def prefixEnd_1949890 : Nat := 4983230072969 + 3 ^ 40 * 1949890 * 2
def baseEnd_1949890 : Nat := 444991463731325013381167

theorem tailTrace_1949890 : CollatzResearch.WordTrace tailWord_1949890 prefixEnd_1949890 444991463731325013381167 := by
  unfold tailWord_1949890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779582726472254886113781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47412220603926013029636749 17779582726472254886113781)
  ·
    refine ⟨1666835880606773895573167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17779582726472254886113781 1666835880606773895573167)
    ·
      refine ⟨2500253820910160843359751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666835880606773895573167 2500253820910160843359751)
      ·
        refine ⟨3750380731365241265039627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500253820910160843359751 3750380731365241265039627)
        ·
          refine ⟨5625571097047861897559441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750380731365241265039627 5625571097047861897559441)
          ·
            refine ⟨4219178322785896423169581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625571097047861897559441 4219178322785896423169581)
            ·
              refine ⟨1582191871044711158688593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219178322785896423169581 1582191871044711158688593)
              ·
                refine ⟨1186643903283533369016445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582191871044711158688593 1186643903283533369016445)
                ·
                  refine ⟨444991463731325013381167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186643903283533369016445 444991463731325013381167)
                  ·
                    rfl

theorem cell21_1949890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1949890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1949890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1949890 prefixEnd_1949890 := by exact prefixLift 1949890
  have htrace : WordTrace (prefixWord ++ tailWord_1949890) baseStart_1949890 baseEnd_1949890 := by
    simpa [prefixWord, tailWord_1949890, baseEnd_1949890] using wordTrace_append hprefix tailTrace_1949890
  have hstable : (prefixWord ++ tailWord_1949890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1949890).length < 2 ^ (prefixWord ++ tailWord_1949890).sum := by decide
  have hdescent : baseEnd_1949890 < baseStart_1949890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1949890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950033 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_1950033 : Nat := 118140960795 + 1950033 * 2 ^ 59
def prefixEnd_1950033 : Nat := 4983230072969 + 3 ^ 40 * 1950033 * 2
def baseEnd_1950033 : Nat := 445024098279588542497541

theorem tailTrace_1950033 : CollatzResearch.WordTrace tailWord_1950033 prefixEnd_1950033 445024098279588542497541 := by
  unfold tailWord_1950033
  simp only [CollatzResearch.WordTrace]
  refine ⟨71123546544370954966910753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47415697696247303311273835 71123546544370954966910753)
  ·
    refine ⟨53342659908278216225183065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71123546544370954966910753 53342659908278216225183065)
    ·
      refine ⟨40006994931208662168887299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53342659908278216225183065 40006994931208662168887299)
      ·
        refine ⟨60010492396812993253330949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40006994931208662168887299 60010492396812993253330949)
        ·
          refine ⟨11251967324402436234999553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60010492396812993253330949 11251967324402436234999553)
          ·
            refine ⟨8438975493301827176249665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251967324402436234999553 8438975493301827176249665)
            ·
              refine ⟨6329231619976370382187249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438975493301827176249665 6329231619976370382187249)
              ·
                refine ⟨4746923714982277786640437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329231619976370382187249 4746923714982277786640437)
                ·
                  refine ⟨445024098279588542497541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4746923714982277786640437 445024098279588542497541)
                  ·
                    rfl

theorem cell21_1950033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_1950033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950033 prefixEnd_1950033 := by exact prefixLift 1950033
  have htrace : WordTrace (prefixWord ++ tailWord_1950033) baseStart_1950033 baseEnd_1950033 := by
    simpa [prefixWord, tailWord_1950033, baseEnd_1950033] using wordTrace_append hprefix tailTrace_1950033
  have hstable : (prefixWord ++ tailWord_1950033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950033).length < 2 ^ (prefixWord ++ tailWord_1950033).sum := by decide
  have hdescent : baseEnd_1950033 < baseStart_1950033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950036 : List Nat := [2, 4, 1, 1, 2, 4, 2, 5]
def baseStart_1950036 : Nat := 118140960795 + 1950036 * 2 ^ 59
def prefixEnd_1950036 : Nat := 4983230072969 + 3 ^ 40 * 1950036 * 2
def baseEnd_1950036 : Nat := 148341594306820401315845

theorem tailTrace_1950036 : CollatzResearch.WordTrace tailWord_1950036 prefixEnd_1950036 148341594306820401315845 := by
  unfold tailWord_1950036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35561827981680043239634981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47415770642240057652846641 35561827981680043239634981)
  ·
    refine ⟨6667842746565008107431559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35561827981680043239634981 6667842746565008107431559)
    ·
      refine ⟨10001764119847512161147339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6667842746565008107431559 10001764119847512161147339)
      ·
        refine ⟨15002646179771268241721009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10001764119847512161147339 15002646179771268241721009)
        ·
          refine ⟨11251984634828451181290757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15002646179771268241721009 11251984634828451181290757)
          ·
            refine ⟨2109747119030334596492017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11251984634828451181290757 2109747119030334596492017)
            ·
              refine ⟨1582310339272750947369013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109747119030334596492017 1582310339272750947369013)
              ·
                refine ⟨148341594306820401315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582310339272750947369013 148341594306820401315845)
                ·
                  rfl

theorem cell21_1950036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_1950036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950036 prefixEnd_1950036 := by exact prefixLift 1950036
  have htrace : WordTrace (prefixWord ++ tailWord_1950036) baseStart_1950036 baseEnd_1950036 := by
    simpa [prefixWord, tailWord_1950036, baseEnd_1950036] using wordTrace_append hprefix tailTrace_1950036
  have hstable : (prefixWord ++ tailWord_1950036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950036).length < 2 ^ (prefixWord ++ tailWord_1950036).sum := by decide
  have hdescent : baseEnd_1950036 < baseStart_1950036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950047 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_1950047 : Nat := 118140960795 + 1950047 * 2 ^ 59
def prefixEnd_1950047 : Nat := 4983230072969 + 3 ^ 40 * 1950047 * 2
def baseEnd_1950047 : Nat := 445027293270327629264179

theorem tailTrace_1950047 : CollatzResearch.WordTrace tailWord_1950047 prefixEnd_1950047 445027293270327629264179 := by
  unfold tailWord_1950047
  simp only [CollatzResearch.WordTrace]
  refine ⟨71124057166320235357920395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47416038110880156905280263 71124057166320235357920395)
  ·
    refine ⟨106686085749480353036880593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71124057166320235357920395 106686085749480353036880593)
    ·
      refine ⟨80014564312110264777660445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106686085749480353036880593 80014564312110264777660445)
      ·
        refine ⟨30005461617041349291622667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80014564312110264777660445 30005461617041349291622667)
        ·
          refine ⟨45008192425562023937434001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30005461617041349291622667 45008192425562023937434001)
          ·
            refine ⟨33756144319171517953075501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45008192425562023937434001 33756144319171517953075501)
            ·
              refine ⟨12658554119689319232403313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33756144319171517953075501 12658554119689319232403313)
              ·
                refine ⟨9493915589766989424302485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658554119689319232403313 9493915589766989424302485)
                ·
                  refine ⟨445027293270327629264179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9493915589766989424302485 445027293270327629264179)
                  ·
                    rfl

theorem cell21_1950047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_1950047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950047 prefixEnd_1950047 := by exact prefixLift 1950047
  have htrace : WordTrace (prefixWord ++ tailWord_1950047) baseStart_1950047 baseEnd_1950047 := by
    simpa [prefixWord, tailWord_1950047, baseEnd_1950047] using wordTrace_append hprefix tailTrace_1950047
  have hstable : (prefixWord ++ tailWord_1950047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950047).length < 2 ^ (prefixWord ++ tailWord_1950047).sum := by decide
  have hdescent : baseEnd_1950047 < baseStart_1950047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950081 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_1950081 : Nat := 118140960795 + 1950081 * 2 ^ 59
def prefixEnd_1950081 : Nat := 4983230072969 + 3 ^ 40 * 1950081 * 2
def baseEnd_1950081 : Nat := 445035052533551125697443

theorem tailTrace_1950081 : CollatzResearch.WordTrace tailWord_1950081 prefixEnd_1950081 445035052533551125697443 := by
  unfold tailWord_1950081
  simp only [CollatzResearch.WordTrace]
  refine ⟨71125297248197059164658097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47416864832131372776438731 71125297248197059164658097)
  ·
    refine ⟨53343972936147794373493573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71125297248197059164658097 53343972936147794373493573)
    ·
      refine ⟨10001994925527711445030045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53343972936147794373493573 10001994925527711445030045)
      ·
        refine ⟨3750748097072891791886267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10001994925527711445030045 3750748097072891791886267)
        ·
          refine ⟨5626122145609337687829401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750748097072891791886267 5626122145609337687829401)
          ·
            refine ⟨4219591609207003265872051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626122145609337687829401 4219591609207003265872051)
            ·
              refine ⟨6329387413810504898808077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219591609207003265872051 6329387413810504898808077)
              ·
                refine ⟨2373520280178939337053029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6329387413810504898808077 2373520280178939337053029)
                ·
                  refine ⟨445035052533551125697443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373520280178939337053029 445035052533551125697443)
                  ·
                    rfl

theorem cell21_1950081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_1950081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950081 prefixEnd_1950081 := by exact prefixLift 1950081
  have htrace : WordTrace (prefixWord ++ tailWord_1950081) baseStart_1950081 baseEnd_1950081 := by
    simpa [prefixWord, tailWord_1950081, baseEnd_1950081] using wordTrace_append hprefix tailTrace_1950081
  have hstable : (prefixWord ++ tailWord_1950081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950081).length < 2 ^ (prefixWord ++ tailWord_1950081).sum := by decide
  have hdescent : baseEnd_1950081 < baseStart_1950081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950168 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1950168 : Nat := 118140960795 + 1950168 * 2 ^ 59
def prefixEnd_1950168 : Nat := 4983230072969 + 3 ^ 40 * 1950168 * 2
def baseEnd_1950168 : Nat := 445054907118858307747265

theorem tailTrace_1950168 : CollatzResearch.WordTrace tailWord_1950168 prefixEnd_1950168 445054907118858307747265 := by
  unfold tailWord_1950168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564235199440936511537579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47418980265921248682050105 35564235199440936511537579)
  ·
    refine ⟨53346352799161404767306369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35564235199440936511537579 53346352799161404767306369)
    ·
      refine ⟨40009764599371053575479777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53346352799161404767306369 40009764599371053575479777)
      ·
        refine ⟨30007323449528290181609833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40009764599371053575479777 30007323449528290181609833)
        ·
          refine ⟨22505492587146217636207375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30007323449528290181609833 22505492587146217636207375)
          ·
            refine ⟨33758238880719326454311063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22505492587146217636207375 33758238880719326454311063)
            ·
              refine ⟨50637358321078989681466595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33758238880719326454311063 50637358321078989681466595)
              ·
                refine ⟨75956037481618484522199893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50637358321078989681466595 75956037481618484522199893)
                ·
                  refine ⟨445054907118858307747265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75956037481618484522199893 445054907118858307747265)
                  ·
                    rfl

theorem cell21_1950168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1950168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950168 prefixEnd_1950168 := by exact prefixLift 1950168
  have htrace : WordTrace (prefixWord ++ tailWord_1950168) baseStart_1950168 baseEnd_1950168 := by
    simpa [prefixWord, tailWord_1950168, baseEnd_1950168] using wordTrace_append hprefix tailTrace_1950168
  have hstable : (prefixWord ++ tailWord_1950168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950168).length < 2 ^ (prefixWord ++ tailWord_1950168).sum := by decide
  have hdescent : baseEnd_1950168 < baseStart_1950168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950219 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 3]
def baseStart_1950219 : Nat := 118140960795 + 1950219 * 2 ^ 59
def prefixEnd_1950219 : Nat := 4983230072969 + 3 ^ 40 * 1950219 * 2
def baseEnd_1950219 : Nat := 445066546013693552397161

theorem tailTrace_1950219 : CollatzResearch.WordTrace tailWord_1950219 prefixEnd_1950219 445066546013693552397161 := by
  unfold tailWord_1950219
  simp only [CollatzResearch.WordTrace]
  refine ⟨71130330521697108733181711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47420220347798072488787807 71130330521697108733181711)
  ·
    refine ⟨106695495782545663099772567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71130330521697108733181711 106695495782545663099772567)
    ·
      refine ⟨160043243673818494649658851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106695495782545663099772567 160043243673818494649658851)
      ·
        refine ⟨240064865510727741974488277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160043243673818494649658851 240064865510727741974488277)
        ·
          refine ⟨5626520285407681452527069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 240064865510727741974488277 5626520285407681452527069)
          ·
            refine ⟨2109945107027880544697651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5626520285407681452527069 2109945107027880544697651)
            ·
              refine ⟨3164917660541820817046477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109945107027880544697651 3164917660541820817046477)
              ·
                refine ⟨1186844122703182806392429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3164917660541820817046477 1186844122703182806392429)
                ·
                  refine ⟨445066546013693552397161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186844122703182806392429 445066546013693552397161)
                  ·
                    rfl

theorem cell21_1950219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].length) (baseStart_1950219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950219 prefixEnd_1950219 := by exact prefixLift 1950219
  have htrace : WordTrace (prefixWord ++ tailWord_1950219) baseStart_1950219 baseEnd_1950219 := by
    simpa [prefixWord, tailWord_1950219, baseEnd_1950219] using wordTrace_append hprefix tailTrace_1950219
  have hstable : (prefixWord ++ tailWord_1950219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950219).length < 2 ^ (prefixWord ++ tailWord_1950219).sum := by decide
  have hdescent : baseEnd_1950219 < baseStart_1950219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950250 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1950250 : Nat := 118140960795 + 1950250 * 2 ^ 59
def prefixEnd_1950250 : Nat := 4983230072969 + 3 ^ 40 * 1950250 * 2
def baseEnd_1950250 : Nat := 445073620636044387380431

theorem tailTrace_1950250 : CollatzResearch.WordTrace tailWord_1950250 prefixEnd_1950250 445073620636044387380431 := by
  unfold tailWord_1950250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782865296146200256890051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47420974123056534018373469 17782865296146200256890051)
  ·
    refine ⟨26674297944219300385335077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17782865296146200256890051 26674297944219300385335077)
    ·
      refine ⟨5001430864541118822250327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26674297944219300385335077 5001430864541118822250327)
      ·
        refine ⟨7502146296811678233375491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001430864541118822250327 7502146296811678233375491)
        ·
          refine ⟨11253219445217517350063237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502146296811678233375491 11253219445217517350063237)
          ·
            refine ⟨2109978645978284503136857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11253219445217517350063237 2109978645978284503136857)
            ·
              refine ⟨1582483984483713377352643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2109978645978284503136857 1582483984483713377352643)
              ·
                refine ⟨2373725976725570066028965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582483984483713377352643 2373725976725570066028965)
                ·
                  refine ⟨445073620636044387380431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373725976725570066028965 445073620636044387380431)
                  ·
                    rfl

theorem cell21_1950250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1950250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950250 prefixEnd_1950250 := by exact prefixLift 1950250
  have htrace : WordTrace (prefixWord ++ tailWord_1950250) baseStart_1950250 baseEnd_1950250 := by
    simpa [prefixWord, tailWord_1950250, baseEnd_1950250] using wordTrace_append hprefix tailTrace_1950250
  have hstable : (prefixWord ++ tailWord_1950250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950250).length < 2 ^ (prefixWord ++ tailWord_1950250).sum := by decide
  have hdescent : baseEnd_1950250 < baseStart_1950250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950289 : List Nat := [1, 2, 2, 1, 3, 12]
def baseStart_1950289 : Nat := 118140960795 + 1950289 * 2 ^ 59
def prefixEnd_1950289 : Nat := 4983230072969 + 3 ^ 40 * 1950289 * 2
def baseEnd_1950289 : Nat := 16484537813606999490013

theorem tailTrace_1950289 : CollatzResearch.WordTrace tailWord_1950289 prefixEnd_1950289 16484537813606999490013 := by
  unfold tailWord_1950289
  simp only [CollatzResearch.WordTrace]
  refine ⟨71132883631443510688229921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47421922420962340458819947 71132883631443510688229921)
  ·
    refine ⟨53349662723582633016172441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71132883631443510688229921 53349662723582633016172441)
    ·
      refine ⟨40012247042686974762129331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53349662723582633016172441 40012247042686974762129331)
      ·
        refine ⟨60018370564030462143193997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40012247042686974762129331 60018370564030462143193997)
        ·
          refine ⟨22506888961511423303697749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60018370564030462143193997 22506888961511423303697749)
          ·
            refine ⟨16484537813606999490013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22506888961511423303697749 16484537813606999490013)
            ·
              rfl

theorem cell21_1950289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 12].length) (baseStart_1950289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950289 prefixEnd_1950289 := by exact prefixLift 1950289
  have htrace : WordTrace (prefixWord ++ tailWord_1950289) baseStart_1950289 baseEnd_1950289 := by
    simpa [prefixWord, tailWord_1950289, baseEnd_1950289] using wordTrace_append hprefix tailTrace_1950289
  have hstable : (prefixWord ++ tailWord_1950289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950289).length < 2 ^ (prefixWord ++ tailWord_1950289).sum := by decide
  have hdescent : baseEnd_1950289 < baseStart_1950289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950292 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1950292 : Nat := 118140960795 + 1950292 * 2 ^ 59
def prefixEnd_1950292 : Nat := 4983230072969 + 3 ^ 40 * 1950292 * 2
def baseEnd_1950292 : Nat := 445083205608261647680345

theorem tailTrace_1950292 : CollatzResearch.WordTrace tailWord_1950292 prefixEnd_1950292 445083205608261647680345 := by
  unfold tailWord_1950292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566496525216321100294565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47421995366955094800392753 35566496525216321100294565)
  ·
    refine ⟨6668718098478060206305231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35566496525216321100294565 6668718098478060206305231)
    ·
      refine ⟨10003077147717090309457847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668718098478060206305231 10003077147717090309457847)
      ·
        refine ⟨15004615721575635464186771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10003077147717090309457847 15004615721575635464186771)
        ·
          refine ⟨22506923582363453196280157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004615721575635464186771 22506923582363453196280157)
          ·
            refine ⟨8440096343386294948605059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22506923582363453196280157 8440096343386294948605059)
            ·
              refine ⟨12660144515079442422907589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440096343386294948605059 12660144515079442422907589)
              ·
                refine ⟨2373777096577395454295173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12660144515079442422907589 2373777096577395454295173)
                ·
                  refine ⟨445083205608261647680345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373777096577395454295173 445083205608261647680345)
                  ·
                    rfl

theorem cell21_1950292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1950292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950292 prefixEnd_1950292 := by exact prefixLift 1950292
  have htrace : WordTrace (prefixWord ++ tailWord_1950292) baseStart_1950292 baseEnd_1950292 := by
    simpa [prefixWord, tailWord_1950292, baseEnd_1950292] using wordTrace_append hprefix tailTrace_1950292
  have hstable : (prefixWord ++ tailWord_1950292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950292).length < 2 ^ (prefixWord ++ tailWord_1950292).sum := by decide
  have hdescent : baseEnd_1950292 < baseStart_1950292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950354 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1950354 : Nat := 118140960795 + 1950354 * 2 ^ 59
def prefixEnd_1950354 : Nat := 4983230072969 + 3 ^ 40 * 1950354 * 2
def baseEnd_1950354 : Nat := 445097354852963317646885

theorem tailTrace_1950354 : CollatzResearch.WordTrace tailWord_1950354 prefixEnd_1950354 445097354852963317646885 := by
  unfold tailWord_1950354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783813594052006697336529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47423502917472017859564077 17783813594052006697336529)
  ·
    refine ⟨13337860195539005023002397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17783813594052006697336529 13337860195539005023002397)
    ·
      refine ⟨5001697573327126883625899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13337860195539005023002397 5001697573327126883625899)
      ·
        refine ⟨7502546359990690325438849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001697573327126883625899 7502546359990690325438849)
        ·
          refine ⟨5626909769993017744079137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7502546359990690325438849 5626909769993017744079137)
          ·
            refine ⟨4220182327494763308059353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626909769993017744079137 4220182327494763308059353)
            ·
              refine ⟨3165136745621072481044515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220182327494763308059353 3165136745621072481044515)
              ·
                refine ⟨4747705118431608721566773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165136745621072481044515 4747705118431608721566773)
                ·
                  refine ⟨445097354852963317646885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4747705118431608721566773 445097354852963317646885)
                  ·
                    rfl

theorem cell21_1950354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1950354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950354 prefixEnd_1950354 := by exact prefixLift 1950354
  have htrace : WordTrace (prefixWord ++ tailWord_1950354) baseStart_1950354 baseEnd_1950354 := by
    simpa [prefixWord, tailWord_1950354, baseEnd_1950354] using wordTrace_append hprefix tailTrace_1950354
  have hstable : (prefixWord ++ tailWord_1950354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950354).length < 2 ^ (prefixWord ++ tailWord_1950354).sum := by decide
  have hdescent : baseEnd_1950354 < baseStart_1950354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950441 : List Nat := [1, 2, 1, 1, 1, 2, 6, 7]
def baseStart_1950441 : Nat := 118140960795 + 1950441 * 2 ^ 59
def prefixEnd_1950441 : Nat := 4983230072969 + 3 ^ 40 * 1950441 * 2
def baseEnd_1950441 : Nat := 148372403146090166565569

theorem tailTrace_1950441 : CollatzResearch.WordTrace tailWord_1950441 prefixEnd_1950441 148372403146090166565569 := by
  unfold tailWord_1950441
  simp only [CollatzResearch.WordTrace]
  refine ⟨71138427526892840647763177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47425618351261893765175451 71138427526892840647763177)
  ·
    refine ⟨53353820645169630485822383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71138427526892840647763177 53353820645169630485822383)
    ·
      refine ⟨80030730967754445728733575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53353820645169630485822383 80030730967754445728733575)
      ·
        refine ⟨120046096451631668593100363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80030730967754445728733575 120046096451631668593100363)
        ·
          refine ⟨180069144677447502889650545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120046096451631668593100363 180069144677447502889650545)
          ·
            refine ⟨135051858508085627167237909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180069144677447502889650545 135051858508085627167237909)
            ·
              refine ⟨6330555867566513773464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135051858508085627167237909 6330555867566513773464277)
              ·
                refine ⟨148372403146090166565569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6330555867566513773464277 148372403146090166565569)
                ·
                  rfl

theorem cell21_1950441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_1950441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950441 prefixEnd_1950441 := by exact prefixLift 1950441
  have htrace : WordTrace (prefixWord ++ tailWord_1950441) baseStart_1950441 baseEnd_1950441 := by
    simpa [prefixWord, tailWord_1950441, baseEnd_1950441] using wordTrace_append hprefix tailTrace_1950441
  have hstable : (prefixWord ++ tailWord_1950441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950441).length < 2 ^ (prefixWord ++ tailWord_1950441).sum := by decide
  have hdescent : baseEnd_1950441 < baseStart_1950441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950551 : List Nat := [1, 1, 3, 2, 4, 3, 2, 5]
def baseStart_1950551 : Nat := 118140960795 + 1950551 * 2 ^ 59
def prefixEnd_1950551 : Nat := 4983230072969 + 3 ^ 40 * 1950551 * 2
def baseEnd_1950551 : Nat := 148380770978978250954383

theorem tailTrace_1950551 : CollatzResearch.WordTrace tailWord_1950551 prefixEnd_1950551 148380770978978250954383 := by
  unfold tailWord_1950551
  simp only [CollatzResearch.WordTrace]
  refine ⟨71142439556494329434267507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47428293037662886289511671 71142439556494329434267507)
  ·
    refine ⟨106713659334741494151401261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71142439556494329434267507 106713659334741494151401261)
    ·
      refine ⟨40017622250528060306775473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106713659334741494151401261 40017622250528060306775473)
      ·
        refine ⟨30013216687896045230081605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40017622250528060306775473 30013216687896045230081605)
        ·
          refine ⟨5627478128980508480640301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30013216687896045230081605 5627478128980508480640301)
          ·
            refine ⟨2110304298367690680240113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5627478128980508480640301 2110304298367690680240113)
            ·
              refine ⟨1582728223775768010180085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110304298367690680240113 1582728223775768010180085)
              ·
                refine ⟨148380770978978250954383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582728223775768010180085 148380770978978250954383)
                ·
                  rfl

theorem cell21_1950551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].length) (baseStart_1950551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950551 prefixEnd_1950551 := by exact prefixLift 1950551
  have htrace : WordTrace (prefixWord ++ tailWord_1950551) baseStart_1950551 baseEnd_1950551 := by
    simpa [prefixWord, tailWord_1950551, baseEnd_1950551] using wordTrace_append hprefix tailTrace_1950551
  have hstable : (prefixWord ++ tailWord_1950551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950551).length < 2 ^ (prefixWord ++ tailWord_1950551).sum := by decide
  have hdescent : baseEnd_1950551 < baseStart_1950551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950582 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1950582 : Nat := 118140960795 + 1950582 * 2 ^ 59
def prefixEnd_1950582 : Nat := 4983230072969 + 3 ^ 40 * 1950582 * 2
def baseEnd_1950582 : Nat := 445149387559285587846419

theorem tailTrace_1950582 : CollatzResearch.WordTrace tailWord_1950582 prefixEnd_1950582 445149387559285587846419 := by
  unfold tailWord_1950582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446473138711376358040375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47429046812921347819097333 4446473138711376358040375)
  ·
    refine ⟨6669709708067064537060563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446473138711376358040375 6669709708067064537060563)
    ·
      refine ⟨10004564562100596805590845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669709708067064537060563 10004564562100596805590845)
      ·
        refine ⟨3751711710787723802096567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10004564562100596805590845 3751711710787723802096567)
        ·
          refine ⟨5627567566181585703144851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751711710787723802096567 5627567566181585703144851)
          ·
            refine ⟨8441351349272378554717277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627567566181585703144851 8441351349272378554717277)
            ·
              refine ⟨3165506755977141958018979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8441351349272378554717277 3165506755977141958018979)
              ·
                refine ⟨4748260133965712937028469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165506755977141958018979 4748260133965712937028469)
                ·
                  refine ⟨445149387559285587846419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4748260133965712937028469 445149387559285587846419)
                  ·
                    rfl

theorem cell21_1950582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1950582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950582 prefixEnd_1950582 := by exact prefixLift 1950582
  have htrace : WordTrace (prefixWord ++ tailWord_1950582) baseStart_1950582 baseEnd_1950582 := by
    simpa [prefixWord, tailWord_1950582, baseEnd_1950582] using wordTrace_append hprefix tailTrace_1950582
  have hstable : (prefixWord ++ tailWord_1950582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950582).length < 2 ^ (prefixWord ++ tailWord_1950582).sum := by decide
  have hdescent : baseEnd_1950582 < baseStart_1950582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950644 : List Nat := [2, 5, 2, 1, 1, 3, 1, 6]
def baseStart_1950644 : Nat := 118140960795 + 1950644 * 2 ^ 59
def prefixEnd_1950644 : Nat := 4983230072969 + 3 ^ 40 * 1950644 * 2
def baseEnd_1950644 : Nat := 148387845601329085937653

theorem tailTrace_1950644 : CollatzResearch.WordTrace tailWord_1950644 prefixEnd_1950644 148387845601329085937653 := by
  unfold tailWord_1950644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35572915772578703158701493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47430554363438270878268657 35572915772578703158701493)
  ·
    refine ⟨3334960853679253421128265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35572915772578703158701493 3334960853679253421128265)
    ·
      refine ⟨2501220640259440065846199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334960853679253421128265 2501220640259440065846199)
      ·
        refine ⟨3751830960389160098769299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501220640259440065846199 3751830960389160098769299)
        ·
          refine ⟨5627746440583740148153949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751830960389160098769299 5627746440583740148153949)
          ·
            refine ⟨2110404915218902555557731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5627746440583740148153949 2110404915218902555557731)
            ·
              refine ⟨3165607372828353833336597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110404915218902555557731 3165607372828353833336597)
              ·
                refine ⟨148387845601329085937653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3165607372828353833336597 148387845601329085937653)
                ·
                  rfl

theorem cell21_1950644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_1950644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950644 prefixEnd_1950644 := by exact prefixLift 1950644
  have htrace : WordTrace (prefixWord ++ tailWord_1950644) baseStart_1950644 baseEnd_1950644 := by
    simpa [prefixWord, tailWord_1950644, baseEnd_1950644] using wordTrace_append hprefix tailTrace_1950644
  have hstable : (prefixWord ++ tailWord_1950644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950644).length < 2 ^ (prefixWord ++ tailWord_1950644).sum := by decide
  have hdescent : baseEnd_1950644 < baseStart_1950644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950706 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1950706 : Nat := 118140960795 + 1950706 * 2 ^ 59
def prefixEnd_1950706 : Nat := 4983230072969 + 3 ^ 40 * 1950706 * 2
def baseEnd_1950706 : Nat := 445177686048688927779499

theorem tailTrace_1950706 : CollatzResearch.WordTrace tailWord_1950706 prefixEnd_1950706 445177686048688927779499 := by
  unfold tailWord_1950706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787023217733197726539993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47432061913955193937439981 17787023217733197726539993)
  ·
    refine ⟨13340267413299898294904995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17787023217733197726539993 13340267413299898294904995)
    ·
      refine ⟨20010401119949847442357493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340267413299898294904995 20010401119949847442357493)
      ·
        refine ⟨1875975104995298197721015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20010401119949847442357493 1875975104995298197721015)
        ·
          refine ⟨2813962657492947296581523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875975104995298197721015 2813962657492947296581523)
          ·
            refine ⟨4220943986239420944872285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813962657492947296581523 4220943986239420944872285)
            ·
              refine ⟨1582853994839782854327107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4220943986239420944872285 1582853994839782854327107)
              ·
                refine ⟨2374280992259674281490661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582853994839782854327107 2374280992259674281490661)
                ·
                  refine ⟨445177686048688927779499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374280992259674281490661 445177686048688927779499)
                  ·
                    rfl

theorem cell21_1950706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1950706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950706 prefixEnd_1950706 := by exact prefixLift 1950706
  have htrace : WordTrace (prefixWord ++ tailWord_1950706) baseStart_1950706 baseEnd_1950706 := by
    simpa [prefixWord, tailWord_1950706, baseEnd_1950706] using wordTrace_append hprefix tailTrace_1950706
  have hstable : (prefixWord ++ tailWord_1950706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950706).length < 2 ^ (prefixWord ++ tailWord_1950706).sum := by decide
  have hdescent : baseEnd_1950706 < baseStart_1950706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950734 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_1950734 : Nat := 118140960795 + 1950734 * 2 ^ 59
def prefixEnd_1950734 : Nat := 4983230072969 + 3 ^ 40 * 1950734 * 2
def baseEnd_1950734 : Nat := 445184076030167101312775

theorem tailTrace_1950734 : CollatzResearch.WordTrace tailWord_1950734 prefixEnd_1950734 445184076030167101312775 := by
  unfold tailWord_1950734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893639264353918961022407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47432742743220901125452837 8893639264353918961022407)
  ·
    refine ⟨13340458896530878441533611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8893639264353918961022407 13340458896530878441533611)
    ·
      refine ⟨20010688344796317662300417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340458896530878441533611 20010688344796317662300417)
      ·
        refine ⟨15008016258597238246725313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20010688344796317662300417 15008016258597238246725313)
        ·
          refine ⟨11256012193947928685043985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15008016258597238246725313 11256012193947928685043985)
          ·
            refine ⟨8442009145460946513782989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11256012193947928685043985 8442009145460946513782989)
            ·
              refine ⟨3165753429547854942668621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8442009145460946513782989 3165753429547854942668621)
              ·
                refine ⟨1187157536080445603500733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3165753429547854942668621 1187157536080445603500733)
                ·
                  refine ⟨445184076030167101312775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187157536080445603500733 445184076030167101312775)
                  ·
                    rfl

theorem cell21_1950734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_1950734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950734 prefixEnd_1950734 := by exact prefixLift 1950734
  have htrace : WordTrace (prefixWord ++ tailWord_1950734) baseStart_1950734 baseEnd_1950734 := by
    simpa [prefixWord, tailWord_1950734, baseEnd_1950734] using wordTrace_append hprefix tailTrace_1950734
  have hstable : (prefixWord ++ tailWord_1950734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950734).length < 2 ^ (prefixWord ++ tailWord_1950734).sum := by decide
  have hdescent : baseEnd_1950734 < baseStart_1950734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950911 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_1950911 : Nat := 118140960795 + 1950911 * 2 ^ 59
def prefixEnd_1950911 : Nat := 4983230072969 + 3 ^ 40 * 1950911 * 2
def baseEnd_1950911 : Nat := 445224469841654126862413

theorem tailTrace_1950911 : CollatzResearch.WordTrace tailWord_1950911 prefixEnd_1950911 445224469841654126862413 := by
  unfold tailWord_1950911
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155569835190110917372587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47437046556793407278248391 71155569835190110917372587)
  ·
    refine ⟨106733354752785166376058881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155569835190110917372587 106733354752785166376058881)
    ·
      refine ⟨80050016064588874782044161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106733354752785166376058881 80050016064588874782044161)
      ·
        refine ⟨60037512048441656086533121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80050016064588874782044161 60037512048441656086533121)
        ·
          refine ⟨45028134036331242064899841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60037512048441656086533121 45028134036331242064899841)
          ·
            refine ⟨33771100527248431548674881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45028134036331242064899841 33771100527248431548674881)
            ·
              refine ⟨25328325395436323661506161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33771100527248431548674881 25328325395436323661506161)
              ·
                refine ⟨18996244046577242746129621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25328325395436323661506161 18996244046577242746129621)
                ·
                  refine ⟨445224469841654126862413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18996244046577242746129621 445224469841654126862413)
                  ·
                    rfl

theorem cell21_1950911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_1950911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950911 prefixEnd_1950911 := by exact prefixLift 1950911
  have htrace : WordTrace (prefixWord ++ tailWord_1950911) baseStart_1950911 baseEnd_1950911 := by
    simpa [prefixWord, tailWord_1950911, baseEnd_1950911] using wordTrace_append hprefix tailTrace_1950911
  have hstable : (prefixWord ++ tailWord_1950911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950911).length < 2 ^ (prefixWord ++ tailWord_1950911).sum := by decide
  have hdescent : baseEnd_1950911 < baseStart_1950911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950990 : List Nat := [4, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1950990 : Nat := 118140960795 + 1950990 * 2 ^ 59
def prefixEnd_1950990 : Nat := 4983230072969 + 3 ^ 40 * 1950990 * 2
def baseEnd_1950990 : Nat := 148414166239322515015195

theorem tailTrace_1950990 : CollatzResearch.WordTrace tailWord_1950990 prefixEnd_1950990 148414166239322515015195 := by
  unfold tailWord_1950990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894806400237988426187303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47438967467935938272998949 8894806400237988426187303)
  ·
    refine ⟨13342209600356982639280955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894806400237988426187303 13342209600356982639280955)
    ·
      refine ⟨20013314400535473958921433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342209600356982639280955 20013314400535473958921433)
      ·
        refine ⟨15009985800401605469191075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20013314400535473958921433 15009985800401605469191075)
        ·
          refine ⟨22514978700602408203786613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15009985800401605469191075 22514978700602408203786613)
          ·
            refine ⟨2110779253181475769104995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22514978700602408203786613 2110779253181475769104995)
            ·
              refine ⟨3166168879772213653657493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110779253181475769104995 3166168879772213653657493)
              ·
                refine ⟨148414166239322515015195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3166168879772213653657493 148414166239322515015195)
                ·
                  rfl

theorem cell21_1950990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1950990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1950990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1950990 prefixEnd_1950990 := by exact prefixLift 1950990
  have htrace : WordTrace (prefixWord ++ tailWord_1950990) baseStart_1950990 baseEnd_1950990 := by
    simpa [prefixWord, tailWord_1950990, baseEnd_1950990] using wordTrace_append hprefix tailTrace_1950990
  have hstable : (prefixWord ++ tailWord_1950990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950990).length < 2 ^ (prefixWord ++ tailWord_1950990).sum := by decide
  have hdescent : baseEnd_1950990 < baseStart_1950990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951052 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1951052 : Nat := 118140960795 + 1951052 * 2 ^ 59
def prefixEnd_1951052 : Nat := 4983230072969 + 3 ^ 40 * 1951052 * 2
def baseEnd_1951052 : Nat := 445256647962669215012125

theorem tailTrace_1951052 : CollatzResearch.WordTrace tailWord_1951052 prefixEnd_1951052 445256647962669215012125 := by
  unfold tailWord_1951052
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580356263839645999127705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47440475018452861332170273 35580356263839645999127705)
  ·
    refine ⟨26685267197879734499345779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35580356263839645999127705 26685267197879734499345779)
    ·
      refine ⟨40027900796819601749018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26685267197879734499345779 40027900796819601749018669)
      ·
        refine ⟨15010462798807350655882001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40027900796819601749018669 15010462798807350655882001)
        ·
          refine ⟨11257847099105512991911501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15010462798807350655882001 11257847099105512991911501)
          ·
            refine ⟨4221692662164567371966813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11257847099105512991911501 4221692662164567371966813)
            ·
              refine ⟨1583134748311712764487555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4221692662164567371966813 1583134748311712764487555)
              ·
                refine ⟨2374702122467569146731333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583134748311712764487555 2374702122467569146731333)
                ·
                  refine ⟨445256647962669215012125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374702122467569146731333 445256647962669215012125)
                  ·
                    rfl

theorem cell21_1951052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1951052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951052 prefixEnd_1951052 := by exact prefixLift 1951052
  have htrace : WordTrace (prefixWord ++ tailWord_1951052) baseStart_1951052 baseEnd_1951052 := by
    simpa [prefixWord, tailWord_1951052, baseEnd_1951052] using wordTrace_append hprefix tailTrace_1951052
  have hstable : (prefixWord ++ tailWord_1951052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951052).length < 2 ^ (prefixWord ++ tailWord_1951052).sum := by decide
  have hdescent : baseEnd_1951052 < baseStart_1951052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951111 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_1951111 : Nat := 118140960795 + 1951111 * 2 ^ 59
def prefixEnd_1951111 : Nat := 4983230072969 + 3 ^ 40 * 1951111 * 2
def baseEnd_1951111 : Nat := 445270112566498223528671

theorem tailTrace_1951111 : CollatzResearch.WordTrace tailWord_1951111 prefixEnd_1951111 445270112566498223528671 := by
  unfold tailWord_1951111
  simp only [CollatzResearch.WordTrace]
  refine ⟨71162864434465545074653187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47441909622977030049768791 71162864434465545074653187)
  ·
    refine ⟨106744296651698317611979781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71162864434465545074653187 106744296651698317611979781)
    ·
      refine ⟨20014555622193434552246209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106744296651698317611979781 20014555622193434552246209)
      ·
        refine ⟨15010916716645075914184657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20014555622193434552246209 15010916716645075914184657)
        ·
          refine ⟨11258187537483806935638493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15010916716645075914184657 11258187537483806935638493)
          ·
            refine ⟨4221820326556427600864435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11258187537483806935638493 4221820326556427600864435)
            ·
              refine ⟨6332730489834641401296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221820326556427600864435 6332730489834641401296653)
              ·
                refine ⟨2374773933687990525486245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6332730489834641401296653 2374773933687990525486245)
                ·
                  refine ⟨445270112566498223528671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374773933687990525486245 445270112566498223528671)
                  ·
                    rfl

theorem cell21_1951111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_1951111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951111 prefixEnd_1951111 := by exact prefixLift 1951111
  have htrace : WordTrace (prefixWord ++ tailWord_1951111) baseStart_1951111 baseEnd_1951111 := by
    simpa [prefixWord, tailWord_1951111, baseEnd_1951111] using wordTrace_append hprefix tailTrace_1951111
  have hstable : (prefixWord ++ tailWord_1951111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951111).length < 2 ^ (prefixWord ++ tailWord_1951111).sum := by decide
  have hdescent : baseEnd_1951111 < baseStart_1951111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951190 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1951190 : Nat := 118140960795 + 1951190 * 2 ^ 59
def prefixEnd_1951190 : Nat := 4983230072969 + 3 ^ 40 * 1951190 * 2
def baseEnd_1951190 : Nat := 445288141442811641711843

theorem tailTrace_1951190 : CollatzResearch.WordTrace tailWord_1951190 prefixEnd_1951190 445288141442811641711843 := by
  unfold tailWord_1951190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447859112573708847923689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47443830534119561044519349 4447859112573708847923689)
  ·
    refine ⟨3335894334430281635942767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4447859112573708847923689 3335894334430281635942767)
    ·
      refine ⟨5003841501645422453914151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335894334430281635942767 5003841501645422453914151)
      ·
        refine ⟨7505762252468133680871227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003841501645422453914151 7505762252468133680871227)
        ·
          refine ⟨11258643378702200521306841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505762252468133680871227 11258643378702200521306841)
          ·
            refine ⟨8443982534026650390980131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11258643378702200521306841 8443982534026650390980131)
            ·
              refine ⟨12665973801039975586470197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443982534026650390980131 12665973801039975586470197)
              ·
                refine ⟨1187435043847497711231581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12665973801039975586470197 1187435043847497711231581)
                ·
                  refine ⟨445288141442811641711843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187435043847497711231581 445288141442811641711843)
                  ·
                    rfl

theorem cell21_1951190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1951190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951190 prefixEnd_1951190 := by exact prefixLift 1951190
  have htrace : WordTrace (prefixWord ++ tailWord_1951190) baseStart_1951190 baseEnd_1951190 := by
    simpa [prefixWord, tailWord_1951190, baseEnd_1951190] using wordTrace_append hprefix tailTrace_1951190
  have hstable : (prefixWord ++ tailWord_1951190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951190).length < 2 ^ (prefixWord ++ tailWord_1951190).sum := by decide
  have hdescent : baseEnd_1951190 < baseStart_1951190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951215 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_1951215 : Nat := 118140960795 + 1951215 * 2 ^ 59
def prefixEnd_1951215 : Nat := 4983230072969 + 3 ^ 40 * 1951215 * 2
def baseEnd_1951215 : Nat := 445293846783417153795125

theorem tailTrace_1951215 : CollatzResearch.WordTrace tailWord_1951215 prefixEnd_1951215 445293846783417153795125 := by
  unfold tailWord_1951215
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166657626088770836439099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47444438417392513890959399 71166657626088770836439099)
  ·
    refine ⟨106749986439133156254658649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71166657626088770836439099 106749986439133156254658649)
    ·
      refine ⟨80062489829349867190993987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106749986439133156254658649 80062489829349867190993987)
      ·
        refine ⟨120093734744024800786490981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80062489829349867190993987 120093734744024800786490981)
        ·
          refine ⟨22517575264504650147467059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120093734744024800786490981 22517575264504650147467059)
          ·
            refine ⟨33776362896756975221200589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517575264504650147467059 33776362896756975221200589)
            ·
              refine ⟨12666136086283865707950221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33776362896756975221200589 12666136086283865707950221)
              ·
                refine ⟨4749801032356449640481333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12666136086283865707950221 4749801032356449640481333)
                ·
                  refine ⟨445293846783417153795125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749801032356449640481333 445293846783417153795125)
                  ·
                    rfl

theorem cell21_1951215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_1951215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951215 prefixEnd_1951215 := by exact prefixLift 1951215
  have htrace : WordTrace (prefixWord ++ tailWord_1951215) baseStart_1951215 baseEnd_1951215 := by
    simpa [prefixWord, tailWord_1951215, baseEnd_1951215] using wordTrace_append hprefix tailTrace_1951215
  have hstable : (prefixWord ++ tailWord_1951215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951215).length < 2 ^ (prefixWord ++ tailWord_1951215).sum := by decide
  have hdescent : baseEnd_1951215 < baseStart_1951215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951221 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1951221 : Nat := 118140960795 + 1951221 * 2 ^ 59
def prefixEnd_1951221 : Nat := 4983230072969 + 3 ^ 40 * 1951221 * 2
def baseEnd_1951221 : Nat := 445295216065162476695113

theorem tailTrace_1951221 : CollatzResearch.WordTrace tailWord_1951221 prefixEnd_1951221 445295216065162476695113 := by
  unfold tailWord_1951221
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166876464067033861157517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47444584309378022574105011 71166876464067033861157517)
  ·
    refine ⟨26687578674025137697934069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71166876464067033861157517 26687578674025137697934069)
    ·
      refine ⟨2501960500689856659181319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26687578674025137697934069 2501960500689856659181319)
      ·
        refine ⟨3752940751034784988771979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501960500689856659181319 3752940751034784988771979)
        ·
          refine ⟨5629411126552177483157969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752940751034784988771979 5629411126552177483157969)
          ·
            refine ⟨4222058344914133112368477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5629411126552177483157969 4222058344914133112368477)
            ·
              refine ⟨1583271879342799917138179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4222058344914133112368477 1583271879342799917138179)
              ·
                refine ⟨2374907819014199875707269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583271879342799917138179 2374907819014199875707269)
                ·
                  refine ⟨445295216065162476695113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374907819014199875707269 445295216065162476695113)
                  ·
                    rfl

theorem cell21_1951221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1951221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951221 prefixEnd_1951221 := by exact prefixLift 1951221
  have htrace : WordTrace (prefixWord ++ tailWord_1951221) baseStart_1951221 baseEnd_1951221 := by
    simpa [prefixWord, tailWord_1951221, baseEnd_1951221] using wordTrace_append hprefix tailTrace_1951221
  have hstable : (prefixWord ++ tailWord_1951221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951221).length < 2 ^ (prefixWord ++ tailWord_1951221).sum := by decide
  have hdescent : baseEnd_1951221 < baseStart_1951221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951305 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_1951305 : Nat := 118140960795 + 1951305 * 2 ^ 59
def prefixEnd_1951305 : Nat := 4983230072969 + 3 ^ 40 * 1951305 * 2
def baseEnd_1951305 : Nat := 445314386009596997294941

theorem tailTrace_1951305 : CollatzResearch.WordTrace tailWord_1951305 prefixEnd_1951305 445314386009596997294941 := by
  unfold tailWord_1951305
  simp only [CollatzResearch.WordTrace]
  refine ⟨71169940195762716207215369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47446626797175144138143579 71169940195762716207215369)
  ·
    refine ⟨53377455146822037155411527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71169940195762716207215369 53377455146822037155411527)
    ·
      refine ⟨80066182720233055733117291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53377455146822037155411527 80066182720233055733117291)
      ·
        refine ⟨120099274080349583599675937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80066182720233055733117291 120099274080349583599675937)
        ·
          refine ⟨90074455560262187699756953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120099274080349583599675937 90074455560262187699756953)
          ·
            refine ⟨67555841670196640774817715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90074455560262187699756953 67555841670196640774817715)
            ·
              refine ⟨101333762505294961162226573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67555841670196640774817715 101333762505294961162226573)
              ·
                refine ⟨38000160939485610435834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101333762505294961162226573 38000160939485610435834965)
                ·
                  refine ⟨445314386009596997294941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38000160939485610435834965 445314386009596997294941)
                  ·
                    rfl

theorem cell21_1951305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_1951305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951305 prefixEnd_1951305 := by exact prefixLift 1951305
  have htrace : WordTrace (prefixWord ++ tailWord_1951305) baseStart_1951305 baseEnd_1951305 := by
    simpa [prefixWord, tailWord_1951305, baseEnd_1951305] using wordTrace_append hprefix tailTrace_1951305
  have hstable : (prefixWord ++ tailWord_1951305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951305).length < 2 ^ (prefixWord ++ tailWord_1951305).sum := by decide
  have hdescent : baseEnd_1951305 < baseStart_1951305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
