import V185TrunkScan22Chunk095

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_860729 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_860729 : Nat := 118140960795 + 860729 * 2 ^ 59
def prefixEnd_860729 : Nat := 4983230072969 + 3 ^ 40 * 860729 * 2
def baseEnd_860729 : Nat := 294645126842578751686057

theorem tailTrace_860729 : CollatzResearch.WordTrace tailWord_860729 prefixEnd_860729 294645126842578751686057 := by
  unfold tailWord_860729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393365698733308654977241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20928910465822205769984827 31393365698733308654977241)
  ·
    refine ⟨23545024274049981491232931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31393365698733308654977241 23545024274049981491232931)
    ·
      refine ⟨35317536411074972236849397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23545024274049981491232931 35317536411074972236849397)
      ·
        refine ⟨3311019038538278647204631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35317536411074972236849397 3311019038538278647204631)
        ·
          refine ⟨4966528557807417970806947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311019038538278647204631 4966528557807417970806947)
          ·
            refine ⟨7449792836711126956210421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966528557807417970806947 7449792836711126956210421)
            ·
              refine ⟨698418078441668152144727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7449792836711126956210421 698418078441668152144727)
              ·
                refine ⟨1047627117662502228217091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698418078441668152144727 1047627117662502228217091)
                ·
                  refine ⟨1571440676493753342325637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047627117662502228217091 1571440676493753342325637)
                  ·
                    refine ⟨294645126842578751686057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571440676493753342325637 294645126842578751686057)
                    ·
                      rfl

theorem cell22_860729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_860729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860729 prefixEnd_860729 := by exact prefixLift 860729
  have htrace : WordTrace (prefixWord ++ tailWord_860729) baseStart_860729 baseEnd_860729 := by
    simpa [prefixWord, tailWord_860729, baseEnd_860729] using wordTrace_append hprefix tailTrace_860729
  have hstable : (prefixWord ++ tailWord_860729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860729).length < 2 ^ (prefixWord ++ tailWord_860729).sum := by decide
  have hdescent : baseEnd_860729 < baseStart_860729 := by decide
  rcases family_descends (prefixWord ++ tailWord_860729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860772 : List Nat := [2, 3, 1, 1, 2, 2, 5, 6]
def baseStart_860772 : Nat := 118140960795 + 860772 * 2 ^ 59
def prefixEnd_860772 : Nat := 4983230072969 + 3 ^ 40 * 860772 * 2
def baseEnd_860772 : Nat := 32739982957926774762325

theorem tailTrace_860772 : CollatzResearch.WordTrace tailWord_860772 prefixEnd_860772 32739982957926774762325 := by
  unfold tailWord_860772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697467018788763499396285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20929956025051684665861713 15697467018788763499396285)
  ·
    refine ⟨5886550132045786312273607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15697467018788763499396285 5886550132045786312273607)
    ·
      refine ⟨8829825198068679468410411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886550132045786312273607 8829825198068679468410411)
      ·
        refine ⟨13244737797103019202615617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8829825198068679468410411 13244737797103019202615617)
        ·
          refine ⟨9933553347827264401961713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13244737797103019202615617 9933553347827264401961713)
          ·
            refine ⟨7450165010870448301471285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9933553347827264401961713 7450165010870448301471285)
            ·
              refine ⟨698452969769104528262933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7450165010870448301471285 698452969769104528262933)
              ·
                refine ⟨32739982957926774762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698452969769104528262933 32739982957926774762325)
                ·
                  rfl

theorem cell22_860772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_860772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860772 prefixEnd_860772 := by exact prefixLift 860772
  have htrace : WordTrace (prefixWord ++ tailWord_860772) baseStart_860772 baseEnd_860772 := by
    simpa [prefixWord, tailWord_860772, baseEnd_860772] using wordTrace_append hprefix tailTrace_860772
  have hstable : (prefixWord ++ tailWord_860772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860772).length < 2 ^ (prefixWord ++ tailWord_860772).sum := by decide
  have hdescent : baseEnd_860772 < baseStart_860772 := by decide
  rcases family_descends (prefixWord ++ tailWord_860772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860804 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_860804 : Nat := 118140960795 + 860804 * 2 ^ 59
def prefixEnd_860804 : Nat := 4983230072969 + 3 ^ 40 * 860804 * 2
def baseEnd_860804 : Nat := 294670800875303556060827

theorem tailTrace_860804 : CollatzResearch.WordTrace tailWord_860804 prefixEnd_860804 294670800875303556060827 := by
  unfold tailWord_860804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698050586730798231978733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20930734115641064309304977 15698050586730798231978733)
  ·
    refine ⟨5886768970024049336992025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15698050586730798231978733 5886768970024049336992025)
    ·
      refine ⟨4415076727518037002744019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886768970024049336992025 4415076727518037002744019)
      ·
        refine ⟨6622615091277055504116029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415076727518037002744019 6622615091277055504116029)
        ·
          refine ⟨2483480659228895814043511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6622615091277055504116029 2483480659228895814043511)
          ·
            refine ⟨3725220988843343721065267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483480659228895814043511 3725220988843343721065267)
            ·
              refine ⟨5587831483265015581597901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725220988843343721065267 5587831483265015581597901)
              ·
                refine ⟨2095436806224380843099213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587831483265015581597901 2095436806224380843099213)
                ·
                  refine ⟨785788802334142816162205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2095436806224380843099213 785788802334142816162205)
                  ·
                    refine ⟨294670800875303556060827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785788802334142816162205 294670800875303556060827)
                    ·
                      rfl

theorem cell22_860804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_860804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860804 prefixEnd_860804 := by exact prefixLift 860804
  have htrace : WordTrace (prefixWord ++ tailWord_860804) baseStart_860804 baseEnd_860804 := by
    simpa [prefixWord, tailWord_860804, baseEnd_860804] using wordTrace_append hprefix tailTrace_860804
  have hstable : (prefixWord ++ tailWord_860804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860804).length < 2 ^ (prefixWord ++ tailWord_860804).sum := by decide
  have hdescent : baseEnd_860804 < baseStart_860804 := by decide
  rcases family_descends (prefixWord ++ tailWord_860804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860909 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_860909 : Nat := 118140960795 + 860909 * 2 ^ 59
def prefixEnd_860909 : Nat := 4983230072969 + 3 ^ 40 * 860909 * 2
def baseEnd_860909 : Nat := 294706744521118282185505

theorem tailTrace_860909 : CollatzResearch.WordTrace tailWord_860909 prefixEnd_860909 294706744521118282185505 := by
  unfold tailWord_860909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31399930838081199396529781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20933287225387466264353187 31399930838081199396529781)
  ·
    refine ⟨2943743516070112443424667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31399930838081199396529781 2943743516070112443424667)
    ·
      refine ⟨4415615274105168665137001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943743516070112443424667 4415615274105168665137001)
      ·
        refine ⟨3311711455578876498852751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4415615274105168665137001 3311711455578876498852751)
        ·
          refine ⟨4967567183368314748279127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311711455578876498852751 4967567183368314748279127)
          ·
            refine ⟨7451350775052472122418691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967567183368314748279127 7451350775052472122418691)
            ·
              refine ⟨11177026162578708183628037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451350775052472122418691 11177026162578708183628037)
              ·
                refine ⟨2095692405483507784430257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11177026162578708183628037 2095692405483507784430257)
                ·
                  refine ⟨1571769304112630838322693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095692405483507784430257 1571769304112630838322693)
                  ·
                    refine ⟨294706744521118282185505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571769304112630838322693 294706744521118282185505)
                    ·
                      rfl

theorem cell22_860909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_860909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860909 prefixEnd_860909 := by exact prefixLift 860909
  have htrace : WordTrace (prefixWord ++ tailWord_860909) baseStart_860909 baseEnd_860909 := by
    simpa [prefixWord, tailWord_860909, baseEnd_860909] using wordTrace_append hprefix tailTrace_860909
  have hstable : (prefixWord ++ tailWord_860909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860909).length < 2 ^ (prefixWord ++ tailWord_860909).sum := by decide
  have hdescent : baseEnd_860909 < baseStart_860909 := by decide
  rcases family_descends (prefixWord ++ tailWord_860909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860911 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 2, 3]
def baseStart_860911 : Nat := 118140960795 + 860911 * 2 ^ 59
def prefixEnd_860911 : Nat := 4983230072969 + 3 ^ 40 * 860911 * 2
def baseEnd_860911 : Nat := 294707429161990943635499

theorem tailTrace_860911 : CollatzResearch.WordTrace tailWord_860911 prefixEnd_860911 294707429161990943635499 := by
  unfold tailWord_860911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31400003784073953738102587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20933335856049302492068391 31400003784073953738102587)
  ·
    refine ⟨47100005676110930607153881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31400003784073953738102587 47100005676110930607153881)
    ·
      refine ⟨35325004257083197955365411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47100005676110930607153881 35325004257083197955365411)
      ·
        refine ⟨52987506385624796933048117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325004257083197955365411 52987506385624796933048117)
        ·
          refine ⟨4967578723652324712473261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52987506385624796933048117 4967578723652324712473261)
          ·
            refine ⟨1862842021369621767177473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4967578723652324712473261 1862842021369621767177473)
            ·
              refine ⟨1397131516027216325383105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862842021369621767177473 1397131516027216325383105)
              ·
                refine ⟨1047848637020412244037329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397131516027216325383105 1047848637020412244037329)
                ·
                  refine ⟨785886477765309183027997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047848637020412244037329 785886477765309183027997)
                  ·
                    refine ⟨294707429161990943635499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785886477765309183027997 294707429161990943635499)
                    ·
                      rfl

theorem cell22_860911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_860911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860911 prefixEnd_860911 := by exact prefixLift 860911
  have htrace : WordTrace (prefixWord ++ tailWord_860911) baseStart_860911 baseEnd_860911 := by
    simpa [prefixWord, tailWord_860911, baseEnd_860911] using wordTrace_append hprefix tailTrace_860911
  have hstable : (prefixWord ++ tailWord_860911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860911).length < 2 ^ (prefixWord ++ tailWord_860911).sum := by decide
  have hdescent : baseEnd_860911 < baseStart_860911 := by decide
  rcases family_descends (prefixWord ++ tailWord_860911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860924 : List Nat := [2, 2, 2, 1, 3, 4, 1, 7]
def baseStart_860924 : Nat := 118140960795 + 860924 * 2 ^ 59
def prefixEnd_860924 : Nat := 4983230072969 + 3 ^ 40 * 860924 * 2
def baseEnd_860924 : Nat := 32745764369740360340051

theorem tailTrace_860924 : CollatzResearch.WordTrace tailWord_860924 prefixEnd_860924 32745764369740360340051 := by
  unfold tailWord_860924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700238966513428479162913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20933651955351237972217217 15700238966513428479162913)
  ·
    refine ⟨11775179224885071359372185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15700238966513428479162913 11775179224885071359372185)
    ·
      refine ⟨8831384418663803519529139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11775179224885071359372185 8831384418663803519529139)
      ·
        refine ⟨13247076627995705279293709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8831384418663803519529139 13247076627995705279293709)
        ·
          refine ⟨4967653735498389479735141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13247076627995705279293709 4967653735498389479735141)
          ·
            refine ⟨931435075405948027450339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4967653735498389479735141 931435075405948027450339)
            ·
              refine ⟨1397152613108922041175509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931435075405948027450339 1397152613108922041175509)
              ·
                refine ⟨32745764369740360340051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1397152613108922041175509 32745764369740360340051)
                ·
                  rfl

theorem cell22_860924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_860924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860924 prefixEnd_860924 := by exact prefixLift 860924
  have htrace : WordTrace (prefixWord ++ tailWord_860924) baseStart_860924 baseEnd_860924 := by
    simpa [prefixWord, tailWord_860924, baseEnd_860924] using wordTrace_append hprefix tailTrace_860924
  have hstable : (prefixWord ++ tailWord_860924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860924).length < 2 ^ (prefixWord ++ tailWord_860924).sum := by decide
  have hdescent : baseEnd_860924 < baseStart_860924 := by decide
  rcases family_descends (prefixWord ++ tailWord_860924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860952 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_860952 : Nat := 118140960795 + 860952 * 2 ^ 59
def prefixEnd_860952 : Nat := 4983230072969 + 3 ^ 40 * 860952 * 2
def baseEnd_860952 : Nat := 98240488099960167786791

theorem tailTrace_860952 : CollatzResearch.WordTrace tailWord_860952 prefixEnd_860952 98240488099960167786791 := by
  unfold tailWord_860952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700749588462708870172555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20934332784616945160230073 15700749588462708870172555)
  ·
    refine ⟨23551124382694063305258833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700749588462708870172555 23551124382694063305258833)
    ·
      refine ⟨17663343287020547478944125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23551124382694063305258833 17663343287020547478944125)
      ·
        refine ⟨6623753732632705304604047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17663343287020547478944125 6623753732632705304604047)
        ·
          refine ⟨9935630598949057956906071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6623753732632705304604047 9935630598949057956906071)
          ·
            refine ⟨14903445898423586935359107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935630598949057956906071 14903445898423586935359107)
            ·
              refine ⟨22355168847635380403038661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14903445898423586935359107 22355168847635380403038661)
              ·
                refine ⟨4191594158931633825569749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22355168847635380403038661 4191594158931633825569749)
                ·
                  refine ⟨98240488099960167786791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4191594158931633825569749 98240488099960167786791)
                  ·
                    rfl

theorem cell22_860952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_860952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860952 prefixEnd_860952 := by exact prefixLift 860952
  have htrace : WordTrace (prefixWord ++ tailWord_860952) baseStart_860952 baseEnd_860952 := by
    simpa [prefixWord, tailWord_860952, baseEnd_860952] using wordTrace_append hprefix tailTrace_860952
  have hstable : (prefixWord ++ tailWord_860952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860952).length < 2 ^ (prefixWord ++ tailWord_860952).sum := by decide
  have hdescent : baseEnd_860952 < baseStart_860952 := by decide
  rcases family_descends (prefixWord ++ tailWord_860952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860997 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 8]
def baseStart_860997 : Nat := 118140960795 + 860997 * 2 ^ 59
def prefixEnd_860997 : Nat := 4983230072969 + 3 ^ 40 * 860997 * 2
def baseEnd_860997 : Nat := 98245622906505128661745

theorem tailTrace_860997 : CollatzResearch.WordTrace tailWord_860997 prefixEnd_860997 98245622906505128661745 := by
  unfold tailWord_860997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31403140461762390425733245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20935426974508260283822163 31403140461762390425733245)
  ·
    refine ⟨11776177673160896409649967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31403140461762390425733245 11776177673160896409649967)
    ·
      refine ⟨17664266509741344614474951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11776177673160896409649967 17664266509741344614474951)
      ·
        refine ⟨26496399764612016921712427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17664266509741344614474951 26496399764612016921712427)
        ·
          refine ⟨39744599646918025382568641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26496399764612016921712427 39744599646918025382568641)
          ·
            refine ⟨29808449735188519036926481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39744599646918025382568641 29808449735188519036926481)
            ·
              refine ⟨22356337301391389277694861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29808449735188519036926481 22356337301391389277694861)
              ·
                refine ⟨8383626488021770979135573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22356337301391389277694861 8383626488021770979135573)
                ·
                  refine ⟨98245622906505128661745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8383626488021770979135573 98245622906505128661745)
                  ·
                    rfl

theorem cell22_860997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_860997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860997 prefixEnd_860997 := by exact prefixLift 860997
  have htrace : WordTrace (prefixWord ++ tailWord_860997) baseStart_860997 baseEnd_860997 := by
    simpa [prefixWord, tailWord_860997, baseEnd_860997] using wordTrace_append hprefix tailTrace_860997
  have hstable : (prefixWord ++ tailWord_860997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860997).length < 2 ^ (prefixWord ++ tailWord_860997).sum := by decide
  have hdescent : baseEnd_860997 < baseStart_860997 := by decide
  rcases family_descends (prefixWord ++ tailWord_860997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861031 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 6]
def baseStart_861031 : Nat := 118140960795 + 861031 * 2 ^ 59
def prefixEnd_861031 : Nat := 4983230072969 + 3 ^ 40 * 861031 * 2
def baseEnd_861031 : Nat := 98249502538116876878377

theorem tailTrace_861031 : CollatzResearch.WordTrace tailWord_861031 prefixEnd_861031 98249502538116876878377 := by
  unfold tailWord_861031
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404380543639214232470947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936253695759476154980631 31404380543639214232470947)
  ·
    refine ⟨47106570815458821348706421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31404380543639214232470947 47106570815458821348706421)
    ·
      refine ⟨4416241013949264501441227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47106570815458821348706421 4416241013949264501441227)
      ·
        refine ⟨6624361520923896752161841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416241013949264501441227 6624361520923896752161841)
        ·
          refine ⟨4968271140692922564121381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6624361520923896752161841 4968271140692922564121381)
          ·
            refine ⟨931550838879922980772759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4968271140692922564121381 931550838879922980772759)
            ·
              refine ⟨1397326258319884471159139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931550838879922980772759 1397326258319884471159139)
              ·
                refine ⟨2095989387479826706738709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397326258319884471159139 2095989387479826706738709)
                ·
                  refine ⟨98249502538116876878377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2095989387479826706738709 98249502538116876878377)
                  ·
                    rfl

theorem cell22_861031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].length) (baseStart_861031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861031 prefixEnd_861031 := by exact prefixLift 861031
  have htrace : WordTrace (prefixWord ++ tailWord_861031) baseStart_861031 baseEnd_861031 := by
    simpa [prefixWord, tailWord_861031, baseEnd_861031] using wordTrace_append hprefix tailTrace_861031
  have hstable : (prefixWord ++ tailWord_861031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861031).length < 2 ^ (prefixWord ++ tailWord_861031).sum := by decide
  have hdescent : baseEnd_861031 < baseStart_861031 := by decide
  rcases family_descends (prefixWord ++ tailWord_861031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861061 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_861061 : Nat := 118140960795 + 861061 * 2 ^ 59
def prefixEnd_861061 : Nat := 4983230072969 + 3 ^ 40 * 861061 * 2
def baseEnd_861061 : Nat := 294758777227440552385039

theorem tailTrace_861061 : CollatzResearch.WordTrace tailWord_861061 prefixEnd_861061 294758777227440552385039 := by
  unfold tailWord_861061
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405474733530529356063037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20936983155687019570708691 31405474733530529356063037)
  ·
    refine ⟨11777053025073948508523639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31405474733530529356063037 11777053025073948508523639)
    ·
      refine ⟨17665579537610922762785459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777053025073948508523639 17665579537610922762785459)
      ·
        refine ⟨26498369306416384144178189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17665579537610922762785459 26498369306416384144178189)
        ·
          refine ⟨9936888489906144054066821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26498369306416384144178189 9936888489906144054066821)
          ·
            refine ⟨1863166591857402010137529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9936888489906144054066821 1863166591857402010137529)
            ·
              refine ⟨1397374943893051507603147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863166591857402010137529 1397374943893051507603147)
              ·
                refine ⟨2096062415839577261404721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397374943893051507603147 2096062415839577261404721)
                ·
                  refine ⟨1572046811879682946053541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096062415839577261404721 1572046811879682946053541)
                  ·
                    refine ⟨294758777227440552385039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572046811879682946053541 294758777227440552385039)
                    ·
                      rfl

theorem cell22_861061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_861061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861061 prefixEnd_861061 := by exact prefixLift 861061
  have htrace : WordTrace (prefixWord ++ tailWord_861061) baseStart_861061 baseEnd_861061 := by
    simpa [prefixWord, tailWord_861061, baseEnd_861061] using wordTrace_append hprefix tailTrace_861061
  have hstable : (prefixWord ++ tailWord_861061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861061).length < 2 ^ (prefixWord ++ tailWord_861061).sum := by decide
  have hdescent : baseEnd_861061 < baseStart_861061 := by decide
  rcases family_descends (prefixWord ++ tailWord_861061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861082 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_861082 : Nat := 118140960795 + 861082 * 2 ^ 59
def prefixEnd_861082 : Nat := 4983230072969 + 3 ^ 40 * 861082 * 2
def baseEnd_861082 : Nat := 98255321985534499203325

theorem tailTrace_861082 : CollatzResearch.WordTrace tailWord_861082 prefixEnd_861082 98255321985534499203325 := by
  unfold tailWord_861082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851560166613612485644375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20937493777636299961718333 7851560166613612485644375)
  ·
    refine ⟨11777340249920418728466563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7851560166613612485644375 11777340249920418728466563)
    ·
      refine ⟨17666010374880628092699845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777340249920418728466563 17666010374880628092699845)
      ·
        refine ⟨3312376945290117767381221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17666010374880628092699845 3312376945290117767381221)
        ·
          refine ⟨621070677241897081383979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3312376945290117767381221 621070677241897081383979)
          ·
            refine ⟨931606015862845622075969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621070677241897081383979 931606015862845622075969)
            ·
              refine ⟨698704511897134216556977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931606015862845622075969 698704511897134216556977)
              ·
                refine ⟨524028383922850662417733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698704511897134216556977 524028383922850662417733)
                ·
                  refine ⟨98255321985534499203325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524028383922850662417733 98255321985534499203325)
                  ·
                    rfl

theorem cell22_861082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_861082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861082 prefixEnd_861082 := by exact prefixLift 861082
  have htrace : WordTrace (prefixWord ++ tailWord_861082) baseStart_861082 baseEnd_861082 := by
    simpa [prefixWord, tailWord_861082, baseEnd_861082] using wordTrace_append hprefix tailTrace_861082
  have hstable : (prefixWord ++ tailWord_861082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861082).length < 2 ^ (prefixWord ++ tailWord_861082).sum := by decide
  have hdescent : baseEnd_861082 < baseStart_861082 := by decide
  rcases family_descends (prefixWord ++ tailWord_861082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861138 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_861138 : Nat := 118140960795 + 861138 * 2 ^ 59
def prefixEnd_861138 : Nat := 4983230072969 + 3 ^ 40 * 861138 * 2
def baseEnd_861138 : Nat := 98261711967012672736601

theorem tailTrace_861138 : CollatzResearch.WordTrace tailWord_861138 prefixEnd_861138 98261711967012672736601 := by
  unfold tailWord_861138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852070788562892876654017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20938855436167714337744045 7852070788562892876654017)
  ·
    refine ⟨5889053091422169657490513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7852070788562892876654017 5889053091422169657490513)
    ·
      refine ⟨4416789818566627243117885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5889053091422169657490513 4416789818566627243117885)
      ·
        refine ⟨1656296181962485216169207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4416789818566627243117885 1656296181962485216169207)
        ·
          refine ⟨2484444272943727824253811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656296181962485216169207 2484444272943727824253811)
          ·
            refine ⟨3726666409415591736380717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484444272943727824253811 3726666409415591736380717)
            ·
              refine ⟨1397499903530846901142769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3726666409415591736380717 1397499903530846901142769)
              ·
                refine ⟨1048124927648135175857077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397499903530846901142769 1048124927648135175857077)
                ·
                  refine ⟨98261711967012672736601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048124927648135175857077 98261711967012672736601)
                  ·
                    rfl

theorem cell22_861138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_861138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861138 prefixEnd_861138 := by exact prefixLift 861138
  have htrace : WordTrace (prefixWord ++ tailWord_861138) baseStart_861138 baseEnd_861138 := by
    simpa [prefixWord, tailWord_861138, baseEnd_861138] using wordTrace_append hprefix tailTrace_861138
  have hstable : (prefixWord ++ tailWord_861138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861138).length < 2 ^ (prefixWord ++ tailWord_861138).sum := by decide
  have hdescent : baseEnd_861138 < baseStart_861138 := by decide
  rcases family_descends (prefixWord ++ tailWord_861138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861142 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_861142 : Nat := 118140960795 + 861142 * 2 ^ 59
def prefixEnd_861142 : Nat := 4983230072969 + 3 ^ 40 * 861142 * 2
def baseEnd_861142 : Nat := 294786505182783341109791

theorem tailTrace_861142 : CollatzResearch.WordTrace tailWord_861142 prefixEnd_861142 294786505182783341109791 := by
  unfold tailWord_861142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963026815389817511860105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20938952697491386793174453 1963026815389817511860105)
  ·
    refine ⟨1472270111542363133895079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1963026815389817511860105 1472270111542363133895079)
    ·
      refine ⟨2208405167313544700842619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472270111542363133895079 2208405167313544700842619)
      ·
        refine ⟨3312607750970317051263929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208405167313544700842619 3312607750970317051263929)
        ·
          refine ⟨2484455813227737788447947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312607750970317051263929 2484455813227737788447947)
          ·
            refine ⟨3726683719841606682671921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484455813227737788447947 3726683719841606682671921)
            ·
              refine ⟨2795012789881205012003941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726683719841606682671921 2795012789881205012003941)
              ·
                refine ⟨524064898102725939750739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2795012789881205012003941 524064898102725939750739)
                ·
                  refine ⟨786097347154088909626109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524064898102725939750739 786097347154088909626109)
                  ·
                    refine ⟨294786505182783341109791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786097347154088909626109 294786505182783341109791)
                    ·
                      rfl

theorem cell22_861142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_861142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861142 prefixEnd_861142 := by exact prefixLift 861142
  have htrace : WordTrace (prefixWord ++ tailWord_861142) baseStart_861142 baseEnd_861142 := by
    simpa [prefixWord, tailWord_861142, baseEnd_861142] using wordTrace_append hprefix tailTrace_861142
  have hstable : (prefixWord ++ tailWord_861142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861142).length < 2 ^ (prefixWord ++ tailWord_861142).sum := by decide
  have hdescent : baseEnd_861142 < baseStart_861142 := by decide
  rcases family_descends (prefixWord ++ tailWord_861142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861196 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_861196 : Nat := 118140960795 + 861196 * 2 ^ 59
def prefixEnd_861196 : Nat := 4983230072969 + 3 ^ 40 * 861196 * 2
def baseEnd_861196 : Nat := 294804990486345200259625

theorem tailTrace_861196 : CollatzResearch.WordTrace tailWord_861196 prefixEnd_861196 294804990486345200259625 := by
  unfold tailWord_861196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705199294020723706113721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20940265725360964941484961 15705199294020723706113721)
  ·
    refine ⟨11778899470515542779585291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15705199294020723706113721 11778899470515542779585291)
    ·
      refine ⟨17668349205773314169377937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11778899470515542779585291 17668349205773314169377937)
      ·
        refine ⟨13251261904329985627033453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17668349205773314169377937 13251261904329985627033453)
        ·
          refine ⟨4969223214123744610137545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13251261904329985627033453 4969223214123744610137545)
          ·
            refine ⟨3726917410592808457603159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4969223214123744610137545 3726917410592808457603159)
            ·
              refine ⟨5590376115889212686404739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726917410592808457603159 5590376115889212686404739)
              ·
                refine ⟨8385564173833819029607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590376115889212686404739 8385564173833819029607109)
                ·
                  refine ⟨1572293282593841068051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8385564173833819029607109 1572293282593841068051333)
                  ·
                    refine ⟨294804990486345200259625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572293282593841068051333 294804990486345200259625)
                    ·
                      rfl

theorem cell22_861196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_861196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861196 prefixEnd_861196 := by exact prefixLift 861196
  have htrace : WordTrace (prefixWord ++ tailWord_861196) baseStart_861196 baseEnd_861196 := by
    simpa [prefixWord, tailWord_861196, baseEnd_861196] using wordTrace_append hprefix tailTrace_861196
  have hstable : (prefixWord ++ tailWord_861196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861196).length < 2 ^ (prefixWord ++ tailWord_861196).sum := by decide
  have hdescent : baseEnd_861196 < baseStart_861196 := by decide
  rcases family_descends (prefixWord ++ tailWord_861196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861198 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_861198 : Nat := 118140960795 + 861198 * 2 ^ 59
def prefixEnd_861198 : Nat := 4983230072969 + 3 ^ 40 * 861198 * 2
def baseEnd_861198 : Nat := 294805675127217861709619

theorem tailTrace_861198 : CollatzResearch.WordTrace tailWord_861198 prefixEnd_861198 294805675127217861709619 := by
  unfold tailWord_861198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926308941754275219225031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20940314356022801169200165 3926308941754275219225031)
  ·
    refine ⟨5889463412631412828837547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926308941754275219225031 5889463412631412828837547)
    ·
      refine ⟨8834195118947119243256321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889463412631412828837547 8834195118947119243256321)
      ·
        refine ⟨6625646339210339432442241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8834195118947119243256321 6625646339210339432442241)
        ·
          refine ⟨4969234754407754574331681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6625646339210339432442241 4969234754407754574331681)
          ·
            refine ⟨3726926065805815930748761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4969234754407754574331681 3726926065805815930748761)
            ·
              refine ⟨2795194549354361948061571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726926065805815930748761 2795194549354361948061571)
              ·
                refine ⟨4192791824031542922092357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795194549354361948061571 4192791824031542922092357)
                ·
                  refine ⟨786148467005914297892317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4192791824031542922092357 786148467005914297892317)
                  ·
                    refine ⟨294805675127217861709619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786148467005914297892317 294805675127217861709619)
                    ·
                      rfl

theorem cell22_861198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_861198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861198 prefixEnd_861198 := by exact prefixLift 861198
  have htrace : WordTrace (prefixWord ++ tailWord_861198) baseStart_861198 baseEnd_861198 := by
    simpa [prefixWord, tailWord_861198, baseEnd_861198] using wordTrace_append hprefix tailTrace_861198
  have hstable : (prefixWord ++ tailWord_861198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861198).length < 2 ^ (prefixWord ++ tailWord_861198).sum := by decide
  have hdescent : baseEnd_861198 < baseStart_861198 := by decide
  rcases family_descends (prefixWord ++ tailWord_861198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861215 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 2, 3]
def baseStart_861215 : Nat := 118140960795 + 861215 * 2 ^ 59
def prefixEnd_861215 : Nat := 4983230072969 + 3 ^ 40 * 861215 * 2
def baseEnd_861215 : Nat := 294811494574635484034567

theorem tailTrace_861215 : CollatzResearch.WordTrace tailWord_861215 prefixEnd_861215 294811494574635484034567 := by
  unfold tailWord_861215
  simp only [CollatzResearch.WordTrace]
  refine ⟨31411091574972613657169099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20940727716648409104779399 31411091574972613657169099)
  ·
    refine ⟨47116637362458920485753649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31411091574972613657169099 47116637362458920485753649)
    ·
      refine ⟨35337478021844190364315237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47116637362458920485753649 35337478021844190364315237)
      ·
        refine ⟨6625777129095785693309107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35337478021844190364315237 6625777129095785693309107)
        ·
          refine ⟨9938665693643678539963661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625777129095785693309107 9938665693643678539963661)
          ·
            refine ⟨3726999635116379452486373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9938665693643678539963661 3726999635116379452486373)
            ·
              refine ⟨698812431584321147341195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3726999635116379452486373 698812431584321147341195)
              ·
                refine ⟨1048218647376481721011793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698812431584321147341195 1048218647376481721011793)
                ·
                  refine ⟨786163985532361290758845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048218647376481721011793 786163985532361290758845)
                  ·
                    refine ⟨294811494574635484034567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786163985532361290758845 294811494574635484034567)
                    ·
                      rfl

theorem cell22_861215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_861215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861215 prefixEnd_861215 := by exact prefixLift 861215
  have htrace : WordTrace (prefixWord ++ tailWord_861215) baseStart_861215 baseEnd_861215 := by
    simpa [prefixWord, tailWord_861215, baseEnd_861215] using wordTrace_append hprefix tailTrace_861215
  have hstable : (prefixWord ++ tailWord_861215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861215).length < 2 ^ (prefixWord ++ tailWord_861215).sum := by decide
  have hdescent : baseEnd_861215 < baseStart_861215 := by decide
  rcases family_descends (prefixWord ++ tailWord_861215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861277 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_861277 : Nat := 118140960795 + 861277 * 2 ^ 59
def prefixEnd_861277 : Nat := 4983230072969 + 3 ^ 40 * 861277 * 2
def baseEnd_861277 : Nat := 294832718441687988984377

theorem tailTrace_861277 : CollatzResearch.WordTrace tailWord_861277 prefixEnd_861277 294832718441687988984377 := by
  unfold tailWord_861277
  simp only [CollatzResearch.WordTrace]
  refine ⟨31413352900747998245926085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20942235267165332163950723 31413352900747998245926085)
  ·
    refine ⟨5890003668890249671111141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31413352900747998245926085 5890003668890249671111141)
    ·
      refine ⟨1104375687916921813333339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5890003668890249671111141 1104375687916921813333339)
      ·
        refine ⟨1656563531875382720000009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104375687916921813333339 1656563531875382720000009)
        ·
          refine ⟨1242422648906537040000007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656563531875382720000009 1242422648906537040000007)
          ·
            refine ⟨1863633973359805560000011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242422648906537040000007 1863633973359805560000011)
            ·
              refine ⟨2795450960039708340000017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863633973359805560000011 2795450960039708340000017)
              ·
                refine ⟨2096588220029781255000013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795450960039708340000017 2096588220029781255000013)
                ·
                  refine ⟨786220582511167970625005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2096588220029781255000013 786220582511167970625005)
                  ·
                    refine ⟨294832718441687988984377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786220582511167970625005 294832718441687988984377)
                    ·
                      rfl

theorem cell22_861277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_861277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861277 prefixEnd_861277 := by exact prefixLift 861277
  have htrace : WordTrace (prefixWord ++ tailWord_861277) baseStart_861277 baseEnd_861277 := by
    simpa [prefixWord, tailWord_861277, baseEnd_861277] using wordTrace_append hprefix tailTrace_861277
  have hstable : (prefixWord ++ tailWord_861277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861277).length < 2 ^ (prefixWord ++ tailWord_861277).sum := by decide
  have hdescent : baseEnd_861277 < baseStart_861277 := by decide
  rcases family_descends (prefixWord ++ tailWord_861277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861303 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 1, 4]
def baseStart_861303 : Nat := 118140960795 + 861303 * 2 ^ 59
def prefixEnd_861303 : Nat := 4983230072969 + 3 ^ 40 * 861303 * 2
def baseEnd_861303 : Nat := 294841618773032587834297

theorem tailTrace_861303 : CollatzResearch.WordTrace tailWord_861303 prefixEnd_861303 294841618773032587834297 := by
  unfold tailWord_861303
  simp only [CollatzResearch.WordTrace]
  refine ⟨31414301198653804686372563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20942867465769203124248375 31414301198653804686372563)
  ·
    refine ⟨47121451797980707029558845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31414301198653804686372563 47121451797980707029558845)
    ·
      refine ⟨17670544424242765136084567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47121451797980707029558845 17670544424242765136084567)
      ·
        refine ⟨26505816636364147704126851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17670544424242765136084567 26505816636364147704126851)
        ·
          refine ⟨39758724954546221556190277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26505816636364147704126851 39758724954546221556190277)
          ·
            refine ⟨7454760928977416541785677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39758724954546221556190277 7454760928977416541785677)
            ·
              refine ⟨2795535348366531203169629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7454760928977416541785677 2795535348366531203169629)
              ·
                refine ⟨1048325755637449201188611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795535348366531203169629 1048325755637449201188611)
                ·
                  refine ⟨1572488633456173801782917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048325755637449201188611 1572488633456173801782917)
                  ·
                    refine ⟨294841618773032587834297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572488633456173801782917 294841618773032587834297)
                    ·
                      rfl

theorem cell22_861303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_861303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861303 prefixEnd_861303 := by exact prefixLift 861303
  have htrace : WordTrace (prefixWord ++ tailWord_861303) baseStart_861303 baseEnd_861303 := by
    simpa [prefixWord, tailWord_861303, baseEnd_861303] using wordTrace_append hprefix tailTrace_861303
  have hstable : (prefixWord ++ tailWord_861303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861303).length < 2 ^ (prefixWord ++ tailWord_861303).sum := by decide
  have hdescent : baseEnd_861303 < baseStart_861303 := by decide
  rcases family_descends (prefixWord ++ tailWord_861303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861331 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_861331 : Nat := 118140960795 + 861331 * 2 ^ 59
def prefixEnd_861331 : Nat := 4983230072969 + 3 ^ 40 * 861331 * 2
def baseEnd_861331 : Nat := 294851203745249848134211

theorem tailTrace_861331 : CollatzResearch.WordTrace tailWord_861331 prefixEnd_861331 294851203745249848134211 := by
  unfold tailWord_861331
  simp only [CollatzResearch.WordTrace]
  refine ⟨31415322442552365468391847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20943548295034910312261231 31415322442552365468391847)
  ·
    refine ⟨47122983663828548202587771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31415322442552365468391847 47122983663828548202587771)
    ·
      refine ⟨70684475495742822303881657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47122983663828548202587771 70684475495742822303881657)
      ·
        refine ⟨53013356621807116727911243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70684475495742822303881657 53013356621807116727911243)
        ·
          refine ⟨79520034932710675091866865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53013356621807116727911243 79520034932710675091866865)
          ·
            refine ⟨59640026199533006318900149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79520034932710675091866865 59640026199533006318900149)
            ·
              refine ⟨5591252456206219342396889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59640026199533006318900149 5591252456206219342396889)
              ·
                refine ⟨4193439342154664506797667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591252456206219342396889 4193439342154664506797667)
                ·
                  refine ⟨6290159013231996760196501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193439342154664506797667 6290159013231996760196501)
                  ·
                    refine ⟨294851203745249848134211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6290159013231996760196501 294851203745249848134211)
                    ·
                      rfl

theorem cell22_861331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_861331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861331 prefixEnd_861331 := by exact prefixLift 861331
  have htrace : WordTrace (prefixWord ++ tailWord_861331) baseStart_861331 baseEnd_861331 := by
    simpa [prefixWord, tailWord_861331, baseEnd_861331] using wordTrace_append hprefix tailTrace_861331
  have hstable : (prefixWord ++ tailWord_861331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861331).length < 2 ^ (prefixWord ++ tailWord_861331).sum := by decide
  have hdescent : baseEnd_861331 < baseStart_861331 := by decide
  rcases family_descends (prefixWord ++ tailWord_861331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861348 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_861348 : Nat := 118140960795 + 861348 * 2 ^ 59
def prefixEnd_861348 : Nat := 4983230072969 + 3 ^ 40 * 861348 * 2
def baseEnd_861348 : Nat := 294857023192667470459159

theorem tailTrace_861348 : CollatzResearch.WordTrace tailWord_861348 prefixEnd_861348 294857023192667470459159 := by
  unfold tailWord_861348
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707971241745388685880349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20943961655660518247840465 15707971241745388685880349)
  ·
    refine ⟨5890489215654520757205131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15707971241745388685880349 5890489215654520757205131)
    ·
      refine ⟨8835733823481781135807697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890489215654520757205131 8835733823481781135807697)
      ·
        refine ⟨6626800367611335851855773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8835733823481781135807697 6626800367611335851855773)
        ·
          refine ⟨2485050137854250944445915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6626800367611335851855773 2485050137854250944445915)
          ·
            refine ⟨3727575206781376416668873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485050137854250944445915 3727575206781376416668873)
            ·
              refine ⟨2795681405086032312501655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727575206781376416668873 2795681405086032312501655)
              ·
                refine ⟨4193522107629048468752483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795681405086032312501655 4193522107629048468752483)
                ·
                  refine ⟨6290283161443572703128725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193522107629048468752483 6290283161443572703128725)
                  ·
                    refine ⟨294857023192667470459159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6290283161443572703128725 294857023192667470459159)
                    ·
                      rfl

theorem cell22_861348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_861348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861348 prefixEnd_861348 := by exact prefixLift 861348
  have htrace : WordTrace (prefixWord ++ tailWord_861348) baseStart_861348 baseEnd_861348 := by
    simpa [prefixWord, tailWord_861348, baseEnd_861348] using wordTrace_append hprefix tailTrace_861348
  have hstable : (prefixWord ++ tailWord_861348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861348).length < 2 ^ (prefixWord ++ tailWord_861348).sum := by decide
  have hdescent : baseEnd_861348 < baseStart_861348 := by decide
  rcases family_descends (prefixWord ++ tailWord_861348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861380 : List Nat := [2, 3, 3, 1, 3, 1, 2, 7]
def baseStart_861380 : Nat := 118140960795 + 861380 * 2 ^ 59
def prefixEnd_861380 : Nat := 4983230072969 + 3 ^ 40 * 861380 * 2
def baseEnd_861380 : Nat := 32763108605181117073229

theorem tailTrace_861380 : CollatzResearch.WordTrace tailWord_861380 prefixEnd_861380 32763108605181117073229 := by
  unfold tailWord_861380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708554809687423418462797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20944739746249897891283729 15708554809687423418462797)
  ·
    refine ⟨5890708053632783781923549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15708554809687423418462797 5890708053632783781923549)
    ·
      refine ⟨2209015520112293918221331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5890708053632783781923549 2209015520112293918221331)
      ·
        refine ⟨3313523280168440877331997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209015520112293918221331 3313523280168440877331997)
        ·
          refine ⟨1242571230063165328999499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3313523280168440877331997 1242571230063165328999499)
          ·
            refine ⟨1863856845094747993499249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242571230063165328999499 1863856845094747993499249)
            ·
              refine ⟨1397892633821060995124437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863856845094747993499249 1397892633821060995124437)
              ·
                refine ⟨32763108605181117073229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1397892633821060995124437 32763108605181117073229)
                ·
                  rfl

theorem cell22_861380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_861380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861380 prefixEnd_861380 := by exact prefixLift 861380
  have htrace : WordTrace (prefixWord ++ tailWord_861380) baseStart_861380 baseEnd_861380 := by
    simpa [prefixWord, tailWord_861380, baseEnd_861380] using wordTrace_append hprefix tailTrace_861380
  have hstable : (prefixWord ++ tailWord_861380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861380).length < 2 ^ (prefixWord ++ tailWord_861380).sum := by decide
  have hdescent : baseEnd_861380 < baseStart_861380 := by decide
  rcases family_descends (prefixWord ++ tailWord_861380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861391 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 9]
def baseStart_861391 : Nat := 118140960795 + 861391 * 2 ^ 59
def prefixEnd_861391 : Nat := 4983230072969 + 3 ^ 40 * 861391 * 2
def baseEnd_861391 : Nat := 98290580990476563878009

theorem tailTrace_861391 : CollatzResearch.WordTrace tailWord_861391 prefixEnd_861391 98290580990476563878009 := by
  unfold tailWord_861391
  simp only [CollatzResearch.WordTrace]
  refine ⟨31417510822334995715576027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20945007214889997143717351 31417510822334995715576027)
  ·
    refine ⟨47126266233502493573364041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31417510822334995715576027 47126266233502493573364041)
    ·
      refine ⟨35344699675126870180023031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47126266233502493573364041 35344699675126870180023031)
      ·
        refine ⟨53017049512690305270034547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35344699675126870180023031 53017049512690305270034547)
        ·
          refine ⟨79525574269035457905051821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53017049512690305270034547 79525574269035457905051821)
          ·
            refine ⟨29822090350888296714394433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79525574269035457905051821 29822090350888296714394433)
            ·
              refine ⟨22366567763166222535795825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29822090350888296714394433 22366567763166222535795825)
              ·
                refine ⟨16774925822374666901846869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22366567763166222535795825 16774925822374666901846869)
                ·
                  refine ⟨98290580990476563878009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16774925822374666901846869 98290580990476563878009)
                  ·
                    rfl

theorem cell22_861391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_861391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861391 prefixEnd_861391 := by exact prefixLift 861391
  have htrace : WordTrace (prefixWord ++ tailWord_861391) baseStart_861391 baseEnd_861391 := by
    simpa [prefixWord, tailWord_861391, baseEnd_861391] using wordTrace_append hprefix tailTrace_861391
  have hstable : (prefixWord ++ tailWord_861391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861391).length < 2 ^ (prefixWord ++ tailWord_861391).sum := by decide
  have hdescent : baseEnd_861391 < baseStart_861391 := by decide
  rcases family_descends (prefixWord ++ tailWord_861391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861472 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_861472 : Nat := 118140960795 + 861472 * 2 ^ 59
def prefixEnd_861472 : Nat := 4983230072969 + 3 ^ 40 * 861472 * 2
def baseEnd_861472 : Nat := 294899470926772480358779

theorem tailTrace_861472 : CollatzResearch.WordTrace tailWord_861472 prefixEnd_861472 294899470926772480358779 := by
  unfold tailWord_861472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710232567520773274637335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20946976756694364366183113 15710232567520773274637335)
  ·
    refine ⟨23565348851281159911956003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15710232567520773274637335 23565348851281159911956003)
    ·
      refine ⟨35348023276921739867934005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23565348851281159911956003 35348023276921739867934005)
      ·
        refine ⟨3313877182211413112618813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35348023276921739867934005 3313877182211413112618813)
        ·
          refine ⟨1242703943329279917232055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3313877182211413112618813 1242703943329279917232055)
          ·
            refine ⟨1864055914993919875848083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242703943329279917232055 1864055914993919875848083)
            ·
              refine ⟨2796083872490879813772125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864055914993919875848083 2796083872490879813772125)
              ·
                refine ⟨1048531452184079930164547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2796083872490879813772125 1048531452184079930164547)
                ·
                  refine ⟨1572797178276119895246821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048531452184079930164547 1572797178276119895246821)
                  ·
                    refine ⟨294899470926772480358779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572797178276119895246821 294899470926772480358779)
                    ·
                      rfl

theorem cell22_861472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_861472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861472 prefixEnd_861472 := by exact prefixLift 861472
  have htrace : WordTrace (prefixWord ++ tailWord_861472) baseStart_861472 baseEnd_861472 := by
    simpa [prefixWord, tailWord_861472, baseEnd_861472] using wordTrace_append hprefix tailTrace_861472
  have hstable : (prefixWord ++ tailWord_861472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861472).length < 2 ^ (prefixWord ++ tailWord_861472).sum := by decide
  have hdescent : baseEnd_861472 < baseStart_861472 := by decide
  rcases family_descends (prefixWord ++ tailWord_861472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861498 : List Nat := [3, 1, 1, 1, 4, 1, 2, 9]
def baseStart_861498 : Nat := 118140960795 + 861498 * 2 ^ 59
def prefixEnd_861498 : Nat := 4983230072969 + 3 ^ 40 * 861498 * 2
def baseEnd_861498 : Nat := 32767596806457453245411

theorem tailTrace_861498 : CollatzResearch.WordTrace tailWord_861498 prefixEnd_861498 32767596806457453245411 := by
  unfold tailWord_861498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855353358236838247430287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20947608955298235326480765 7855353358236838247430287)
  ·
    refine ⟨11783030037355257371145431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855353358236838247430287 11783030037355257371145431)
    ·
      refine ⟨17674545056032886056718147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783030037355257371145431 17674545056032886056718147)
      ·
        refine ⟨26511817584049329085077221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17674545056032886056718147 26511817584049329085077221)
        ·
          refine ⟨4970965797009249203451979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26511817584049329085077221 4970965797009249203451979)
          ·
            refine ⟨7456448695513873805177969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970965797009249203451979 7456448695513873805177969)
            ·
              refine ⟨5592336521635405353883477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7456448695513873805177969 5592336521635405353883477)
              ·
                refine ⟨32767596806457453245411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5592336521635405353883477 32767596806457453245411)
                ·
                  rfl

theorem cell22_861498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_861498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861498 prefixEnd_861498 := by exact prefixLift 861498
  have htrace : WordTrace (prefixWord ++ tailWord_861498) baseStart_861498 baseEnd_861498 := by
    simpa [prefixWord, tailWord_861498, baseEnd_861498] using wordTrace_append hprefix tailTrace_861498
  have hstable : (prefixWord ++ tailWord_861498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861498).length < 2 ^ (prefixWord ++ tailWord_861498).sum := by decide
  have hdescent : baseEnd_861498 < baseStart_861498 := by decide
  rcases family_descends (prefixWord ++ tailWord_861498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861530 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_861530 : Nat := 118140960795 + 861530 * 2 ^ 59
def prefixEnd_861530 : Nat := 4983230072969 + 3 ^ 40 * 861530 * 2
def baseEnd_861530 : Nat := 294919325512079662408601

theorem tailTrace_861530 : CollatzResearch.WordTrace tailWord_861530 prefixEnd_861530 294919325512079662408601 := by
  unfold tailWord_861530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855645142207855613721511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20948387045887614969924029 7855645142207855613721511)
  ·
    refine ⟨11783467713311783420582267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855645142207855613721511 11783467713311783420582267)
    ·
      refine ⟨17675201569967675130873401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783467713311783420582267 17675201569967675130873401)
      ·
        refine ⟨13256401177475756348155051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17675201569967675130873401 13256401177475756348155051)
        ·
          refine ⟨19884601766213634522232577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13256401177475756348155051 19884601766213634522232577)
          ·
            refine ⟨14913451324660225891674433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19884601766213634522232577 14913451324660225891674433)
            ·
              refine ⟨11185088493495169418755825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14913451324660225891674433 11185088493495169418755825)
              ·
                refine ⟨8388816370121377064066869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11185088493495169418755825 8388816370121377064066869)
                ·
                  refine ⟨786451534698879099756269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8388816370121377064066869 786451534698879099756269)
                  ·
                    refine ⟨294919325512079662408601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786451534698879099756269 294919325512079662408601)
                    ·
                      rfl

theorem cell22_861530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_861530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861530 prefixEnd_861530 := by exact prefixLift 861530
  have htrace : WordTrace (prefixWord ++ tailWord_861530) baseStart_861530 baseEnd_861530 := by
    simpa [prefixWord, tailWord_861530, baseEnd_861530] using wordTrace_append hprefix tailTrace_861530
  have hstable : (prefixWord ++ tailWord_861530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861530).length < 2 ^ (prefixWord ++ tailWord_861530).sum := by decide
  have hdescent : baseEnd_861530 < baseStart_861530 := by decide
  rcases family_descends (prefixWord ++ tailWord_861530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861598 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_861598 : Nat := 118140960795 + 861598 * 2 ^ 59
def prefixEnd_861598 : Nat := 4983230072969 + 3 ^ 40 * 861598 * 2
def baseEnd_861598 : Nat := 294942603301750151708393

theorem tailTrace_861598 : CollatzResearch.WordTrace tailWord_861598 prefixEnd_861598 294942603301750151708393 := by
  unfold tailWord_861598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928132591573133758545181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20950040488390046712240965 3928132591573133758545181)
  ·
    refine ⟨1473049721839925159454443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3928132591573133758545181 1473049721839925159454443)
    ·
      refine ⟨2209574582759887739181665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473049721839925159454443 2209574582759887739181665)
      ·
        refine ⟨1657180937069915804386249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209574582759887739181665 1657180937069915804386249)
        ·
          refine ⟨1242885702802436853289687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657180937069915804386249 1242885702802436853289687)
          ·
            refine ⟨1864328554203655279934531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242885702802436853289687 1864328554203655279934531)
            ·
              refine ⟨2796492831305482919901797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864328554203655279934531 2796492831305482919901797)
              ·
                refine ⟨524342405869778047481587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2796492831305482919901797 524342405869778047481587)
                ·
                  refine ⟨786513608804667071222381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524342405869778047481587 786513608804667071222381)
                  ·
                    refine ⟨294942603301750151708393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786513608804667071222381 294942603301750151708393)
                    ·
                      rfl

theorem cell22_861598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_861598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861598 prefixEnd_861598 := by exact prefixLift 861598
  have htrace : WordTrace (prefixWord ++ tailWord_861598) baseStart_861598 baseEnd_861598 := by
    simpa [prefixWord, tailWord_861598, baseEnd_861598] using wordTrace_append hprefix tailTrace_861598
  have hstable : (prefixWord ++ tailWord_861598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861598).length < 2 ^ (prefixWord ++ tailWord_861598).sum := by decide
  have hdescent : baseEnd_861598 < baseStart_861598 := by decide
  rcases family_descends (prefixWord ++ tailWord_861598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861671 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 2, 3]
def baseStart_861671 : Nat := 118140960795 + 861671 * 2 ^ 59
def prefixEnd_861671 : Nat := 4983230072969 + 3 ^ 40 * 861671 * 2
def baseEnd_861671 : Nat := 294967592693602294633169

theorem tailTrace_861671 : CollatzResearch.WordTrace tailWord_861671 prefixEnd_861671 294967592693602294633169 := by
  unfold tailWord_861671
  simp only [CollatzResearch.WordTrace]
  refine ⟨31427723261320603535768867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20951815507547069023845911 31427723261320603535768867)
  ·
    refine ⟨47141584891980905303653301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31427723261320603535768867 47141584891980905303653301)
    ·
      refine ⟨4419523583623209872217497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47141584891980905303653301 4419523583623209872217497)
      ·
        refine ⟨3314642687717407404163123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4419523583623209872217497 3314642687717407404163123)
        ·
          refine ⟨4971964031576111106244685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314642687717407404163123 4971964031576111106244685)
          ·
            refine ⟨1864486511841041664841757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4971964031576111106244685 1864486511841041664841757)
            ·
              refine ⟨699182441940390624315659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1864486511841041664841757 699182441940390624315659)
              ·
                refine ⟨1048773662910585936473489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699182441940390624315659 1048773662910585936473489)
                ·
                  refine ⟨786580247182939452355117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048773662910585936473489 786580247182939452355117)
                  ·
                    refine ⟨294967592693602294633169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786580247182939452355117 294967592693602294633169)
                    ·
                      rfl

theorem cell22_861671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_861671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861671 prefixEnd_861671 := by exact prefixLift 861671
  have htrace : WordTrace (prefixWord ++ tailWord_861671) baseStart_861671 baseEnd_861671 := by
    simpa [prefixWord, tailWord_861671, baseEnd_861671] using wordTrace_append hprefix tailTrace_861671
  have hstable : (prefixWord ++ tailWord_861671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861671).length < 2 ^ (prefixWord ++ tailWord_861671).sum := by decide
  have hdescent : baseEnd_861671 < baseStart_861671 := by decide
  rcases family_descends (prefixWord ++ tailWord_861671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861699 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 1, 3]
def baseStart_861699 : Nat := 118140960795 + 861699 * 2 ^ 59
def prefixEnd_861699 : Nat := 4983230072969 + 3 ^ 40 * 861699 * 2
def baseEnd_861699 : Nat := 294977177665819554933083

theorem tailTrace_861699 : CollatzResearch.WordTrace tailWord_861699 prefixEnd_861699 294977177665819554933083 := by
  unfold tailWord_861699
  simp only [CollatzResearch.WordTrace]
  refine ⟨31428744505219164317788151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952496336812776211858767 31428744505219164317788151)
  ·
    refine ⟨47143116757828746476682227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31428744505219164317788151 47143116757828746476682227)
    ·
      refine ⟨70714675136743119715023341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47143116757828746476682227 70714675136743119715023341)
      ·
        refine ⟨26518003176278669893133753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70714675136743119715023341 26518003176278669893133753)
        ·
          refine ⟨19888502382209002419850315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26518003176278669893133753 19888502382209002419850315)
          ·
            refine ⟨29832753573313503629775473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19888502382209002419850315 29832753573313503629775473)
            ·
              refine ⟨22374565179985127722331605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29832753573313503629775473 22374565179985127722331605)
              ·
                refine ⟨524403871405901430992147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22374565179985127722331605 524403871405901430992147)
                ·
                  refine ⟨786605807108852146488221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524403871405901430992147 786605807108852146488221)
                  ·
                    refine ⟨294977177665819554933083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786605807108852146488221 294977177665819554933083)
                    ·
                      rfl

theorem cell22_861699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 3].length) (baseStart_861699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861699 prefixEnd_861699 := by exact prefixLift 861699
  have htrace : WordTrace (prefixWord ++ tailWord_861699) baseStart_861699 baseEnd_861699 := by
    simpa [prefixWord, tailWord_861699, baseEnd_861699] using wordTrace_append hprefix tailTrace_861699
  have hstable : (prefixWord ++ tailWord_861699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861699).length < 2 ^ (prefixWord ++ tailWord_861699).sum := by decide
  have hdescent : baseEnd_861699 < baseStart_861699 := by decide
  rcases family_descends (prefixWord ++ tailWord_861699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861729 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 5]
def baseStart_861729 : Nat := 118140960795 + 861729 * 2 ^ 59
def prefixEnd_861729 : Nat := 4983230072969 + 3 ^ 40 * 861729 * 2
def baseEnd_861729 : Nat := 98329149092969825560997

theorem tailTrace_861729 : CollatzResearch.WordTrace tailWord_861729 prefixEnd_861729 98329149092969825560997 := by
  unfold tailWord_861729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429838695110479441380241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20953225796740319627586827 31429838695110479441380241)
  ·
    refine ⟨23572379021332859581035181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31429838695110479441380241 23572379021332859581035181)
    ·
      refine ⟨8839642132999822342888193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23572379021332859581035181 8839642132999822342888193)
      ·
        refine ⟨6629731599749866757166145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8839642132999822342888193 6629731599749866757166145)
        ·
          refine ⟨4972298699812400067874609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6629731599749866757166145 4972298699812400067874609)
          ·
            refine ⟨3729224024859300050905957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972298699812400067874609 3729224024859300050905957)
            ·
              refine ⟨699229504661118759544867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3729224024859300050905957 699229504661118759544867)
              ·
                refine ⟨1048844256991678139317301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699229504661118759544867 1048844256991678139317301)
                ·
                  refine ⟨98329149092969825560997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048844256991678139317301 98329149092969825560997)
                  ·
                    rfl

theorem cell22_861729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_861729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861729 prefixEnd_861729 := by exact prefixLift 861729
  have htrace : WordTrace (prefixWord ++ tailWord_861729) baseStart_861729 baseEnd_861729 := by
    simpa [prefixWord, tailWord_861729, baseEnd_861729] using wordTrace_append hprefix tailTrace_861729
  have hstable : (prefixWord ++ tailWord_861729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861729).length < 2 ^ (prefixWord ++ tailWord_861729).sum := by decide
  have hdescent : baseEnd_861729 < baseStart_861729 := by decide
  rcases family_descends (prefixWord ++ tailWord_861729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861898 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_861898 : Nat := 118140960795 + 861898 * 2 ^ 59
def prefixEnd_861898 : Nat := 4983230072969 + 3 ^ 40 * 861898 * 2
def baseEnd_861898 : Nat := 98348433144216456402491

theorem tailTrace_861898 : CollatzResearch.WordTrace tailWord_861898 prefixEnd_861898 98348433144216456402491 := by
  unfold tailWord_861898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859000657874555326070587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20957335087665480869521565 7859000657874555326070587)
  ·
    refine ⟨11788500986811832989105881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7859000657874555326070587 11788500986811832989105881)
    ·
      refine ⟨8841375740108874741829411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11788500986811832989105881 8841375740108874741829411)
      ·
        refine ⟨13262063610163312112744117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8841375740108874741829411 13262063610163312112744117)
        ·
          refine ⟨1243318463452810510569761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13262063610163312112744117 1243318463452810510569761)
          ·
            refine ⟨932488847589607882927321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243318463452810510569761 932488847589607882927321)
            ·
              refine ⟨699366635692205912195491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932488847589607882927321 699366635692205912195491)
              ·
                refine ⟨1049049953538308868293237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699366635692205912195491 1049049953538308868293237)
                ·
                  refine ⟨98348433144216456402491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1049049953538308868293237 98348433144216456402491)
                  ·
                    rfl

theorem cell22_861898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_861898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861898 prefixEnd_861898 := by exact prefixLift 861898
  have htrace : WordTrace (prefixWord ++ tailWord_861898) baseStart_861898 baseEnd_861898 := by
    simpa [prefixWord, tailWord_861898, baseEnd_861898] using wordTrace_append hprefix tailTrace_861898
  have hstable : (prefixWord ++ tailWord_861898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861898).length < 2 ^ (prefixWord ++ tailWord_861898).sum := by decide
  have hdescent : baseEnd_861898 < baseStart_861898 := by decide
  rcases family_descends (prefixWord ++ tailWord_861898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861924 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_861924 : Nat := 118140960795 + 861924 * 2 ^ 59
def prefixEnd_861924 : Nat := 4983230072969 + 3 ^ 40 * 861924 * 2
def baseEnd_861924 : Nat := 295054199763993968057393

theorem tailTrace_861924 : CollatzResearch.WordTrace tailWord_861924 prefixEnd_861924 295054199763993968057393 := by
  unfold tailWord_861924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718475464702013872364413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20957967286269351829819217 15718475464702013872364413)
  ·
    refine ⟨5894428299263255202136655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15718475464702013872364413 5894428299263255202136655)
    ·
      refine ⟨8841642448894882803204983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894428299263255202136655 8841642448894882803204983)
      ·
        refine ⟨13262463673342324204807475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8841642448894882803204983 13262463673342324204807475)
        ·
          refine ⟨19893695510013486307211213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13262463673342324204807475 19893695510013486307211213)
          ·
            refine ⟨7460135816255057365204205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19893695510013486307211213 7460135816255057365204205)
            ·
              refine ⟨2797550931095646511951577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460135816255057365204205 2797550931095646511951577)
              ·
                refine ⟨2098163198321734883963683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797550931095646511951577 2098163198321734883963683)
                ·
                  refine ⟨3147244797482602325945525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098163198321734883963683 3147244797482602325945525)
                  ·
                    refine ⟨295054199763993968057393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3147244797482602325945525 295054199763993968057393)
                    ·
                      rfl

theorem cell22_861924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_861924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861924 prefixEnd_861924 := by exact prefixLift 861924
  have htrace : WordTrace (prefixWord ++ tailWord_861924) baseStart_861924 baseEnd_861924 := by
    simpa [prefixWord, tailWord_861924, baseEnd_861924] using wordTrace_append hprefix tailTrace_861924
  have hstable : (prefixWord ++ tailWord_861924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861924).length < 2 ^ (prefixWord ++ tailWord_861924).sum := by decide
  have hdescent : baseEnd_861924 < baseStart_861924 := by decide
  rcases family_descends (prefixWord ++ tailWord_861924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861928 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_861928 : Nat := 118140960795 + 861928 * 2 ^ 59
def prefixEnd_861928 : Nat := 4983230072969 + 3 ^ 40 * 861928 * 2
def baseEnd_861928 : Nat := 295055569045739290957381

theorem tailTrace_861928 : CollatzResearch.WordTrace tailWord_861928 prefixEnd_861928 295055569045739290957381 := by
  unfold tailWord_861928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718548410694768213937219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20958064547593024285249625 15718548410694768213937219)
  ·
    refine ⟨23577822616042152320905829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718548410694768213937219 23577822616042152320905829)
    ·
      refine ⟨4420841740507903560169843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23577822616042152320905829 4420841740507903560169843)
      ·
        refine ⟨6631262610761855340254765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420841740507903560169843 6631262610761855340254765)
        ·
          refine ⟨2486723479035695752595537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6631262610761855340254765 2486723479035695752595537)
          ·
            refine ⟨1865042609276771814446653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486723479035695752595537 1865042609276771814446653)
            ·
              refine ⟨699390978478789430417495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865042609276771814446653 699390978478789430417495)
              ·
                refine ⟨1049086467718184145626243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699390978478789430417495 1049086467718184145626243)
                ·
                  refine ⟨1573629701577276218439365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049086467718184145626243 1573629701577276218439365)
                  ·
                    refine ⟨295055569045739290957381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573629701577276218439365 295055569045739290957381)
                    ·
                      rfl

theorem cell22_861928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_861928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861928 prefixEnd_861928 := by exact prefixLift 861928
  have htrace : WordTrace (prefixWord ++ tailWord_861928) baseStart_861928 baseEnd_861928 := by
    simpa [prefixWord, tailWord_861928, baseEnd_861928] using wordTrace_append hprefix tailTrace_861928
  have hstable : (prefixWord ++ tailWord_861928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861928).length < 2 ^ (prefixWord ++ tailWord_861928).sum := by decide
  have hdescent : baseEnd_861928 < baseStart_861928 := by decide
  rcases family_descends (prefixWord ++ tailWord_861928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861937 : List Nat := [1, 2, 2, 2, 2, 13]
def baseStart_861937 : Nat := 118140960795 + 861937 * 2 ^ 59
def prefixEnd_861937 : Nat := 4983230072969 + 3 ^ 40 * 861937 * 2
def baseEnd_861937 : Nat := 3642699381847731697313

theorem tailTrace_861937 : CollatzResearch.WordTrace tailWord_861937 prefixEnd_861937 3642699381847731697313 := by
  unfold tailWord_861937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437425078356930964952065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20958283385571287309968043 31437425078356930964952065)
  ·
    refine ⟨23578068808767698223714049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31437425078356930964952065 23578068808767698223714049)
    ·
      refine ⟨17683551606575773667785537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23578068808767698223714049 17683551606575773667785537)
      ·
        refine ⟨13262663704931830250839153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17683551606575773667785537 13262663704931830250839153)
        ·
          refine ⟨9946997778698872688129365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13262663704931830250839153 9946997778698872688129365)
          ·
            refine ⟨3642699381847731697313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 9946997778698872688129365 3642699381847731697313)
            ·
              rfl

theorem cell22_861937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 13].length) (baseStart_861937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861937 prefixEnd_861937 := by exact prefixLift 861937
  have htrace : WordTrace (prefixWord ++ tailWord_861937) baseStart_861937 baseEnd_861937 := by
    simpa [prefixWord, tailWord_861937, baseEnd_861937] using wordTrace_append hprefix tailTrace_861937
  have hstable : (prefixWord ++ tailWord_861937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861937).length < 2 ^ (prefixWord ++ tailWord_861937).sum := by decide
  have hdescent : baseEnd_861937 < baseStart_861937 := by decide
  rcases family_descends (prefixWord ++ tailWord_861937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861939 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_861939 : Nat := 118140960795 + 861939 * 2 ^ 59
def prefixEnd_861939 : Nat := 4983230072969 + 3 ^ 40 * 861939 * 2
def baseEnd_861939 : Nat := 295059334570538928932347

theorem tailTrace_861939 : CollatzResearch.WordTrace tailWord_861939 prefixEnd_861939 295059334570538928932347 := by
  unfold tailWord_861939
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437498024349685306524871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20958332016233123537683247 31437498024349685306524871)
  ·
    refine ⟨47156247036524527959787307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31437498024349685306524871 47156247036524527959787307)
    ·
      refine ⟨70734370554786791939680961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47156247036524527959787307 70734370554786791939680961)
      ·
        refine ⟨53050777916090093954760721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70734370554786791939680961 53050777916090093954760721)
        ·
          refine ⟨39788083437067570466070541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53050777916090093954760721 39788083437067570466070541)
          ·
            refine ⟨14920531288900338924776453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39788083437067570466070541 14920531288900338924776453)
            ·
              refine ⟨2797599616668813548395585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14920531288900338924776453 2797599616668813548395585)
              ·
                refine ⟨2098199712501610161296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797599616668813548395585 2098199712501610161296689)
                ·
                  refine ⟨1573649784376207620972517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098199712501610161296689 1573649784376207620972517)
                  ·
                    refine ⟨295059334570538928932347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573649784376207620972517 295059334570538928932347)
                    ·
                      rfl

theorem cell22_861939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_861939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861939 prefixEnd_861939 := by exact prefixLift 861939
  have htrace : WordTrace (prefixWord ++ tailWord_861939) baseStart_861939 baseEnd_861939 := by
    simpa [prefixWord, tailWord_861939, baseEnd_861939] using wordTrace_append hprefix tailTrace_861939
  have hstable : (prefixWord ++ tailWord_861939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861939).length < 2 ^ (prefixWord ++ tailWord_861939).sum := by decide
  have hdescent : baseEnd_861939 < baseStart_861939 := by decide
  rcases family_descends (prefixWord ++ tailWord_861939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861986 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_861986 : Nat := 118140960795 + 861986 * 2 ^ 59
def prefixEnd_861986 : Nat := 4983230072969 + 3 ^ 40 * 861986 * 2
def baseEnd_861986 : Nat := 295075423631046473007203

theorem tailTrace_861986 : CollatzResearch.WordTrace tailWord_861986 prefixEnd_861986 295075423631046473007203 := by
  unfold tailWord_861986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859803063794853083371453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20959474836786274888990541 7859803063794853083371453)
  ·
    refine ⟨2947426148923069906264295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7859803063794853083371453 2947426148923069906264295)
    ·
      refine ⟨4421139223384604859396443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947426148923069906264295 4421139223384604859396443)
      ·
        refine ⟨6631708835076907289094665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421139223384604859396443 6631708835076907289094665)
        ·
          refine ⟨4973781626307680466820999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631708835076907289094665 4973781626307680466820999)
          ·
            refine ⟨7460672439461520700231499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973781626307680466820999 7460672439461520700231499)
            ·
              refine ⟨11191008659192281050347249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460672439461520700231499 11191008659192281050347249)
              ·
                refine ⟨8393256494394210787760437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11191008659192281050347249 8393256494394210787760437)
                ·
                  refine ⟨786867796349457261352541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8393256494394210787760437 786867796349457261352541)
                  ·
                    refine ⟨295075423631046473007203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786867796349457261352541 295075423631046473007203)
                    ·
                      rfl

theorem cell22_861986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_861986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_861986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_861986 prefixEnd_861986 := by exact prefixLift 861986
  have htrace : WordTrace (prefixWord ++ tailWord_861986) baseStart_861986 baseEnd_861986 := by
    simpa [prefixWord, tailWord_861986, baseEnd_861986] using wordTrace_append hprefix tailTrace_861986
  have hstable : (prefixWord ++ tailWord_861986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861986).length < 2 ^ (prefixWord ++ tailWord_861986).sum := by decide
  have hdescent : baseEnd_861986 < baseStart_861986 := by decide
  rcases family_descends (prefixWord ++ tailWord_861986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862003 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 3, 3]
def baseStart_862003 : Nat := 118140960795 + 862003 * 2 ^ 59
def prefixEnd_862003 : Nat := 4983230072969 + 3 ^ 40 * 862003 * 2
def baseEnd_862003 : Nat := 295081243078464095332151

theorem tailTrace_862003 : CollatzResearch.WordTrace tailWord_862003 prefixEnd_862003 295081243078464095332151 := by
  unfold tailWord_862003
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439832296117824236854663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20959888197411882824569775 31439832296117824236854663)
  ·
    refine ⟨47159748444176736355281995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31439832296117824236854663 47159748444176736355281995)
    ·
      refine ⟨70739622666265104532922993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47159748444176736355281995 70739622666265104532922993)
      ·
        refine ⟨53054716999698828399692245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70739622666265104532922993 53054716999698828399692245)
        ·
          refine ⟨1243469929680441290617787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53054716999698828399692245 1243469929680441290617787)
          ·
            refine ⟨1865204894520661935926681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243469929680441290617787 1865204894520661935926681)
            ·
              refine ⟨1398903670890496451945011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865204894520661935926681 1398903670890496451945011)
              ·
                refine ⟨2098355506335744677917517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398903670890496451945011 2098355506335744677917517)
                ·
                  refine ⟨786883314875904254219069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2098355506335744677917517 786883314875904254219069)
                  ·
                    refine ⟨295081243078464095332151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786883314875904254219069 295081243078464095332151)
                    ·
                      rfl

theorem cell22_862003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].length) (baseStart_862003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862003 prefixEnd_862003 := by exact prefixLift 862003
  have htrace : WordTrace (prefixWord ++ tailWord_862003) baseStart_862003 baseEnd_862003 := by
    simpa [prefixWord, tailWord_862003, baseEnd_862003] using wordTrace_append hprefix tailTrace_862003
  have hstable : (prefixWord ++ tailWord_862003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862003).length < 2 ^ (prefixWord ++ tailWord_862003).sum := by decide
  have hdescent : baseEnd_862003 < baseStart_862003 := by decide
  rcases family_descends (prefixWord ++ tailWord_862003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862061 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 6]
def baseStart_862061 : Nat := 118140960795 + 862061 * 2 ^ 59
def prefixEnd_862061 : Nat := 4983230072969 + 3 ^ 40 * 862061 * 2
def baseEnd_862061 : Nat := 98367032554590425793991

theorem tailTrace_862061 : CollatzResearch.WordTrace tailWord_862061 prefixEnd_862061 98367032554590425793991 := by
  unfold tailWord_862061
  simp only [CollatzResearch.WordTrace]
  refine ⟨31441947729907700142466037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20961298486605133428310691 31441947729907700142466037)
  ·
    refine ⟨2947682599678846888356191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31441947729907700142466037 2947682599678846888356191)
    ·
      refine ⟨4421523899518270332534287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947682599678846888356191 4421523899518270332534287)
      ·
        refine ⟨6632285849277405498801431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421523899518270332534287 6632285849277405498801431)
        ·
          refine ⟨9948428773916108248202147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632285849277405498801431 9948428773916108248202147)
          ·
            refine ⟨14922643160874162372303221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9948428773916108248202147 14922643160874162372303221)
            ·
              refine ⟨1398997796331952722403427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14922643160874162372303221 1398997796331952722403427)
              ·
                refine ⟨2098496694497929083605141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398997796331952722403427 2098496694497929083605141)
                ·
                  refine ⟨98367032554590425793991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2098496694497929083605141 98367032554590425793991)
                  ·
                    rfl

theorem cell22_862061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_862061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862061 prefixEnd_862061 := by exact prefixLift 862061
  have htrace : WordTrace (prefixWord ++ tailWord_862061) baseStart_862061 baseEnd_862061 := by
    simpa [prefixWord, tailWord_862061, baseEnd_862061] using wordTrace_append hprefix tailTrace_862061
  have hstable : (prefixWord ++ tailWord_862061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862061).length < 2 ^ (prefixWord ++ tailWord_862061).sum := by decide
  have hdescent : baseEnd_862061 < baseStart_862061 := by decide
  rcases family_descends (prefixWord ++ tailWord_862061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862074 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_862074 : Nat := 118140960795 + 862074 * 2 ^ 59
def prefixEnd_862074 : Nat := 4983230072969 + 3 ^ 40 * 862074 * 2
def baseEnd_862074 : Nat := 295105547829443576806933

theorem tailTrace_862074 : CollatzResearch.WordTrace tailWord_862074 prefixEnd_862074 295105547829443576806933 := by
  unfold tailWord_862074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860605469715150840672319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20961614585907068908459517 7860605469715150840672319)
  ·
    refine ⟨11790908204572726261008479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7860605469715150840672319 11790908204572726261008479)
    ·
      refine ⟨17686362306859089391512719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790908204572726261008479 17686362306859089391512719)
      ·
        refine ⟨26529543460288634087269079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17686362306859089391512719 26529543460288634087269079)
        ·
          refine ⟨39794315190432951130903619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26529543460288634087269079 39794315190432951130903619)
          ·
            refine ⟨59691472785649426696355429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794315190432951130903619 59691472785649426696355429)
            ·
              refine ⟨11192151147309267505566643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59691472785649426696355429 11192151147309267505566643)
              ·
                refine ⟨16788226720963901258349965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192151147309267505566643 16788226720963901258349965)
                ·
                  refine ⟨6295585020361462971881237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16788226720963901258349965 6295585020361462971881237)
                  ·
                    refine ⟨295105547829443576806933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6295585020361462971881237 295105547829443576806933)
                    ·
                      rfl

theorem cell22_862074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_862074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862074 prefixEnd_862074 := by exact prefixLift 862074
  have htrace : WordTrace (prefixWord ++ tailWord_862074) baseStart_862074 baseEnd_862074 := by
    simpa [prefixWord, tailWord_862074, baseEnd_862074] using wordTrace_append hprefix tailTrace_862074
  have hstable : (prefixWord ++ tailWord_862074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862074).length < 2 ^ (prefixWord ++ tailWord_862074).sum := by decide
  have hdescent : baseEnd_862074 < baseStart_862074 := by decide
  rcases family_descends (prefixWord ++ tailWord_862074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862089 : List Nat := [1, 2, 1, 1, 5, 1, 1, 10]
def baseStart_862089 : Nat := 118140960795 + 862089 * 2 ^ 59
def prefixEnd_862089 : Nat := 4983230072969 + 3 ^ 40 * 862089 * 2
def baseEnd_862089 : Nat := 32790075848443170853543

theorem tailTrace_862089 : CollatzResearch.WordTrace tailWord_862089 prefixEnd_862089 32790075848443170853543 := by
  unfold tailWord_862089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31442968973806260924485321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20961979315870840616323547 31442968973806260924485321)
  ·
    refine ⟨23582226730354695693363991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31442968973806260924485321 23582226730354695693363991)
    ·
      refine ⟨35373340095532043540045987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23582226730354695693363991 35373340095532043540045987)
      ·
        refine ⟨53060010143298065310068981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35373340095532043540045987 53060010143298065310068981)
        ·
          refine ⟨4974375950934193622818967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53060010143298065310068981 4974375950934193622818967)
          ·
            refine ⟨7461563926401290434228451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974375950934193622818967 7461563926401290434228451)
            ·
              refine ⟨11192345889601935651342677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461563926401290434228451 11192345889601935651342677)
              ·
                refine ⟨32790075848443170853543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11192345889601935651342677 32790075848443170853543)
                ·
                  rfl

theorem cell22_862089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 10].length) (baseStart_862089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862089 prefixEnd_862089 := by exact prefixLift 862089
  have htrace : WordTrace (prefixWord ++ tailWord_862089) baseStart_862089 baseEnd_862089 := by
    simpa [prefixWord, tailWord_862089, baseEnd_862089] using wordTrace_append hprefix tailTrace_862089
  have hstable : (prefixWord ++ tailWord_862089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862089).length < 2 ^ (prefixWord ++ tailWord_862089).sum := by decide
  have hdescent : baseEnd_862089 < baseStart_862089 := by decide
  rcases family_descends (prefixWord ++ tailWord_862089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862108 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_862108 : Nat := 118140960795 + 862108 * 2 ^ 59
def prefixEnd_862108 : Nat := 4983230072969 + 3 ^ 40 * 862108 * 2
def baseEnd_862108 : Nat := 295117186724278821456829

theorem tailTrace_862108 : CollatzResearch.WordTrace tailWord_862108 prefixEnd_862108 295117186724278821456829 := by
  unfold tailWord_862108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721830980368713584713489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20962441307158284779617985 15721830980368713584713489)
  ·
    refine ⟨11791373235276535188535117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15721830980368713584713489 11791373235276535188535117)
    ·
      refine ⟨4421764963228700695700669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11791373235276535188535117 4421764963228700695700669)
      ·
        refine ⟨1658161861210762760887751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4421764963228700695700669 1658161861210762760887751)
        ·
          refine ⟨2487242791816144141331627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658161861210762760887751 2487242791816144141331627)
          ·
            refine ⟨3730864187724216211997441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487242791816144141331627 3730864187724216211997441)
            ·
              refine ⟨2798148140793162158998081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730864187724216211997441 2798148140793162158998081)
              ·
                refine ⟨2098611105594871619248561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798148140793162158998081 2098611105594871619248561)
                ·
                  refine ⟨1573958329196153714436421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098611105594871619248561 1573958329196153714436421)
                  ·
                    refine ⟨295117186724278821456829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573958329196153714436421 295117186724278821456829)
                    ·
                      rfl

theorem cell22_862108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_862108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862108 prefixEnd_862108 := by exact prefixLift 862108
  have htrace : WordTrace (prefixWord ++ tailWord_862108) baseStart_862108 baseEnd_862108 := by
    simpa [prefixWord, tailWord_862108, baseEnd_862108] using wordTrace_append hprefix tailTrace_862108
  have hstable : (prefixWord ++ tailWord_862108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862108).length < 2 ^ (prefixWord ++ tailWord_862108).sum := by decide
  have hdescent : baseEnd_862108 < baseStart_862108 := by decide
  rcases family_descends (prefixWord ++ tailWord_862108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862140 : List Nat := [2, 2, 2, 5, 1, 1, 3, 6]
def baseStart_862140 : Nat := 118140960795 + 862140 * 2 ^ 59
def prefixEnd_862140 : Nat := 4983230072969 + 3 ^ 40 * 862140 * 2
def baseEnd_862140 : Nat := 32792015664249044961859

theorem tailTrace_862140 : CollatzResearch.WordTrace tailWord_862140 prefixEnd_862140 32792015664249044961859 := by
  unfold tailWord_862140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722414548310748317295937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20963219397747664423061249 15722414548310748317295937)
  ·
    refine ⟨11791810911233061237971953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15722414548310748317295937 11791810911233061237971953)
    ·
      refine ⟨8843858183424795928478965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11791810911233061237971953 8843858183424795928478965)
      ·
        refine ⟨829111704696074618294903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8843858183424795928478965 829111704696074618294903)
        ·
          refine ⟨1243667557044111927442355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829111704696074618294903 1243667557044111927442355)
          ·
            refine ⟨1865501335566167891163533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243667557044111927442355 1865501335566167891163533)
            ·
              refine ⟨699563000837312959186325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865501335566167891163533 699563000837312959186325)
              ·
                refine ⟨32792015664249044961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 699563000837312959186325 32792015664249044961859)
                ·
                  rfl

theorem cell22_862140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_862140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862140 prefixEnd_862140 := by exact prefixLift 862140
  have htrace : WordTrace (prefixWord ++ tailWord_862140) baseStart_862140 baseEnd_862140 := by
    simpa [prefixWord, tailWord_862140, baseEnd_862140] using wordTrace_append hprefix tailTrace_862140
  have hstable : (prefixWord ++ tailWord_862140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862140).length < 2 ^ (prefixWord ++ tailWord_862140).sum := by decide
  have hdescent : baseEnd_862140 < baseStart_862140 := by decide
  rcases family_descends (prefixWord ++ tailWord_862140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862155 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 1, 3]
def baseStart_862155 : Nat := 118140960795 + 862155 * 2 ^ 59
def prefixEnd_862155 : Nat := 4983230072969 + 3 ^ 40 * 862155 * 2
def baseEnd_862155 : Nat := 295133275784786365531685

theorem tailTrace_862155 : CollatzResearch.WordTrace tailWord_862155 prefixEnd_862155 295133275784786365531685 := by
  unfold tailWord_862155
  simp only [CollatzResearch.WordTrace]
  refine ⟨31445376191567154196387919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20963584127711436130925279 31445376191567154196387919)
  ·
    refine ⟨47168064287350731294581879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31445376191567154196387919 47168064287350731294581879)
    ·
      refine ⟨70752096431026096941872819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47168064287350731294581879 70752096431026096941872819)
      ·
        refine ⟨106128144646539145412809229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70752096431026096941872819 106128144646539145412809229)
        ·
          refine ⟨39798054242452179529803461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106128144646539145412809229 39798054242452179529803461)
          ·
            refine ⟨7462135170459783661838149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39798054242452179529803461 7462135170459783661838149)
            ·
              refine ⟨1399150344461209436594653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7462135170459783661838149 1399150344461209436594653)
              ·
                refine ⟨524681379172953538722995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399150344461209436594653 524681379172953538722995)
                ·
                  refine ⟨787022068759430308084493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524681379172953538722995 787022068759430308084493)
                  ·
                    refine ⟨295133275784786365531685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787022068759430308084493 295133275784786365531685)
                    ·
                      rfl

theorem cell22_862155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 3].length) (baseStart_862155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862155 prefixEnd_862155 := by exact prefixLift 862155
  have htrace : WordTrace (prefixWord ++ tailWord_862155) baseStart_862155 baseEnd_862155 := by
    simpa [prefixWord, tailWord_862155, baseEnd_862155] using wordTrace_append hprefix tailTrace_862155
  have hstable : (prefixWord ++ tailWord_862155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862155).length < 2 ^ (prefixWord ++ tailWord_862155).sum := by decide
  have hdescent : baseEnd_862155 < baseStart_862155 := by decide
  rcases family_descends (prefixWord ++ tailWord_862155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862211 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_862211 : Nat := 118140960795 + 862211 * 2 ^ 59
def prefixEnd_862211 : Nat := 4983230072969 + 3 ^ 40 * 862211 * 2
def baseEnd_862211 : Nat := 295152445729220886131513

theorem tailTrace_862211 : CollatzResearch.WordTrace tailWord_862211 prefixEnd_862211 295152445729220886131513 := by
  unfold tailWord_862211
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447418679364275760426487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964945786242850506950991 31447418679364275760426487)
  ·
    refine ⟨47171128019046413640639731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31447418679364275760426487 47171128019046413640639731)
    ·
      refine ⟨70756692028569620460959597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47171128019046413640639731 70756692028569620460959597)
      ·
        refine ⟨26533759510713607672859849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70756692028569620460959597 26533759510713607672859849)
        ·
          refine ⟨19900319633035205754644887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26533759510713607672859849 19900319633035205754644887)
          ·
            refine ⟨29850479449552808631967331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19900319633035205754644887 29850479449552808631967331)
            ·
              refine ⟨44775719174329212947950997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29850479449552808631967331 44775719174329212947950997)
              ·
                refine ⟨2098861836296681856935203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44775719174329212947950997 2098861836296681856935203)
                ·
                  refine ⟨3148292754445022785402805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098861836296681856935203 3148292754445022785402805)
                  ·
                    refine ⟨295152445729220886131513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3148292754445022785402805 295152445729220886131513)
                    ·
                      rfl

theorem cell22_862211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_862211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862211 prefixEnd_862211 := by exact prefixLift 862211
  have htrace : WordTrace (prefixWord ++ tailWord_862211) baseStart_862211 baseEnd_862211 := by
    simpa [prefixWord, tailWord_862211, baseEnd_862211] using wordTrace_append hprefix tailTrace_862211
  have hstable : (prefixWord ++ tailWord_862211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862211).length < 2 ^ (prefixWord ++ tailWord_862211).sum := by decide
  have hdescent : baseEnd_862211 < baseStart_862211 := by decide
  rcases family_descends (prefixWord ++ tailWord_862211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862245 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_862245 : Nat := 118140960795 + 862245 * 2 ^ 59
def prefixEnd_862245 : Nat := 4983230072969 + 3 ^ 40 * 862245 * 2
def baseEnd_862245 : Nat := 295164084624056130781409

theorem tailTrace_862245 : CollatzResearch.WordTrace tailWord_862245 prefixEnd_862245 295164084624056130781409 := by
  unfold tailWord_862245
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448658761241099567164189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20965772507494066378109459 31448658761241099567164189)
  ·
    refine ⟨11793247035465412337686571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31448658761241099567164189 11793247035465412337686571)
    ·
      refine ⟨17689870553198118506529857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793247035465412337686571 17689870553198118506529857)
      ·
        refine ⟨13267402914898588879897393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17689870553198118506529857 13267402914898588879897393)
        ·
          refine ⟨9950552186173941659923045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267402914898588879897393 9950552186173941659923045)
          ·
            refine ⟨1865728534907614061235571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9950552186173941659923045 1865728534907614061235571)
            ·
              refine ⟨2798592802361421091853357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865728534907614061235571 2798592802361421091853357)
              ·
                refine ⟨1049472300885532909445009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2798592802361421091853357 1049472300885532909445009)
                ·
                  refine ⟨787104225664149682083757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049472300885532909445009 787104225664149682083757)
                  ·
                    refine ⟨295164084624056130781409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787104225664149682083757 295164084624056130781409)
                    ·
                      rfl

theorem cell22_862245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_862245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862245 prefixEnd_862245 := by exact prefixLift 862245
  have htrace : WordTrace (prefixWord ++ tailWord_862245) baseStart_862245 baseEnd_862245 := by
    simpa [prefixWord, tailWord_862245, baseEnd_862245] using wordTrace_append hprefix tailTrace_862245
  have hstable : (prefixWord ++ tailWord_862245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862245).length < 2 ^ (prefixWord ++ tailWord_862245).sum := by decide
  have hdescent : baseEnd_862245 < baseStart_862245 := by decide
  rcases family_descends (prefixWord ++ tailWord_862245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862318 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_862318 : Nat := 118140960795 + 862318 * 2 ^ 59
def prefixEnd_862318 : Nat := 4983230072969 + 3 ^ 40 * 862318 * 2
def baseEnd_862318 : Nat := 295189074015908273706185

theorem tailTrace_862318 : CollatzResearch.WordTrace tailWord_862318 prefixEnd_862318 295189074015908273706185 := by
  unfold tailWord_862318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931415161247079129321451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20967547526651088689714405 3931415161247079129321451)
  ·
    refine ⟨5897122741870618693982177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931415161247079129321451 5897122741870618693982177)
    ·
      refine ⟨4422842056402964020486633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5897122741870618693982177 4422842056402964020486633)
      ·
        refine ⟨3317131542302223015364975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4422842056402964020486633 3317131542302223015364975)
        ·
          refine ⟨4975697313453334523047463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317131542302223015364975 4975697313453334523047463)
          ·
            refine ⟨7463545970180001784571195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975697313453334523047463 7463545970180001784571195)
            ·
              refine ⟨11195318955270002676856793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463545970180001784571195 11195318955270002676856793)
              ·
                refine ⟨8396489216452502007642595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195318955270002676856793 8396489216452502007642595)
                ·
                  refine ⟨12594733824678753011463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396489216452502007642595 12594733824678753011463893)
                  ·
                    refine ⟨295189074015908273706185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12594733824678753011463893 295189074015908273706185)
                    ·
                      rfl

theorem cell22_862318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_862318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862318 prefixEnd_862318 := by exact prefixLift 862318
  have htrace : WordTrace (prefixWord ++ tailWord_862318) baseStart_862318 baseEnd_862318 := by
    simpa [prefixWord, tailWord_862318, baseEnd_862318] using wordTrace_append hprefix tailTrace_862318
  have hstable : (prefixWord ++ tailWord_862318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862318).length < 2 ^ (prefixWord ++ tailWord_862318).sum := by decide
  have hdescent : baseEnd_862318 < baseStart_862318 := by decide
  rcases family_descends (prefixWord ++ tailWord_862318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862337 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 5]
def baseStart_862337 : Nat := 118140960795 + 862337 * 2 ^ 59
def prefixEnd_862337 : Nat := 4983230072969 + 3 ^ 40 * 862337 * 2
def baseEnd_862337 : Nat := 98398526034732852493709

theorem tailTrace_862337 : CollatzResearch.WordTrace tailWord_862337 prefixEnd_862337 98398526034732852493709 := by
  unfold tailWord_862337
  simp only [CollatzResearch.WordTrace]
  refine ⟨31452014276907799279513265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20968009517938532853008843 31452014276907799279513265)
  ·
    refine ⟨23589010707680849459634949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31452014276907799279513265 23589010707680849459634949)
    ·
      refine ⟨4422939507690159273681553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23589010707680849459634949 4422939507690159273681553)
      ·
        refine ⟨3317204630767619455261165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4422939507690159273681553 3317204630767619455261165)
        ·
          refine ⟨1243951736537857295722937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3317204630767619455261165 1243951736537857295722937)
          ·
            refine ⟨932963802403392971792203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243951736537857295722937 932963802403392971792203)
            ·
              refine ⟨1399445703605089457688305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932963802403392971792203 1399445703605089457688305)
              ·
                refine ⟨1049584277703817093266229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399445703605089457688305 1049584277703817093266229)
                ·
                  refine ⟨98398526034732852493709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1049584277703817093266229 98398526034732852493709)
                  ·
                    rfl

theorem cell22_862337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_862337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862337 prefixEnd_862337 := by exact prefixLift 862337
  have htrace : WordTrace (prefixWord ++ tailWord_862337) baseStart_862337 baseEnd_862337 := by
    simpa [prefixWord, tailWord_862337, baseEnd_862337] using wordTrace_append hprefix tailTrace_862337
  have hstable : (prefixWord ++ tailWord_862337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862337).length < 2 ^ (prefixWord ++ tailWord_862337).sum := by decide
  have hdescent : baseEnd_862337 < baseStart_862337 := by decide
  rcases family_descends (prefixWord ++ tailWord_862337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862367 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 1, 4]
def baseStart_862367 : Nat := 118140960795 + 862367 * 2 ^ 59
def prefixEnd_862367 : Nat := 4983230072969 + 3 ^ 40 * 862367 * 2
def baseEnd_862367 : Nat := 295205847717288479231035

theorem tailTrace_862367 : CollatzResearch.WordTrace tailWord_862367 prefixEnd_862367 295205847717288479231035 := by
  unfold tailWord_862367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31453108466799114403105355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20968738977866076268736903 31453108466799114403105355)
  ·
    refine ⟨47179662700198671604658033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31453108466799114403105355 47179662700198671604658033)
    ·
      refine ⟨35384747025149003703493525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47179662700198671604658033 35384747025149003703493525)
      ·
        refine ⟨1658660016803859548601259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35384747025149003703493525 1658660016803859548601259)
        ·
          refine ⟨2487990025205789322901889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658660016803859548601259 2487990025205789322901889)
          ·
            refine ⟨1865992518904341992176417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487990025205789322901889 1865992518904341992176417)
            ·
              refine ⟨1399494389178256494132313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865992518904341992176417 1399494389178256494132313)
              ·
                refine ⟨1049620791883692370599235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399494389178256494132313 1049620791883692370599235)
                ·
                  refine ⟨1574431187825538555898853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049620791883692370599235 1574431187825538555898853)
                  ·
                    refine ⟨295205847717288479231035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574431187825538555898853 295205847717288479231035)
                    ·
                      rfl

theorem cell22_862367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_862367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862367 prefixEnd_862367 := by exact prefixLift 862367
  have htrace : WordTrace (prefixWord ++ tailWord_862367) baseStart_862367 baseEnd_862367 := by
    simpa [prefixWord, tailWord_862367, baseEnd_862367] using wordTrace_append hprefix tailTrace_862367
  have hstable : (prefixWord ++ tailWord_862367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862367).length < 2 ^ (prefixWord ++ tailWord_862367).sum := by decide
  have hdescent : baseEnd_862367 < baseStart_862367 := by decide
  rcases family_descends (prefixWord ++ tailWord_862367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862414 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_862414 : Nat := 118140960795 + 862414 * 2 ^ 59
def prefixEnd_862414 : Nat := 4983230072969 + 3 ^ 40 * 862414 * 2
def baseEnd_862414 : Nat := 295221936777796023305891

theorem tailTrace_862414 : CollatzResearch.WordTrace tailWord_862414 prefixEnd_862414 295221936777796023305891 := by
  unfold tailWord_862414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931852837203605178758287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20969881798419227620044197 3931852837203605178758287)
  ·
    refine ⟨5897779255805407768137431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931852837203605178758287 5897779255805407768137431)
    ·
      refine ⟨8846668883708111652206147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5897779255805407768137431 8846668883708111652206147)
      ·
        refine ⟨13270003325562167478309221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8846668883708111652206147 13270003325562167478309221)
        ·
          refine ⟨2488125623542906402182979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13270003325562167478309221 2488125623542906402182979)
          ·
            refine ⟨3732188435314359603274469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488125623542906402182979 3732188435314359603274469)
            ·
              refine ⟨699785331621442425613963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3732188435314359603274469 699785331621442425613963)
              ·
                refine ⟨1049677997432163638420945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699785331621442425613963 1049677997432163638420945)
                ·
                  refine ⟨787258498074122728815709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049677997432163638420945 787258498074122728815709)
                  ·
                    refine ⟨295221936777796023305891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787258498074122728815709 295221936777796023305891)
                    ·
                      rfl

theorem cell22_862414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_862414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862414 prefixEnd_862414 := by exact prefixLift 862414
  have htrace : WordTrace (prefixWord ++ tailWord_862414) baseStart_862414 baseEnd_862414 := by
    simpa [prefixWord, tailWord_862414, baseEnd_862414] using wordTrace_append hprefix tailTrace_862414
  have hstable : (prefixWord ++ tailWord_862414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862414).length < 2 ^ (prefixWord ++ tailWord_862414).sum := by decide
  have hdescent : baseEnd_862414 < baseStart_862414 := by decide
  rcases family_descends (prefixWord ++ tailWord_862414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862425 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_862425 : Nat := 118140960795 + 862425 * 2 ^ 59
def prefixEnd_862425 : Nat := 4983230072969 + 3 ^ 40 * 862425 * 2
def baseEnd_862425 : Nat := 295225702302595661280857

theorem tailTrace_862425 : CollatzResearch.WordTrace tailWord_862425 prefixEnd_862425 295225702302595661280857 := by
  unfold tailWord_862425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455223900588990308716729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20970149267059326872477819 31455223900588990308716729)
  ·
    refine ⟨23591417925441742731537547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31455223900588990308716729 23591417925441742731537547)
    ·
      refine ⟨35387126888162614097306321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23591417925441742731537547 35387126888162614097306321)
      ·
        refine ⟨26540345166121960572979741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35387126888162614097306321 26540345166121960572979741)
        ·
          refine ⟨9952629437295735214867403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26540345166121960572979741 9952629437295735214867403)
          ·
            refine ⟨14928944155943602822301105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952629437295735214867403 14928944155943602822301105)
            ·
              refine ⟨11196708116957702116725829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14928944155943602822301105 11196708116957702116725829)
              ·
                refine ⟨2099382771929569146886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11196708116957702116725829 2099382771929569146886093)
                ·
                  refine ⟨787268539473588430082285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2099382771929569146886093 787268539473588430082285)
                  ·
                    refine ⟨295225702302595661280857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787268539473588430082285 295225702302595661280857)
                    ·
                      rfl

theorem cell22_862425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_862425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862425 prefixEnd_862425 := by exact prefixLift 862425
  have htrace : WordTrace (prefixWord ++ tailWord_862425) baseStart_862425 baseEnd_862425 := by
    simpa [prefixWord, tailWord_862425, baseEnd_862425] using wordTrace_append hprefix tailTrace_862425
  have hstable : (prefixWord ++ tailWord_862425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862425).length < 2 ^ (prefixWord ++ tailWord_862425).sum := by decide
  have hdescent : baseEnd_862425 < baseStart_862425 := by decide
  rcases family_descends (prefixWord ++ tailWord_862425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862485 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_862485 : Nat := 118140960795 + 862485 * 2 ^ 59
def prefixEnd_862485 : Nat := 4983230072969 + 3 ^ 40 * 862485 * 2
def baseEnd_862485 : Nat := 295246241528775504780673

theorem tailTrace_862485 : CollatzResearch.WordTrace tailWord_862485 prefixEnd_862485 295246241528775504780673 := by
  unfold tailWord_862485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457412280371620555900909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20971608186914413703933939 31457412280371620555900909)
  ·
    refine ⟨11796529605139357708462841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31457412280371620555900909 11796529605139357708462841)
    ·
      refine ⟨8847397203854518281347131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11796529605139357708462841 8847397203854518281347131)
      ·
        refine ⟨13271095805781777422020697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847397203854518281347131 13271095805781777422020697)
        ·
          refine ⟨9953321854336333066515523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13271095805781777422020697 9953321854336333066515523)
          ·
            refine ⟨14929982781504499599773285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9953321854336333066515523 14929982781504499599773285)
            ·
              refine ⟨2799371771532093674957491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14929982781504499599773285 2799371771532093674957491)
              ·
                refine ⟨4199057657298140512436237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799371771532093674957491 4199057657298140512436237)
                ·
                  refine ⟨1574646621486802692163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4199057657298140512436237 1574646621486802692163589)
                  ·
                    refine ⟨295246241528775504780673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574646621486802692163589 295246241528775504780673)
                    ·
                      rfl

theorem cell22_862485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_862485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862485 prefixEnd_862485 := by exact prefixLift 862485
  have htrace : WordTrace (prefixWord ++ tailWord_862485) baseStart_862485 baseEnd_862485 := by
    simpa [prefixWord, tailWord_862485, baseEnd_862485] using wordTrace_append hprefix tailTrace_862485
  have hstable : (prefixWord ++ tailWord_862485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862485).length < 2 ^ (prefixWord ++ tailWord_862485).sum := by decide
  have hdescent : baseEnd_862485 < baseStart_862485 := by decide
  rcases family_descends (prefixWord ++ tailWord_862485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862506 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_862506 : Nat := 118140960795 + 862506 * 2 ^ 59
def prefixEnd_862506 : Nat := 4983230072969 + 3 ^ 40 * 862506 * 2
def baseEnd_862506 : Nat := 98417810085979483335203

theorem tailTrace_862506 : CollatzResearch.WordTrace tailWord_862506 prefixEnd_862506 98417810085979483335203 := by
  unfold tailWord_862506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7864544553323885285603843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20972118808863694094943581 7864544553323885285603843)
  ·
    refine ⟨11796816829985827928405765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7864544553323885285603843 11796816829985827928405765)
    ·
      refine ⟨2211903155622342736576081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11796816829985827928405765 2211903155622342736576081)
      ·
        refine ⟨1658927366716757052432061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211903155622342736576081 1658927366716757052432061)
        ·
          refine ⟨622097762518783894662023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1658927366716757052432061 622097762518783894662023)
          ·
            refine ⟨933146643778175841993035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622097762518783894662023 933146643778175841993035)
            ·
              refine ⟨1399719965667263762989553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933146643778175841993035 1399719965667263762989553)
              ·
                refine ⟨1049789974250447822242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399719965667263762989553 1049789974250447822242165)
                ·
                  refine ⟨98417810085979483335203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1049789974250447822242165 98417810085979483335203)
                  ·
                    rfl

theorem cell22_862506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_862506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862506 prefixEnd_862506 := by exact prefixLift 862506
  have htrace : WordTrace (prefixWord ++ tailWord_862506) baseStart_862506 baseEnd_862506 := by
    simpa [prefixWord, tailWord_862506, baseEnd_862506] using wordTrace_append hprefix tailTrace_862506
  have hstable : (prefixWord ++ tailWord_862506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862506).length < 2 ^ (prefixWord ++ tailWord_862506).sum := by decide
  have hdescent : baseEnd_862506 < baseStart_862506 := by decide
  rcases family_descends (prefixWord ++ tailWord_862506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862517 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 4]
def baseStart_862517 : Nat := 118140960795 + 862517 * 2 ^ 59
def prefixEnd_862517 : Nat := 4983230072969 + 3 ^ 40 * 862517 * 2
def baseEnd_862517 : Nat := 98419065260912695993525

theorem tailTrace_862517 : CollatzResearch.WordTrace tailWord_862517 prefixEnd_862517 98419065260912695993525 := by
  unfold tailWord_862517
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458579416255690021065805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20972386277503793347377203 31458579416255690021065805)
  ·
    refine ⟨11796967281095883757899677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31458579416255690021065805 11796967281095883757899677)
    ·
      refine ⟨4423862730410956409212379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11796967281095883757899677 4423862730410956409212379)
      ·
        refine ⟨6635794095616434613818569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423862730410956409212379 6635794095616434613818569)
        ·
          refine ⟨4976845571712325960363927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635794095616434613818569 4976845571712325960363927)
          ·
            refine ⟨7465268357568488940545891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976845571712325960363927 7465268357568488940545891)
            ·
              refine ⟨11197902536352733410818837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465268357568488940545891 11197902536352733410818837)
              ·
                refine ⟨524901681391534378632133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11197902536352733410818837 524901681391534378632133)
                ·
                  refine ⟨98419065260912695993525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524901681391534378632133 98419065260912695993525)
                  ·
                    rfl

theorem cell22_862517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_862517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862517 prefixEnd_862517 := by exact prefixLift 862517
  have htrace : WordTrace (prefixWord ++ tailWord_862517) baseStart_862517 baseEnd_862517 := by
    simpa [prefixWord, tailWord_862517, baseEnd_862517] using wordTrace_append hprefix tailTrace_862517
  have hstable : (prefixWord ++ tailWord_862517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862517).length < 2 ^ (prefixWord ++ tailWord_862517).sum := by decide
  have hdescent : baseEnd_862517 < baseStart_862517 := by decide
  rcases family_descends (prefixWord ++ tailWord_862517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862545 : List Nat := [1, 2, 2, 1, 4, 3, 1, 8]
def baseStart_862545 : Nat := 118140960795 + 862545 * 2 ^ 59
def prefixEnd_862545 : Nat := 4983230072969 + 3 ^ 40 * 862545 * 2
def baseEnd_862545 : Nat := 32807420083883927586721

theorem tailTrace_862545 : CollatzResearch.WordTrace tailWord_862545 prefixEnd_862545 32807420083883927586721 := by
  unfold tailWord_862545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31459600660154250803085089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20973067106769500535390059 31459600660154250803085089)
  ·
    refine ⟨23594700495115688102313817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31459600660154250803085089 23594700495115688102313817)
    ·
      refine ⟨17696025371336766076735363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23594700495115688102313817 17696025371336766076735363)
      ·
        refine ⟨26544038057005149115103045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17696025371336766076735363 26544038057005149115103045)
        ·
          refine ⟨4977007135688465459081821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26544038057005149115103045 4977007135688465459081821)
          ·
            refine ⟨1866377675883174547155683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4977007135688465459081821 1866377675883174547155683)
            ·
              refine ⟨2799566513824761820733525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866377675883174547155683 2799566513824761820733525)
              ·
                refine ⟨32807420083883927586721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2799566513824761820733525 32807420083883927586721)
                ·
                  rfl

theorem cell22_862545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 8].length) (baseStart_862545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862545 prefixEnd_862545 := by exact prefixLift 862545
  have htrace : WordTrace (prefixWord ++ tailWord_862545) baseStart_862545 baseEnd_862545 := by
    simpa [prefixWord, tailWord_862545, baseEnd_862545] using wordTrace_append hprefix tailTrace_862545
  have hstable : (prefixWord ++ tailWord_862545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862545).length < 2 ^ (prefixWord ++ tailWord_862545).sum := by decide
  have hdescent : baseEnd_862545 < baseStart_862545 := by decide
  rcases family_descends (prefixWord ++ tailWord_862545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862562 : List Nat := [3, 3, 2, 1, 1, 4, 8]
def baseStart_862562 : Nat := 118140960795 + 862562 * 2 ^ 59
def prefixEnd_862562 : Nat := 4983230072969 + 3 ^ 40 * 862562 * 2
def baseEnd_862562 : Nat := 10936022229717517429831

theorem tailTrace_862562 : CollatzResearch.WordTrace tailWord_862562 prefixEnd_862562 10936022229717517429831 := by
  unfold tailWord_862562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865055175273165676613485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20973480467395108470969293 7865055175273165676613485)
  ·
    refine ⟨2949395690727437128730057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7865055175273165676613485 2949395690727437128730057)
    ·
      refine ⟨2212046768045577846547543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2949395690727437128730057 2212046768045577846547543)
      ·
        refine ⟨3318070152068366769821315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212046768045577846547543 3318070152068366769821315)
        ·
          refine ⟨4977105228102550154731973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318070152068366769821315 4977105228102550154731973)
          ·
            refine ⟨933207230269228154012245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4977105228102550154731973 933207230269228154012245)
            ·
              refine ⟨10936022229717517429831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 933207230269228154012245 10936022229717517429831)
              ·
                rfl

theorem cell22_862562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 8].length) (baseStart_862562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862562 prefixEnd_862562 := by exact prefixLift 862562
  have htrace : WordTrace (prefixWord ++ tailWord_862562) baseStart_862562 baseEnd_862562 := by
    simpa [prefixWord, tailWord_862562, baseEnd_862562] using wordTrace_append hprefix tailTrace_862562
  have hstable : (prefixWord ++ tailWord_862562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862562).length < 2 ^ (prefixWord ++ tailWord_862562).sum := by decide
  have hdescent : baseEnd_862562 < baseStart_862562 := by decide
  rcases family_descends (prefixWord ++ tailWord_862562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862652 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_862652 : Nat := 118140960795 + 862652 * 2 ^ 59
def prefixEnd_862652 : Nat := 4983230072969 + 3 ^ 40 * 862652 * 2
def baseEnd_862652 : Nat := 98434469680547578618387

theorem tailTrace_862652 : CollatzResearch.WordTrace tailWord_862652 prefixEnd_862652 98434469680547578618387 := by
  unfold tailWord_862652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731751635383304038615105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20975668847177738718153473 15731751635383304038615105)
  ·
    refine ⟨11798813726537478028961329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15731751635383304038615105 11798813726537478028961329)
    ·
      refine ⟨8849110294903108521720997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11798813726537478028961329 8849110294903108521720997)
      ·
        refine ⟨1659208180294332847822687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8849110294903108521720997 1659208180294332847822687)
        ·
          refine ⟨2488812270441499271734031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659208180294332847822687 2488812270441499271734031)
          ·
            refine ⟨3733218405662248907601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488812270441499271734031 3733218405662248907601047)
            ·
              refine ⟨5599827608493373361401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733218405662248907601047 5599827608493373361401571)
              ·
                refine ⟨8399741412740060042102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599827608493373361401571 8399741412740060042102357)
                ·
                  refine ⟨98434469680547578618387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8399741412740060042102357 98434469680547578618387)
                  ·
                    rfl

theorem cell22_862652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_862652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862652 prefixEnd_862652 := by exact prefixLift 862652
  have htrace : WordTrace (prefixWord ++ tailWord_862652) baseStart_862652 baseEnd_862652 := by
    simpa [prefixWord, tailWord_862652, baseEnd_862652] using wordTrace_append hprefix tailTrace_862652
  have hstable : (prefixWord ++ tailWord_862652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862652).length < 2 ^ (prefixWord ++ tailWord_862652).sum := by decide
  have hdescent : baseEnd_862652 < baseStart_862652 := by decide
  rcases family_descends (prefixWord ++ tailWord_862652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862667 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 4, 3]
def baseStart_862667 : Nat := 118140960795 + 862667 * 2 ^ 59
def prefixEnd_862667 : Nat := 4983230072969 + 3 ^ 40 * 862667 * 2
def baseEnd_862667 : Nat := 295308543848187696730115

theorem tailTrace_862667 : CollatzResearch.WordTrace tailWord_862667 prefixEnd_862667 295308543848187696730115 := by
  unfold tailWord_862667
  simp only [CollatzResearch.WordTrace]
  refine ⟨31464050365712265639026255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20976033577141510426017503 31464050365712265639026255)
  ·
    refine ⟨47196075548568398458539383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31464050365712265639026255 47196075548568398458539383)
    ·
      refine ⟨70794113322852597687809075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47196075548568398458539383 70794113322852597687809075)
      ·
        refine ⟨106191169984278896531713613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70794113322852597687809075 106191169984278896531713613)
        ·
          refine ⟨39821688744104586199392605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106191169984278896531713613 39821688744104586199392605)
          ·
            refine ⟨14933133279039219824772227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39821688744104586199392605 14933133279039219824772227)
            ·
              refine ⟨22399699918558829737158341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933133279039219824772227 22399699918558829737158341)
              ·
                refine ⟨4199943734729780575717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22399699918558829737158341 4199943734729780575717189)
                ·
                  refine ⟨787489450261833857946973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4199943734729780575717189 787489450261833857946973)
                  ·
                    refine ⟨295308543848187696730115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787489450261833857946973 295308543848187696730115)
                    ·
                      rfl

theorem cell22_862667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].length) (baseStart_862667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862667 prefixEnd_862667 := by exact prefixLift 862667
  have htrace : WordTrace (prefixWord ++ tailWord_862667) baseStart_862667 baseEnd_862667 := by
    simpa [prefixWord, tailWord_862667, baseEnd_862667] using wordTrace_append hprefix tailTrace_862667
  have hstable : (prefixWord ++ tailWord_862667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862667).length < 2 ^ (prefixWord ++ tailWord_862667).sum := by decide
  have hdescent : baseEnd_862667 < baseStart_862667 := by decide
  rcases family_descends (prefixWord ++ tailWord_862667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862682 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_862682 : Nat := 118140960795 + 862682 * 2 ^ 59
def prefixEnd_862682 : Nat := 4983230072969 + 3 ^ 40 * 862682 * 2
def baseEnd_862682 : Nat := 295313678654732657605069

theorem tailTrace_862682 : CollatzResearch.WordTrace tailWord_862682 prefixEnd_862682 295313678654732657605069 := by
  unfold tailWord_862682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866149365164480800205575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20976398307105282133881533 7866149365164480800205575)
  ·
    refine ⟨11799224047746721200308363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866149365164480800205575 11799224047746721200308363)
    ·
      refine ⟨17698836071620081800462545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11799224047746721200308363 17698836071620081800462545)
      ·
        refine ⟨13274127053715061350346909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17698836071620081800462545 13274127053715061350346909)
        ·
          refine ⟨4977797645143148006380091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13274127053715061350346909 4977797645143148006380091)
          ·
            refine ⟨7466696467714722009570137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977797645143148006380091 7466696467714722009570137)
            ·
              refine ⟨5600022350786041507177603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466696467714722009570137 5600022350786041507177603)
              ·
                refine ⟨8400033526179062260766405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5600022350786041507177603 8400033526179062260766405)
                ·
                  refine ⟨1575006286158574173893701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8400033526179062260766405 1575006286158574173893701)
                  ·
                    refine ⟨295313678654732657605069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575006286158574173893701 295313678654732657605069)
                    ·
                      rfl

theorem cell22_862682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_862682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862682 prefixEnd_862682 := by exact prefixLift 862682
  have htrace : WordTrace (prefixWord ++ tailWord_862682) baseStart_862682 baseEnd_862682 := by
    simpa [prefixWord, tailWord_862682, baseEnd_862682] using wordTrace_append hprefix tailTrace_862682
  have hstable : (prefixWord ++ tailWord_862682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862682).length < 2 ^ (prefixWord ++ tailWord_862682).sum := by decide
  have hdescent : baseEnd_862682 < baseStart_862682 := by decide
  rcases family_descends (prefixWord ++ tailWord_862682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862701 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_862701 : Nat := 118140960795 + 862701 * 2 ^ 59
def prefixEnd_862701 : Nat := 4983230072969 + 3 ^ 40 * 862701 * 2
def baseEnd_862701 : Nat := 295320182743022941380011

theorem tailTrace_862701 : CollatzResearch.WordTrace tailWord_862701 prefixEnd_862701 295320182743022941380011 := by
  unfold tailWord_862701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31465290447589089445763957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20976860298392726297175971 31465290447589089445763957)
  ·
    refine ⟨2949870979461477135540371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31465290447589089445763957 2949870979461477135540371)
    ·
      refine ⟨4424806469192215703310557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2949870979461477135540371 4424806469192215703310557)
      ·
        refine ⟨1659302425947080888741459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4424806469192215703310557 1659302425947080888741459)
        ·
          refine ⟨2488953638920621333112189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659302425947080888741459 2488953638920621333112189)
          ·
            refine ⟨933357614595232999917071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2488953638920621333112189 933357614595232999917071)
            ·
              refine ⟨1400036421892849499875607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933357614595232999917071 1400036421892849499875607)
              ·
                refine ⟨2100054632839274249813411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400036421892849499875607 2100054632839274249813411)
                ·
                  refine ⟨3150081949258911374720117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100054632839274249813411 3150081949258911374720117)
                  ·
                    refine ⟨295320182743022941380011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3150081949258911374720117 295320182743022941380011)
                    ·
                      rfl

theorem cell22_862701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_862701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862701 prefixEnd_862701 := by exact prefixLift 862701
  have htrace : WordTrace (prefixWord ++ tailWord_862701) baseStart_862701 baseEnd_862701 := by
    simpa [prefixWord, tailWord_862701, baseEnd_862701] using wordTrace_append hprefix tailTrace_862701
  have hstable : (prefixWord ++ tailWord_862701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862701).length < 2 ^ (prefixWord ++ tailWord_862701).sum := by decide
  have hdescent : baseEnd_862701 < baseStart_862701 := by decide
  rcases family_descends (prefixWord ++ tailWord_862701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862733 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_862733 : Nat := 118140960795 + 862733 * 2 ^ 59
def prefixEnd_862733 : Nat := 4983230072969 + 3 ^ 40 * 862733 * 2
def baseEnd_862733 : Nat := 295331136996985524579913

theorem tailTrace_862733 : CollatzResearch.WordTrace tailWord_862733 prefixEnd_862733 295331136996985524579913 := by
  unfold tailWord_862733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466457583473158910928853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20977638388982105940619235 31466457583473158910928853)
  ·
    refine ⟨737495099612652161974895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31466457583473158910928853 737495099612652161974895)
    ·
      refine ⟨1106242649418978242962343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737495099612652161974895 1106242649418978242962343)
      ·
        refine ⟨1659363974128467364443515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106242649418978242962343 1659363974128467364443515)
        ·
          refine ⟨2489045961192701046665273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659363974128467364443515 2489045961192701046665273)
          ·
            refine ⟨1866784470894525784998955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489045961192701046665273 1866784470894525784998955)
            ·
              refine ⟨2800176706341788677498433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866784470894525784998955 2800176706341788677498433)
              ·
                refine ⟨2100132529756341508123825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800176706341788677498433 2100132529756341508123825)
                ·
                  refine ⟨1575099397317256131092869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100132529756341508123825 1575099397317256131092869)
                  ·
                    refine ⟨295331136996985524579913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575099397317256131092869 295331136996985524579913)
                    ·
                      rfl

theorem cell22_862733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_862733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862733 prefixEnd_862733 := by exact prefixLift 862733
  have htrace : WordTrace (prefixWord ++ tailWord_862733) baseStart_862733 baseEnd_862733 := by
    simpa [prefixWord, tailWord_862733, baseEnd_862733] using wordTrace_append hprefix tailTrace_862733
  have hstable : (prefixWord ++ tailWord_862733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862733).length < 2 ^ (prefixWord ++ tailWord_862733).sum := by decide
  have hdescent : baseEnd_862733 < baseStart_862733 := by decide
  rcases family_descends (prefixWord ++ tailWord_862733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862746 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_862746 : Nat := 118140960795 + 862746 * 2 ^ 59
def prefixEnd_862746 : Nat := 4983230072969 + 3 ^ 40 * 862746 * 2
def baseEnd_862746 : Nat := 295335587162657824004873

theorem tailTrace_862746 : CollatzResearch.WordTrace tailWord_862746 prefixEnd_862746 295335587162657824004873 := by
  unfold tailWord_862746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866732933106515532788023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20977954488284041420768061 7866732933106515532788023)
  ·
    refine ⟨11800099399659773299182035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866732933106515532788023 11800099399659773299182035)
    ·
      refine ⟨17700149099489659948773053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11800099399659773299182035 17700149099489659948773053)
      ·
        refine ⟨6637555912308622480789895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17700149099489659948773053 6637555912308622480789895)
        ·
          refine ⟨9956333868462933721184843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637555912308622480789895 9956333868462933721184843)
          ·
            refine ⟨14934500802694400581777265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9956333868462933721184843 14934500802694400581777265)
            ·
              refine ⟨11200875602020800436332949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14934500802694400581777265 11200875602020800436332949)
              ·
                refine ⟨525041043844725020453107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11200875602020800436332949 525041043844725020453107)
                ·
                  refine ⟨787561565767087530679661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525041043844725020453107 787561565767087530679661)
                  ·
                    refine ⟨295335587162657824004873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787561565767087530679661 295335587162657824004873)
                    ·
                      rfl

theorem cell22_862746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_862746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862746 prefixEnd_862746 := by exact prefixLift 862746
  have htrace : WordTrace (prefixWord ++ tailWord_862746) baseStart_862746 baseEnd_862746 := by
    simpa [prefixWord, tailWord_862746, baseEnd_862746] using wordTrace_append hprefix tailTrace_862746
  have hstable : (prefixWord ++ tailWord_862746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862746).length < 2 ^ (prefixWord ++ tailWord_862746).sum := by decide
  have hdescent : baseEnd_862746 < baseStart_862746 := by decide
  rcases family_descends (prefixWord ++ tailWord_862746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862757 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_862757 : Nat := 118140960795 + 862757 * 2 ^ 59
def prefixEnd_862757 : Nat := 4983230072969 + 3 ^ 40 * 862757 * 2
def baseEnd_862757 : Nat := 295339352687457461979839

theorem tailTrace_862757 : CollatzResearch.WordTrace tailWord_862757 prefixEnd_862757 295339352687457461979839 := by
  unfold tailWord_862757
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467332935386211009802525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20978221956924140673201683 31467332935386211009802525)
  ·
    refine ⟨11800249850769829128675947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31467332935386211009802525 11800249850769829128675947)
    ·
      refine ⟨17700374776154743693013921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11800249850769829128675947 17700374776154743693013921)
      ·
        refine ⟨13275281082116057769760441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17700374776154743693013921 13275281082116057769760441)
        ·
          refine ⟨9956460811587043327320331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13275281082116057769760441 9956460811587043327320331)
          ·
            refine ⟨14934691217380564990980497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9956460811587043327320331 14934691217380564990980497)
            ·
              refine ⟨11201018413035423743235373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14934691217380564990980497 11201018413035423743235373)
              ·
                refine ⟨4200381904888283903713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11201018413035423743235373 4200381904888283903713265)
                ·
                  refine ⟨3150286428666212927784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200381904888283903713265 3150286428666212927784949)
                  ·
                    refine ⟨295339352687457461979839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3150286428666212927784949 295339352687457461979839)
                    ·
                      rfl

theorem cell22_862757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_862757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862757 prefixEnd_862757 := by exact prefixLift 862757
  have htrace : WordTrace (prefixWord ++ tailWord_862757) baseStart_862757 baseEnd_862757 := by
    simpa [prefixWord, tailWord_862757, baseEnd_862757] using wordTrace_append hprefix tailTrace_862757
  have hstable : (prefixWord ++ tailWord_862757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862757).length < 2 ^ (prefixWord ++ tailWord_862757).sum := by decide
  have hdescent : baseEnd_862757 < baseStart_862757 := by decide
  rcases family_descends (prefixWord ++ tailWord_862757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862797 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_862797 : Nat := 118140960795 + 862797 * 2 ^ 59
def prefixEnd_862797 : Nat := 4983230072969 + 3 ^ 40 * 862797 * 2
def baseEnd_862797 : Nat := 295353045504910690979717

theorem tailTrace_862797 : CollatzResearch.WordTrace tailWord_862797 prefixEnd_862797 295353045504910690979717 := by
  unfold tailWord_862797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468791855241297841258645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979194570160865227505763 31468791855241297841258645)
  ·
    refine ⟨1475099618214435836308999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31468791855241297841258645 1475099618214435836308999)
    ·
      refine ⟨2212649427321653754463499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475099618214435836308999 2212649427321653754463499)
      ·
        refine ⟨3318974140982480631695249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212649427321653754463499 3318974140982480631695249)
        ·
          refine ⟨2489230605736860473771437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3318974140982480631695249 2489230605736860473771437)
          ·
            refine ⟨933461477151322677664289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2489230605736860473771437 933461477151322677664289)
            ·
              refine ⟨700096107863492008248217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933461477151322677664289 700096107863492008248217)
              ·
                refine ⟨525072080897619006186163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700096107863492008248217 525072080897619006186163)
                ·
                  refine ⟨787608121346428509279245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525072080897619006186163 787608121346428509279245)
                  ·
                    refine ⟨295353045504910690979717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787608121346428509279245 295353045504910690979717)
                    ·
                      rfl

theorem cell22_862797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_862797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862797 prefixEnd_862797 := by exact prefixLift 862797
  have htrace : WordTrace (prefixWord ++ tailWord_862797) baseStart_862797 baseEnd_862797 := by
    simpa [prefixWord, tailWord_862797, baseEnd_862797] using wordTrace_append hprefix tailTrace_862797
  have hstable : (prefixWord ++ tailWord_862797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862797).length < 2 ^ (prefixWord ++ tailWord_862797).sum := by decide
  have hdescent : baseEnd_862797 < baseStart_862797 := by decide
  rcases family_descends (prefixWord ++ tailWord_862797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862819 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_862819 : Nat := 118140960795 + 862819 * 2 ^ 59
def prefixEnd_862819 : Nat := 4983230072969 + 3 ^ 40 * 862819 * 2
def baseEnd_862819 : Nat := 295360576554509966929649

theorem tailTrace_862819 : CollatzResearch.WordTrace tailWord_862819 prefixEnd_862819 295360576554509966929649 := by
  unfold tailWord_862819
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469594261161595598559511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979729507441063732373007 31469594261161595598559511)
  ·
    refine ⟨47204391391742393397839267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31469594261161595598559511 47204391391742393397839267)
    ·
      refine ⟨70806587087613590096758901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47204391391742393397839267 70806587087613590096758901)
      ·
        refine ⟨6638117539463774071571147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70806587087613590096758901 6638117539463774071571147)
        ·
          refine ⟨9957176309195661107356721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638117539463774071571147 9957176309195661107356721)
          ·
            refine ⟨7467882231896745830517541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957176309195661107356721 7467882231896745830517541)
            ·
              refine ⟨1400227918480639843222039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7467882231896745830517541 1400227918480639843222039)
              ·
                refine ⟨2100341877720959764833059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400227918480639843222039 2100341877720959764833059)
                ·
                  refine ⟨3150512816581439647249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100341877720959764833059 3150512816581439647249589)
                  ·
                    refine ⟨295360576554509966929649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3150512816581439647249589 295360576554509966929649)
                    ·
                      rfl

theorem cell22_862819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_862819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862819 prefixEnd_862819 := by exact prefixLift 862819
  have htrace : WordTrace (prefixWord ++ tailWord_862819) baseStart_862819 baseEnd_862819 := by
    simpa [prefixWord, tailWord_862819, baseEnd_862819] using wordTrace_append hprefix tailTrace_862819
  have hstable : (prefixWord ++ tailWord_862819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862819).length < 2 ^ (prefixWord ++ tailWord_862819).sum := by decide
  have hdescent : baseEnd_862819 < baseStart_862819 := by decide
  rcases family_descends (prefixWord ++ tailWord_862819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862853 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_862853 : Nat := 118140960795 + 862853 * 2 ^ 59
def prefixEnd_862853 : Nat := 4983230072969 + 3 ^ 40 * 862853 * 2
def baseEnd_862853 : Nat := 295372215449345211579545

theorem tailTrace_862853 : CollatzResearch.WordTrace tailWord_862853 prefixEnd_862853 295372215449345211579545 := by
  unfold tailWord_862853
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470834343038419405297213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20980556228692279603531475 31470834343038419405297213)
  ·
    refine ⟨11801562878639407276986455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31470834343038419405297213 11801562878639407276986455)
    ·
      refine ⟨17702344317959110915479683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11801562878639407276986455 17702344317959110915479683)
      ·
        refine ⟨26553516476938666373219525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17702344317959110915479683 26553516476938666373219525)
        ·
          refine ⟨4978784339425999944978661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26553516476938666373219525 4978784339425999944978661)
          ·
            refine ⟨933522063642374989683499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4978784339425999944978661 933522063642374989683499)
            ·
              refine ⟨1400283095463562484525249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933522063642374989683499 1400283095463562484525249)
              ·
                refine ⟨1050212321597671863393937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400283095463562484525249 1050212321597671863393937)
                ·
                  refine ⟨787659241198253897545453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050212321597671863393937 787659241198253897545453)
                  ·
                    refine ⟨295372215449345211579545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787659241198253897545453 295372215449345211579545)
                    ·
                      rfl

theorem cell22_862853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_862853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862853 prefixEnd_862853 := by exact prefixLift 862853
  have htrace : WordTrace (prefixWord ++ tailWord_862853) baseStart_862853 baseEnd_862853 := by
    simpa [prefixWord, tailWord_862853, baseEnd_862853] using wordTrace_append hprefix tailTrace_862853
  have hstable : (prefixWord ++ tailWord_862853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862853).length < 2 ^ (prefixWord ++ tailWord_862853).sum := by decide
  have hdescent : baseEnd_862853 < baseStart_862853 := by decide
  rcases family_descends (prefixWord ++ tailWord_862853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862956 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_862956 : Nat := 118140960795 + 862956 * 2 ^ 59
def prefixEnd_862956 : Nat := 4983230072969 + 3 ^ 40 * 862956 * 2
def baseEnd_862956 : Nat := 98469158151429092084743

theorem tailTrace_862956 : CollatzResearch.WordTrace tailWord_862956 prefixEnd_862956 98469158151429092084743 := by
  unfold tailWord_862956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737295530832633998148361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20983060707776845330864481 15737295530832633998148361)
  ·
    refine ⟨11802971648124475498611271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15737295530832633998148361 11802971648124475498611271)
    ·
      refine ⟨17704457472186713247916907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802971648124475498611271 17704457472186713247916907)
      ·
        refine ⟨26556686208280069871875361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704457472186713247916907 26556686208280069871875361)
        ·
          refine ⟨19917514656210052403906521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26556686208280069871875361 19917514656210052403906521)
          ·
            refine ⟨14938135992157539302929891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19917514656210052403906521 14938135992157539302929891)
            ·
              refine ⟨22407203988236308954394837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938135992157539302929891 22407203988236308954394837)
              ·
                refine ⟨525168843474288491118629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22407203988236308954394837 525168843474288491118629)
                ·
                  refine ⟨98469158151429092084743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525168843474288491118629 98469158151429092084743)
                  ·
                    rfl

theorem cell22_862956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_862956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_862956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_862956 prefixEnd_862956 := by exact prefixLift 862956
  have htrace : WordTrace (prefixWord ++ tailWord_862956) baseStart_862956 baseEnd_862956 := by
    simpa [prefixWord, tailWord_862956, baseEnd_862956] using wordTrace_append hprefix tailTrace_862956
  have hstable : (prefixWord ++ tailWord_862956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862956).length < 2 ^ (prefixWord ++ tailWord_862956).sum := by decide
  have hdescent : baseEnd_862956 < baseStart_862956 := by decide
  rcases family_descends (prefixWord ++ tailWord_862956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863018 : List Nat := [3, 1, 4, 3, 1, 1, 9]
def baseStart_863018 : Nat := 118140960795 + 863018 * 2 ^ 59
def prefixEnd_863018 : Nat := 4983230072969 + 3 ^ 40 * 863018 * 2
def baseEnd_863018 : Nat := 10941803641531103007557

theorem tailTrace_863018 : CollatzResearch.WordTrace tailWord_863018 prefixEnd_863018 10941803641531103007557 := by
  unfold tailWord_863018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869213096860163146263427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20984568258293768390035805 7869213096860163146263427)
  ·
    refine ⟨11803819645290244719395141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7869213096860163146263427 11803819645290244719395141)
    ·
      refine ⟨2213216183491920884886589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11803819645290244719395141 2213216183491920884886589)
      ·
        refine ⟨829956068809470331832471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2213216183491920884886589 829956068809470331832471)
        ·
          refine ⟨1244934103214205497748707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829956068809470331832471 1244934103214205497748707)
          ·
            refine ⟨1867401154821308246623061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244934103214205497748707 1867401154821308246623061)
            ·
              refine ⟨10941803641531103007557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1867401154821308246623061 10941803641531103007557)
              ·
                rfl

theorem cell22_863018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 9].length) (baseStart_863018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863018 prefixEnd_863018 := by exact prefixLift 863018
  have htrace : WordTrace (prefixWord ++ tailWord_863018) baseStart_863018 baseEnd_863018 := by
    simpa [prefixWord, tailWord_863018, baseEnd_863018] using wordTrace_append hprefix tailTrace_863018
  have hstable : (prefixWord ++ tailWord_863018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863018).length < 2 ^ (prefixWord ++ tailWord_863018).sum := by decide
  have hdescent : baseEnd_863018 < baseStart_863018 := by decide
  rcases family_descends (prefixWord ++ tailWord_863018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863022 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_863022 : Nat := 118140960795 + 863022 * 2 ^ 59
def prefixEnd_863022 : Nat := 4983230072969 + 3 ^ 40 * 863022 * 2
def baseEnd_863022 : Nat := 295430067603085104104027

theorem tailTrace_863022 : CollatzResearch.WordTrace tailWord_863022 prefixEnd_863022 295430067603085104104027 := by
  unfold tailWord_863022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934624784928270158524915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20984665519617440845466213 3934624784928270158524915)
  ·
    refine ⟨5901937177392405237787373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3934624784928270158524915 5901937177392405237787373)
    ·
      refine ⟨2213226441522151964170265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5901937177392405237787373 2213226441522151964170265)
      ·
        refine ⟨1659919831141613973127699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213226441522151964170265 1659919831141613973127699)
        ·
          refine ⟨2489879746712420959691549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659919831141613973127699 2489879746712420959691549)
          ·
            refine ⟨933704905017157859884331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2489879746712420959691549 933704905017157859884331)
            ·
              refine ⟨1400557357525736789826497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933704905017157859884331 1400557357525736789826497)
              ·
                refine ⟨1050418018144302592369873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400557357525736789826497 1050418018144302592369873)
                ·
                  refine ⟨787813513608226944277405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050418018144302592369873 787813513608226944277405)
                  ·
                    refine ⟨295430067603085104104027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787813513608226944277405 295430067603085104104027)
                    ·
                      rfl

theorem cell22_863022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_863022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863022 prefixEnd_863022 := by exact prefixLift 863022
  have htrace : WordTrace (prefixWord ++ tailWord_863022) baseStart_863022 baseEnd_863022 := by
    simpa [prefixWord, tailWord_863022, baseEnd_863022] using wordTrace_append hprefix tailTrace_863022
  have hstable : (prefixWord ++ tailWord_863022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863022).length < 2 ^ (prefixWord ++ tailWord_863022).sum := by decide
  have hdescent : baseEnd_863022 < baseStart_863022 := by decide
  rcases family_descends (prefixWord ++ tailWord_863022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863059 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_863059 : Nat := 118140960795 + 863059 * 2 ^ 59
def prefixEnd_863059 : Nat := 4983230072969 + 3 ^ 40 * 863059 * 2
def baseEnd_863059 : Nat := 295442733459229340928913

theorem tailTrace_863059 : CollatzResearch.WordTrace tailWord_863059 prefixEnd_863059 295442733459229340928913 := by
  unfold tailWord_863059
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478347780292116587296231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20985565186861411058197487 31478347780292116587296231)
  ·
    refine ⟨47217521670438174880944347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31478347780292116587296231 47217521670438174880944347)
    ·
      refine ⟨70826282505657262321416521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47217521670438174880944347 70826282505657262321416521)
      ·
        refine ⟨53119711879242946741062391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70826282505657262321416521 53119711879242946741062391)
        ·
          refine ⟨79679567818864420111593587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53119711879242946741062391 79679567818864420111593587)
          ·
            refine ⟨119519351728296630167390381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79679567818864420111593587 119519351728296630167390381)
            ·
              refine ⟨44819756898111236312771393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119519351728296630167390381 44819756898111236312771393)
              ·
                refine ⟨33614817673583427234578545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44819756898111236312771393 33614817673583427234578545)
                ·
                  refine ⟨25211113255187570425933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33614817673583427234578545 25211113255187570425933909)
                  ·
                    refine ⟨295442733459229340928913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25211113255187570425933909 295442733459229340928913)
                    ·
                      rfl

theorem cell22_863059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_863059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863059 prefixEnd_863059 := by exact prefixLift 863059
  have htrace : WordTrace (prefixWord ++ tailWord_863059) baseStart_863059 baseEnd_863059 := by
    simpa [prefixWord, tailWord_863059, baseEnd_863059] using wordTrace_append hprefix tailTrace_863059
  have hstable : (prefixWord ++ tailWord_863059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863059).length < 2 ^ (prefixWord ++ tailWord_863059).sum := by decide
  have hdescent : baseEnd_863059 < baseStart_863059 := by decide
  rcases family_descends (prefixWord ++ tailWord_863059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863091 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 6]
def baseStart_863091 : Nat := 118140960795 + 863091 * 2 ^ 59
def prefixEnd_863091 : Nat := 4983230072969 + 3 ^ 40 * 863091 * 2
def baseEnd_863091 : Nat := 98484562571063974709605

theorem tailTrace_863091 : CollatzResearch.WordTrace tailWord_863091 prefixEnd_863091 98484562571063974709605 := by
  unfold tailWord_863091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479514916176186052461127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20986343277450790701640751 31479514916176186052461127)
  ·
    refine ⟨47219272374264279078691691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31479514916176186052461127 47219272374264279078691691)
    ·
      refine ⟨70828908561396418618037537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47219272374264279078691691 70828908561396418618037537)
      ·
        refine ⟨53121681421047313963528153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70828908561396418618037537 53121681421047313963528153)
        ·
          refine ⟨39841261065785485472646115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53121681421047313963528153 39841261065785485472646115)
          ·
            refine ⟨59761891598678228208969173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39841261065785485472646115 59761891598678228208969173)
            ·
              refine ⟨1400669334344020973647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59761891598678228208969173 1400669334344020973647715)
              ·
                refine ⟨2101004001516031460471573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400669334344020973647715 2101004001516031460471573)
                ·
                  refine ⟨98484562571063974709605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2101004001516031460471573 98484562571063974709605)
                  ·
                    rfl

theorem cell22_863091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_863091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863091 prefixEnd_863091 := by exact prefixLift 863091
  have htrace : WordTrace (prefixWord ++ tailWord_863091) baseStart_863091 baseEnd_863091 := by
    simpa [prefixWord, tailWord_863091, baseEnd_863091] using wordTrace_append hprefix tailTrace_863091
  have hstable : (prefixWord ++ tailWord_863091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863091).length < 2 ^ (prefixWord ++ tailWord_863091).sum := by decide
  have hdescent : baseEnd_863091 < baseStart_863091 := by decide
  rcases family_descends (prefixWord ++ tailWord_863091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863140 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_863140 : Nat := 118140960795 + 863140 * 2 ^ 59
def prefixEnd_863140 : Nat := 4983230072969 + 3 ^ 40 * 863140 * 2
def baseEnd_863140 : Nat := 295470461414572129653665

theorem tailTrace_863140 : CollatzResearch.WordTrace tailWord_863140 prefixEnd_863140 295470461414572129653665 := by
  unfold tailWord_863140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740651046499333710497437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20987534728665778280663249 15740651046499333710497437)
  ·
    refine ⟨5902744142437250141436539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15740651046499333710497437 5902744142437250141436539)
    ·
      refine ⟨8854116213655875212154809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902744142437250141436539 8854116213655875212154809)
      ·
        refine ⟨6640587160241906409116107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8854116213655875212154809 6640587160241906409116107)
        ·
          refine ⟨9960880740362859613674161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6640587160241906409116107 9960880740362859613674161)
          ·
            refine ⟨7470660555272144710255621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960880740362859613674161 7470660555272144710255621)
            ·
              refine ⟨1400748854113527133172929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7470660555272144710255621 1400748854113527133172929)
              ·
                refine ⟨1050561640585145349879697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400748854113527133172929 1050561640585145349879697)
                ·
                  refine ⟨787921230438859012409773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050561640585145349879697 787921230438859012409773)
                  ·
                    refine ⟨295470461414572129653665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787921230438859012409773 295470461414572129653665)
                    ·
                      rfl

theorem cell22_863140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_863140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863140 prefixEnd_863140 := by exact prefixLift 863140
  have htrace : WordTrace (prefixWord ++ tailWord_863140) baseStart_863140 baseEnd_863140 := by
    simpa [prefixWord, tailWord_863140, baseEnd_863140] using wordTrace_append hprefix tailTrace_863140
  have hstable : (prefixWord ++ tailWord_863140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863140).length < 2 ^ (prefixWord ++ tailWord_863140).sum := by decide
  have hdescent : baseEnd_863140 < baseStart_863140 := by decide
  rcases family_descends (prefixWord ++ tailWord_863140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863168 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_863168 : Nat := 118140960795 + 863168 * 2 ^ 59
def prefixEnd_863168 : Nat := 4983230072969 + 3 ^ 40 * 863168 * 2
def baseEnd_863168 : Nat := 295480046386789389953579

theorem tailTrace_863168 : CollatzResearch.WordTrace tailWord_863168 prefixEnd_863168 295480046386789389953579 := by
  unfold tailWord_863168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741161668448614101507079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20988215557931485468676105 15741161668448614101507079)
  ·
    refine ⟨23611742502672921152260619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15741161668448614101507079 23611742502672921152260619)
    ·
      refine ⟨35417613754009381728390929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23611742502672921152260619 35417613754009381728390929)
      ·
        refine ⟨26563210315507036296293197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35417613754009381728390929 26563210315507036296293197)
        ·
          refine ⟨9961203868315138611109949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26563210315507036296293197 9961203868315138611109949)
          ·
            refine ⟨3735451450618176979166231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9961203868315138611109949 3735451450618176979166231)
            ·
              refine ⟨5603177175927265468749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735451450618176979166231 5603177175927265468749347)
              ·
                refine ⟨8404765763890898203124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603177175927265468749347 8404765763890898203124021)
                ·
                  refine ⟨787946790364771706542877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8404765763890898203124021 787946790364771706542877)
                  ·
                    refine ⟨295480046386789389953579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787946790364771706542877 295480046386789389953579)
                    ·
                      rfl

theorem cell22_863168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_863168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863168 prefixEnd_863168 := by exact prefixLift 863168
  have htrace : WordTrace (prefixWord ++ tailWord_863168) baseStart_863168 baseEnd_863168 := by
    simpa [prefixWord, tailWord_863168, baseEnd_863168] using wordTrace_append hprefix tailTrace_863168
  have hstable : (prefixWord ++ tailWord_863168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863168).length < 2 ^ (prefixWord ++ tailWord_863168).sum := by decide
  have hdescent : baseEnd_863168 < baseStart_863168 := by decide
  rcases family_descends (prefixWord ++ tailWord_863168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863202 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_863202 : Nat := 118140960795 + 863202 * 2 ^ 59
def prefixEnd_863202 : Nat := 4983230072969 + 3 ^ 40 * 863202 * 2
def baseEnd_863202 : Nat := 295491685281624634603475

theorem tailTrace_863202 : CollatzResearch.WordTrace tailWord_863202 prefixEnd_863202 295491685281624634603475 := by
  unfold tailWord_863202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870890854693513002437965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20989042279182701339834573 7870890854693513002437965)
  ·
    refine ⟨2951584070510067375914237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7870890854693513002437965 2951584070510067375914237)
    ·
      refine ⟨1106844026441275265967839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2951584070510067375914237 1106844026441275265967839)
      ·
        refine ⟨1660266039661912898951759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106844026441275265967839 1660266039661912898951759)
        ·
          refine ⟨2490399059492869348427639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660266039661912898951759 2490399059492869348427639)
          ·
            refine ⟨3735598589239304022641459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490399059492869348427639 3735598589239304022641459)
            ·
              refine ⟨5603397883858956033962189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735598589239304022641459 5603397883858956033962189)
              ·
                refine ⟨2101274206447108512735821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5603397883858956033962189 2101274206447108512735821)
                ·
                  refine ⟨787977827417665692275933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2101274206447108512735821 787977827417665692275933)
                  ·
                    refine ⟨295491685281624634603475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 787977827417665692275933 295491685281624634603475)
                    ·
                      rfl

theorem cell22_863202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_863202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863202 prefixEnd_863202 := by exact prefixLift 863202
  have htrace : WordTrace (prefixWord ++ tailWord_863202) baseStart_863202 baseEnd_863202 := by
    simpa [prefixWord, tailWord_863202, baseEnd_863202] using wordTrace_append hprefix tailTrace_863202
  have hstable : (prefixWord ++ tailWord_863202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863202).length < 2 ^ (prefixWord ++ tailWord_863202).sum := by decide
  have hdescent : baseEnd_863202 < baseStart_863202 := by decide
  rcases family_descends (prefixWord ++ tailWord_863202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863215 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 5]
def baseStart_863215 : Nat := 118140960795 + 863215 * 2 ^ 59
def prefixEnd_863215 : Nat := 4983230072969 + 3 ^ 40 * 863215 * 2
def baseEnd_863215 : Nat := 98498711815765644676145

theorem tailTrace_863215 : CollatzResearch.WordTrace tailWord_863215 prefixEnd_863215 98498711815765644676145 := by
  unfold tailWord_863215
  simp only [CollatzResearch.WordTrace]
  refine ⟨31484037567726955229975099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20989358378484636819983399 31484037567726955229975099)
  ·
    refine ⟨47226056351590432844962649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31484037567726955229975099 47226056351590432844962649)
    ·
      refine ⟨35419542263692824633721987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47226056351590432844962649 35419542263692824633721987)
      ·
        refine ⟨53129313395539236950582981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35419542263692824633721987 53129313395539236950582981)
        ·
          refine ⟨9961746261663606928234309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53129313395539236950582981 9961746261663606928234309)
          ·
            refine ⟨1867827424061926299043933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9961746261663606928234309 1867827424061926299043933)
            ·
              refine ⟨700435284023222362141475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1867827424061926299043933 700435284023222362141475)
              ·
                refine ⟨1050652926034833543212213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700435284023222362141475 1050652926034833543212213)
                ·
                  refine ⟨98498711815765644676145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1050652926034833543212213 98498711815765644676145)
                  ·
                    rfl

theorem cell22_863215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 5].length) (baseStart_863215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863215 prefixEnd_863215 := by exact prefixLift 863215
  have htrace : WordTrace (prefixWord ++ tailWord_863215) baseStart_863215 baseEnd_863215 := by
    simpa [prefixWord, tailWord_863215, baseEnd_863215] using wordTrace_append hprefix tailTrace_863215
  have hstable : (prefixWord ++ tailWord_863215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863215).length < 2 ^ (prefixWord ++ tailWord_863215).sum := by decide
  have hdescent : baseEnd_863215 < baseStart_863215 := by decide
  rcases family_descends (prefixWord ++ tailWord_863215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863275 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 2, 3]
def baseStart_863275 : Nat := 118140960795 + 863275 * 2 ^ 59
def prefixEnd_863275 : Nat := 4983230072969 + 3 ^ 40 * 863275 * 2
def baseEnd_863275 : Nat := 295516674673476777528251

theorem tailTrace_863275 : CollatzResearch.WordTrace tailWord_863275 prefixEnd_863275 295516674673476777528251 := by
  unfold tailWord_863275
  simp only [CollatzResearch.WordTrace]
  refine ⟨31486225947509585477159279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20990817298339723651439519 31486225947509585477159279)
  ·
    refine ⟨47229338921264378215738919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31486225947509585477159279 47229338921264378215738919)
    ·
      refine ⟨70844008381896567323608379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47229338921264378215738919 70844008381896567323608379)
      ·
        refine ⟨106266012572844850985412569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70844008381896567323608379 106266012572844850985412569)
        ·
          refine ⟨79699509429633638239059427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106266012572844850985412569 79699509429633638239059427)
          ·
            refine ⟨119549264144450457358589141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79699509429633638239059427 119549264144450457358589141)
            ·
              refine ⟨2801935878385557594341933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119549264144450457358589141 2801935878385557594341933)
              ·
                refine ⟨1050725954394584097878225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2801935878385557594341933 1050725954394584097878225)
                ·
                  refine ⟨788044465795938073408669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050725954394584097878225 788044465795938073408669)
                  ·
                    refine ⟨295516674673476777528251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788044465795938073408669 295516674673476777528251)
                    ·
                      rfl

theorem cell22_863275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].length) (baseStart_863275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863275 prefixEnd_863275 := by exact prefixLift 863275
  have htrace : WordTrace (prefixWord ++ tailWord_863275) baseStart_863275 baseEnd_863275 := by
    simpa [prefixWord, tailWord_863275, baseEnd_863275] using wordTrace_append hprefix tailTrace_863275
  have hstable : (prefixWord ++ tailWord_863275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863275).length < 2 ^ (prefixWord ++ tailWord_863275).sum := by decide
  have hdescent : baseEnd_863275 < baseStart_863275 := by decide
  rcases family_descends (prefixWord ++ tailWord_863275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863288 : List Nat := [2, 1, 2, 1, 5, 1, 2, 8]
def baseStart_863288 : Nat := 118140960795 + 863288 * 2 ^ 59
def prefixEnd_863288 : Nat := 4983230072969 + 3 ^ 40 * 863288 * 2
def baseEnd_863288 : Nat := 32835680537683230772579

theorem tailTrace_863288 : CollatzResearch.WordTrace tailWord_863288 prefixEnd_863288 32835680537683230772579 := by
  unfold tailWord_863288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743350048231244348691259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20991133397641659131588345 15743350048231244348691259)
  ·
    refine ⟨23615025072346866523036889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15743350048231244348691259 23615025072346866523036889)
    ·
      refine ⟨17711268804260149892277667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23615025072346866523036889 17711268804260149892277667)
      ·
        refine ⟨26566903206390224838416501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711268804260149892277667 26566903206390224838416501)
        ·
          refine ⟨2490647175599083578601547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26566903206390224838416501 2490647175599083578601547)
          ·
            refine ⟨3735970763398625367902321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490647175599083578601547 3735970763398625367902321)
            ·
              refine ⟨2801978072548969025926741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735970763398625367902321 2801978072548969025926741)
              ·
                refine ⟨32835680537683230772579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2801978072548969025926741 32835680537683230772579)
                ·
                  rfl

theorem cell22_863288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_863288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863288 prefixEnd_863288 := by exact prefixLift 863288
  have htrace : WordTrace (prefixWord ++ tailWord_863288) baseStart_863288 baseEnd_863288 := by
    simpa [prefixWord, tailWord_863288, baseEnd_863288] using wordTrace_append hprefix tailTrace_863288
  have hstable : (prefixWord ++ tailWord_863288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863288).length < 2 ^ (prefixWord ++ tailWord_863288).sum := by decide
  have hdescent : baseEnd_863288 < baseStart_863288 := by decide
  rcases family_descends (prefixWord ++ tailWord_863288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863309 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_863309 : Nat := 118140960795 + 863309 * 2 ^ 59
def prefixEnd_863309 : Nat := 4983230072969 + 3 ^ 40 * 863309 * 2
def baseEnd_863309 : Nat := 295528313568312022178147

theorem tailTrace_863309 : CollatzResearch.WordTrace tailWord_863309 prefixEnd_863309 295528313568312022178147 := by
  unfold tailWord_863309
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487466029386409283896981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20991644019590939522597987 31487466029386409283896981)
  ·
    refine ⟨1475974970127487935182671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31487466029386409283896981 1475974970127487935182671)
    ·
      refine ⟨2213962455191231902774007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475974970127487935182671 2213962455191231902774007)
      ·
        refine ⟨3320943682786847854161011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213962455191231902774007 3320943682786847854161011)
        ·
          refine ⟨4981415524180271781241517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320943682786847854161011 4981415524180271781241517)
          ·
            refine ⟨1868030821567601917965569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4981415524180271781241517 1868030821567601917965569)
            ·
              refine ⟨1401023116175701438474177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868030821567601917965569 1401023116175701438474177)
              ·
                refine ⟨1050767337131776078855633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401023116175701438474177 1050767337131776078855633)
                ·
                  refine ⟨788075502848832059141725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050767337131776078855633 788075502848832059141725)
                  ·
                    refine ⟨295528313568312022178147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788075502848832059141725 295528313568312022178147)
                    ·
                      rfl

theorem cell22_863309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_863309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863309 prefixEnd_863309 := by exact prefixLift 863309
  have htrace : WordTrace (prefixWord ++ tailWord_863309) baseStart_863309 baseEnd_863309 := by
    simpa [prefixWord, tailWord_863309, baseEnd_863309] using wordTrace_append hprefix tailTrace_863309
  have hstable : (prefixWord ++ tailWord_863309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863309).length < 2 ^ (prefixWord ++ tailWord_863309).sum := by decide
  have hdescent : baseEnd_863309 < baseStart_863309 := by decide
  rcases family_descends (prefixWord ++ tailWord_863309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863320 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_863320 : Nat := 118140960795 + 863320 * 2 ^ 59
def prefixEnd_863320 : Nat := 4983230072969 + 3 ^ 40 * 863320 * 2
def baseEnd_863320 : Nat := 295532079093111660153113

theorem tailTrace_863320 : CollatzResearch.WordTrace tailWord_863320 prefixEnd_863320 295532079093111660153113 := by
  unfold tailWord_863320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743933616173279081273707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20991911488231038775031609 15743933616173279081273707)
  ·
    refine ⟨23615900424259918621910561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15743933616173279081273707 23615900424259918621910561)
    ·
      refine ⟨17711925318194938966432921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23615900424259918621910561 17711925318194938966432921)
      ·
        refine ⟨13283943988646204224824691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17711925318194938966432921 13283943988646204224824691)
        ·
          refine ⟨19925915982969306337237037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13283943988646204224824691 19925915982969306337237037)
          ·
            refine ⟨7472218493613489876463889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19925915982969306337237037 7472218493613489876463889)
            ·
              refine ⟨5604163870210117407347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472218493613489876463889 5604163870210117407347917)
              ·
                refine ⟨2101561451328794027755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5604163870210117407347917 2101561451328794027755469)
                ·
                  refine ⟨788085544248297760408301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2101561451328794027755469 788085544248297760408301)
                  ·
                    refine ⟨295532079093111660153113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788085544248297760408301 295532079093111660153113)
                    ·
                      rfl

theorem cell22_863320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_863320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863320 prefixEnd_863320 := by exact prefixLift 863320
  have htrace : WordTrace (prefixWord ++ tailWord_863320) baseStart_863320 baseEnd_863320 := by
    simpa [prefixWord, tailWord_863320, baseEnd_863320] using wordTrace_append hprefix tailTrace_863320
  have hstable : (prefixWord ++ tailWord_863320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863320).length < 2 ^ (prefixWord ++ tailWord_863320).sum := by decide
  have hdescent : baseEnd_863320 < baseStart_863320 := by decide
  rcases family_descends (prefixWord ++ tailWord_863320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863326 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_863326 : Nat := 118140960795 + 863326 * 2 ^ 59
def prefixEnd_863326 : Nat := 4983230072969 + 3 ^ 40 * 863326 * 2
def baseEnd_863326 : Nat := 295534133015729644503095

theorem tailTrace_863326 : CollatzResearch.WordTrace tailWord_863326 prefixEnd_863326 295534133015729644503095 := by
  unfold tailWord_863326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936010758790602648408229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20992057380216547458177221 3936010758790602648408229)
  ·
    refine ⟨738002017273237996576543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3936010758790602648408229 738002017273237996576543)
    ·
      refine ⟨1107003025909856994864815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738002017273237996576543 1107003025909856994864815)
      ·
        refine ⟨1660504538864785492297223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107003025909856994864815 1660504538864785492297223)
        ·
          refine ⟨2490756808297178238445835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660504538864785492297223 2490756808297178238445835)
          ·
            refine ⟨3736135212445767357668753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490756808297178238445835 3736135212445767357668753)
            ·
              refine ⟨2802101409334325518251565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736135212445767357668753 2802101409334325518251565)
              ·
                refine ⟨1050788028500372069344337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2802101409334325518251565 1050788028500372069344337)
                ·
                  refine ⟨788091021375279052008253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050788028500372069344337 788091021375279052008253)
                  ·
                    refine ⟨295534133015729644503095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788091021375279052008253 295534133015729644503095)
                    ·
                      rfl

theorem cell22_863326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_863326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863326 prefixEnd_863326 := by exact prefixLift 863326
  have htrace : WordTrace (prefixWord ++ tailWord_863326) baseStart_863326 baseEnd_863326 := by
    simpa [prefixWord, tailWord_863326, baseEnd_863326] using wordTrace_append hprefix tailTrace_863326
  have hstable : (prefixWord ++ tailWord_863326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863326).length < 2 ^ (prefixWord ++ tailWord_863326).sum := by decide
  have hdescent : baseEnd_863326 < baseStart_863326 := by decide
  rcases family_descends (prefixWord ++ tailWord_863326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863350 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_863350 : Nat := 118140960795 + 863350 * 2 ^ 59
def prefixEnd_863350 : Nat := 4983230072969 + 3 ^ 40 * 863350 * 2
def baseEnd_863350 : Nat := 98514116235400527301007

theorem tailTrace_863350 : CollatzResearch.WordTrace tailWord_863350 prefixEnd_863350 98514116235400527301007 := by
  unfold tailWord_863350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968060088889867080383719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20992640948158582190759669 1968060088889867080383719)
  ·
    refine ⟨2952090133334800620575579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1968060088889867080383719 2952090133334800620575579)
    ·
      refine ⟨4428135200002200930863369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952090133334800620575579 4428135200002200930863369)
      ·
        refine ⟨3321101400001650698147527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428135200002200930863369 3321101400001650698147527)
        ·
          refine ⟨4981652100002476047221291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321101400001650698147527 4981652100002476047221291)
          ·
            refine ⟨7472478150003714070831937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981652100002476047221291 7472478150003714070831937)
            ·
              refine ⟨5604358612502785553123953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472478150003714070831937 5604358612502785553123953)
              ·
                refine ⟨4203268959377089164842965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5604358612502785553123953 4203268959377089164842965)
                ·
                  refine ⟨98514116235400527301007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4203268959377089164842965 98514116235400527301007)
                  ·
                    rfl

theorem cell22_863350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_863350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863350 prefixEnd_863350 := by exact prefixLift 863350
  have htrace : WordTrace (prefixWord ++ tailWord_863350) baseStart_863350 baseEnd_863350 := by
    simpa [prefixWord, tailWord_863350, baseEnd_863350] using wordTrace_append hprefix tailTrace_863350
  have hstable : (prefixWord ++ tailWord_863350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863350).length < 2 ^ (prefixWord ++ tailWord_863350).sum := by decide
  have hdescent : baseEnd_863350 < baseStart_863350 := by decide
  rcases family_descends (prefixWord ++ tailWord_863350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863397 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_863397 : Nat := 118140960795 + 863397 * 2 ^ 59
def prefixEnd_863397 : Nat := 4983230072969 + 3 ^ 40 * 863397 * 2
def baseEnd_863397 : Nat := 295558437766709125977877

theorem tailTrace_863397 : CollatzResearch.WordTrace tailWord_863397 prefixEnd_863397 295558437766709125977877 := by
  unfold tailWord_863397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31490675653067600313100445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20993783768711733542066963 31490675653067600313100445)
  ·
    refine ⟨11809003369900350117412667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31490675653067600313100445 11809003369900350117412667)
    ·
      refine ⟨17713505054850525176119001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11809003369900350117412667 17713505054850525176119001)
      ·
        refine ⟨13285128791137893882089251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17713505054850525176119001 13285128791137893882089251)
        ·
          refine ⟨19927693186706840823133877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13285128791137893882089251 19927693186706840823133877)
          ·
            refine ⟨1868221236253766327168801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19927693186706840823133877 1868221236253766327168801)
            ·
              refine ⟨1401165927190324745376601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868221236253766327168801 1401165927190324745376601)
              ·
                refine ⟨1050874445392743559032451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401165927190324745376601 1050874445392743559032451)
                ·
                  refine ⟨1576311668089115338548677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050874445392743559032451 1576311668089115338548677)
                  ·
                    refine ⟨295558437766709125977877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1576311668089115338548677 295558437766709125977877)
                    ·
                      rfl

theorem cell22_863397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_863397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863397 prefixEnd_863397 := by exact prefixLift 863397
  have htrace : WordTrace (prefixWord ++ tailWord_863397) baseStart_863397 baseEnd_863397 := by
    simpa [prefixWord, tailWord_863397, baseEnd_863397] using wordTrace_append hprefix tailTrace_863397
  have hstable : (prefixWord ++ tailWord_863397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863397).length < 2 ^ (prefixWord ++ tailWord_863397).sum := by decide
  have hdescent : baseEnd_863397 < baseStart_863397 := by decide
  rcases family_descends (prefixWord ++ tailWord_863397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863423 : List Nat := [1, 1, 2, 2, 2, 2, 12]
def baseStart_863423 : Nat := 118140960795 + 863423 * 2 ^ 59
def prefixEnd_863423 : Nat := 4983230072969 + 3 ^ 40 * 863423 * 2
def baseEnd_863423 : Nat := 10946938448076063882511

theorem tailTrace_863423 : CollatzResearch.WordTrace tailWord_863423 prefixEnd_863423 10946938448076063882511 := by
  unfold tailWord_863423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491623950973406753546923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20994415967315604502364615 31491623950973406753546923)
  ·
    refine ⟨47237435926460110130320385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31491623950973406753546923 47237435926460110130320385)
    ·
      refine ⟨35428076944845082597740289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47237435926460110130320385 35428076944845082597740289)
      ·
        refine ⟨26571057708633811948305217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35428076944845082597740289 26571057708633811948305217)
        ·
          refine ⟨19928293281475358961228913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26571057708633811948305217 19928293281475358961228913)
          ·
            refine ⟨14946219961106519220921685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19928293281475358961228913 14946219961106519220921685)
            ·
              refine ⟨10946938448076063882511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 14946219961106519220921685 10946938448076063882511)
              ·
                rfl

theorem cell22_863423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 12].length) (baseStart_863423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863423 prefixEnd_863423 := by exact prefixLift 863423
  have htrace : WordTrace (prefixWord ++ tailWord_863423) baseStart_863423 baseEnd_863423 := by
    simpa [prefixWord, tailWord_863423, baseEnd_863423] using wordTrace_append hprefix tailTrace_863423
  have hstable : (prefixWord ++ tailWord_863423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863423).length < 2 ^ (prefixWord ++ tailWord_863423).sum := by decide
  have hdescent : baseEnd_863423 < baseStart_863423 := by decide
  rcases family_descends (prefixWord ++ tailWord_863423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863500 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_863500 : Nat := 118140960795 + 863500 * 2 ^ 59
def prefixEnd_863500 : Nat := 4983230072969 + 3 ^ 40 * 863500 * 2
def baseEnd_863500 : Nat := 295593696771651190652561

theorem tailTrace_863500 : CollatzResearch.WordTrace tailWord_863500 prefixEnd_863500 295593696771651190652561 := by
  unfold tailWord_863500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15747216185847224452049977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20996288247796299269399969 15747216185847224452049977)
  ·
    refine ⟨11810412139385418339037483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15747216185847224452049977 11810412139385418339037483)
    ·
      refine ⟨17715618209078127508556225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11810412139385418339037483 17715618209078127508556225)
      ·
        refine ⟨13286713656808595631417169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17715618209078127508556225 13286713656808595631417169)
        ·
          refine ⟨9965035242606446723562877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286713656808595631417169 9965035242606446723562877)
          ·
            refine ⟨3736888215977417521336079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9965035242606446723562877 3736888215977417521336079)
            ·
              refine ⟨5605332323966126282004119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736888215977417521336079 5605332323966126282004119)
              ·
                refine ⟨8407998485949189423006179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605332323966126282004119 8407998485949189423006179)
                ·
                  refine ⟨12611997728923784134509269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407998485949189423006179 12611997728923784134509269)
                  ·
                    refine ⟨295593696771651190652561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12611997728923784134509269 295593696771651190652561)
                    ·
                      rfl

theorem cell22_863500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_863500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863500 prefixEnd_863500 := by exact prefixLift 863500
  have htrace : WordTrace (prefixWord ++ tailWord_863500) baseStart_863500 baseEnd_863500 := by
    simpa [prefixWord, tailWord_863500, baseEnd_863500] using wordTrace_append hprefix tailTrace_863500
  have hstable : (prefixWord ++ tailWord_863500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863500).length < 2 ^ (prefixWord ++ tailWord_863500).sum := by decide
  have hdescent : baseEnd_863500 < baseStart_863500 := by decide
  rcases family_descends (prefixWord ++ tailWord_863500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863502 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_863502 : Nat := 118140960795 + 863502 * 2 ^ 59
def prefixEnd_863502 : Nat := 4983230072969 + 3 ^ 40 * 863502 * 2
def baseEnd_863502 : Nat := 98531460470841284034185

theorem tailTrace_863502 : CollatzResearch.WordTrace tailWord_863502 prefixEnd_863502 98531460470841284034185 := by
  unfold tailWord_863502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936813164710900405709095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20996336878458135497115173 3936813164710900405709095)
  ·
    refine ⟨5905219747066350608563643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936813164710900405709095 5905219747066350608563643)
    ·
      refine ⟨8857829620599525912845465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905219747066350608563643 8857829620599525912845465)
      ·
        refine ⟨6643372215449644434634099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8857829620599525912845465 6643372215449644434634099)
        ·
          refine ⟨9965058323174466651951149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643372215449644434634099 9965058323174466651951149)
          ·
            refine ⟨3736896871190424994481681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9965058323174466651951149 3736896871190424994481681)
            ·
              refine ⟨2802672653392818745861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736896871190424994481681 2802672653392818745861261)
              ·
                refine ⟨1051002245022307029697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2802672653392818745861261 1051002245022307029697973)
                ·
                  refine ⟨98531460470841284034185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1051002245022307029697973 98531460470841284034185)
                  ·
                    rfl

theorem cell22_863502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_863502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863502 prefixEnd_863502 := by exact prefixLift 863502
  have htrace : WordTrace (prefixWord ++ tailWord_863502) baseStart_863502 baseEnd_863502 := by
    simpa [prefixWord, tailWord_863502, baseEnd_863502] using wordTrace_append hprefix tailTrace_863502
  have hstable : (prefixWord ++ tailWord_863502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863502).length < 2 ^ (prefixWord ++ tailWord_863502).sum := by decide
  have hdescent : baseEnd_863502 < baseStart_863502 := by decide
  rcases family_descends (prefixWord ++ tailWord_863502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863574 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_863574 : Nat := 118140960795 + 863574 * 2 ^ 59
def prefixEnd_863574 : Nat := 4983230072969 + 3 ^ 40 * 863574 * 2
def baseEnd_863574 : Nat := 295619028483939664302335

theorem tailTrace_863574 : CollatzResearch.WordTrace tailWord_863574 prefixEnd_863574 295619028483939664302335 := by
  unfold tailWord_863574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968570710839147471393361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20998087582284239694862517 1968570710839147471393361)
  ·
    refine ⟨1476428033129360603545021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1968570710839147471393361 1476428033129360603545021)
    ·
      refine ⟨553660512423510226329383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1476428033129360603545021 553660512423510226329383)
      ·
        refine ⟨830490768635265339494075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553660512423510226329383 830490768635265339494075)
        ·
          refine ⟨1245736152952898009241113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830490768635265339494075 1245736152952898009241113)
          ·
            refine ⟨934302114714673506930835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245736152952898009241113 934302114714673506930835)
            ·
              refine ⟨1401453172072010260396253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934302114714673506930835 1401453172072010260396253)
              ·
                refine ⟨525544939527003847648595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1401453172072010260396253 525544939527003847648595)
                ·
                  refine ⟨788317409290505771472893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525544939527003847648595 788317409290505771472893)
                  ·
                    refine ⟨295619028483939664302335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788317409290505771472893 295619028483939664302335)
                    ·
                      rfl

theorem cell22_863574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_863574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863574 prefixEnd_863574 := by exact prefixLift 863574
  have htrace : WordTrace (prefixWord ++ tailWord_863574) baseStart_863574 baseEnd_863574 := by
    simpa [prefixWord, tailWord_863574, baseEnd_863574] using wordTrace_append hprefix tailTrace_863574
  have hstable : (prefixWord ++ tailWord_863574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863574).length < 2 ^ (prefixWord ++ tailWord_863574).sum := by decide
  have hdescent : baseEnd_863574 < baseStart_863574 := by decide
  rcases family_descends (prefixWord ++ tailWord_863574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863598 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_863598 : Nat := 118140960795 + 863598 * 2 ^ 59
def prefixEnd_863598 : Nat := 4983230072969 + 3 ^ 40 * 863598 * 2
def baseEnd_863598 : Nat := 98542414724803867234087

theorem tailTrace_863598 : CollatzResearch.WordTrace tailWord_863598 prefixEnd_863598 98542414724803867234087 := by
  unfold tailWord_863598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937250840667426455145931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20998671150226274427444965 3937250840667426455145931)
  ·
    refine ⟨5905876261001139682718897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937250840667426455145931 5905876261001139682718897)
    ·
      refine ⟨4429407195750854762039173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5905876261001139682718897 4429407195750854762039173)
      ·
        refine ⟨830513849203285267882345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4429407195750854762039173 830513849203285267882345)
        ·
          refine ⟨622885386902463950911759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830513849203285267882345 622885386902463950911759)
          ·
            refine ⟨934328080353695926367639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622885386902463950911759 934328080353695926367639)
            ·
              refine ⟨1401492120530543889551459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934328080353695926367639 1401492120530543889551459)
              ·
                refine ⟨2102238180795815834327189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401492120530543889551459 2102238180795815834327189)
                ·
                  refine ⟨98542414724803867234087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2102238180795815834327189 98542414724803867234087)
                  ·
                    rfl

theorem cell22_863598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_863598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863598 prefixEnd_863598 := by exact prefixLift 863598
  have htrace : WordTrace (prefixWord ++ tailWord_863598) baseStart_863598 baseEnd_863598 := by
    simpa [prefixWord, tailWord_863598, baseEnd_863598] using wordTrace_append hprefix tailTrace_863598
  have hstable : (prefixWord ++ tailWord_863598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863598).length < 2 ^ (prefixWord ++ tailWord_863598).sum := by decide
  have hdescent : baseEnd_863598 < baseStart_863598 := by decide
  rcases family_descends (prefixWord ++ tailWord_863598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863652 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_863652 : Nat := 118140960795 + 863652 * 2 ^ 59
def prefixEnd_863652 : Nat := 4983230072969 + 3 ^ 40 * 863652 * 2
def baseEnd_863652 : Nat := 295645729477973460852095

theorem tailTrace_863652 : CollatzResearch.WordTrace tailWord_863652 prefixEnd_863652 295645729477973460852095 := by
  unfold tailWord_863652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749988133571889431816605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20999984178095852575755473 15749988133571889431816605)
  ·
    refine ⟨5906245550089458536931227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15749988133571889431816605 5906245550089458536931227)
    ·
      refine ⟨8859368325134187805396841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906245550089458536931227 8859368325134187805396841)
      ·
        refine ⟨6644526243850640854047631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859368325134187805396841 6644526243850640854047631)
        ·
          refine ⟨9966789365775961281071447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644526243850640854047631 9966789365775961281071447)
          ·
            refine ⟨14950184048663941921607171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966789365775961281071447 14950184048663941921607171)
            ·
              refine ⟨22425276072995912882410757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14950184048663941921607171 22425276072995912882410757)
              ·
                refine ⟨4204739263686733665452017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22425276072995912882410757 4204739263686733665452017)
                ·
                  refine ⟨3153554447765050249089013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204739263686733665452017 3153554447765050249089013)
                  ·
                    refine ⟨295645729477973460852095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3153554447765050249089013 295645729477973460852095)
                    ·
                      rfl

theorem cell22_863652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_863652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863652 prefixEnd_863652 := by exact prefixLift 863652
  have htrace : WordTrace (prefixWord ++ tailWord_863652) baseStart_863652 baseEnd_863652 := by
    simpa [prefixWord, tailWord_863652, baseEnd_863652] using wordTrace_append hprefix tailTrace_863652
  have hstable : (prefixWord ++ tailWord_863652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863652).length < 2 ^ (prefixWord ++ tailWord_863652).sum := by decide
  have hdescent : baseEnd_863652 < baseStart_863652 := by decide
  rcases family_descends (prefixWord ++ tailWord_863652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863669 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_863669 : Nat := 118140960795 + 863669 * 2 ^ 59
def prefixEnd_863669 : Nat := 4983230072969 + 3 ^ 40 * 863669 * 2
def baseEnd_863669 : Nat := 295651548925391083177043

theorem tailTrace_863669 : CollatzResearch.WordTrace tailWord_863669 prefixEnd_863669 295651548925391083177043 := by
  unfold tailWord_863669
  simp only [CollatzResearch.WordTrace]
  refine ⟨31500596308082190767002061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21000397538721460511334707 31500596308082190767002061)
  ·
    refine ⟨11812723615530821537625773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31500596308082190767002061 11812723615530821537625773)
    ·
      refine ⟨4429771355824058076609665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11812723615530821537625773 4429771355824058076609665)
      ·
        refine ⟨3322328516868043557457249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4429771355824058076609665 3322328516868043557457249)
        ·
          refine ⟨2491746387651032668092937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322328516868043557457249 2491746387651032668092937)
          ·
            refine ⟨1868809790738274501069703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491746387651032668092937 1868809790738274501069703)
            ·
              refine ⟨2803214686107411751604555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868809790738274501069703 2803214686107411751604555)
              ·
                refine ⟨4204822029161117627406833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803214686107411751604555 4204822029161117627406833)
                ·
                  refine ⟨3153616521870838220555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204822029161117627406833 3153616521870838220555125)
                  ·
                    refine ⟨295651548925391083177043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3153616521870838220555125 295651548925391083177043)
                    ·
                      rfl

theorem cell22_863669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_863669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863669 prefixEnd_863669 := by exact prefixLift 863669
  have htrace : WordTrace (prefixWord ++ tailWord_863669) baseStart_863669 baseEnd_863669 := by
    simpa [prefixWord, tailWord_863669, baseEnd_863669] using wordTrace_append hprefix tailTrace_863669
  have hstable : (prefixWord ++ tailWord_863669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863669).length < 2 ^ (prefixWord ++ tailWord_863669).sum := by decide
  have hdescent : baseEnd_863669 < baseStart_863669 := by decide
  rcases family_descends (prefixWord ++ tailWord_863669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863746 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_863746 : Nat := 118140960795 + 863746 * 2 ^ 59
def prefixEnd_863746 : Nat := 4983230072969 + 3 ^ 40 * 863746 * 2
def baseEnd_863746 : Nat := 295677907598988549001807

theorem tailTrace_863746 : CollatzResearch.WordTrace tailWord_863746 prefixEnd_863746 295677907598988549001807 := by
  unfold tailWord_863746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875851182200808229388773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21002269819202155278370061 7875851182200808229388773)
  ·
    refine ⟨1476722096662651543010395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7875851182200808229388773 1476722096662651543010395)
    ·
      refine ⟨2215083144993977314515593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476722096662651543010395 2215083144993977314515593)
      ·
        refine ⟨1661312358745482985886695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2215083144993977314515593 1661312358745482985886695)
        ·
          refine ⟨2491968538118224478830043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661312358745482985886695 2491968538118224478830043)
          ·
            refine ⟨3737952807177336718245065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491968538118224478830043 3737952807177336718245065)
            ·
              refine ⟨2803464605383002538683799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737952807177336718245065 2803464605383002538683799)
              ·
                refine ⟨4205196908074503808025699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803464605383002538683799 4205196908074503808025699)
                ·
                  refine ⟨6307795362111755712038549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205196908074503808025699 6307795362111755712038549)
                  ·
                    refine ⟨295677907598988549001807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6307795362111755712038549 295677907598988549001807)
                    ·
                      rfl

theorem cell22_863746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_863746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863746 prefixEnd_863746 := by exact prefixLift 863746
  have htrace : WordTrace (prefixWord ++ tailWord_863746) baseStart_863746 baseEnd_863746 := by
    simpa [prefixWord, tailWord_863746, baseEnd_863746] using wordTrace_append hprefix tailTrace_863746
  have hstable : (prefixWord ++ tailWord_863746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863746).length < 2 ^ (prefixWord ++ tailWord_863746).sum := by decide
  have hdescent : baseEnd_863746 < baseStart_863746 := by decide
  rcases family_descends (prefixWord ++ tailWord_863746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863836 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_863836 : Nat := 118140960795 + 863836 * 2 ^ 59
def prefixEnd_863836 : Nat := 4983230072969 + 3 ^ 40 * 863836 * 2
def baseEnd_863836 : Nat := 295708716438258314251531

theorem tailTrace_863836 : CollatzResearch.WordTrace tailWord_863836 prefixEnd_863836 295708716438258314251531 := by
  unfold tailWord_863836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15753343649238589144165681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21004458198984785525554241 15753343649238589144165681)
  ·
    refine ⟨11815007736928941858124261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15753343649238589144165681 11815007736928941858124261)
    ·
      refine ⟨2215313950674176598398299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11815007736928941858124261 2215313950674176598398299)
      ·
        refine ⟨3322970926011264897597449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215313950674176598398299 3322970926011264897597449)
        ·
          refine ⟨2492228194508448673198087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322970926011264897597449 2492228194508448673198087)
          ·
            refine ⟨3738342291762673009797131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492228194508448673198087 3738342291762673009797131)
            ·
              refine ⟨5607513437644009514695697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738342291762673009797131 5607513437644009514695697)
              ·
                refine ⟨4205635078233007136021773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607513437644009514695697 4205635078233007136021773)
                ·
                  refine ⟨1577113154337377676008165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4205635078233007136021773 1577113154337377676008165)
                  ·
                    refine ⟨295708716438258314251531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577113154337377676008165 295708716438258314251531)
                    ·
                      rfl

theorem cell22_863836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_863836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863836 prefixEnd_863836 := by exact prefixLift 863836
  have htrace : WordTrace (prefixWord ++ tailWord_863836) baseStart_863836 baseEnd_863836 := by
    simpa [prefixWord, tailWord_863836, baseEnd_863836] using wordTrace_append hprefix tailTrace_863836
  have hstable : (prefixWord ++ tailWord_863836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863836).length < 2 ^ (prefixWord ++ tailWord_863836).sum := by decide
  have hdescent : baseEnd_863836 < baseStart_863836 := by decide
  rcases family_descends (prefixWord ++ tailWord_863836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863849 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_863849 : Nat := 118140960795 + 863849 * 2 ^ 59
def prefixEnd_863849 : Nat := 4983230072969 + 3 ^ 40 * 863849 * 2
def baseEnd_863849 : Nat := 295713166603930613676491

theorem tailTrace_863849 : CollatzResearch.WordTrace tailWord_863849 prefixEnd_863849 295713166603930613676491 := by
  unfold tailWord_863849
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507161447430081508554601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21004774298286721005703067 31507161447430081508554601)
  ·
    refine ⟨23630371085572561131415951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31507161447430081508554601 23630371085572561131415951)
    ·
      refine ⟨35445556628358841697123927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23630371085572561131415951 35445556628358841697123927)
      ·
        refine ⟨53168334942538262545685891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35445556628358841697123927 53168334942538262545685891)
        ·
          refine ⟨79752502413807393818528837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53168334942538262545685891 79752502413807393818528837)
          ·
            refine ⟨14953594202588886340974157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79752502413807393818528837 14953594202588886340974157)
            ·
              refine ⟨5607597825970832377865309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14953594202588886340974157 5607597825970832377865309)
              ·
                refine ⟨2102849184739062141699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5607597825970832377865309 2102849184739062141699491)
                ·
                  refine ⟨3154273777108593212549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102849184739062141699491 3154273777108593212549237)
                  ·
                    refine ⟨295713166603930613676491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3154273777108593212549237 295713166603930613676491)
                    ·
                      rfl

theorem cell22_863849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_863849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863849 prefixEnd_863849 := by exact prefixLift 863849
  have htrace : WordTrace (prefixWord ++ tailWord_863849) baseStart_863849 baseEnd_863849 := by
    simpa [prefixWord, tailWord_863849, baseEnd_863849] using wordTrace_append hprefix tailTrace_863849
  have hstable : (prefixWord ++ tailWord_863849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863849).length < 2 ^ (prefixWord ++ tailWord_863849).sum := by decide
  have hdescent : baseEnd_863849 < baseStart_863849 := by decide
  rcases family_descends (prefixWord ++ tailWord_863849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863879 : List Nat := [1, 1, 4, 2, 1, 4, 9]
def baseStart_863879 : Nat := 118140960795 + 863879 * 2 ^ 59
def prefixEnd_863879 : Nat := 4983230072969 + 3 ^ 40 * 863879 * 2
def baseEnd_863879 : Nat := 10952719859889649460237

theorem tailTrace_863879 : CollatzResearch.WordTrace tailWord_863879 prefixEnd_863879 10952719859889649460237 := by
  unfold tailWord_863879
  simp only [CollatzResearch.WordTrace]
  refine ⟨31508255637321396632146691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21005503758214264421431127 31508255637321396632146691)
  ·
    refine ⟨47262383455982094948220037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31508255637321396632146691 47262383455982094948220037)
    ·
      refine ⟨8861696897996642802791257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47262383455982094948220037 8861696897996642802791257)
      ·
        refine ⟨6646272673497482102093443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8861696897996642802791257 6646272673497482102093443)
        ·
          refine ⟨9969409010246223153140165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646272673497482102093443 9969409010246223153140165)
          ·
            refine ⟨1869264189421166841213781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9969409010246223153140165 1869264189421166841213781)
            ·
              refine ⟨10952719859889649460237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1869264189421166841213781 10952719859889649460237)
              ·
                rfl

theorem cell22_863879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 9].length) (baseStart_863879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863879 prefixEnd_863879 := by exact prefixLift 863879
  have htrace : WordTrace (prefixWord ++ tailWord_863879) baseStart_863879 baseEnd_863879 := by
    simpa [prefixWord, tailWord_863879, baseEnd_863879] using wordTrace_append hprefix tailTrace_863879
  have hstable : (prefixWord ++ tailWord_863879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863879).length < 2 ^ (prefixWord ++ tailWord_863879).sum := by decide
  have hdescent : baseEnd_863879 < baseStart_863879 := by decide
  rcases family_descends (prefixWord ++ tailWord_863879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863900 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_863900 : Nat := 118140960795 + 863900 * 2 ^ 59
def prefixEnd_863900 : Nat := 4983230072969 + 3 ^ 40 * 863900 * 2
def baseEnd_863900 : Nat := 295730624946183480651335

theorem tailTrace_863900 : CollatzResearch.WordTrace tailWord_863900 prefixEnd_863900 295730624946183480651335 := by
  unfold tailWord_863900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754510785122658609330577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21006014380163544812440769 15754510785122658609330577)
  ·
    refine ⟨11815883088841993956997933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15754510785122658609330577 11815883088841993956997933)
    ·
      refine ⟨4430956158315747733874225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11815883088841993956997933 4430956158315747733874225)
      ·
        refine ⟨3323217118736810800405669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430956158315747733874225 3323217118736810800405669)
        ·
          refine ⟨623103209763152025076063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3323217118736810800405669 623103209763152025076063)
          ·
            refine ⟨934654814644728037614095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623103209763152025076063 934654814644728037614095)
            ·
              refine ⟨1401982221967092056421143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934654814644728037614095 1401982221967092056421143)
              ·
                refine ⟨2102973332950638084631715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401982221967092056421143 2102973332950638084631715)
                ·
                  refine ⟨3154459999425957126947573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102973332950638084631715 3154459999425957126947573)
                  ·
                    refine ⟨295730624946183480651335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3154459999425957126947573 295730624946183480651335)
                    ·
                      rfl

theorem cell22_863900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_863900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863900 prefixEnd_863900 := by exact prefixLift 863900
  have htrace : WordTrace (prefixWord ++ tailWord_863900) baseStart_863900 baseEnd_863900 := by
    simpa [prefixWord, tailWord_863900, baseEnd_863900] using wordTrace_append hprefix tailTrace_863900
  have hstable : (prefixWord ++ tailWord_863900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863900).length < 2 ^ (prefixWord ++ tailWord_863900).sum := by decide
  have hdescent : baseEnd_863900 < baseStart_863900 := by decide
  rcases family_descends (prefixWord ++ tailWord_863900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863909 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_863909 : Nat := 118140960795 + 863909 * 2 ^ 59
def prefixEnd_863909 : Nat := 4983230072969 + 3 ^ 40 * 863909 * 2
def baseEnd_863909 : Nat := 295733705830110457176307

theorem tailTrace_863909 : CollatzResearch.WordTrace tailWord_863909 prefixEnd_863909 295733705830110457176307 := by
  unfold tailWord_863909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31509349827212711755738781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21006233218141807837159187 31509349827212711755738781)
  ·
    refine ⟨11816006185204766908402043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31509349827212711755738781 11816006185204766908402043)
    ·
      refine ⟨17724009277807150362603065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11816006185204766908402043 17724009277807150362603065)
      ·
        refine ⟨13293006958355362771952299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17724009277807150362603065 13293006958355362771952299)
        ·
          refine ⟨19939510437533044157928449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13293006958355362771952299 19939510437533044157928449)
          ·
            refine ⟨14954632828149783118446337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19939510437533044157928449 14954632828149783118446337)
            ·
              refine ⟨11215974621112337338834753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14954632828149783118446337 11215974621112337338834753)
              ·
                refine ⟨8411980965834253004126065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11215974621112337338834753 8411980965834253004126065)
                ·
                  refine ⟨6308985724375689753094549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8411980965834253004126065 6308985724375689753094549)
                  ·
                    refine ⟨295733705830110457176307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6308985724375689753094549 295733705830110457176307)
                    ·
                      rfl

theorem cell22_863909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_863909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_863909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_863909 prefixEnd_863909 := by exact prefixLift 863909
  have htrace : WordTrace (prefixWord ++ tailWord_863909) baseStart_863909 baseEnd_863909 := by
    simpa [prefixWord, tailWord_863909, baseEnd_863909] using wordTrace_append hprefix tailTrace_863909
  have hstable : (prefixWord ++ tailWord_863909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863909).length < 2 ^ (prefixWord ++ tailWord_863909).sum := by decide
  have hdescent : baseEnd_863909 < baseStart_863909 := by decide
  rcases family_descends (prefixWord ++ tailWord_863909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864033 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_864033 : Nat := 118140960795 + 864033 * 2 ^ 59
def prefixEnd_864033 : Nat := 4983230072969 + 3 ^ 40 * 864033 * 2
def baseEnd_864033 : Nat := 295776153564215467075927

theorem tailTrace_864033 : CollatzResearch.WordTrace tailWord_864033 prefixEnd_864033 295776153564215467075927 := by
  unfold tailWord_864033
  simp only [CollatzResearch.WordTrace]
  refine ⟨31513872478763480933252753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21009248319175653955501835 31513872478763480933252753)
  ·
    refine ⟨23635404359072610699939565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31513872478763480933252753 23635404359072610699939565)
    ·
      refine ⟨8863276634652229012477337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23635404359072610699939565 8863276634652229012477337)
      ·
        refine ⟨6647457475989171759358003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863276634652229012477337 6647457475989171759358003)
        ·
          refine ⟨9971186213983757639037005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647457475989171759358003 9971186213983757639037005)
          ·
            refine ⟨3739194830243909114638877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9971186213983757639037005 3739194830243909114638877)
            ·
              refine ⟨1402198061341465917989579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3739194830243909114638877 1402198061341465917989579)
              ·
                refine ⟨2103297092012198876984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402198061341465917989579 2103297092012198876984369)
                ·
                  refine ⟨1577472819009149157738277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103297092012198876984369 1577472819009149157738277)
                  ·
                    refine ⟨295776153564215467075927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577472819009149157738277 295776153564215467075927)
                    ·
                      rfl

theorem cell22_864033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_864033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864033 prefixEnd_864033 := by exact prefixLift 864033
  have htrace : WordTrace (prefixWord ++ tailWord_864033) baseStart_864033 baseEnd_864033 := by
    simpa [prefixWord, tailWord_864033, baseEnd_864033] using wordTrace_append hprefix tailTrace_864033
  have hstable : (prefixWord ++ tailWord_864033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864033).length < 2 ^ (prefixWord ++ tailWord_864033).sum := by decide
  have hdescent : baseEnd_864033 < baseStart_864033 := by decide
  rcases family_descends (prefixWord ++ tailWord_864033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864052 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_864052 : Nat := 118140960795 + 864052 * 2 ^ 59
def prefixEnd_864052 : Nat := 4983230072969 + 3 ^ 40 * 864052 * 2
def baseEnd_864052 : Nat := 295782657652505750850869

theorem tailTrace_864052 : CollatzResearch.WordTrace tailWord_864052 prefixEnd_864052 295782657652505750850869 := by
  unfold tailWord_864052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757282732847323589097205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21009710310463098118796273 15757282732847323589097205)
  ·
    refine ⟨1477245256204436586477863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15757282732847323589097205 1477245256204436586477863)
    ·
      refine ⟨2215867884306654879716795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477245256204436586477863 2215867884306654879716795)
      ·
        refine ⟨3323801826459982319575193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215867884306654879716795 3323801826459982319575193)
        ·
          refine ⟨2492851369844986739681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323801826459982319575193 2492851369844986739681395)
          ·
            refine ⟨3739277054767480109522093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492851369844986739681395 3739277054767480109522093)
            ·
              refine ⟨1402228895537805041070785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3739277054767480109522093 1402228895537805041070785)
              ·
                refine ⟨1051671671653353780803089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402228895537805041070785 1051671671653353780803089)
                ·
                  refine ⟨788753753740015335602317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051671671653353780803089 788753753740015335602317)
                  ·
                    refine ⟨295782657652505750850869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788753753740015335602317 295782657652505750850869)
                    ·
                      rfl

theorem cell22_864052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_864052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864052 prefixEnd_864052 := by exact prefixLift 864052
  have htrace : WordTrace (prefixWord ++ tailWord_864052) baseStart_864052 baseEnd_864052 := by
    simpa [prefixWord, tailWord_864052, baseEnd_864052] using wordTrace_append hprefix tailTrace_864052
  have hstable : (prefixWord ++ tailWord_864052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864052).length < 2 ^ (prefixWord ++ tailWord_864052).sum := by decide
  have hdescent : baseEnd_864052 < baseStart_864052 := by decide
  rcases family_descends (prefixWord ++ tailWord_864052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864153 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_864153 : Nat := 118140960795 + 864153 * 2 ^ 59
def prefixEnd_864153 : Nat := 4983230072969 + 3 ^ 40 * 864153 * 2
def baseEnd_864153 : Nat := 295817232016575154075559

theorem tailTrace_864153 : CollatzResearch.WordTrace tailWord_864153 prefixEnd_864153 295817232016575154075559 := by
  unfold tailWord_864153
  simp only [CollatzResearch.WordTrace]
  refine ⟨31518249238328741427621113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21012166158885827618414075 31518249238328741427621113)
  ·
    refine ⟨23638686928746556070715835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31518249238328741427621113 23638686928746556070715835)
    ·
      refine ⟨35458030393119834106073753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23638686928746556070715835 35458030393119834106073753)
      ·
        refine ⟨26593522794839875579555315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35458030393119834106073753 26593522794839875579555315)
        ·
          refine ⟨39890284192259813369332973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26593522794839875579555315 39890284192259813369332973)
          ·
            refine ⟨14958856572097430013499865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39890284192259813369332973 14958856572097430013499865)
            ·
              refine ⟨11219142429073072510124899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14958856572097430013499865 11219142429073072510124899)
              ·
                refine ⟨16828713643609608765187349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219142429073072510124899 16828713643609608765187349)
                ·
                  refine ⟨788845952044200410868157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16828713643609608765187349 788845952044200410868157)
                  ·
                    refine ⟨295817232016575154075559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788845952044200410868157 295817232016575154075559)
                    ·
                      rfl

theorem cell22_864153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_864153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864153 prefixEnd_864153 := by exact prefixLift 864153
  have htrace : WordTrace (prefixWord ++ tailWord_864153) baseStart_864153 baseEnd_864153 := by
    simpa [prefixWord, tailWord_864153, baseEnd_864153] using wordTrace_append hprefix tailTrace_864153
  have hstable : (prefixWord ++ tailWord_864153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864153).length < 2 ^ (prefixWord ++ tailWord_864153).sum := by decide
  have hdescent : baseEnd_864153 < baseStart_864153 := by decide
  rcases family_descends (prefixWord ++ tailWord_864153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864157 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_864157 : Nat := 118140960795 + 864157 * 2 ^ 59
def prefixEnd_864157 : Nat := 4983230072969 + 3 ^ 40 * 864157 * 2
def baseEnd_864157 : Nat := 295818601298320476975547

theorem tailTrace_864157 : CollatzResearch.WordTrace tailWord_864157 prefixEnd_864157 295818601298320476975547 := by
  unfold tailWord_864157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31518395130314250110766725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21012263420209500073844483 31518395130314250110766725)
  ·
    refine ⟨5909699086933921895768761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31518395130314250110766725 5909699086933921895768761)
    ·
      refine ⟨4432274315200441421826571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5909699086933921895768761 4432274315200441421826571)
      ·
        refine ⟨6648411472800662132739857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432274315200441421826571 6648411472800662132739857)
        ·
          refine ⟨4986308604600496599554893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648411472800662132739857 4986308604600496599554893)
          ·
            refine ⟨1869865726725186224833085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4986308604600496599554893 1869865726725186224833085)
            ·
              refine ⟨701199647521944834312407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1869865726725186224833085 701199647521944834312407)
              ·
                refine ⟨1051799471282917251468611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701199647521944834312407 1051799471282917251468611)
                ·
                  refine ⟨1577699206924375877202917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051799471282917251468611 1577699206924375877202917)
                  ·
                    refine ⟨295818601298320476975547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577699206924375877202917 295818601298320476975547)
                    ·
                      rfl

theorem cell22_864157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_864157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864157 prefixEnd_864157 := by exact prefixLift 864157
  have htrace : WordTrace (prefixWord ++ tailWord_864157) baseStart_864157 baseEnd_864157 := by
    simpa [prefixWord, tailWord_864157, baseEnd_864157] using wordTrace_append hprefix tailTrace_864157
  have hstable : (prefixWord ++ tailWord_864157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864157).length < 2 ^ (prefixWord ++ tailWord_864157).sum := by decide
  have hdescent : baseEnd_864157 < baseStart_864157 := by decide
  rcases family_descends (prefixWord ++ tailWord_864157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864200 : List Nat := [2, 1, 3, 1, 4, 2, 3, 6]
def baseStart_864200 : Nat := 118140960795 + 864200 * 2 ^ 59
def prefixEnd_864200 : Nat := 4983230072969 + 3 ^ 40 * 864200 * 2
def baseEnd_864200 : Nat := 32870369008564744238935

theorem tailTrace_864200 : CollatzResearch.WordTrace tailWord_864200 prefixEnd_864200 32870369008564744238935 := by
  unfold tailWord_864200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759981734579234227291027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21013308979438978969721369 15759981734579234227291027)
  ·
    refine ⟨23639972601868851340936541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759981734579234227291027 23639972601868851340936541)
    ·
      refine ⟨8864989725700819252851203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23639972601868851340936541 8864989725700819252851203)
      ·
        refine ⟨13297484588551228879276805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8864989725700819252851203 13297484588551228879276805)
        ·
          refine ⟨2493278360353355414864401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13297484588551228879276805 2493278360353355414864401)
          ·
            refine ⟨1869958770265016561148301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493278360353355414864401 1869958770265016561148301)
            ·
              refine ⟨701234538849381210430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1869958770265016561148301 701234538849381210430613)
              ·
                refine ⟨32870369008564744238935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 701234538849381210430613 32870369008564744238935)
                ·
                  rfl

theorem cell22_864200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_864200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864200 prefixEnd_864200 := by exact prefixLift 864200
  have htrace : WordTrace (prefixWord ++ tailWord_864200) baseStart_864200 baseEnd_864200 := by
    simpa [prefixWord, tailWord_864200, baseEnd_864200] using wordTrace_append hprefix tailTrace_864200
  have hstable : (prefixWord ++ tailWord_864200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864200).length < 2 ^ (prefixWord ++ tailWord_864200).sum := by decide
  have hdescent : baseEnd_864200 < baseStart_864200 := by decide
  rcases family_descends (prefixWord ++ tailWord_864200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864221 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_864221 : Nat := 118140960795 + 864221 * 2 ^ 59
def prefixEnd_864221 : Nat := 4983230072969 + 3 ^ 40 * 864221 * 2
def baseEnd_864221 : Nat := 295840509806245643375351

theorem tailTrace_864221 : CollatzResearch.WordTrace tailWord_864221 prefixEnd_864221 295840509806245643375351 := by
  unfold tailWord_864221
  simp only [CollatzResearch.WordTrace]
  refine ⟨31520729402082389041096517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21013819601388259360731011 31520729402082389041096517)
  ·
    refine ⟨5910136762890447945205597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31520729402082389041096517 5910136762890447945205597)
    ·
      refine ⟨2216301286083917979452099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5910136762890447945205597 2216301286083917979452099)
      ·
        refine ⟨3324451929125876969178149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216301286083917979452099 3324451929125876969178149)
        ·
          refine ⟨623334736711101931720903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3324451929125876969178149 623334736711101931720903)
          ·
            refine ⟨935002105066652897581355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623334736711101931720903 935002105066652897581355)
            ·
              refine ⟨1402503157599979346372033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935002105066652897581355 1402503157599979346372033)
              ·
                refine ⟨1051877368199984509779025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402503157599979346372033 1051877368199984509779025)
                ·
                  refine ⟨788908026149988382334269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051877368199984509779025 788908026149988382334269)
                  ·
                    refine ⟨295840509806245643375351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788908026149988382334269 295840509806245643375351)
                    ·
                      rfl

theorem cell22_864221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_864221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864221 prefixEnd_864221 := by exact prefixLift 864221
  have htrace : WordTrace (prefixWord ++ tailWord_864221) baseStart_864221 baseEnd_864221 := by
    simpa [prefixWord, tailWord_864221, baseEnd_864221] using wordTrace_append hprefix tailTrace_864221
  have hstable : (prefixWord ++ tailWord_864221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864221).length < 2 ^ (prefixWord ++ tailWord_864221).sum := by decide
  have hdescent : baseEnd_864221 < baseStart_864221 := by decide
  rcases family_descends (prefixWord ++ tailWord_864221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864228 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_864228 : Nat := 118140960795 + 864228 * 2 ^ 59
def prefixEnd_864228 : Nat := 4983230072969 + 3 ^ 40 * 864228 * 2
def baseEnd_864228 : Nat := 98614302016433319483443

theorem tailTrace_864228 : CollatzResearch.WordTrace tailWord_864228 prefixEnd_864228 98614302016433319483443 := by
  unfold tailWord_864228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760492356528514618300669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21013989808704686157734225 15760492356528514618300669)
  ·
    refine ⟨5910184633698192981862751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15760492356528514618300669 5910184633698192981862751)
    ·
      refine ⟨8865276950547289472794127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910184633698192981862751 8865276950547289472794127)
      ·
        refine ⟨13297915425820934209191191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865276950547289472794127 13297915425820934209191191)
        ·
          refine ⟨19946873138731401313786787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297915425820934209191191 19946873138731401313786787)
          ·
            refine ⟨29920309708097101970680181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946873138731401313786787 29920309708097101970680181)
            ·
              refine ⟨2805029035134103309751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29920309708097101970680181 2805029035134103309751267)
              ·
                refine ⟨4207543552701154964626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805029035134103309751267 4207543552701154964626901)
                ·
                  refine ⟨98614302016433319483443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4207543552701154964626901 98614302016433319483443)
                  ·
                    rfl

theorem cell22_864228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_864228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864228 prefixEnd_864228 := by exact prefixLift 864228
  have htrace : WordTrace (prefixWord ++ tailWord_864228) baseStart_864228 baseEnd_864228 := by
    simpa [prefixWord, tailWord_864228, baseEnd_864228] using wordTrace_append hprefix tailTrace_864228
  have hstable : (prefixWord ++ tailWord_864228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864228).length < 2 ^ (prefixWord ++ tailWord_864228).sum := by decide
  have hdescent : baseEnd_864228 < baseStart_864228 := by decide
  rcases family_descends (prefixWord ++ tailWord_864228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864266 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_864266 : Nat := 118140960795 + 864266 * 2 ^ 59
def prefixEnd_864266 : Nat := 4983230072969 + 3 ^ 40 * 864266 * 2
def baseEnd_864266 : Nat := 295855914225880526000213

theorem tailTrace_864266 : CollatzResearch.WordTrace tailWord_864266 prefixEnd_864266 295855914225880526000213 := by
  unfold tailWord_864266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880592671729840431621163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21014913791279574484323101 7880592671729840431621163)
  ·
    refine ⟨11820889007594760647431745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880592671729840431621163 11820889007594760647431745)
    ·
      refine ⟨8865666755696070485573809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11820889007594760647431745 8865666755696070485573809)
      ·
        refine ⟨6649250066772052864180357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8865666755696070485573809 6649250066772052864180357)
        ·
          refine ⟨1246734387519759912033817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6649250066772052864180357 1246734387519759912033817)
          ·
            refine ⟨935050790639819934025363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246734387519759912033817 935050790639819934025363)
            ·
              refine ⟨1402576185959729901038045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935050790639819934025363 1402576185959729901038045)
              ·
                refine ⟨525966069734898712889267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402576185959729901038045 525966069734898712889267)
                ·
                  refine ⟨788949104602348069333901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525966069734898712889267 788949104602348069333901)
                  ·
                    refine ⟨295855914225880526000213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788949104602348069333901 295855914225880526000213)
                    ·
                      rfl

theorem cell22_864266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_864266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864266 prefixEnd_864266 := by exact prefixLift 864266
  have htrace : WordTrace (prefixWord ++ tailWord_864266) baseStart_864266 baseEnd_864266 := by
    simpa [prefixWord, tailWord_864266, baseEnd_864266] using wordTrace_append hprefix tailTrace_864266
  have hstable : (prefixWord ++ tailWord_864266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864266).length < 2 ^ (prefixWord ++ tailWord_864266).sum := by decide
  have hdescent : baseEnd_864266 < baseStart_864266 := by decide
  rcases family_descends (prefixWord ++ tailWord_864266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864275 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 1, 4]
def baseStart_864275 : Nat := 118140960795 + 864275 * 2 ^ 59
def prefixEnd_864275 : Nat := 4983230072969 + 3 ^ 40 * 864275 * 2
def baseEnd_864275 : Nat := 295858995109807502525185

theorem tailTrace_864275 : CollatzResearch.WordTrace tailWord_864275 prefixEnd_864275 295858995109807502525185 := by
  unfold tailWord_864275
  simp only [CollatzResearch.WordTrace]
  refine ⟨31522698943886756263562279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21015132629257837509041519 31522698943886756263562279)
  ·
    refine ⟨47284048415830134395343419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31522698943886756263562279 47284048415830134395343419)
    ·
      refine ⟨70926072623745201593015129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47284048415830134395343419 70926072623745201593015129)
      ·
        refine ⟨53194554467808901194761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70926072623745201593015129 53194554467808901194761347)
        ·
          refine ⟨79791831701713351792142021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53194554467808901194761347 79791831701713351792142021)
          ·
            refine ⟨14960968444071253461026629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79791831701713351792142021 14960968444071253461026629)
            ·
              refine ⟨2805181583263360023942493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14960968444071253461026629 2805181583263360023942493)
              ·
                refine ⟨1051943093723760008978435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2805181583263360023942493 1051943093723760008978435)
                ·
                  refine ⟨1577914640585640013467653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051943093723760008978435 1577914640585640013467653)
                  ·
                    refine ⟨295858995109807502525185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577914640585640013467653 295858995109807502525185)
                    ·
                      rfl

theorem cell22_864275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_864275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864275 prefixEnd_864275 := by exact prefixLift 864275
  have htrace : WordTrace (prefixWord ++ tailWord_864275) baseStart_864275 baseEnd_864275 := by
    simpa [prefixWord, tailWord_864275, baseEnd_864275] using wordTrace_append hprefix tailTrace_864275
  have hstable : (prefixWord ++ tailWord_864275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864275).length < 2 ^ (prefixWord ++ tailWord_864275).sum := by decide
  have hdescent : baseEnd_864275 < baseStart_864275 := by decide
  rcases family_descends (prefixWord ++ tailWord_864275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864296 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_864296 : Nat := 118140960795 + 864296 * 2 ^ 59
def prefixEnd_864296 : Nat := 4983230072969 + 3 ^ 40 * 864296 * 2
def baseEnd_864296 : Nat := 98622061279656815916707

theorem tailTrace_864296 : CollatzResearch.WordTrace tailWord_864296 prefixEnd_864296 98622061279656815916707 := by
  unfold tailWord_864296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761732438405338425038371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21015643251207117900051161 15761732438405338425038371)
  ·
    refine ⟨23642598657608007637557557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15761732438405338425038371 23642598657608007637557557)
    ·
      refine ⟨2216493624150750716021021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23642598657608007637557557 2216493624150750716021021)
      ·
        refine ⟨831185109056531518507883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2216493624150750716021021 831185109056531518507883)
        ·
          refine ⟨1246777663584797277761825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831185109056531518507883 1246777663584797277761825)
          ·
            refine ⟨935083247688597958321369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246777663584797277761825 935083247688597958321369)
            ·
              refine ⟨701312435766448468741027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935083247688597958321369 701312435766448468741027)
              ·
                refine ⟨1051968653649672703111541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701312435766448468741027 1051968653649672703111541)
                ·
                  refine ⟨98622061279656815916707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1051968653649672703111541 98622061279656815916707)
                  ·
                    rfl

theorem cell22_864296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_864296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864296 prefixEnd_864296 := by exact prefixLift 864296
  have htrace : WordTrace (prefixWord ++ tailWord_864296) baseStart_864296 baseEnd_864296 := by
    simpa [prefixWord, tailWord_864296, baseEnd_864296] using wordTrace_append hprefix tailTrace_864296
  have hstable : (prefixWord ++ tailWord_864296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864296).length < 2 ^ (prefixWord ++ tailWord_864296).sum := by decide
  have hdescent : baseEnd_864296 < baseStart_864296 := by decide
  rcases family_descends (prefixWord ++ tailWord_864296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864303 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_864303 : Nat := 118140960795 + 864303 * 2 ^ 59
def prefixEnd_864303 : Nat := 4983230072969 + 3 ^ 40 * 864303 * 2
def baseEnd_864303 : Nat := 295868580082024762825099

theorem tailTrace_864303 : CollatzResearch.WordTrace tailWord_864303 prefixEnd_864303 295868580082024762825099 := by
  unfold tailWord_864303
  simp only [CollatzResearch.WordTrace]
  refine ⟨31523720187785317045581563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21015813458523544697054375 31523720187785317045581563)
  ·
    refine ⟨47285580281677975568372345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31523720187785317045581563 47285580281677975568372345)
    ·
      refine ⟨35464185211258481676279259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47285580281677975568372345 35464185211258481676279259)
      ·
        refine ⟨53196277816887722514418889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35464185211258481676279259 53196277816887722514418889)
        ·
          refine ⟨39897208362665791885814167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53196277816887722514418889 39897208362665791885814167)
          ·
            refine ⟨59845812543998687828721251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39897208362665791885814167 59845812543998687828721251)
            ·
              refine ⟨89768718815998031743081877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59845812543998687828721251 89768718815998031743081877)
              ·
                refine ⟨4207908694499907737956963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89768718815998031743081877 4207908694499907737956963)
                ·
                  refine ⟨6311863041749861606935445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207908694499907737956963 6311863041749861606935445)
                  ·
                    refine ⟨295868580082024762825099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6311863041749861606935445 295868580082024762825099)
                    ·
                      rfl

theorem cell22_864303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_864303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864303 prefixEnd_864303 := by exact prefixLift 864303
  have htrace : WordTrace (prefixWord ++ tailWord_864303) baseStart_864303 baseEnd_864303 := by
    simpa [prefixWord, tailWord_864303, baseEnd_864303] using wordTrace_append hprefix tailTrace_864303
  have hstable : (prefixWord ++ tailWord_864303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864303).length < 2 ^ (prefixWord ++ tailWord_864303).sum := by decide
  have hdescent : baseEnd_864303 < baseStart_864303 := by decide
  rcases family_descends (prefixWord ++ tailWord_864303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864320 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_864320 : Nat := 118140960795 + 864320 * 2 ^ 59
def prefixEnd_864320 : Nat := 4983230072969 + 3 ^ 40 * 864320 * 2
def baseEnd_864320 : Nat := 295874399529442385150047

theorem tailTrace_864320 : CollatzResearch.WordTrace tailWord_864320 prefixEnd_864320 295874399529442385150047 := by
  unfold tailWord_864320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762170114361864474475207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21016226819149152632633609 15762170114361864474475207)
  ·
    refine ⟨23643255171542796711712811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15762170114361864474475207 23643255171542796711712811)
    ·
      refine ⟨35464882757314195067569217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643255171542796711712811 35464882757314195067569217)
      ·
        refine ⟨26598662067985646300676913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35464882757314195067569217 26598662067985646300676913)
        ·
          refine ⟨19948996550989234725507685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26598662067985646300676913 19948996550989234725507685)
          ·
            refine ⟨3740436853310481511032691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19948996550989234725507685 3740436853310481511032691)
            ·
              refine ⟨5610655279965722266549037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740436853310481511032691 5610655279965722266549037)
              ·
                refine ⟨2103995729987145849955889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5610655279965722266549037 2103995729987145849955889)
                ·
                  refine ⟨1577996797490359387466917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103995729987145849955889 1577996797490359387466917)
                  ·
                    refine ⟨295874399529442385150047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1577996797490359387466917 295874399529442385150047)
                    ·
                      rfl

theorem cell22_864320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_864320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864320 prefixEnd_864320 := by exact prefixLift 864320
  have htrace : WordTrace (prefixWord ++ tailWord_864320) baseStart_864320 baseEnd_864320 := by
    simpa [prefixWord, tailWord_864320, baseEnd_864320] using wordTrace_append hprefix tailTrace_864320
  have hstable : (prefixWord ++ tailWord_864320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864320).length < 2 ^ (prefixWord ++ tailWord_864320).sum := by decide
  have hdescent : baseEnd_864320 < baseStart_864320 := by decide
  rcases family_descends (prefixWord ++ tailWord_864320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864326 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_864326 : Nat := 118140960795 + 864326 * 2 ^ 59
def prefixEnd_864326 : Nat := 4983230072969 + 3 ^ 40 * 864326 * 2
def baseEnd_864326 : Nat := 295876453452060369500029

theorem tailTrace_864326 : CollatzResearch.WordTrace tailWord_864326 prefixEnd_864326 295876453452060369500029 := by
  unfold tailWord_864326
  simp only [CollatzResearch.WordTrace]
  refine ⟨985142470834437249177151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21016372711134661315779221 985142470834437249177151)
  ·
    refine ⟨1477713706251655873765727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985142470834437249177151 1477713706251655873765727)
    ·
      refine ⟨2216570559377483810648591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477713706251655873765727 2216570559377483810648591)
      ·
        refine ⟨3324855839066225715972887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216570559377483810648591 3324855839066225715972887)
        ·
          refine ⟨4987283758599338573959331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324855839066225715972887 4987283758599338573959331)
          ·
            refine ⟨7480925637899007860938997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987283758599338573959331 7480925637899007860938997)
            ·
              refine ⟨701336778553031986963031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7480925637899007860938997 701336778553031986963031)
              ·
                refine ⟨1052005167829547980444547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701336778553031986963031 1052005167829547980444547)
                ·
                  refine ⟨1578007751744321970666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052005167829547980444547 1578007751744321970666821)
                  ·
                    refine ⟨295876453452060369500029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578007751744321970666821 295876453452060369500029)
                    ·
                      rfl

theorem cell22_864326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_864326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864326 prefixEnd_864326 := by exact prefixLift 864326
  have htrace : WordTrace (prefixWord ++ tailWord_864326) baseStart_864326 baseEnd_864326 := by
    simpa [prefixWord, tailWord_864326, baseEnd_864326] using wordTrace_append hprefix tailTrace_864326
  have hstable : (prefixWord ++ tailWord_864326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864326).length < 2 ^ (prefixWord ++ tailWord_864326).sum := by decide
  have hdescent : baseEnd_864326 < baseStart_864326 := by decide
  rcases family_descends (prefixWord ++ tailWord_864326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864365 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_864365 : Nat := 118140960795 + 864365 * 2 ^ 59
def prefixEnd_864365 : Nat := 4983230072969 + 3 ^ 40 * 864365 * 2
def baseEnd_864365 : Nat := 295889803949077267774909

theorem tailTrace_864365 : CollatzResearch.WordTrace tailWord_864365 prefixEnd_864365 295889803949077267774909 := by
  unfold tailWord_864365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525981513560701634338549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21017321009040467756225699 31525981513560701634338549)
  ·
    refine ⟨2955560766896315778219239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31525981513560701634338549 2955560766896315778219239)
    ·
      refine ⟨4433341150344473667328859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955560766896315778219239 4433341150344473667328859)
      ·
        refine ⟨6650011725516710500993289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433341150344473667328859 6650011725516710500993289)
        ·
          refine ⟨4987508794137532875744967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6650011725516710500993289 4987508794137532875744967)
          ·
            refine ⟨7481263191206299313617451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987508794137532875744967 7481263191206299313617451)
            ·
              refine ⟨11221894786809448970426177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481263191206299313617451 11221894786809448970426177)
              ·
                refine ⟨8416421090107086727819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11221894786809448970426177 8416421090107086727819633)
                ·
                  refine ⟨6312315817580315045864725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8416421090107086727819633 6312315817580315045864725)
                  ·
                    refine ⟨295889803949077267774909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6312315817580315045864725 295889803949077267774909)
                    ·
                      rfl

theorem cell22_864365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_864365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864365 prefixEnd_864365 := by exact prefixLift 864365
  have htrace : WordTrace (prefixWord ++ tailWord_864365) baseStart_864365 baseEnd_864365 := by
    simpa [prefixWord, tailWord_864365, baseEnd_864365] using wordTrace_append hprefix tailTrace_864365
  have hstable : (prefixWord ++ tailWord_864365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864365).length < 2 ^ (prefixWord ++ tailWord_864365).sum := by decide
  have hdescent : baseEnd_864365 < baseStart_864365 := by decide
  rcases family_descends (prefixWord ++ tailWord_864365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864367 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 3, 3]
def baseStart_864367 : Nat := 118140960795 + 864367 * 2 ^ 59
def prefixEnd_864367 : Nat := 4983230072969 + 3 ^ 40 * 864367 * 2
def baseEnd_864367 : Nat := 295890488589949929224903

theorem tailTrace_864367 : CollatzResearch.WordTrace tailWord_864367 prefixEnd_864367 295890488589949929224903 := by
  unfold tailWord_864367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526054459553455975911355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21017369639702303983940903 31526054459553455975911355)
  ·
    refine ⟨47289081689330183963867033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31526054459553455975911355 47289081689330183963867033)
    ·
      refine ⟨35466811266997637972900275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47289081689330183963867033 35466811266997637972900275)
      ·
        refine ⟨53200216900496456959350413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35466811266997637972900275 53200216900496456959350413)
        ·
          refine ⟨19950081337686171359756405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53200216900496456959350413 19950081337686171359756405)
          ·
            refine ⟨1870320125408078564977163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19950081337686171359756405 1870320125408078564977163)
            ·
              refine ⟨2805480188112117847465745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870320125408078564977163 2805480188112117847465745)
              ·
                refine ⟨2104110141084088385599309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805480188112117847465745 2104110141084088385599309)
                ·
                  refine ⟨789041302906533144599741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2104110141084088385599309 789041302906533144599741)
                  ·
                    refine ⟨295890488589949929224903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789041302906533144599741 295890488589949929224903)
                    ·
                      rfl

theorem cell22_864367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_864367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864367 prefixEnd_864367 := by exact prefixLift 864367
  have htrace : WordTrace (prefixWord ++ tailWord_864367) baseStart_864367 baseEnd_864367 := by
    simpa [prefixWord, tailWord_864367, baseEnd_864367] using wordTrace_append hprefix tailTrace_864367
  have hstable : (prefixWord ++ tailWord_864367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864367).length < 2 ^ (prefixWord ++ tailWord_864367).sum := by decide
  have hdescent : baseEnd_864367 < baseStart_864367 := by decide
  rcases family_descends (prefixWord ++ tailWord_864367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864440 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_864440 : Nat := 118140960795 + 864440 * 2 ^ 59
def prefixEnd_864440 : Nat := 4983230072969 + 3 ^ 40 * 864440 * 2
def baseEnd_864440 : Nat := 295915477981802072149679

theorem tailTrace_864440 : CollatzResearch.WordTrace tailWord_864440 prefixEnd_864440 295915477981802072149679 := by
  unfold tailWord_864440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15764358494144494721659387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21019144658859326295545849 15764358494144494721659387)
  ·
    refine ⟨23646537741216742082489081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15764358494144494721659387 23646537741216742082489081)
    ·
      refine ⟨17734903305912556561866811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23646537741216742082489081 17734903305912556561866811)
      ·
        refine ⟨26602354958868834842800217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17734903305912556561866811 26602354958868834842800217)
        ·
          refine ⟨19951766219151626132100163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26602354958868834842800217 19951766219151626132100163)
          ·
            refine ⟨29927649328727439198150245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19951766219151626132100163 29927649328727439198150245)
            ·
              refine ⟨5611434249136394849653171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29927649328727439198150245 5611434249136394849653171)
              ·
                refine ⟨8417151373704592274479757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611434249136394849653171 8417151373704592274479757)
                ·
                  refine ⟨3156431765139222102929909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8417151373704592274479757 3156431765139222102929909)
                  ·
                    refine ⟨295915477981802072149679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3156431765139222102929909 295915477981802072149679)
                    ·
                      rfl

theorem cell22_864440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_864440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864440 prefixEnd_864440 := by exact prefixLift 864440
  have htrace : WordTrace (prefixWord ++ tailWord_864440) baseStart_864440 baseEnd_864440 := by
    simpa [prefixWord, tailWord_864440, baseEnd_864440] using wordTrace_append hprefix tailTrace_864440
  have hstable : (prefixWord ++ tailWord_864440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864440).length < 2 ^ (prefixWord ++ tailWord_864440).sum := by decide
  have hdescent : baseEnd_864440 < baseStart_864440 := by decide
  rcases family_descends (prefixWord ++ tailWord_864440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864459 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 4]
def baseStart_864459 : Nat := 118140960795 + 864459 * 2 ^ 59
def prefixEnd_864459 : Nat := 4983230072969 + 3 ^ 40 * 864459 * 2
def baseEnd_864459 : Nat := 98640660690030785308207

theorem tailTrace_864459 : CollatzResearch.WordTrace tailWord_864459 prefixEnd_864459 98640660690030785308207 := by
  unfold tailWord_864459
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529409975220155688260431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21019606650146770458840287 31529409975220155688260431)
  ·
    refine ⟨47294114962830233532390647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31529409975220155688260431 47294114962830233532390647)
    ·
      refine ⟨70941172444245350298585971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47294114962830233532390647 70941172444245350298585971)
      ·
        refine ⟨106411758666368025447878957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70941172444245350298585971 106411758666368025447878957)
        ·
          refine ⟨39904409499888009542954609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106411758666368025447878957 39904409499888009542954609)
          ·
            refine ⟨29928307124916007157215957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39904409499888009542954609 29928307124916007157215957)
            ·
              refine ⟨701444698240218917747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29928307124916007157215957 701444698240218917747249)
              ·
                refine ⟨526083523680164188310437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701444698240218917747249 526083523680164188310437)
                ·
                  refine ⟨98640660690030785308207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526083523680164188310437 98640660690030785308207)
                  ·
                    rfl

theorem cell22_864459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 4].length) (baseStart_864459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864459 prefixEnd_864459 := by exact prefixLift 864459
  have htrace : WordTrace (prefixWord ++ tailWord_864459) baseStart_864459 baseEnd_864459 := by
    simpa [prefixWord, tailWord_864459, baseEnd_864459] using wordTrace_append hprefix tailTrace_864459
  have hstable : (prefixWord ++ tailWord_864459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864459).length < 2 ^ (prefixWord ++ tailWord_864459).sum := by decide
  have hdescent : baseEnd_864459 < baseStart_864459 := by decide
  rcases family_descends (prefixWord ++ tailWord_864459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864487 : List Nat := [1, 1, 5, 3, 1, 1, 2, 8]
def baseStart_864487 : Nat := 118140960795 + 864487 * 2 ^ 59
def prefixEnd_864487 : Nat := 4983230072969 + 3 ^ 40 * 864487 * 2
def baseEnd_864487 : Nat := 32881285226923290691615

theorem tailTrace_864487 : CollatzResearch.WordTrace tailWord_864487 prefixEnd_864487 32881285226923290691615 := by
  unfold tailWord_864487
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530431219118716470279715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21020287479412477646853143 31530431219118716470279715)
  ·
    refine ⟨47295646828678074705419573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31530431219118716470279715 47295646828678074705419573)
    ·
      refine ⟨4433966890188569503633085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47295646828678074705419573 4433966890188569503633085)
      ·
        refine ⟨1662737583820713563862407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4433966890188569503633085 1662737583820713563862407)
        ·
          refine ⟨2494106375731070345793611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662737583820713563862407 2494106375731070345793611)
          ·
            refine ⟨3741159563596605518690417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494106375731070345793611 3741159563596605518690417)
            ·
              refine ⟨2805869672697454139017813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3741159563596605518690417 2805869672697454139017813)
              ·
                refine ⟨32881285226923290691615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2805869672697454139017813 32881285226923290691615)
                ·
                  rfl

theorem cell22_864487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 8].length) (baseStart_864487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864487 prefixEnd_864487 := by exact prefixLift 864487
  have htrace : WordTrace (prefixWord ++ tailWord_864487) baseStart_864487 baseEnd_864487 := by
    simpa [prefixWord, tailWord_864487, baseEnd_864487] using wordTrace_append hprefix tailTrace_864487
  have hstable : (prefixWord ++ tailWord_864487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864487).length < 2 ^ (prefixWord ++ tailWord_864487).sum := by decide
  have hdescent : baseEnd_864487 < baseStart_864487 := by decide
  rcases family_descends (prefixWord ++ tailWord_864487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864564 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_864564 : Nat := 118140960795 + 864564 * 2 ^ 59
def prefixEnd_864564 : Nat := 4983230072969 + 3 ^ 40 * 864564 * 2
def baseEnd_864564 : Nat := 295957925715907082049299

theorem tailTrace_864564 : CollatzResearch.WordTrace tailWord_864564 prefixEnd_864564 295957925715907082049299 := by
  unfold tailWord_864564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766619819919879310416373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21022159759893172413888497 15766619819919879310416373)
  ·
    refine ⟨1478120608117488685351535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15766619819919879310416373 1478120608117488685351535)
    ·
      refine ⟨2217180912176233028027303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478120608117488685351535 2217180912176233028027303)
      ·
        refine ⟨3325771368264349542040955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217180912176233028027303 3325771368264349542040955)
        ·
          refine ⟨4988657052396524313061433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325771368264349542040955 4988657052396524313061433)
          ·
            refine ⟨3741492789297393234796075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4988657052396524313061433 3741492789297393234796075)
            ·
              refine ⟨5612239183946089852194113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741492789297393234796075 5612239183946089852194113)
              ·
                refine ⟨4209179387959567389145585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5612239183946089852194113 4209179387959567389145585)
                ·
                  refine ⟨3156884540969675541859189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4209179387959567389145585 3156884540969675541859189)
                  ·
                    refine ⟨295957925715907082049299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3156884540969675541859189 295957925715907082049299)
                    ·
                      rfl

theorem cell22_864564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_864564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864564 prefixEnd_864564 := by exact prefixLift 864564
  have htrace : WordTrace (prefixWord ++ tailWord_864564) baseStart_864564 baseEnd_864564 := by
    simpa [prefixWord, tailWord_864564, baseEnd_864564] using wordTrace_append hprefix tailTrace_864564
  have hstable : (prefixWord ++ tailWord_864564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864564).length < 2 ^ (prefixWord ++ tailWord_864564).sum := by decide
  have hdescent : baseEnd_864564 < baseStart_864564 := by decide
  rcases family_descends (prefixWord ++ tailWord_864564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864596 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_864596 : Nat := 118140960795 + 864596 * 2 ^ 59
def prefixEnd_864596 : Nat := 4983230072969 + 3 ^ 40 * 864596 * 2
def baseEnd_864596 : Nat := 295968879969869665249201

theorem tailTrace_864596 : CollatzResearch.WordTrace tailWord_864596 prefixEnd_864596 295968879969869665249201 := by
  unfold tailWord_864596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767203387861914042998821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21022937850482552057331761 15767203387861914042998821)
  ·
    refine ⟨2956350635224108883062279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15767203387861914042998821 2956350635224108883062279)
    ·
      refine ⟨4434525952836163324593419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956350635224108883062279 4434525952836163324593419)
      ·
        refine ⟨6651788929254244986890129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434525952836163324593419 6651788929254244986890129)
        ·
          refine ⟨4988841696940683740167597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651788929254244986890129 4988841696940683740167597)
          ·
            refine ⟨1870815636352756402562849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988841696940683740167597 1870815636352756402562849)
            ·
              refine ⟨1403111727264567301922137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870815636352756402562849 1403111727264567301922137)
              ·
                refine ⟨1052333795448425476441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403111727264567301922137 1052333795448425476441603)
                ·
                  refine ⟨1578500693172638214662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052333795448425476441603 1578500693172638214662405)
                  ·
                    refine ⟨295968879969869665249201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578500693172638214662405 295968879969869665249201)
                    ·
                      rfl

theorem cell22_864596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_864596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864596 prefixEnd_864596 := by exact prefixLift 864596
  have htrace : WordTrace (prefixWord ++ tailWord_864596) baseStart_864596 baseEnd_864596 := by
    simpa [prefixWord, tailWord_864596, baseEnd_864596] using wordTrace_append hprefix tailTrace_864596
  have hstable : (prefixWord ++ tailWord_864596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864596).length < 2 ^ (prefixWord ++ tailWord_864596).sum := by decide
  have hdescent : baseEnd_864596 < baseStart_864596 := by decide
  rcases family_descends (prefixWord ++ tailWord_864596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864607 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_864607 : Nat := 118140960795 + 864607 * 2 ^ 59
def prefixEnd_864607 : Nat := 4983230072969 + 3 ^ 40 * 864607 * 2
def baseEnd_864607 : Nat := 295972645494669303224167

theorem tailTrace_864607 : CollatzResearch.WordTrace tailWord_864607 prefixEnd_864607 295972645494669303224167 := by
  unfold tailWord_864607
  simp only [CollatzResearch.WordTrace]
  refine ⟨31534807978683976964648075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21023205319122651309765383 31534807978683976964648075)
  ·
    refine ⟨47302211968025965446972113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31534807978683976964648075 47302211968025965446972113)
    ·
      refine ⟨35476658976019474085229085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47302211968025965446972113 35476658976019474085229085)
      ·
        refine ⟨13303747116007302781960907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35476658976019474085229085 13303747116007302781960907)
        ·
          refine ⟨19955620674010954172941361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13303747116007302781960907 19955620674010954172941361)
          ·
            refine ⟨14966715505508215629706021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19955620674010954172941361 14966715505508215629706021)
            ·
              refine ⟨2806259157282790430569879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14966715505508215629706021 2806259157282790430569879)
              ·
                refine ⟨4209388735924185645854819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806259157282790430569879 4209388735924185645854819)
                ·
                  refine ⟨6314083103886278468782229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209388735924185645854819 6314083103886278468782229)
                  ·
                    refine ⟨295972645494669303224167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6314083103886278468782229 295972645494669303224167)
                    ·
                      rfl

theorem cell22_864607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_864607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864607 prefixEnd_864607 := by exact prefixLift 864607
  have htrace : WordTrace (prefixWord ++ tailWord_864607) baseStart_864607 baseEnd_864607 := by
    simpa [prefixWord, tailWord_864607, baseEnd_864607] using wordTrace_append hprefix tailTrace_864607
  have hstable : (prefixWord ++ tailWord_864607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864607).length < 2 ^ (prefixWord ++ tailWord_864607).sum := by decide
  have hdescent : baseEnd_864607 < baseStart_864607 := by decide
  rcases family_descends (prefixWord ++ tailWord_864607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864624 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_864624 : Nat := 118140960795 + 864624 * 2 ^ 59
def prefixEnd_864624 : Nat := 4983230072969 + 3 ^ 40 * 864624 * 2
def baseEnd_864624 : Nat := 295978464942086925549115

theorem tailTrace_864624 : CollatzResearch.WordTrace tailWord_864624 prefixEnd_864624 295978464942086925549115 := by
  unfold tailWord_864624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767714009811194434008463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21023618679748259245344617 15767714009811194434008463)
  ·
    refine ⟨23651571014716791651012695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15767714009811194434008463 23651571014716791651012695)
    ·
      refine ⟨35477356522075187476519043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651571014716791651012695 35477356522075187476519043)
      ·
        refine ⟨53216034783112781214778565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35477356522075187476519043 53216034783112781214778565)
        ·
          refine ⟨9978006521833646477770981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53216034783112781214778565 9978006521833646477770981)
          ·
            refine ⟨1870876222843808714582059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9978006521833646477770981 1870876222843808714582059)
            ·
              refine ⟨2806314334265713071873089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870876222843808714582059 2806314334265713071873089)
              ·
                refine ⟨2104735750699284803904817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806314334265713071873089 2104735750699284803904817)
                ·
                  refine ⟨1578551813024463602928613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104735750699284803904817 1578551813024463602928613)
                  ·
                    refine ⟨295978464942086925549115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578551813024463602928613 295978464942086925549115)
                    ·
                      rfl

theorem cell22_864624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_864624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864624 prefixEnd_864624 := by exact prefixLift 864624
  have htrace : WordTrace (prefixWord ++ tailWord_864624) baseStart_864624 baseEnd_864624 := by
    simpa [prefixWord, tailWord_864624, baseEnd_864624] using wordTrace_append hprefix tailTrace_864624
  have hstable : (prefixWord ++ tailWord_864624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864624).length < 2 ^ (prefixWord ++ tailWord_864624).sum := by decide
  have hdescent : baseEnd_864624 < baseStart_864624 := by decide
  rcases family_descends (prefixWord ++ tailWord_864624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864714 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_864714 : Nat := 118140960795 + 864714 * 2 ^ 59
def prefixEnd_864714 : Nat := 4983230072969 + 3 ^ 40 * 864714 * 2
def baseEnd_864714 : Nat := 296009273781356690798839

theorem tailTrace_864714 : CollatzResearch.WordTrace tailWord_864714 prefixEnd_864714 296009273781356690798839 := by
  unfold tailWord_864714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884677647324083559698299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21025807059530889492528797 7884677647324083559698299)
  ·
    refine ⟨11827016470986125339547449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884677647324083559698299 11827016470986125339547449)
    ·
      refine ⟨8870262353239594004660587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11827016470986125339547449 8870262353239594004660587)
      ·
        refine ⟨13305393529859391006990881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870262353239594004660587 13305393529859391006990881)
        ·
          refine ⟨9979045147394543255243161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13305393529859391006990881 9979045147394543255243161)
          ·
            refine ⟨7484283860545907441432371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9979045147394543255243161 7484283860545907441432371)
            ·
              refine ⟨11226425790818861162148557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484283860545907441432371 11226425790818861162148557)
              ·
                refine ⟨4209909671557072935805709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11226425790818861162148557 4209909671557072935805709)
                ·
                  refine ⟨1578716126833902350927141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4209909671557072935805709 1578716126833902350927141)
                  ·
                    refine ⟨296009273781356690798839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1578716126833902350927141 296009273781356690798839)
                    ·
                      rfl

theorem cell22_864714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_864714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864714 prefixEnd_864714 := by exact prefixLift 864714
  have htrace : WordTrace (prefixWord ++ tailWord_864714) baseStart_864714 baseEnd_864714 := by
    simpa [prefixWord, tailWord_864714, baseEnd_864714] using wordTrace_append hprefix tailTrace_864714
  have hstable : (prefixWord ++ tailWord_864714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864714).length < 2 ^ (prefixWord ++ tailWord_864714).sum := by decide
  have hdescent : baseEnd_864714 < baseStart_864714 := by decide
  rcases family_descends (prefixWord ++ tailWord_864714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864722 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_864722 : Nat := 118140960795 + 864722 * 2 ^ 59
def prefixEnd_864722 : Nat := 4983230072969 + 3 ^ 40 * 864722 * 2
def baseEnd_864722 : Nat := 296012012344847336598815

theorem tailTrace_864722 : CollatzResearch.WordTrace tailWord_864722 prefixEnd_864722 296012012344847336598815 := by
  unfold tailWord_864722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884750593316837901271105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21026001582178234403389613 7884750593316837901271105)
  ·
    refine ⟨5913562944987628425953329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7884750593316837901271105 5913562944987628425953329)
    ·
      refine ⟨4435172208740721319464997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5913562944987628425953329 4435172208740721319464997)
      ·
        refine ⟨831594789138885247399687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4435172208740721319464997 831594789138885247399687)
        ·
          refine ⟨1247392183708327871099531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831594789138885247399687 1247392183708327871099531)
          ·
            refine ⟨1871088275562491806649297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247392183708327871099531 1871088275562491806649297)
            ·
              refine ⟨1403316206671868854986973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871088275562491806649297 1403316206671868854986973)
              ·
                refine ⟨526243577501950820620115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403316206671868854986973 526243577501950820620115)
                ·
                  refine ⟨789365366252926230930173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526243577501950820620115 789365366252926230930173)
                  ·
                    refine ⟨296012012344847336598815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789365366252926230930173 296012012344847336598815)
                    ·
                      rfl

theorem cell22_864722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_864722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864722 prefixEnd_864722 := by exact prefixLift 864722
  have htrace : WordTrace (prefixWord ++ tailWord_864722) baseStart_864722 baseEnd_864722 := by
    simpa [prefixWord, tailWord_864722, baseEnd_864722] using wordTrace_append hprefix tailTrace_864722
  have hstable : (prefixWord ++ tailWord_864722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864722).length < 2 ^ (prefixWord ++ tailWord_864722).sum := by decide
  have hdescent : baseEnd_864722 < baseStart_864722 := by decide
  rcases family_descends (prefixWord ++ tailWord_864722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864746 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_864746 : Nat := 118140960795 + 864746 * 2 ^ 59
def prefixEnd_864746 : Nat := 4983230072969 + 3 ^ 40 * 864746 * 2
def baseEnd_864746 : Nat := 98673409345106424666247

theorem tailTrace_864746 : CollatzResearch.WordTrace tailWord_864746 prefixEnd_864746 98673409345106424666247 := by
  unfold tailWord_864746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884969431295100925989523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21026585150120269135972061 7884969431295100925989523)
  ·
    refine ⟨11827454146942651388984285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884969431295100925989523 11827454146942651388984285)
    ·
      refine ⟨4435295305103494270869107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11827454146942651388984285 4435295305103494270869107)
      ·
        refine ⟨6652942957655241406303661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4435295305103494270869107 6652942957655241406303661)
        ·
          refine ⟨2494853609120715527363873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6652942957655241406303661 2494853609120715527363873)
          ·
            refine ⟨1871140206840536645522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494853609120715527363873 1871140206840536645522905)
            ·
              refine ⟨1403355155130402484142179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871140206840536645522905 1403355155130402484142179)
              ·
                refine ⟨2105032732695603726213269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403355155130402484142179 2105032732695603726213269)
                ·
                  refine ⟨98673409345106424666247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2105032732695603726213269 98673409345106424666247)
                  ·
                    rfl

theorem cell22_864746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_864746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864746 prefixEnd_864746 := by exact prefixLift 864746
  have htrace : WordTrace (prefixWord ++ tailWord_864746) baseStart_864746 baseEnd_864746 := by
    simpa [prefixWord, tailWord_864746, baseEnd_864746] using wordTrace_append hprefix tailTrace_864746
  have hstable : (prefixWord ++ tailWord_864746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864746).length < 2 ^ (prefixWord ++ tailWord_864746).sum := by decide
  have hdescent : baseEnd_864746 < baseStart_864746 := by decide
  rcases family_descends (prefixWord ++ tailWord_864746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864761 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_864761 : Nat := 118140960795 + 864761 * 2 ^ 59
def prefixEnd_864761 : Nat := 4983230072969 + 3 ^ 40 * 864761 * 2
def baseEnd_864761 : Nat := 296025362841864234873695

theorem tailTrace_864761 : CollatzResearch.WordTrace tailWord_864761 prefixEnd_864761 296025362841864234873695 := by
  unfold tailWord_864761
  simp only [CollatzResearch.WordTrace]
  refine ⟨31540424820126061265754137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21026949880084040843836091 31540424820126061265754137)
  ·
    refine ⟨23655318615094545949315603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31540424820126061265754137 23655318615094545949315603)
    ·
      refine ⟨35482977922641818923973405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23655318615094545949315603 35482977922641818923973405)
      ·
        refine ⟨13306116720990682096490027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35482977922641818923973405 13306116720990682096490027)
        ·
          refine ⟨19959175081486023144735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306116720990682096490027 19959175081486023144735041)
          ·
            refine ⟨14969381311114517358551281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19959175081486023144735041 14969381311114517358551281)
            ·
              refine ⟨11227035983335888018913461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14969381311114517358551281 11227035983335888018913461)
              ·
                refine ⟨1052534623437739501773137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11227035983335888018913461 1052534623437739501773137)
                ·
                  refine ⟨789400967578304626329853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052534623437739501773137 789400967578304626329853)
                  ·
                    refine ⟨296025362841864234873695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789400967578304626329853 296025362841864234873695)
                    ·
                      rfl

theorem cell22_864761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_864761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864761 prefixEnd_864761 := by exact prefixLift 864761
  have htrace : WordTrace (prefixWord ++ tailWord_864761) baseStart_864761 baseEnd_864761 := by
    simpa [prefixWord, tailWord_864761, baseEnd_864761] using wordTrace_append hprefix tailTrace_864761
  have hstable : (prefixWord ++ tailWord_864761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864761).length < 2 ^ (prefixWord ++ tailWord_864761).sum := by decide
  have hdescent : baseEnd_864761 < baseStart_864761 := by decide
  rcases family_descends (prefixWord ++ tailWord_864761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864896 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_864896 : Nat := 118140960795 + 864896 * 2 ^ 59
def prefixEnd_864896 : Nat := 4983230072969 + 3 ^ 40 * 864896 * 2
def baseEnd_864896 : Nat := 296071576100768882748281

theorem tailTrace_864896 : CollatzResearch.WordTrace tailWord_864896 prefixEnd_864896 296071576100768882748281 := by
  unfold tailWord_864896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772674337318489660959271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21030232449757986214612361 15772674337318489660959271)
  ·
    refine ⟨23659011505977734491438907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15772674337318489660959271 23659011505977734491438907)
    ·
      refine ⟨35488517258966601737158361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23659011505977734491438907 35488517258966601737158361)
      ·
        refine ⟨26616387944224951302868771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35488517258966601737158361 26616387944224951302868771)
        ·
          refine ⟨39924581916337426954303157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616387944224951302868771 39924581916337426954303157)
          ·
            refine ⟨3742929554656633776965921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39924581916337426954303157 3742929554656633776965921)
            ·
              refine ⟨2807197165992475332724441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742929554656633776965921 2807197165992475332724441)
              ·
                refine ⟨2105397874494356499543331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807197165992475332724441 2105397874494356499543331)
                ·
                  refine ⟨3158096811741534749314997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105397874494356499543331 3158096811741534749314997)
                  ·
                    refine ⟨296071576100768882748281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158096811741534749314997 296071576100768882748281)
                    ·
                      rfl

theorem cell22_864896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_864896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864896 prefixEnd_864896 := by exact prefixLift 864896
  have htrace : WordTrace (prefixWord ++ tailWord_864896) baseStart_864896 baseEnd_864896 := by
    simpa [prefixWord, tailWord_864896, baseEnd_864896] using wordTrace_append hprefix tailTrace_864896
  have hstable : (prefixWord ++ tailWord_864896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864896).length < 2 ^ (prefixWord ++ tailWord_864896).sum := by decide
  have hdescent : baseEnd_864896 < baseStart_864896 := by decide
  rcases family_descends (prefixWord ++ tailWord_864896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864900 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_864900 : Nat := 118140960795 + 864900 * 2 ^ 59
def prefixEnd_864900 : Nat := 4983230072969 + 3 ^ 40 * 864900 * 2
def baseEnd_864900 : Nat := 296072945382514205648269

theorem tailTrace_864900 : CollatzResearch.WordTrace tailWord_864900 prefixEnd_864900 296072945382514205648269 := by
  unfold tailWord_864900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772747283311244002532077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21030329711081658670042769 15772747283311244002532077)
  ·
    refine ⟨5914780231241716500949529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15772747283311244002532077 5914780231241716500949529)
    ·
      refine ⟨4436085173431287375712147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5914780231241716500949529 4436085173431287375712147)
      ·
        refine ⟨6654127760146931063568221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436085173431287375712147 6654127760146931063568221)
        ·
          refine ⟨2495297910055099148838083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6654127760146931063568221 2495297910055099148838083)
          ·
            refine ⟨3742946865082648723257125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495297910055099148838083 3742946865082648723257125)
            ·
              refine ⟨701802537202996635610711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3742946865082648723257125 701802537202996635610711)
              ·
                refine ⟨1052703805804494953416067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701802537202996635610711 1052703805804494953416067)
                ·
                  refine ⟨1579055708706742430124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052703805804494953416067 1579055708706742430124101)
                  ·
                    refine ⟨296072945382514205648269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579055708706742430124101 296072945382514205648269)
                    ·
                      rfl

theorem cell22_864900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_864900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864900 prefixEnd_864900 := by exact prefixLift 864900
  have htrace : WordTrace (prefixWord ++ tailWord_864900) baseStart_864900 baseEnd_864900 := by
    simpa [prefixWord, tailWord_864900, baseEnd_864900] using wordTrace_append hprefix tailTrace_864900
  have hstable : (prefixWord ++ tailWord_864900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864900).length < 2 ^ (prefixWord ++ tailWord_864900).sum := by decide
  have hdescent : baseEnd_864900 < baseStart_864900 := by decide
  rcases family_descends (prefixWord ++ tailWord_864900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864943 : List Nat := [1, 1, 2, 1, 2, 7, 2, 6]
def baseStart_864943 : Nat := 118140960795 + 864943 * 2 ^ 59
def prefixEnd_864943 : Nat := 4983230072969 + 3 ^ 40 * 864943 * 2
def baseEnd_864943 : Nat := 32898629462364047424793

theorem tailTrace_864943 : CollatzResearch.WordTrace tailWord_864943 prefixEnd_864943 32898629462364047424793 := by
  unfold tailWord_864943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547062905466706348879483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21031375270311137565919655 31547062905466706348879483)
  ·
    refine ⟨47320594358200059523319225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31547062905466706348879483 47320594358200059523319225)
    ·
      refine ⟨35490445768650044642489419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47320594358200059523319225 35490445768650044642489419)
      ·
        refine ⟨53235668652975066963734129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35490445768650044642489419 53235668652975066963734129)
        ·
          refine ⟨39926751489731300222800597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53235668652975066963734129 39926751489731300222800597)
          ·
            refine ⟨935783238040577348971889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39926751489731300222800597 935783238040577348971889)
            ·
              refine ⟨701837428530433011728917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935783238040577348971889 701837428530433011728917)
              ·
                refine ⟨32898629462364047424793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 701837428530433011728917 32898629462364047424793)
                ·
                  rfl

theorem cell22_864943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 6].length) (baseStart_864943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864943 prefixEnd_864943 := by exact prefixLift 864943
  have htrace : WordTrace (prefixWord ++ tailWord_864943) baseStart_864943 baseEnd_864943 := by
    simpa [prefixWord, tailWord_864943, baseEnd_864943] using wordTrace_append hprefix tailTrace_864943
  have hstable : (prefixWord ++ tailWord_864943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864943).length < 2 ^ (prefixWord ++ tailWord_864943).sum := by decide
  have hdescent : baseEnd_864943 < baseStart_864943 := by decide
  rcases family_descends (prefixWord ++ tailWord_864943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864966 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_864966 : Nat := 118140960795 + 864966 * 2 ^ 59
def prefixEnd_864966 : Nat := 4983230072969 + 3 ^ 40 * 864966 * 2
def baseEnd_864966 : Nat := 98698512843770677832689

theorem tailTrace_864966 : CollatzResearch.WordTrace tailWord_864966 prefixEnd_864966 98698512843770677832689 := by
  unfold tailWord_864966
  simp only [CollatzResearch.WordTrace]
  refine ⟨985871930761980664905211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21031934522922254184644501 985871930761980664905211)
  ·
    refine ⟨1478807896142970997357817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985871930761980664905211 1478807896142970997357817)
    ·
      refine ⟨1109105922107228248018363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1478807896142970997357817 1109105922107228248018363)
      ·
        refine ⟨1663658883160842372027545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109105922107228248018363 1663658883160842372027545)
        ·
          refine ⟨1247744162370631779020659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1663658883160842372027545 1247744162370631779020659)
          ·
            refine ⟨1871616243555947668530989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247744162370631779020659 1871616243555947668530989)
            ·
              refine ⟨701856091333480375699121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1871616243555947668530989 701856091333480375699121)
              ·
                refine ⟨526392068500110281774341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701856091333480375699121 526392068500110281774341)
                ·
                  refine ⟨98698512843770677832689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526392068500110281774341 98698512843770677832689)
                  ·
                    rfl

theorem cell22_864966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_864966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864966 prefixEnd_864966 := by exact prefixLift 864966
  have htrace : WordTrace (prefixWord ++ tailWord_864966) baseStart_864966 baseEnd_864966 := by
    simpa [prefixWord, tailWord_864966, baseEnd_864966] using wordTrace_append hprefix tailTrace_864966
  have hstable : (prefixWord ++ tailWord_864966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864966).length < 2 ^ (prefixWord ++ tailWord_864966).sum := by decide
  have hdescent : baseEnd_864966 < baseStart_864966 := by decide
  rcases family_descends (prefixWord ++ tailWord_864966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864981 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_864981 : Nat := 118140960795 + 864981 * 2 ^ 59
def prefixEnd_864981 : Nat := 4983230072969 + 3 ^ 40 * 864981 * 2
def baseEnd_864981 : Nat := 296100673337856994373021

theorem tailTrace_864981 : CollatzResearch.WordTrace tailWord_864981 prefixEnd_864981 296100673337856994373021 := by
  unfold tailWord_864981
  simp only [CollatzResearch.WordTrace]
  refine ⟨31548448879329038838762797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21032299252886025892508531 31548448879329038838762797)
  ·
    refine ⟨11830668329748389564536049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31548448879329038838762797 11830668329748389564536049)
    ·
      refine ⟨8873001247311292173402037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11830668329748389564536049 8873001247311292173402037)
      ·
        refine ⟨831843866935433641256441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8873001247311292173402037 831843866935433641256441)
        ·
          refine ⟨623882900201575230942331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831843866935433641256441 623882900201575230942331)
          ·
            refine ⟨935824350302362846413497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623882900201575230942331 935824350302362846413497)
            ·
              refine ⟨701868262726772134810123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935824350302362846413497 701868262726772134810123)
              ·
                refine ⟨1052802394090158202215185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701868262726772134810123 1052802394090158202215185)
                ·
                  refine ⟨789601795567618651661389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052802394090158202215185 789601795567618651661389)
                  ·
                    refine ⟨296100673337856994373021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789601795567618651661389 296100673337856994373021)
                    ·
                      rfl

theorem cell22_864981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_864981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864981 prefixEnd_864981 := by exact prefixLift 864981
  have htrace : WordTrace (prefixWord ++ tailWord_864981) baseStart_864981 baseEnd_864981 := by
    simpa [prefixWord, tailWord_864981, baseEnd_864981] using wordTrace_append hprefix tailTrace_864981
  have hstable : (prefixWord ++ tailWord_864981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864981).length < 2 ^ (prefixWord ++ tailWord_864981).sum := by decide
  have hdescent : baseEnd_864981 < baseStart_864981 := by decide
  rcases family_descends (prefixWord ++ tailWord_864981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864986 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_864986 : Nat := 118140960795 + 864986 * 2 ^ 59
def prefixEnd_864986 : Nat := 4983230072969 + 3 ^ 40 * 864986 * 2
def baseEnd_864986 : Nat := 296102384940038647998005

theorem tailTrace_864986 : CollatzResearch.WordTrace tailWord_864986 prefixEnd_864986 296102384940038647998005 := by
  unfold tailWord_864986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887157811077731173173703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21032420829540616461796541 7887157811077731173173703)
  ·
    refine ⟨11830736716616596759760555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7887157811077731173173703 11830736716616596759760555)
    ·
      refine ⟨17746105074924895139640833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11830736716616596759760555 17746105074924895139640833)
      ·
        refine ⟨13309578806193671354730625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17746105074924895139640833 13309578806193671354730625)
        ·
          refine ⟨9982184104645253516047969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13309578806193671354730625 9982184104645253516047969)
          ·
            refine ⟨7486638078483940137035977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9982184104645253516047969 7486638078483940137035977)
            ·
              refine ⟨5614978558862955102776983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7486638078483940137035977 5614978558862955102776983)
              ·
                refine ⟨8422467838294432654165475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614978558862955102776983 8422467838294432654165475)
                ·
                  refine ⟨12633701757441648981248213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8422467838294432654165475 12633701757441648981248213)
                  ·
                    refine ⟨296102384940038647998005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12633701757441648981248213 296102384940038647998005)
                    ·
                      rfl

theorem cell22_864986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_864986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_864986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_864986 prefixEnd_864986 := by exact prefixLift 864986
  have htrace : WordTrace (prefixWord ++ tailWord_864986) baseStart_864986 baseEnd_864986 := by
    simpa [prefixWord, tailWord_864986, baseEnd_864986] using wordTrace_append hprefix tailTrace_864986
  have hstable : (prefixWord ++ tailWord_864986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864986).length < 2 ^ (prefixWord ++ tailWord_864986).sum := by decide
  have hdescent : baseEnd_864986 < baseStart_864986 := by decide
  rcases family_descends (prefixWord ++ tailWord_864986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865018 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_865018 : Nat := 118140960795 + 865018 * 2 ^ 59
def prefixEnd_865018 : Nat := 4983230072969 + 3 ^ 40 * 865018 * 2
def baseEnd_865018 : Nat := 296113339194001231197907

theorem tailTrace_865018 : CollatzResearch.WordTrace tailWord_865018 prefixEnd_865018 296113339194001231197907 := by
  unfold tailWord_865018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887449595048748539464927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21033198920129996105239805 7887449595048748539464927)
  ·
    refine ⟨11831174392573122809197391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7887449595048748539464927 11831174392573122809197391)
    ·
      refine ⟨17746761588859684213796087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11831174392573122809197391 17746761588859684213796087)
      ·
        refine ⟨26620142383289526320694131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17746761588859684213796087 26620142383289526320694131)
        ·
          refine ⟨39930213574934289481041197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26620142383289526320694131 39930213574934289481041197)
          ·
            refine ⟨14973830090600358555390449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39930213574934289481041197 14973830090600358555390449)
            ·
              refine ⟨11230372567950268916542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14973830090600358555390449 11230372567950268916542837)
              ·
                refine ⟨1052847428245337710925891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11230372567950268916542837 1052847428245337710925891)
                ·
                  refine ⟨1579271142368006566388837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052847428245337710925891 1579271142368006566388837)
                  ·
                    refine ⟨296113339194001231197907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579271142368006566388837 296113339194001231197907)
                    ·
                      rfl

theorem cell22_865018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_865018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865018 prefixEnd_865018 := by exact prefixLift 865018
  have htrace : WordTrace (prefixWord ++ tailWord_865018) baseStart_865018 baseEnd_865018 := by
    simpa [prefixWord, tailWord_865018, baseEnd_865018] using wordTrace_append hprefix tailTrace_865018
  have hstable : (prefixWord ++ tailWord_865018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865018).length < 2 ^ (prefixWord ++ tailWord_865018).sum := by decide
  have hdescent : baseEnd_865018 < baseStart_865018 := by decide
  rcases family_descends (prefixWord ++ tailWord_865018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865026 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_865026 : Nat := 118140960795 + 865026 * 2 ^ 59
def prefixEnd_865026 : Nat := 4983230072969 + 3 ^ 40 * 865026 * 2
def baseEnd_865026 : Nat := 296116077757491876997883

theorem tailTrace_865026 : CollatzResearch.WordTrace tailWord_865026 prefixEnd_865026 296116077757491876997883 := by
  unfold tailWord_865026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887522541041502881037733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21033393442777341016100621 7887522541041502881037733)
  ·
    refine ⟨1478910476445281790194575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7887522541041502881037733 1478910476445281790194575)
    ·
      refine ⟨2218365714667922685291863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478910476445281790194575 2218365714667922685291863)
      ·
        refine ⟨3327548572001884027937795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218365714667922685291863 3327548572001884027937795)
        ·
          refine ⟨4991322858002826041906693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327548572001884027937795 4991322858002826041906693)
          ·
            refine ⟨935873035875529882857505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4991322858002826041906693 935873035875529882857505)
            ·
              refine ⟨701904776906647412143129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935873035875529882857505 701904776906647412143129)
              ·
                refine ⟨526428582679985559107347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701904776906647412143129 526428582679985559107347)
                ·
                  refine ⟨789642874019978338661021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526428582679985559107347 789642874019978338661021)
                  ·
                    refine ⟨296116077757491876997883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789642874019978338661021 296116077757491876997883)
                    ·
                      rfl

theorem cell22_865026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_865026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865026 prefixEnd_865026 := by exact prefixLift 865026
  have htrace : WordTrace (prefixWord ++ tailWord_865026) baseStart_865026 baseEnd_865026 := by
    simpa [prefixWord, tailWord_865026, baseEnd_865026] using wordTrace_append hprefix tailTrace_865026
  have hstable : (prefixWord ++ tailWord_865026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865026).length < 2 ^ (prefixWord ++ tailWord_865026).sum := by decide
  have hdescent : baseEnd_865026 < baseStart_865026 := by decide
  rcases family_descends (prefixWord ++ tailWord_865026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865048 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_865048 : Nat := 118140960795 + 865048 * 2 ^ 59
def prefixEnd_865048 : Nat := 4983230072969 + 3 ^ 40 * 865048 * 2
def baseEnd_865048 : Nat := 296123608807091152947815

theorem tailTrace_865048 : CollatzResearch.WordTrace tailWord_865048 prefixEnd_865048 296123608807091152947815 := by
  unfold tailWord_865048
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775446285043154640725899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21033928380057539520967865 15775446285043154640725899)
  ·
    refine ⟨23663169427564731961088849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15775446285043154640725899 23663169427564731961088849)
    ·
      refine ⟨17747377070673548970816637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23663169427564731961088849 17747377070673548970816637)
      ·
        refine ⟨6655266401502580864056239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17747377070673548970816637 6655266401502580864056239)
        ·
          refine ⟨9982899602253871296084359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655266401502580864056239 9982899602253871296084359)
          ·
            refine ⟨14974349403380806944126539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982899602253871296084359 14974349403380806944126539)
            ·
              refine ⟨22461524105071210416189809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974349403380806944126539 22461524105071210416189809)
              ·
                refine ⟨16846143078803407812142357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22461524105071210416189809 16846143078803407812142357)
                ·
                  refine ⟨789662956818909741194173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16846143078803407812142357 789662956818909741194173)
                  ·
                    refine ⟨296123608807091152947815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789662956818909741194173 296123608807091152947815)
                    ·
                      rfl

theorem cell22_865048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_865048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865048 prefixEnd_865048 := by exact prefixLift 865048
  have htrace : WordTrace (prefixWord ++ tailWord_865048) baseStart_865048 baseEnd_865048 := by
    simpa [prefixWord, tailWord_865048, baseEnd_865048] using wordTrace_append hprefix tailTrace_865048
  have hstable : (prefixWord ++ tailWord_865048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865048).length < 2 ^ (prefixWord ++ tailWord_865048).sum := by decide
  have hdescent : baseEnd_865048 < baseStart_865048 := by decide
  rcases family_descends (prefixWord ++ tailWord_865048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865069 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_865069 : Nat := 118140960795 + 865069 * 2 ^ 59
def prefixEnd_865069 : Nat := 4983230072969 + 3 ^ 40 * 865069 * 2
def baseEnd_865069 : Nat := 296130797536254098172751

theorem tailTrace_865069 : CollatzResearch.WordTrace tailWord_865069 prefixEnd_865069 296130797536254098172751 := by
  unfold tailWord_865069
  simp only [CollatzResearch.WordTrace]
  refine ⟨31551658503010229867966261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21034439002006819911977507 31551658503010229867966261)
  ·
    refine ⟨2957967984657209050121837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31551658503010229867966261 2957967984657209050121837)
    ·
      refine ⟨1109237994246453393795689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2957967984657209050121837 1109237994246453393795689)
      ·
        refine ⟨831928495684840045346767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109237994246453393795689 831928495684840045346767)
        ·
          refine ⟨1247892743527260068020151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831928495684840045346767 1247892743527260068020151)
          ·
            refine ⟨1871839115290890102030227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247892743527260068020151 1871839115290890102030227)
            ·
              refine ⟨2807758672936335153045341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871839115290890102030227 2807758672936335153045341)
              ·
                refine ⟨1052909502351125682392003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2807758672936335153045341 1052909502351125682392003)
                ·
                  refine ⟨1579364253526688523588005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052909502351125682392003 1579364253526688523588005)
                  ·
                    refine ⟨296130797536254098172751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579364253526688523588005 296130797536254098172751)
                    ·
                      rfl

theorem cell22_865069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_865069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865069 prefixEnd_865069 := by exact prefixLift 865069
  have htrace : WordTrace (prefixWord ++ tailWord_865069) baseStart_865069 baseEnd_865069 := by
    simpa [prefixWord, tailWord_865069, baseEnd_865069] using wordTrace_append hprefix tailTrace_865069
  have hstable : (prefixWord ++ tailWord_865069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865069).length < 2 ^ (prefixWord ++ tailWord_865069).sum := by decide
  have hdescent : baseEnd_865069 < baseStart_865069 := by decide
  rcases family_descends (prefixWord ++ tailWord_865069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865123 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 7]
def baseStart_865123 : Nat := 118140960795 + 865123 * 2 ^ 59
def prefixEnd_865123 : Nat := 4983230072969 + 3 ^ 40 * 865123 * 2
def baseEnd_865123 : Nat := 98716427613271985774195

theorem tailTrace_865123 : CollatzResearch.WordTrace tailWord_865123 prefixEnd_865123 98716427613271985774195 := by
  unfold tailWord_865123
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553628044814597090432023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21035752029876398060288015 31553628044814597090432023)
  ·
    refine ⟨47330442067221895635648035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31553628044814597090432023 47330442067221895635648035)
    ·
      refine ⟨70995663100832843453472053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330442067221895635648035 70995663100832843453472053)
      ·
        refine ⟨6655843415703079073763005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70995663100832843453472053 6655843415703079073763005)
        ·
          refine ⟨2495941280888654652661127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6655843415703079073763005 2495941280888654652661127)
          ·
            refine ⟨3743911921332981978991691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495941280888654652661127 3743911921332981978991691)
            ·
              refine ⟨5615867881999472968487537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743911921332981978991691 5615867881999472968487537)
              ·
                refine ⟨4211900911499604726365653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615867881999472968487537 4211900911499604726365653)
                ·
                  refine ⟨98716427613271985774195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4211900911499604726365653 98716427613271985774195)
                  ·
                    rfl

theorem cell22_865123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_865123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865123 prefixEnd_865123 := by exact prefixLift 865123
  have htrace : WordTrace (prefixWord ++ tailWord_865123) baseStart_865123 baseEnd_865123 := by
    simpa [prefixWord, tailWord_865123, baseEnd_865123] using wordTrace_append hprefix tailTrace_865123
  have hstable : (prefixWord ++ tailWord_865123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865123).length < 2 ^ (prefixWord ++ tailWord_865123).sum := by decide
  have hdescent : baseEnd_865123 < baseStart_865123 := by decide
  rcases family_descends (prefixWord ++ tailWord_865123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865138 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_865138 : Nat := 118140960795 + 865138 * 2 ^ 59
def prefixEnd_865138 : Nat := 4983230072969 + 3 ^ 40 * 865138 * 2
def baseEnd_865138 : Nat := 296154417646360918197539

theorem tailTrace_865138 : CollatzResearch.WordTrace tailWord_865138 prefixEnd_865138 296154417646360918197539 := by
  unfold tailWord_865138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888543784940063663057017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21036116759840169768152045 7888543784940063663057017)
  ·
    refine ⟨5916407838705047747292763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7888543784940063663057017 5916407838705047747292763)
    ·
      refine ⟨8874611758057571620939145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916407838705047747292763 8874611758057571620939145)
      ·
        refine ⟨6655958818543178715704359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8874611758057571620939145 6655958818543178715704359)
        ·
          refine ⟨9983938227814768073556539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655958818543178715704359 9983938227814768073556539)
          ·
            refine ⟨14975907341722152110334809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983938227814768073556539 14975907341722152110334809)
            ·
              refine ⟨11231930506291614082751107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14975907341722152110334809 11231930506291614082751107)
              ·
                refine ⟨16847895759437421124126661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11231930506291614082751107 16847895759437421124126661)
                ·
                  refine ⟨3158980454894516460773749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16847895759437421124126661 3158980454894516460773749)
                  ·
                    refine ⟨296154417646360918197539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3158980454894516460773749 296154417646360918197539)
                    ·
                      rfl

theorem cell22_865138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_865138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865138 prefixEnd_865138 := by exact prefixLift 865138
  have htrace : WordTrace (prefixWord ++ tailWord_865138) baseStart_865138 baseEnd_865138 := by
    simpa [prefixWord, tailWord_865138, baseEnd_865138] using wordTrace_append hprefix tailTrace_865138
  have hstable : (prefixWord ++ tailWord_865138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865138).length < 2 ^ (prefixWord ++ tailWord_865138).sum := by decide
  have hdescent : baseEnd_865138 < baseStart_865138 := by decide
  rcases family_descends (prefixWord ++ tailWord_865138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865157 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 5]
def baseStart_865157 : Nat := 118140960795 + 865157 * 2 ^ 59
def prefixEnd_865157 : Nat := 4983230072969 + 3 ^ 40 * 865157 * 2
def baseEnd_865157 : Nat := 98720307244883733990827

theorem tailTrace_865157 : CollatzResearch.WordTrace tailWord_865157 prefixEnd_865157 98720307244883733990827 := by
  unfold tailWord_865157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554868126691420897169725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21036578751127613931446483 31554868126691420897169725)
  ·
    refine ⟨11833075547509282836438647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31554868126691420897169725 11833075547509282836438647)
    ·
      refine ⟨17749613321263924254657971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833075547509282836438647 17749613321263924254657971)
      ·
        refine ⟨26624419981895886381986957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17749613321263924254657971 26624419981895886381986957)
        ·
          refine ⟨9984157493210957393245109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26624419981895886381986957 9984157493210957393245109)
          ·
            refine ⟨936014764988527255616729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9984157493210957393245109 936014764988527255616729)
            ·
              refine ⟨702011073741395441712547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936014764988527255616729 702011073741395441712547)
              ·
                refine ⟨1053016610612093162568821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702011073741395441712547 1053016610612093162568821)
                ·
                  refine ⟨98720307244883733990827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053016610612093162568821 98720307244883733990827)
                  ·
                    rfl

theorem cell22_865157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_865157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865157 prefixEnd_865157 := by exact prefixLift 865157
  have htrace : WordTrace (prefixWord ++ tailWord_865157) baseStart_865157 baseEnd_865157 := by
    simpa [prefixWord, tailWord_865157, baseEnd_865157] using wordTrace_append hprefix tailTrace_865157
  have hstable : (prefixWord ++ tailWord_865157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865157).length < 2 ^ (prefixWord ++ tailWord_865157).sum := by decide
  have hdescent : baseEnd_865157 < baseStart_865157 := by decide
  rcases family_descends (prefixWord ++ tailWord_865157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865206 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_865206 : Nat := 118140960795 + 865206 * 2 ^ 59
def prefixEnd_865206 : Nat := 4983230072969 + 3 ^ 40 * 865206 * 2
def baseEnd_865206 : Nat := 296177695436031407497331

theorem tailTrace_865206 : CollatzResearch.WordTrace tailWord_865206 prefixEnd_865206 296177695436031407497331 := by
  unfold tailWord_865206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972290956469618891606467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21037770202342601510468981 1972290956469618891606467)
  ·
    refine ⟨2958436434704428337409701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972290956469618891606467 2958436434704428337409701)
    ·
      refine ⟨554706831507080313264319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2958436434704428337409701 554706831507080313264319)
      ·
        refine ⟨832060247260620469896479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554706831507080313264319 832060247260620469896479)
        ·
          refine ⟨1248090370890930704844719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832060247260620469896479 1248090370890930704844719)
          ·
            refine ⟨1872135556336396057267079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248090370890930704844719 1872135556336396057267079)
            ·
              refine ⟨2808203334504594085900619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872135556336396057267079 2808203334504594085900619)
              ·
                refine ⟨4212305001756891128850929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808203334504594085900619 4212305001756891128850929)
                ·
                  refine ⟨3159228751317668346638197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212305001756891128850929 3159228751317668346638197)
                  ·
                    refine ⟨296177695436031407497331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3159228751317668346638197 296177695436031407497331)
                    ·
                      rfl

theorem cell22_865206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_865206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865206 prefixEnd_865206 := by exact prefixLift 865206
  have htrace : WordTrace (prefixWord ++ tailWord_865206) baseStart_865206 baseEnd_865206 := by
    simpa [prefixWord, tailWord_865206, baseEnd_865206] using wordTrace_append hprefix tailTrace_865206
  have hstable : (prefixWord ++ tailWord_865206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865206).length < 2 ^ (prefixWord ++ tailWord_865206).sum := by decide
  have hdescent : baseEnd_865206 < baseStart_865206 := by decide
  rcases family_descends (prefixWord ++ tailWord_865206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865335 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_865335 : Nat := 118140960795 + 865335 * 2 ^ 59
def prefixEnd_865335 : Nat := 4983230072969 + 3 ^ 40 * 865335 * 2
def baseEnd_865335 : Nat := 296221854772318071021935

theorem tailTrace_865335 : CollatzResearch.WordTrace tailWord_865335 prefixEnd_865335 296221854772318071021935 := by
  unfold tailWord_865335
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561360320046557297149459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21040906880031038198099639 31561360320046557297149459)
  ·
    refine ⟨47342040480069835945724189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31561360320046557297149459 47342040480069835945724189)
    ·
      refine ⟨17753265180026188479646571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47342040480069835945724189 17753265180026188479646571)
      ·
        refine ⟨26629897770039282719469857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17753265180026188479646571 26629897770039282719469857)
        ·
          refine ⟨19972423327529462039602393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26629897770039282719469857 19972423327529462039602393)
          ·
            refine ⟨14979317495647096529701795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19972423327529462039602393 14979317495647096529701795)
            ·
              refine ⟨22468976243470644794552693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979317495647096529701795 22468976243470644794552693)
              ·
                refine ⟨2106466522825372949489315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22468976243470644794552693 2106466522825372949489315)
                ·
                  refine ⟨3159699784238059424233973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106466522825372949489315 3159699784238059424233973)
                  ·
                    refine ⟨296221854772318071021935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3159699784238059424233973 296221854772318071021935)
                    ·
                      rfl

theorem cell22_865335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_865335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865335 prefixEnd_865335 := by exact prefixLift 865335
  have htrace : WordTrace (prefixWord ++ tailWord_865335) baseStart_865335 baseEnd_865335 := by
    simpa [prefixWord, tailWord_865335, baseEnd_865335] using wordTrace_append hprefix tailTrace_865335
  have hstable : (prefixWord ++ tailWord_865335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865335).length < 2 ^ (prefixWord ++ tailWord_865335).sum := by decide
  have hdescent : baseEnd_865335 < baseStart_865335 := by decide
  rcases family_descends (prefixWord ++ tailWord_865335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_865380 : Nat := 118140960795 + 865380 * 2 ^ 59
def prefixEnd_865380 : Nat := 4983230072969 + 3 ^ 40 * 865380 * 2
def baseEnd_865380 : Nat := 296237259191952953646797

theorem tailTrace_865380 : CollatzResearch.WordTrace tailWord_865380 prefixEnd_865380 296237259191952953646797 := by
  unfold tailWord_865380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781500802441764991268797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21042001069922353321691729 15781500802441764991268797)
  ·
    refine ⟨5918062800915661871725799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15781500802441764991268797 5918062800915661871725799)
    ·
      refine ⟨8877094201373492807588699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918062800915661871725799 8877094201373492807588699)
      ·
        refine ⟨13315641302060239211383049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877094201373492807588699 13315641302060239211383049)
        ·
          refine ⟨9986730976545179408537287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13315641302060239211383049 9986730976545179408537287)
          ·
            refine ⟨14980096464817769112805931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986730976545179408537287 14980096464817769112805931)
            ·
              refine ⟨22470144697226653669208897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980096464817769112805931 22470144697226653669208897)
              ·
                refine ⟨16852608522919990251906673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22470144697226653669208897 16852608522919990251906673)
                ·
                  refine ⟨12639456392189992688930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16852608522919990251906673 12639456392189992688930005)
                  ·
                    refine ⟨296237259191952953646797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12639456392189992688930005 296237259191952953646797)
                    ·
                      rfl

theorem cell22_865380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_865380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865380 prefixEnd_865380 := by exact prefixLift 865380
  have htrace : WordTrace (prefixWord ++ tailWord_865380) baseStart_865380 baseEnd_865380 := by
    simpa [prefixWord, tailWord_865380, baseEnd_865380] using wordTrace_append hprefix tailTrace_865380
  have hstable : (prefixWord ++ tailWord_865380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865380).length < 2 ^ (prefixWord ++ tailWord_865380).sum := by decide
  have hdescent : baseEnd_865380 < baseStart_865380 := by decide
  rcases family_descends (prefixWord ++ tailWord_865380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865401 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_865401 : Nat := 118140960795 + 865401 * 2 ^ 59
def prefixEnd_865401 : Nat := 4983230072969 + 3 ^ 40 * 865401 * 2
def baseEnd_865401 : Nat := 296244447921115898871733

theorem tailTrace_865401 : CollatzResearch.WordTrace tailWord_865401 prefixEnd_865401 296244447921115898871733 := by
  unfold tailWord_865401
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563767537807450569052057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21042511691871633712701371 31563767537807450569052057)
  ·
    refine ⟨23672825653355587926789043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31563767537807450569052057 23672825653355587926789043)
    ·
      refine ⟨35509238480033381890183565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23672825653355587926789043 35509238480033381890183565)
      ·
        refine ⟨13315964430012518208818837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35509238480033381890183565 13315964430012518208818837)
        ·
          refine ⟨624185832656836791038383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13315964430012518208818837 624185832656836791038383)
          ·
            refine ⟨936278748985255186557575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624185832656836791038383 936278748985255186557575)
            ·
              refine ⟨1404418123477882779836363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936278748985255186557575 1404418123477882779836363)
              ·
                refine ⟨2106627185216824169754545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404418123477882779836363 2106627185216824169754545)
                ·
                  refine ⟨1579970388912618127315909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106627185216824169754545 1579970388912618127315909)
                  ·
                    refine ⟨296244447921115898871733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579970388912618127315909 296244447921115898871733)
                    ·
                      rfl

theorem cell22_865401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_865401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865401 prefixEnd_865401 := by exact prefixLift 865401
  have htrace : WordTrace (prefixWord ++ tailWord_865401) baseStart_865401 baseEnd_865401 := by
    simpa [prefixWord, tailWord_865401, baseEnd_865401] using wordTrace_append hprefix tailTrace_865401
  have hstable : (prefixWord ++ tailWord_865401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865401).length < 2 ^ (prefixWord ++ tailWord_865401).sum := by decide
  have hdescent : baseEnd_865401 < baseStart_865401 := by decide
  rcases family_descends (prefixWord ++ tailWord_865401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865427 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 5]
def baseStart_865427 : Nat := 118140960795 + 865427 * 2 ^ 59
def prefixEnd_865427 : Nat := 4983230072969 + 3 ^ 40 * 865427 * 2
def baseEnd_865427 : Nat := 98751116084153499240551

theorem tailTrace_865427 : CollatzResearch.WordTrace tailWord_865427 prefixEnd_865427 98751116084153499240551 := by
  unfold tailWord_865427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564715835713257009498535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21043143890475504672999023 31564715835713257009498535)
  ·
    refine ⟨47347073753569885514247803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31564715835713257009498535 47347073753569885514247803)
    ·
      refine ⟨71020610630354828271371705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47347073753569885514247803 71020610630354828271371705)
      ·
        refine ⟨53265457972766121203528779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71020610630354828271371705 53265457972766121203528779)
        ·
          refine ⟨79898186959149181805293169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53265457972766121203528779 79898186959149181805293169)
          ·
            refine ⟨59923640219361886353969877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79898186959149181805293169 59923640219361886353969877)
            ·
              refine ⟨1404460317641294211421169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59923640219361886353969877 1404460317641294211421169)
              ·
                refine ⟨1053345238230970658565877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404460317641294211421169 1053345238230970658565877)
                ·
                  refine ⟨98751116084153499240551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053345238230970658565877 98751116084153499240551)
                  ·
                    rfl

theorem cell22_865427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].length) (baseStart_865427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865427 prefixEnd_865427 := by exact prefixLift 865427
  have htrace : WordTrace (prefixWord ++ tailWord_865427) baseStart_865427 baseEnd_865427 := by
    simpa [prefixWord, tailWord_865427, baseEnd_865427] using wordTrace_append hprefix tailTrace_865427
  have hstable : (prefixWord ++ tailWord_865427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865427).length < 2 ^ (prefixWord ++ tailWord_865427).sum := by decide
  have hdescent : baseEnd_865427 < baseStart_865427 := by decide
  rcases family_descends (prefixWord ++ tailWord_865427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865431 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 1, 3]
def baseStart_865431 : Nat := 118140960795 + 865431 * 2 ^ 59
def prefixEnd_865431 : Nat := 4983230072969 + 3 ^ 40 * 865431 * 2
def baseEnd_865431 : Nat := 296254717534205820621641

theorem tailTrace_865431 : CollatzResearch.WordTrace tailWord_865431 prefixEnd_865431 296254717534205820621641 := by
  unfold tailWord_865431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564861727698765692644147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21043241151799177128429431 31564861727698765692644147)
  ·
    refine ⟨47347292591548148538966221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31564861727698765692644147 47347292591548148538966221)
    ·
      refine ⟨17755234721830555702112333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47347292591548148538966221 17755234721830555702112333)
      ·
        refine ⟨6658213020686458388292125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17755234721830555702112333 6658213020686458388292125)
        ·
          refine ⟨2496829882757421895609547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6658213020686458388292125 2496829882757421895609547)
          ·
            refine ⟨3745244824136132843414321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496829882757421895609547 3745244824136132843414321)
            ·
              refine ⟨2808933618102099632560741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745244824136132843414321 2808933618102099632560741)
              ·
                refine ⟨526675053394143681105139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2808933618102099632560741 526675053394143681105139)
                ·
                  refine ⟨790012580091215521657709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526675053394143681105139 790012580091215521657709)
                  ·
                    refine ⟨296254717534205820621641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790012580091215521657709 296254717534205820621641)
                    ·
                      rfl

theorem cell22_865431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_865431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865431 prefixEnd_865431 := by exact prefixLift 865431
  have htrace : WordTrace (prefixWord ++ tailWord_865431) baseStart_865431 baseEnd_865431 := by
    simpa [prefixWord, tailWord_865431, baseEnd_865431] using wordTrace_append hprefix tailTrace_865431
  have hstable : (prefixWord ++ tailWord_865431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865431).length < 2 ^ (prefixWord ++ tailWord_865431).sum := by decide
  have hdescent : baseEnd_865431 < baseStart_865431 := by decide
  rcases family_descends (prefixWord ++ tailWord_865431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865547 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_865547 : Nat := 118140960795 + 865547 * 2 ^ 59
def prefixEnd_865547 : Nat := 4983230072969 + 3 ^ 40 * 865547 * 2
def baseEnd_865547 : Nat := 296294426704820184721285

theorem tailTrace_865547 : CollatzResearch.WordTrace tailWord_865547 prefixEnd_865547 296294426704820184721285 := by
  unfold tailWord_865547
  simp only [CollatzResearch.WordTrace]
  refine ⟨31569092595278517503866895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21046061730185678335911263 31569092595278517503866895)
  ·
    refine ⟨47353638892917776255800343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31569092595278517503866895 47353638892917776255800343)
    ·
      refine ⟨71030458339376664383700515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47353638892917776255800343 71030458339376664383700515)
      ·
        refine ⟨106545687509064996575550773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71030458339376664383700515 106545687509064996575550773)
        ·
          refine ⟨9988658203974843428957885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106545687509064996575550773 9988658203974843428957885)
          ·
            refine ⟨3745746826490566285859207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9988658203974843428957885 3745746826490566285859207)
            ·
              refine ⟨5618620239735849428788811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745746826490566285859207 5618620239735849428788811)
              ·
                refine ⟨8427930359603774143183217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618620239735849428788811 8427930359603774143183217)
                ·
                  refine ⟨6320947769702830607387413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427930359603774143183217 6320947769702830607387413)
                  ·
                    refine ⟨296294426704820184721285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6320947769702830607387413 296294426704820184721285)
                    ·
                      rfl

theorem cell22_865547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_865547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865547 prefixEnd_865547 := by exact prefixLift 865547
  have htrace : WordTrace (prefixWord ++ tailWord_865547) baseStart_865547 baseEnd_865547 := by
    simpa [prefixWord, tailWord_865547, baseEnd_865547] using wordTrace_append hprefix tailTrace_865547
  have hstable : (prefixWord ++ tailWord_865547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865547).length < 2 ^ (prefixWord ++ tailWord_865547).sum := by decide
  have hdescent : baseEnd_865547 < baseStart_865547 := by decide
  rcases family_descends (prefixWord ++ tailWord_865547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865596 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_865596 : Nat := 118140960795 + 865596 * 2 ^ 59
def prefixEnd_865596 : Nat := 4983230072969 + 3 ^ 40 * 865596 * 2
def baseEnd_865596 : Nat := 98770400135400130082045

theorem tailTrace_865596 : CollatzResearch.WordTrace tailWord_865596 prefixEnd_865596 98770400135400130082045 := by
  unfold tailWord_865596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785439886050499436200321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21047253181400665914933761 15785439886050499436200321)
  ·
    refine ⟨11839079914537874577150241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15785439886050499436200321 11839079914537874577150241)
    ·
      refine ⟨8879309935903405932862681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11839079914537874577150241 8879309935903405932862681)
      ·
        refine ⟨6659482451927554449647011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8879309935903405932862681 6659482451927554449647011)
        ·
          refine ⟨9989223677891331674470517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659482451927554449647011 9989223677891331674470517)
          ·
            refine ⟨936489719802312344481611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9989223677891331674470517 936489719802312344481611)
            ·
              refine ⟨1404734579703468516722417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936489719802312344481611 1404734579703468516722417)
              ·
                refine ⟨1053550934777601387541813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404734579703468516722417 1053550934777601387541813)
                ·
                  refine ⟨98770400135400130082045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053550934777601387541813 98770400135400130082045)
                  ·
                    rfl

theorem cell22_865596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_865596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865596 prefixEnd_865596 := by exact prefixLift 865596
  have htrace : WordTrace (prefixWord ++ tailWord_865596) baseStart_865596 baseEnd_865596 := by
    simpa [prefixWord, tailWord_865596, baseEnd_865596] using wordTrace_append hprefix tailTrace_865596
  have hstable : (prefixWord ++ tailWord_865596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865596).length < 2 ^ (prefixWord ++ tailWord_865596).sum := by decide
  have hdescent : baseEnd_865596 < baseStart_865596 := by decide
  rcases family_descends (prefixWord ++ tailWord_865596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865673 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_865673 : Nat := 118140960795 + 865673 * 2 ^ 59
def prefixEnd_865673 : Nat := 4983230072969 + 3 ^ 40 * 865673 * 2
def baseEnd_865673 : Nat := 296337559079797856070899

theorem tailTrace_865673 : CollatzResearch.WordTrace tailWord_865673 prefixEnd_865673 296337559079797856070899 := by
  unfold tailWord_865673
  simp only [CollatzResearch.WordTrace]
  refine ⟨31573688192822041022953673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21049125461881360681969115 31573688192822041022953673)
  ·
    refine ⟨23680266144616530767215255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31573688192822041022953673 23680266144616530767215255)
    ·
      refine ⟨35520399216924796150822883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23680266144616530767215255 35520399216924796150822883)
      ·
        refine ⟨53280598825387194226234325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35520399216924796150822883 53280598825387194226234325)
        ·
          refine ⟨1248764034970012364677367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53280598825387194226234325 1248764034970012364677367)
          ·
            refine ⟨1873146052455018547016051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248764034970012364677367 1873146052455018547016051)
            ·
              refine ⟨2809719078682527820524077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873146052455018547016051 2809719078682527820524077)
              ·
                refine ⟨1053644654505947932696529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2809719078682527820524077 1053644654505947932696529)
                ·
                  refine ⟨790233490879460949522397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053644654505947932696529 790233490879460949522397)
                  ·
                    refine ⟨296337559079797856070899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790233490879460949522397 296337559079797856070899)
                    ·
                      rfl

theorem cell22_865673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_865673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865673 prefixEnd_865673 := by exact prefixLift 865673
  have htrace : WordTrace (prefixWord ++ tailWord_865673) baseStart_865673 baseEnd_865673 := by
    simpa [prefixWord, tailWord_865673, baseEnd_865673] using wordTrace_append hprefix tailTrace_865673
  have hstable : (prefixWord ++ tailWord_865673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865673).length < 2 ^ (prefixWord ++ tailWord_865673).sum := by decide
  have hdescent : baseEnd_865673 < baseStart_865673 := by decide
  rcases family_descends (prefixWord ++ tailWord_865673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865688 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_865688 : Nat := 118140960795 + 865688 * 2 ^ 59
def prefixEnd_865688 : Nat := 4983230072969 + 3 ^ 40 * 865688 * 2
def baseEnd_865688 : Nat := 296342693886342816945853

theorem tailTrace_865688 : CollatzResearch.WordTrace tailWord_865688 prefixEnd_865688 296342693886342816945853 := by
  unfold tailWord_865688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787117643883849292374859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21049490191845132389833145 15787117643883849292374859)
  ·
    refine ⟨23680676465825773938562289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15787117643883849292374859 23680676465825773938562289)
    ·
      refine ⟨17760507349369330453921717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23680676465825773938562289 17760507349369330453921717)
      ·
        refine ⟨1665047564003374730055161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17760507349369330453921717 1665047564003374730055161)
        ·
          refine ⟨1248785673002531047541371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665047564003374730055161 1248785673002531047541371)
          ·
            refine ⟨1873178509503796571312057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248785673002531047541371 1873178509503796571312057)
            ·
              refine ⟨1404883882127847428484043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873178509503796571312057 1404883882127847428484043)
              ·
                refine ⟨2107325823191771142726065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404883882127847428484043 2107325823191771142726065)
                ·
                  refine ⟨1580494367393828357044549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2107325823191771142726065 1580494367393828357044549)
                  ·
                    refine ⟨296342693886342816945853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1580494367393828357044549 296342693886342816945853)
                    ·
                      rfl

theorem cell22_865688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_865688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865688 prefixEnd_865688 := by exact prefixLift 865688
  have htrace : WordTrace (prefixWord ++ tailWord_865688) baseStart_865688 baseEnd_865688 := by
    simpa [prefixWord, tailWord_865688, baseEnd_865688] using wordTrace_append hprefix tailTrace_865688
  have hstable : (prefixWord ++ tailWord_865688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865688).length < 2 ^ (prefixWord ++ tailWord_865688).sum := by decide
  have hdescent : baseEnd_865688 < baseStart_865688 := by decide
  rcases family_descends (prefixWord ++ tailWord_865688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865759 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 8]
def baseStart_865759 : Nat := 118140960795 + 865759 * 2 ^ 59
def prefixEnd_865759 : Nat := 4983230072969 + 3 ^ 40 * 865759 * 2
def baseEnd_865759 : Nat := 98788999545774099473545

theorem tailTrace_865759 : CollatzResearch.WordTrace tailWord_865759 prefixEnd_865759 98788999545774099473545 := by
  unfold tailWord_865759
  simp only [CollatzResearch.WordTrace]
  refine ⟨31576824870510477710584331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051216580340318473722887 31576824870510477710584331)
  ·
    refine ⟨47365237305765716565876497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31576824870510477710584331 47365237305765716565876497)
    ·
      refine ⟨35523927979324287424407373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47365237305765716565876497 35523927979324287424407373)
      ·
        refine ⟨13321472992246607784152765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35523927979324287424407373 13321472992246607784152765)
        ·
          refine ⟨4995552372092477919057287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13321472992246607784152765 4995552372092477919057287)
          ·
            refine ⟨7493328558138716878585931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995552372092477919057287 7493328558138716878585931)
            ·
              refine ⟨11239992837208075317878897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493328558138716878585931 11239992837208075317878897)
              ·
                refine ⟨8429994627906056488409173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11239992837208075317878897 8429994627906056488409173)
                ·
                  refine ⟨98788999545774099473545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8429994627906056488409173 98788999545774099473545)
                  ·
                    rfl

theorem cell22_865759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_865759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865759 prefixEnd_865759 := by exact prefixLift 865759
  have htrace : WordTrace (prefixWord ++ tailWord_865759) baseStart_865759 baseEnd_865759 := by
    simpa [prefixWord, tailWord_865759, baseEnd_865759] using wordTrace_append hprefix tailTrace_865759
  have hstable : (prefixWord ++ tailWord_865759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865759).length < 2 ^ (prefixWord ++ tailWord_865759).sum := by decide
  have hdescent : baseEnd_865759 < baseStart_865759 := by decide
  rcases family_descends (prefixWord ++ tailWord_865759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865776 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_865776 : Nat := 118140960795 + 865776 * 2 ^ 59
def prefixEnd_865776 : Nat := 4983230072969 + 3 ^ 40 * 865776 * 2
def baseEnd_865776 : Nat := 98790939361579973581861

theorem tailTrace_865776 : CollatzResearch.WordTrace tailWord_865776 prefixEnd_865776 98790939361579973581861 := by
  unfold tailWord_865776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788722455724444806976591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21051629940965926409302121 15788722455724444806976591)
  ·
    refine ⟨23683083683586667210464887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15788722455724444806976591 23683083683586667210464887)
    ·
      refine ⟨35524625525380000815697331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23683083683586667210464887 35524625525380000815697331)
      ·
        refine ⟨53286938288070001223545997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35524625525380000815697331 53286938288070001223545997)
        ·
          refine ⟨19982601858026250458829749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53286938288070001223545997 19982601858026250458829749)
          ·
            refine ⟨1873368924189960980515289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19982601858026250458829749 1873368924189960980515289)
            ·
              refine ⟨1405026693142470735386467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873368924189960980515289 1405026693142470735386467)
              ·
                refine ⟨2107540039713706103079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405026693142470735386467 2107540039713706103079701)
                ·
                  refine ⟨98790939361579973581861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2107540039713706103079701 98790939361579973581861)
                  ·
                    rfl

theorem cell22_865776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_865776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865776 prefixEnd_865776 := by exact prefixLift 865776
  have htrace : WordTrace (prefixWord ++ tailWord_865776) baseStart_865776 baseEnd_865776 := by
    simpa [prefixWord, tailWord_865776, baseEnd_865776] using wordTrace_append hprefix tailTrace_865776
  have hstable : (prefixWord ++ tailWord_865776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865776).length < 2 ^ (prefixWord ++ tailWord_865776).sum := by decide
  have hdescent : baseEnd_865776 < baseStart_865776 := by decide
  rcases family_descends (prefixWord ++ tailWord_865776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865838 : List Nat := [4, 1, 3, 1, 2, 2, 2, 7]
def baseStart_865838 : Nat := 118140960795 + 865838 * 2 ^ 59
def prefixEnd_865838 : Nat := 4983230072969 + 3 ^ 40 * 865838 * 2
def baseEnd_865838 : Nat := 32932671327976936188377

theorem tailTrace_865838 : CollatzResearch.WordTrace tailWord_865838 prefixEnd_865838 32932671327976936188377 := by
  unfold tailWord_865838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947463279653034275338771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21053137491482849468473445 3947463279653034275338771)
  ·
    refine ⟨5921194919479551413008157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947463279653034275338771 5921194919479551413008157)
    ·
      refine ⟨2220448094804831779878059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5921194919479551413008157 2220448094804831779878059)
      ·
        refine ⟨3330672142207247669817089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220448094804831779878059 3330672142207247669817089)
        ·
          refine ⟨2498004106655435752362817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330672142207247669817089 2498004106655435752362817)
          ·
            refine ⟨1873503079991576814272113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498004106655435752362817 1873503079991576814272113)
            ·
              refine ⟨1405127309993682610704085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873503079991576814272113 1405127309993682610704085)
              ·
                refine ⟨32932671327976936188377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1405127309993682610704085 32932671327976936188377)
                ·
                  rfl

theorem cell22_865838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_865838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865838 prefixEnd_865838 := by exact prefixLift 865838
  have htrace : WordTrace (prefixWord ++ tailWord_865838) baseStart_865838 baseEnd_865838 := by
    simpa [prefixWord, tailWord_865838, baseEnd_865838] using wordTrace_append hprefix tailTrace_865838
  have hstable : (prefixWord ++ tailWord_865838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865838).length < 2 ^ (prefixWord ++ tailWord_865838).sum := by decide
  have hdescent : baseEnd_865838 < baseStart_865838 := by decide
  rcases family_descends (prefixWord ++ tailWord_865838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865870 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_865870 : Nat := 118140960795 + 865870 * 2 ^ 59
def prefixEnd_865870 : Nat := 4983230072969 + 3 ^ 40 * 865870 * 2
def baseEnd_865870 : Nat := 296404996205755008895295

theorem tailTrace_865870 : CollatzResearch.WordTrace tailWord_865870 prefixEnd_865870 296404996205755008895295 := by
  unfold tailWord_865870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947609171638542958484383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21053915582072229111916709 3947609171638542958484383)
  ·
    refine ⟨5921413757457814437726575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947609171638542958484383 5921413757457814437726575)
    ·
      refine ⟨8882120636186721656589863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5921413757457814437726575 8882120636186721656589863)
      ·
        refine ⟨13323180954280082484884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882120636186721656589863 13323180954280082484884795)
        ·
          refine ⟨19984771431420123727327193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13323180954280082484884795 19984771431420123727327193)
          ·
            refine ⟨14988578573565092795495395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19984771431420123727327193 14988578573565092795495395)
            ·
              refine ⟨22482867860347639193243093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988578573565092795495395 22482867860347639193243093)
              ·
                refine ⟨526942215476897793591635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22482867860347639193243093 526942215476897793591635)
                ·
                  refine ⟨790413323215346690387453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526942215476897793591635 790413323215346690387453)
                  ·
                    refine ⟨296404996205755008895295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790413323215346690387453 296404996205755008895295)
                    ·
                      rfl

theorem cell22_865870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_865870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865870 prefixEnd_865870 := by exact prefixLift 865870
  have htrace : WordTrace (prefixWord ++ tailWord_865870) baseStart_865870 baseEnd_865870 := by
    simpa [prefixWord, tailWord_865870, baseEnd_865870] using wordTrace_append hprefix tailTrace_865870
  have hstable : (prefixWord ++ tailWord_865870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865870).length < 2 ^ (prefixWord ++ tailWord_865870).sum := by decide
  have hdescent : baseEnd_865870 < baseStart_865870 := by decide
  rcases family_descends (prefixWord ++ tailWord_865870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865878 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_865878 : Nat := 118140960795 + 865878 * 2 ^ 59
def prefixEnd_865878 : Nat := 4983230072969 + 3 ^ 40 * 865878 * 2
def baseEnd_865878 : Nat := 98802578256415218231757

theorem tailTrace_865878 : CollatzResearch.WordTrace tailWord_865878 prefixEnd_865878 98802578256415218231757 := by
  unfold tailWord_865878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973822822317460064635393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21054110104719574022777525 1973822822317460064635393)
  ·
    refine ⟨1480367116738095048476545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973822822317460064635393 1480367116738095048476545)
    ·
      refine ⟨1110275337553571286357409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480367116738095048476545 1110275337553571286357409)
      ·
        refine ⟨832706503165178464768057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110275337553571286357409 832706503165178464768057)
        ·
          refine ⟨624529877373883848576043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832706503165178464768057 624529877373883848576043)
          ·
            refine ⟨936794816060825772864065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624529877373883848576043 936794816060825772864065)
            ·
              refine ⟨702596112045619329648049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936794816060825772864065 702596112045619329648049)
              ·
                refine ⟨526947084034214497236037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702596112045619329648049 526947084034214497236037)
                ·
                  refine ⟨98802578256415218231757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526947084034214497236037 98802578256415218231757)
                  ·
                    rfl

theorem cell22_865878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_865878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865878 prefixEnd_865878 := by exact prefixLift 865878
  have htrace : WordTrace (prefixWord ++ tailWord_865878) baseStart_865878 baseEnd_865878 := by
    simpa [prefixWord, tailWord_865878, baseEnd_865878] using wordTrace_append hprefix tailTrace_865878
  have hstable : (prefixWord ++ tailWord_865878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865878).length < 2 ^ (prefixWord ++ tailWord_865878).sum := by decide
  have hdescent : baseEnd_865878 < baseStart_865878 := by decide
  rcases family_descends (prefixWord ++ tailWord_865878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865898 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_865898 : Nat := 118140960795 + 865898 * 2 ^ 59
def prefixEnd_865898 : Nat := 4983230072969 + 3 ^ 40 * 865898 * 2
def baseEnd_865898 : Nat := 296414581177972269195209

theorem tailTrace_865898 : CollatzResearch.WordTrace tailWord_865898 prefixEnd_865898 296414581177972269195209 := by
  unfold tailWord_865898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895473654251726112473587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21054596411337936299929565 7895473654251726112473587)
  ·
    refine ⟨11843210481377589168710381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7895473654251726112473587 11843210481377589168710381)
    ·
      refine ⟨4441203930516595938266393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11843210481377589168710381 4441203930516595938266393)
      ·
        refine ⟨3330902947887446953699795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4441203930516595938266393 3330902947887446953699795)
        ·
          refine ⟨4996354421831170430549693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330902947887446953699795 4996354421831170430549693)
          ·
            refine ⟨1873632908186688911456135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4996354421831170430549693 1873632908186688911456135)
            ·
              refine ⟨2810449362280033367184203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873632908186688911456135 2810449362280033367184203)
              ·
                refine ⟨4215674043420050050776305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810449362280033367184203 4215674043420050050776305)
                ·
                  refine ⟨3161755532565037538082229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215674043420050050776305 3161755532565037538082229)
                  ·
                    refine ⟨296414581177972269195209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3161755532565037538082229 296414581177972269195209)
                    ·
                      rfl

theorem cell22_865898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_865898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865898 prefixEnd_865898 := by exact prefixLift 865898
  have htrace : WordTrace (prefixWord ++ tailWord_865898) baseStart_865898 baseEnd_865898 := by
    simpa [prefixWord, tailWord_865898, baseEnd_865898] using wordTrace_append hprefix tailTrace_865898
  have hstable : (prefixWord ++ tailWord_865898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865898).length < 2 ^ (prefixWord ++ tailWord_865898).sum := by decide
  have hdescent : baseEnd_865898 < baseStart_865898 := by decide
  rcases family_descends (prefixWord ++ tailWord_865898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865913 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_865913 : Nat := 118140960795 + 865913 * 2 ^ 59
def prefixEnd_865913 : Nat := 4983230072969 + 3 ^ 40 * 865913 * 2
def baseEnd_865913 : Nat := 296419715984517230070163

theorem tailTrace_865913 : CollatzResearch.WordTrace tailWord_865913 prefixEnd_865913 296419715984517230070163 := by
  unfold tailWord_865913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582441711952562011690393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21054961141301708007793595 31582441711952562011690393)
  ·
    refine ⟨23686831283964421508767795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31582441711952562011690393 23686831283964421508767795)
    ·
      refine ⟨35530246925946632263151693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23686831283964421508767795 35530246925946632263151693)
      ·
        refine ⟨13323842597229987098681885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35530246925946632263151693 13323842597229987098681885)
        ·
          refine ⟨4996440973961245162005707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13323842597229987098681885 4996440973961245162005707)
          ·
            refine ⟨7494661460941867743008561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996440973961245162005707 7494661460941867743008561)
            ·
              refine ⟨5620996095706400807256421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494661460941867743008561 5620996095706400807256421)
              ·
                refine ⟨1053936767944950151360579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5620996095706400807256421 1053936767944950151360579)
                ·
                  refine ⟨1580905151917425227040869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053936767944950151360579 1580905151917425227040869)
                  ·
                    refine ⟨296419715984517230070163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1580905151917425227040869 296419715984517230070163)
                    ·
                      rfl

theorem cell22_865913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_865913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865913 prefixEnd_865913 := by exact prefixLift 865913
  have htrace : WordTrace (prefixWord ++ tailWord_865913) baseStart_865913 baseEnd_865913 := by
    simpa [prefixWord, tailWord_865913, baseEnd_865913] using wordTrace_append hprefix tailTrace_865913
  have hstable : (prefixWord ++ tailWord_865913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865913).length < 2 ^ (prefixWord ++ tailWord_865913).sum := by decide
  have hdescent : baseEnd_865913 < baseStart_865913 := by decide
  rcases family_descends (prefixWord ++ tailWord_865913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865930 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_865930 : Nat := 118140960795 + 865930 * 2 ^ 59
def prefixEnd_865930 : Nat := 4983230072969 + 3 ^ 40 * 865930 * 2
def baseEnd_865930 : Nat := 296425535431934852395111

theorem tailTrace_865930 : CollatzResearch.WordTrace tailWord_865930 prefixEnd_865930 296425535431934852395111 := by
  unfold tailWord_865930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895765438222743478764811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21055374501927315943372829 7895765438222743478764811)
  ·
    refine ⟨11843648157334115218147217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7895765438222743478764811 11843648157334115218147217)
    ·
      refine ⟨8882736118000586413610413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843648157334115218147217 8882736118000586413610413)
      ·
        refine ⟨3331026044250219905103905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8882736118000586413610413 3331026044250219905103905)
        ·
          refine ⟨2498269533187664928827929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331026044250219905103905 2498269533187664928827929)
          ·
            refine ⟨1873702149890748696620947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498269533187664928827929 1873702149890748696620947)
            ·
              refine ⟨2810553224836123044931421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873702149890748696620947 2810553224836123044931421)
              ·
                refine ⟨1053957459313546141849283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2810553224836123044931421 1053957459313546141849283)
                ·
                  refine ⟨1580936188970319212773925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053957459313546141849283 1580936188970319212773925)
                  ·
                    refine ⟨296425535431934852395111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1580936188970319212773925 296425535431934852395111)
                    ·
                      rfl

theorem cell22_865930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_865930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865930 prefixEnd_865930 := by exact prefixLift 865930
  have htrace : WordTrace (prefixWord ++ tailWord_865930) baseStart_865930 baseEnd_865930 := by
    simpa [prefixWord, tailWord_865930, baseEnd_865930] using wordTrace_append hprefix tailTrace_865930
  have hstable : (prefixWord ++ tailWord_865930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865930).length < 2 ^ (prefixWord ++ tailWord_865930).sum := by decide
  have hdescent : baseEnd_865930 < baseStart_865930 := by decide
  rcases family_descends (prefixWord ++ tailWord_865930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865971 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_865971 : Nat := 118140960795 + 865971 * 2 ^ 59
def prefixEnd_865971 : Nat := 4983230072969 + 3 ^ 40 * 865971 * 2
def baseEnd_865971 : Nat := 296439570569824412119985

theorem tailTrace_865971 : CollatzResearch.WordTrace tailWord_865971 prefixEnd_865971 296439570569824412119985 := by
  unfold tailWord_865971
  simp only [CollatzResearch.WordTrace]
  refine ⟨31584557145742437917301767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21056371430494958611534511 31584557145742437917301767)
  ·
    refine ⟨47376835718613656875952651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31584557145742437917301767 47376835718613656875952651)
    ·
      refine ⟨71065253577920485313928977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47376835718613656875952651 71065253577920485313928977)
      ·
        refine ⟨53298940183440363985446733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71065253577920485313928977 53298940183440363985446733)
        ·
          refine ⟨19987102568790136494542525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53298940183440363985446733 19987102568790136494542525)
          ·
            refine ⟨7495163463296301185453447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19987102568790136494542525 7495163463296301185453447)
            ·
              refine ⟨11242745194944451778180171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495163463296301185453447 11242745194944451778180171)
              ·
                refine ⟨16864117792416677667270257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242745194944451778180171 16864117792416677667270257)
                ·
                  refine ⟨12648088344312508250452693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16864117792416677667270257 12648088344312508250452693)
                  ·
                    refine ⟨296439570569824412119985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12648088344312508250452693 296439570569824412119985)
                    ·
                      rfl

theorem cell22_865971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_865971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_865971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_865971 prefixEnd_865971 := by exact prefixLift 865971
  have htrace : WordTrace (prefixWord ++ tailWord_865971) baseStart_865971 baseEnd_865971 := by
    simpa [prefixWord, tailWord_865971, baseEnd_865971] using wordTrace_append hprefix tailTrace_865971
  have hstable : (prefixWord ++ tailWord_865971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865971).length < 2 ^ (prefixWord ++ tailWord_865971).sum := by decide
  have hdescent : baseEnd_865971 < baseStart_865971 := by decide
  rcases family_descends (prefixWord ++ tailWord_865971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866050 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_866050 : Nat := 118140960795 + 866050 * 2 ^ 59
def prefixEnd_866050 : Nat := 4983230072969 + 3 ^ 40 * 866050 * 2
def baseEnd_866050 : Nat := 296466613884294539394743

theorem tailTrace_866050 : CollatzResearch.WordTrace tailWord_866050 prefixEnd_866050 296466613884294539394743 := by
  unfold tailWord_866050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896859628114058602356901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21058292341637489606285069 7896859628114058602356901)
  ·
    refine ⟨1480661180271385987941919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7896859628114058602356901 1480661180271385987941919)
    ·
      refine ⟨2220991770407078981912879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480661180271385987941919 2220991770407078981912879)
      ·
        refine ⟨3331487655610618472869319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220991770407078981912879 3331487655610618472869319)
        ·
          refine ⟨4997231483415927709303979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331487655610618472869319 4997231483415927709303979)
          ·
            refine ⟨7495847225123891563955969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997231483415927709303979 7495847225123891563955969)
            ·
              refine ⟨5621885418842918672966977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495847225123891563955969 5621885418842918672966977)
              ·
                refine ⟨4216414064132189004725233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621885418842918672966977 4216414064132189004725233)
                ·
                  refine ⟨3162310548099141753543925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216414064132189004725233 3162310548099141753543925)
                  ·
                    refine ⟨296466613884294539394743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3162310548099141753543925 296466613884294539394743)
                    ·
                      rfl

theorem cell22_866050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_866050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866050 prefixEnd_866050 := by exact prefixLift 866050
  have htrace : WordTrace (prefixWord ++ tailWord_866050) baseStart_866050 baseEnd_866050 := by
    simpa [prefixWord, tailWord_866050, baseEnd_866050] using wordTrace_append hprefix tailTrace_866050
  have hstable : (prefixWord ++ tailWord_866050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866050).length < 2 ^ (prefixWord ++ tailWord_866050).sum := by decide
  have hdescent : baseEnd_866050 < baseStart_866050 := by decide
  rcases family_descends (prefixWord ++ tailWord_866050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866097 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 4]
def baseStart_866097 : Nat := 118140960795 + 866097 * 2 ^ 59
def prefixEnd_866097 : Nat := 4983230072969 + 3 ^ 40 * 866097 * 2
def baseEnd_866097 : Nat := 98827567648267361156533

theorem tailTrace_866097 : CollatzResearch.WordTrace tailWord_866097 prefixEnd_866097 98827567648267361156533 := by
  unfold tailWord_866097
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589152743285961436388545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21059435162190640957592363 31589152743285961436388545)
  ·
    refine ⟨23691864557464471077291409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31589152743285961436388545 23691864557464471077291409)
    ·
      refine ⟨17768898418098353307968557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23691864557464471077291409 17768898418098353307968557)
      ·
        refine ⟨6663336906786882490488209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17768898418098353307968557 6663336906786882490488209)
        ·
          refine ⟨4997502680090161867866157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6663336906786882490488209 4997502680090161867866157)
          ·
            refine ⟨1874063505033810700449809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4997502680090161867866157 1874063505033810700449809)
            ·
              refine ⟨1405547628775358025337357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874063505033810700449809 1405547628775358025337357)
              ·
                refine ⟨527080360790759259501509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405547628775358025337357 527080360790759259501509)
                ·
                  refine ⟨98827567648267361156533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527080360790759259501509 98827567648267361156533)
                  ·
                    rfl

theorem cell22_866097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_866097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866097 prefixEnd_866097 := by exact prefixLift 866097
  have htrace : WordTrace (prefixWord ++ tailWord_866097) baseStart_866097 baseEnd_866097 := by
    simpa [prefixWord, tailWord_866097, baseEnd_866097] using wordTrace_append hprefix tailTrace_866097
  have hstable : (prefixWord ++ tailWord_866097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866097).length < 2 ^ (prefixWord ++ tailWord_866097).sum := by decide
  have hdescent : baseEnd_866097 < baseStart_866097 := by decide
  rcases family_descends (prefixWord ++ tailWord_866097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866099 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 1, 4]
def baseStart_866099 : Nat := 118140960795 + 866099 * 2 ^ 59
def prefixEnd_866099 : Nat := 4983230072969 + 3 ^ 40 * 866099 * 2
def baseEnd_866099 : Nat := 296483387585674744919593

theorem tailTrace_866099 : CollatzResearch.WordTrace tailWord_866099 prefixEnd_866099 296483387585674744919593 := by
  unfold tailWord_866099
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589225689278715777961351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21059483792852477185307567 31589225689278715777961351)
  ·
    refine ⟨47383838533918073666942027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31589225689278715777961351 47383838533918073666942027)
    ·
      refine ⟨71075757800877110500413041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47383838533918073666942027 71075757800877110500413041)
      ·
        refine ⟨53306818350657832875309781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71075757800877110500413041 53306818350657832875309781)
        ·
          refine ⟨1249378555093542958015073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53306818350657832875309781 1249378555093542958015073)
          ·
            refine ⟨937033916320157218511305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249378555093542958015073 937033916320157218511305)
            ·
              refine ⟨702775437240117913883479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937033916320157218511305 702775437240117913883479)
              ·
                refine ⟨1054163155860176870825219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702775437240117913883479 1054163155860176870825219)
                ·
                  refine ⟨1581244733790265306237829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054163155860176870825219 1581244733790265306237829)
                  ·
                    refine ⟨296483387585674744919593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1581244733790265306237829 296483387585674744919593)
                    ·
                      rfl

theorem cell22_866099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 4].length) (baseStart_866099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866099 prefixEnd_866099 := by exact prefixLift 866099
  have htrace : WordTrace (prefixWord ++ tailWord_866099) baseStart_866099 baseEnd_866099 := by
    simpa [prefixWord, tailWord_866099, baseEnd_866099] using wordTrace_append hprefix tailTrace_866099
  have hstable : (prefixWord ++ tailWord_866099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866099).length < 2 ^ (prefixWord ++ tailWord_866099).sum := by decide
  have hdescent : baseEnd_866099 < baseStart_866099 := by decide
  rcases family_descends (prefixWord ++ tailWord_866099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866129 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_866129 : Nat := 118140960795 + 866129 * 2 ^ 59
def prefixEnd_866129 : Nat := 4983230072969 + 3 ^ 40 * 866129 * 2
def baseEnd_866129 : Nat := 296493657198764666669501

theorem tailTrace_866129 : CollatzResearch.WordTrace tailWord_866129 prefixEnd_866129 296493657198764666669501 := by
  unfold tailWord_866129
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590319879170030901553441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21060213252780020601035627 31590319879170030901553441)
  ·
    refine ⟨23692739909377523176165081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31590319879170030901553441 23692739909377523176165081)
    ·
      refine ⟨17769554932033142382123811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23692739909377523176165081 17769554932033142382123811)
      ·
        refine ⟨26654332398049713573185717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17769554932033142382123811 26654332398049713573185717)
        ·
          refine ⟨2498843662317160647486161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26654332398049713573185717 2498843662317160647486161)
          ·
            refine ⟨1874132746737870485614621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498843662317160647486161 1874132746737870485614621)
            ·
              refine ⟨702799780026701432105483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874132746737870485614621 702799780026701432105483)
              ·
                refine ⟨1054199670040052148158225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702799780026701432105483 1054199670040052148158225)
                ·
                  refine ⟨790649752530039111118669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054199670040052148158225 790649752530039111118669)
                  ·
                    refine ⟨296493657198764666669501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790649752530039111118669 296493657198764666669501)
                    ·
                      rfl

theorem cell22_866129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_866129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866129 prefixEnd_866129 := by exact prefixLift 866129
  have htrace : WordTrace (prefixWord ++ tailWord_866129) baseStart_866129 baseEnd_866129 := by
    simpa [prefixWord, tailWord_866129, baseEnd_866129] using wordTrace_append hprefix tailTrace_866129
  have hstable : (prefixWord ++ tailWord_866129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866129).length < 2 ^ (prefixWord ++ tailWord_866129).sum := by decide
  have hdescent : baseEnd_866129 < baseStart_866129 := by decide
  rcases family_descends (prefixWord ++ tailWord_866129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866232 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_866232 : Nat := 118140960795 + 866232 * 2 ^ 59
def prefixEnd_866232 : Nat := 4983230072969 + 3 ^ 40 * 866232 * 2
def baseEnd_866232 : Nat := 98842972067902243781395

theorem tailTrace_866232 : CollatzResearch.WordTrace tailWord_866232 prefixEnd_866232 98842972067902243781395 := by
  unfold tailWord_866232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15797038298898439746276475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21062717731864586328368633 15797038298898439746276475)
  ·
    refine ⟨23695557448347659619414713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15797038298898439746276475 23695557448347659619414713)
    ·
      refine ⟨17771668086260744714561035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23695557448347659619414713 17771668086260744714561035)
      ·
        refine ⟨26657502129391117071841553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17771668086260744714561035 26657502129391117071841553)
        ·
          refine ⟨19993126597043337803881165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26657502129391117071841553 19993126597043337803881165)
          ·
            refine ⟨7497422473891251676455437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19993126597043337803881165 7497422473891251676455437)
            ·
              refine ⟨2811533427709219378670789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7497422473891251676455437 2811533427709219378670789)
              ·
                refine ⟨527162517695478633500773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2811533427709219378670789 527162517695478633500773)
                ·
                  refine ⟨98842972067902243781395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527162517695478633500773 98842972067902243781395)
                  ·
                    rfl

theorem cell22_866232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_866232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866232 prefixEnd_866232 := by exact prefixLift 866232
  have htrace : WordTrace (prefixWord ++ tailWord_866232) baseStart_866232 baseEnd_866232 := by
    simpa [prefixWord, tailWord_866232, baseEnd_866232] using wordTrace_append hprefix tailTrace_866232
  have hstable : (prefixWord ++ tailWord_866232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866232).length < 2 ^ (prefixWord ++ tailWord_866232).sum := by decide
  have hdescent : baseEnd_866232 < baseStart_866232 := by decide
  rcases family_descends (prefixWord ++ tailWord_866232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866268 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_866268 : Nat := 118140960795 + 866268 * 2 ^ 59
def prefixEnd_866268 : Nat := 4983230072969 + 3 ^ 40 * 866268 * 2
def baseEnd_866268 : Nat := 296541239739414637444075

theorem tailTrace_866268 : CollatzResearch.WordTrace tailWord_866268 prefixEnd_866268 296541239739414637444075 := by
  unfold tailWord_866268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15797694812833228820431729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21063593083777638427242305 15797694812833228820431729)
  ·
    refine ⟨11848271109624921615323797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15797694812833228820431729 11848271109624921615323797)
    ·
      refine ⟨555387708263668200718303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11848271109624921615323797 555387708263668200718303)
      ·
        refine ⟨833081562395502301077455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555387708263668200718303 833081562395502301077455)
        ·
          refine ⟨1249622343593253451616183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833081562395502301077455 1249622343593253451616183)
          ·
            refine ⟨1874433515389880177424275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249622343593253451616183 1874433515389880177424275)
            ·
              refine ⟨2811650273084820266136413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874433515389880177424275 2811650273084820266136413)
              ·
                refine ⟨1054368852406807599801155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2811650273084820266136413 1054368852406807599801155)
                ·
                  refine ⟨1581553278610211399701733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054368852406807599801155 1581553278610211399701733)
                  ·
                    refine ⟨296541239739414637444075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1581553278610211399701733 296541239739414637444075)
                    ·
                      rfl

theorem cell22_866268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_866268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866268 prefixEnd_866268 := by exact prefixLift 866268
  have htrace : WordTrace (prefixWord ++ tailWord_866268) baseStart_866268 baseEnd_866268 := by
    simpa [prefixWord, tailWord_866268, baseEnd_866268] using wordTrace_append hprefix tailTrace_866268
  have hstable : (prefixWord ++ tailWord_866268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866268).length < 2 ^ (prefixWord ++ tailWord_866268).sum := by decide
  have hdescent : baseEnd_866268 < baseStart_866268 := by decide
  rcases family_descends (prefixWord ++ tailWord_866268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866317 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 4]
def baseStart_866317 : Nat := 118140960795 + 866317 * 2 ^ 59
def prefixEnd_866317 : Nat := 4983230072969 + 3 ^ 40 * 866317 * 2
def baseEnd_866317 : Nat := 98852671146931614322975

theorem tailTrace_866317 : CollatzResearch.WordTrace tailWord_866317 prefixEnd_866317 98852671146931614322975 := by
  unfold tailWord_866317
  simp only [CollatzResearch.WordTrace]
  refine ⟨31597176802488939009397205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21064784534992626006264803 31597176802488939009397205)
  ·
    refine ⟨740558831308334508032747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31597176802488939009397205 740558831308334508032747)
    ·
      refine ⟨1110838246962501762049121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740558831308334508032747 1110838246962501762049121)
      ·
        refine ⟨833128685221876321536841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110838246962501762049121 833128685221876321536841)
        ·
          refine ⟨624846513916407241152631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833128685221876321536841 624846513916407241152631)
          ·
            refine ⟨937269770874610861728947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624846513916407241152631 937269770874610861728947)
            ·
              refine ⟨1405904656311916292593421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937269770874610861728947 1405904656311916292593421)
              ·
                refine ⟨527214246116968609722533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405904656311916292593421 527214246116968609722533)
                ·
                  refine ⟨98852671146931614322975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527214246116968609722533 98852671146931614322975)
                  ·
                    rfl

theorem cell22_866317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_866317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866317 prefixEnd_866317 := by exact prefixLift 866317
  have htrace : WordTrace (prefixWord ++ tailWord_866317) baseStart_866317 baseEnd_866317 := by
    simpa [prefixWord, tailWord_866317, baseEnd_866317] using wordTrace_append hprefix tailTrace_866317
  have hstable : (prefixWord ++ tailWord_866317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866317).length < 2 ^ (prefixWord ++ tailWord_866317).sum := by decide
  have hdescent : baseEnd_866317 < baseStart_866317 := by decide
  rcases family_descends (prefixWord ++ tailWord_866317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866343 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 3, 3]
def baseStart_866343 : Nat := 118140960795 + 866343 * 2 ^ 59
def prefixEnd_866343 : Nat := 4983230072969 + 3 ^ 40 * 866343 * 2
def baseEnd_866343 : Nat := 296566913772139441818845

theorem tailTrace_866343 : CollatzResearch.WordTrace tailWord_866343 prefixEnd_866343 296566913772139441818845 := by
  unfold tailWord_866343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31598125100394745449843683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21065416733596496966562455 31598125100394745449843683)
  ·
    refine ⟨47397187650592118174765525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31598125100394745449843683 47397187650592118174765525)
    ·
      refine ⟨1110871585560752769721067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 47397187650592118174765525 1110871585560752769721067)
      ·
        refine ⟨1666307378341129154581601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110871585560752769721067 1666307378341129154581601)
        ·
          refine ⟨1249730533755846865936201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666307378341129154581601 1249730533755846865936201)
          ·
            refine ⟨937297900316885149452151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249730533755846865936201 937297900316885149452151)
            ·
              refine ⟨1405946850475327724178227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937297900316885149452151 1405946850475327724178227)
              ·
                refine ⟨2108920275712991586267341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405946850475327724178227 2108920275712991586267341)
                ·
                  refine ⟨790845103392371844850253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2108920275712991586267341 790845103392371844850253)
                  ·
                    refine ⟨296566913772139441818845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790845103392371844850253 296566913772139441818845)
                    ·
                      rfl

theorem cell22_866343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_866343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866343 prefixEnd_866343 := by exact prefixLift 866343
  have htrace : WordTrace (prefixWord ++ tailWord_866343) baseStart_866343 baseEnd_866343 := by
    simpa [prefixWord, tailWord_866343, baseEnd_866343] using wordTrace_append hprefix tailTrace_866343
  have hstable : (prefixWord ++ tailWord_866343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866343).length < 2 ^ (prefixWord ++ tailWord_866343).sum := by decide
  have hdescent : baseEnd_866343 < baseStart_866343 := by decide
  rcases family_descends (prefixWord ++ tailWord_866343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866356 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_866356 : Nat := 118140960795 + 866356 * 2 ^ 59
def prefixEnd_866356 : Nat := 4983230072969 + 3 ^ 40 * 866356 * 2
def baseEnd_866356 : Nat := 98857121312603913747935

theorem tailTrace_866356 : CollatzResearch.WordTrace tailWord_866356 prefixEnd_866356 98857121312603913747935 := by
  unfold tailWord_866356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799299624673824335033461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21065732832898432446711281 15799299624673824335033461)
  ·
    refine ⟨1481184339813171031409387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15799299624673824335033461 1481184339813171031409387)
    ·
      refine ⟨2221776509719756547114081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481184339813171031409387 2221776509719756547114081)
      ·
        refine ⟨1666332382289817410335561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221776509719756547114081 1666332382289817410335561)
        ·
          refine ⟨1249749286717363057751671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666332382289817410335561 1249749286717363057751671)
          ·
            refine ⟨1874623930076044586627507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249749286717363057751671 1874623930076044586627507)
            ·
              refine ⟨2811935895114066879941261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874623930076044586627507 2811935895114066879941261)
              ·
                refine ⟨1054475960667775079977973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2811935895114066879941261 1054475960667775079977973)
                ·
                  refine ⟨98857121312603913747935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1054475960667775079977973 98857121312603913747935)
                  ·
                    rfl

theorem cell22_866356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_866356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866356 prefixEnd_866356 := by exact prefixLift 866356
  have htrace : WordTrace (prefixWord ++ tailWord_866356) baseStart_866356 baseEnd_866356 := by
    simpa [prefixWord, tailWord_866356, baseEnd_866356] using wordTrace_append hprefix tailTrace_866356
  have hstable : (prefixWord ++ tailWord_866356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866356).length < 2 ^ (prefixWord ++ tailWord_866356).sum := by decide
  have hdescent : baseEnd_866356 < baseStart_866356 := by decide
  rcases family_descends (prefixWord ++ tailWord_866356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866369 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_866369 : Nat := 118140960795 + 866369 * 2 ^ 59
def prefixEnd_866369 : Nat := 4983230072969 + 3 ^ 40 * 866369 * 2
def baseEnd_866369 : Nat := 296575814103484040668765

theorem tailTrace_866369 : CollatzResearch.WordTrace tailWord_866369 prefixEnd_866369 296575814103484040668765 := by
  unfold tailWord_866369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31599073398300551890290161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21066048932200367926860107 31599073398300551890290161)
  ·
    refine ⟨23699305048725413917717621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31599073398300551890290161 23699305048725413917717621)
    ·
      refine ⟨2221809848318007554786027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23699305048725413917717621 2221809848318007554786027)
      ·
        refine ⟨3332714772477011332179041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221809848318007554786027 3332714772477011332179041)
        ·
          refine ⟨2499536079357758499134281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332714772477011332179041 2499536079357758499134281)
          ·
            refine ⟨1874652059518318874350711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499536079357758499134281 1874652059518318874350711)
            ·
              refine ⟨2811978089277478311526067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874652059518318874350711 2811978089277478311526067)
              ·
                refine ⟨4217967133916217467289101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811978089277478311526067 4217967133916217467289101)
                ·
                  refine ⟨1581737675218581550233413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4217967133916217467289101 1581737675218581550233413)
                  ·
                    refine ⟨296575814103484040668765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1581737675218581550233413 296575814103484040668765)
                    ·
                      rfl

theorem cell22_866369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_866369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866369 prefixEnd_866369 := by exact prefixLift 866369
  have htrace : WordTrace (prefixWord ++ tailWord_866369) baseStart_866369 baseEnd_866369 := by
    simpa [prefixWord, tailWord_866369, baseEnd_866369] using wordTrace_append hprefix tailTrace_866369
  have hstable : (prefixWord ++ tailWord_866369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866369).length < 2 ^ (prefixWord ++ tailWord_866369).sum := by decide
  have hdescent : baseEnd_866369 < baseStart_866369 := by decide
  rcases family_descends (prefixWord ++ tailWord_866369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866382 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_866382 : Nat := 118140960795 + 866382 * 2 ^ 59
def prefixEnd_866382 : Nat := 4983230072969 + 3 ^ 40 * 866382 * 2
def baseEnd_866382 : Nat := 296580264269156340093725

theorem tailTrace_866382 : CollatzResearch.WordTrace tailWord_866382 prefixEnd_866382 296580264269156340093725 := by
  unfold tailWord_866382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949943443406681888814175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21066365031502303407008933 3949943443406681888814175)
  ·
    refine ⟨5924915165110022833221263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949943443406681888814175 5924915165110022833221263)
    ·
      refine ⟨8887372747665034249831895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924915165110022833221263 8887372747665034249831895)
      ·
        refine ⟨13331059121497551374747843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8887372747665034249831895 13331059121497551374747843)
        ·
          refine ⟨19996588682246327062121765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331059121497551374747843 19996588682246327062121765)
          ·
            refine ⟨3749360377921186324147831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19996588682246327062121765 3749360377921186324147831)
            ·
              refine ⟨5624040566881779486221747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749360377921186324147831 5624040566881779486221747)
              ·
                refine ⟨8436060850322669229332621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624040566881779486221747 8436060850322669229332621)
                ·
                  refine ⟨3163522818871000960999733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8436060850322669229332621 3163522818871000960999733)
                  ·
                    refine ⟨296580264269156340093725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3163522818871000960999733 296580264269156340093725)
                    ·
                      rfl

theorem cell22_866382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_866382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866382 prefixEnd_866382 := by exact prefixLift 866382
  have htrace : WordTrace (prefixWord ++ tailWord_866382) baseStart_866382 baseEnd_866382 := by
    simpa [prefixWord, tailWord_866382, baseEnd_866382] using wordTrace_append hprefix tailTrace_866382
  have hstable : (prefixWord ++ tailWord_866382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866382).length < 2 ^ (prefixWord ++ tailWord_866382).sum := by decide
  have hdescent : baseEnd_866382 < baseStart_866382 := by decide
  rcases family_descends (prefixWord ++ tailWord_866382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866412 : List Nat := [2, 2, 1, 1, 3, 3, 3, 7]
def baseStart_866412 : Nat := 118140960795 + 866412 * 2 ^ 59
def prefixEnd_866412 : Nat := 4983230072969 + 3 ^ 40 * 866412 * 2
def baseEnd_866412 : Nat := 32954503764694029093737

theorem tailTrace_866412 : CollatzResearch.WordTrace tailWord_866412 prefixEnd_866412 32954503764694029093737 := by
  unfold tailWord_866412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800320868572385117052745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21067094491429846822736993 15800320868572385117052745)
  ·
    refine ⟨11850240651429288837789559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15800320868572385117052745 11850240651429288837789559)
    ·
      refine ⟨17775360977143933256684339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850240651429288837789559 17775360977143933256684339)
      ·
        refine ⟨26663041465715899885026509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17775360977143933256684339 26663041465715899885026509)
        ·
          refine ⟨9998640549643462456884941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26663041465715899885026509 9998640549643462456884941)
          ·
            refine ⟨3749490206116298421331853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9998640549643462456884941 3749490206116298421331853)
            ·
              refine ⟨1406058827293611907999445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3749490206116298421331853 1406058827293611907999445)
              ·
                refine ⟨32954503764694029093737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1406058827293611907999445 32954503764694029093737)
                ·
                  rfl

theorem cell22_866412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_866412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866412 prefixEnd_866412 := by exact prefixLift 866412
  have htrace : WordTrace (prefixWord ++ tailWord_866412) baseStart_866412 baseEnd_866412 := by
    simpa [prefixWord, tailWord_866412, baseEnd_866412] using wordTrace_append hprefix tailTrace_866412
  have hstable : (prefixWord ++ tailWord_866412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866412).length < 2 ^ (prefixWord ++ tailWord_866412).sum := by decide
  have hdescent : baseEnd_866412 < baseStart_866412 := by decide
  rcases family_descends (prefixWord ++ tailWord_866412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866429 : List Nat := [1, 4, 1, 1, 3, 3, 3, 6]
def baseStart_866429 : Nat := 118140960795 + 866429 * 2 ^ 59
def prefixEnd_866429 : Nat := 4983230072969 + 3 ^ 40 * 866429 * 2
def baseEnd_866429 : Nat := 32955150369962653796509

theorem tailTrace_866429 : CollatzResearch.WordTrace tailWord_866429 prefixEnd_866429 32955150369962653796509 := by
  unfold tailWord_866429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31601261778083182137474341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21067507852055454758316227 31601261778083182137474341)
  ·
    refine ⟨5925236583390596650776439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31601261778083182137474341 5925236583390596650776439)
    ·
      refine ⟨8887854875085894976164659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5925236583390596650776439 8887854875085894976164659)
      ·
        refine ⟨13331782312628842464246989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8887854875085894976164659 13331782312628842464246989)
        ·
          refine ⟨4999418367235815924092621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13331782312628842464246989 4999418367235815924092621)
          ·
            refine ⟨1874781887713430971534733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4999418367235815924092621 1874781887713430971534733)
            ·
              refine ⟨703043207892536614325525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874781887713430971534733 703043207892536614325525)
              ·
                refine ⟨32955150369962653796509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 703043207892536614325525 32955150369962653796509)
                ·
                  rfl

theorem cell22_866429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 6].length) (baseStart_866429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866429 prefixEnd_866429 := by exact prefixLift 866429
  have htrace : WordTrace (prefixWord ++ tailWord_866429) baseStart_866429 baseEnd_866429 := by
    simpa [prefixWord, tailWord_866429, baseEnd_866429] using wordTrace_append hprefix tailTrace_866429
  have hstable : (prefixWord ++ tailWord_866429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866429).length < 2 ^ (prefixWord ++ tailWord_866429).sum := by decide
  have hdescent : baseEnd_866429 < baseStart_866429 := by decide
  rcases family_descends (prefixWord ++ tailWord_866429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866461 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_866461 : Nat := 118140960795 + 866461 * 2 ^ 59
def prefixEnd_866461 : Nat := 4983230072969 + 3 ^ 40 * 866461 * 2
def baseEnd_866461 : Nat := 296607307583626467368483

theorem tailTrace_866461 : CollatzResearch.WordTrace tailWord_866461 prefixEnd_866461 296607307583626467368483 := by
  unfold tailWord_866461
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602428913967251602639237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21068285942644834401759491 31602428913967251602639237)
  ·
    refine ⟨5925455421368859675494857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31602428913967251602639237 5925455421368859675494857)
    ·
      refine ⟨4444091566026644756621143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5925455421368859675494857 4444091566026644756621143)
      ·
        refine ⟨6666137349039967134931715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444091566026644756621143 6666137349039967134931715)
        ·
          refine ⟨9999206023559950702397573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666137349039967134931715 9999206023559950702397573)
          ·
            refine ⟨1874851129417490756699545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9999206023559950702397573 1874851129417490756699545)
            ·
              refine ⟨1406138347063118067524659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874851129417490756699545 1406138347063118067524659)
              ·
                refine ⟨2109207520594677101286989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406138347063118067524659 2109207520594677101286989)
                ·
                  refine ⟨790952820223003912982621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2109207520594677101286989 790952820223003912982621)
                  ·
                    refine ⟨296607307583626467368483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790952820223003912982621 296607307583626467368483)
                    ·
                      rfl

theorem cell22_866461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_866461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866461 prefixEnd_866461 := by exact prefixLift 866461
  have htrace : WordTrace (prefixWord ++ tailWord_866461) baseStart_866461 baseEnd_866461 := by
    simpa [prefixWord, tailWord_866461, baseEnd_866461] using wordTrace_append hprefix tailTrace_866461
  have hstable : (prefixWord ++ tailWord_866461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866461).length < 2 ^ (prefixWord ++ tailWord_866461).sum := by decide
  have hdescent : baseEnd_866461 < baseStart_866461 := by decide
  rcases family_descends (prefixWord ++ tailWord_866461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866547 : List Nat := [1, 1, 1, 2, 2, 4, 1, 10]
def baseStart_866547 : Nat := 118140960795 + 866547 * 2 ^ 59
def prefixEnd_866547 : Nat := 4983230072969 + 3 ^ 40 * 866547 * 2
def baseEnd_866547 : Nat := 32959638571238989968691

theorem tailTrace_866547 : CollatzResearch.WordTrace tailWord_866547 prefixEnd_866547 32959638571238989968691 := by
  unfold tailWord_866547
  simp only [CollatzResearch.WordTrace]
  refine ⟨31605565591655688290269895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21070377061103792193513263 31605565591655688290269895)
  ·
    refine ⟨47408348387483532435404843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31605565591655688290269895 47408348387483532435404843)
    ·
      refine ⟨71112522581225298653107265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47408348387483532435404843 71112522581225298653107265)
      ·
        refine ⟨53334391935918973989830449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71112522581225298653107265 53334391935918973989830449)
        ·
          refine ⟨40000793951939230492372837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53334391935918973989830449 40000793951939230492372837)
          ·
            refine ⟨7500148865988605717319907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40000793951939230492372837 7500148865988605717319907)
            ·
              refine ⟨11250223298982908575979861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500148865988605717319907 11250223298982908575979861)
              ·
                refine ⟨32959638571238989968691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11250223298982908575979861 32959638571238989968691)
                ·
                  rfl

theorem cell22_866547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_866547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866547 prefixEnd_866547 := by exact prefixLift 866547
  have htrace : WordTrace (prefixWord ++ tailWord_866547) baseStart_866547 baseEnd_866547 := by
    simpa [prefixWord, tailWord_866547, baseEnd_866547] using wordTrace_append hprefix tailTrace_866547
  have hstable : (prefixWord ++ tailWord_866547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866547).length < 2 ^ (prefixWord ++ tailWord_866547).sum := by decide
  have hdescent : baseEnd_866547 < baseStart_866547 := by decide
  rcases family_descends (prefixWord ++ tailWord_866547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866564 : List Nat := [2, 3, 2, 2, 3, 10]
def baseStart_866564 : Nat := 118140960795 + 866564 * 2 ^ 59
def prefixEnd_866564 : Nat := 4983230072969 + 3 ^ 40 * 866564 * 2
def baseEnd_866564 : Nat := 3662253908500846074607

theorem tailTrace_866564 : CollatzResearch.WordTrace tailWord_866564 prefixEnd_866564 3662253908500846074607 := by
  unfold tailWord_866564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803092816297050096819373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21070790421729400129092497 15803092816297050096819373)
  ·
    refine ⟨5926159806111393786307265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15803092816297050096819373 5926159806111393786307265)
    ·
      refine ⟨4444619854583545339730449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5926159806111393786307265 4444619854583545339730449)
      ·
        refine ⟨3333464890937659004797837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444619854583545339730449 3333464890937659004797837)
        ·
          refine ⟨1250049334101622126799189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3333464890937659004797837 1250049334101622126799189)
          ·
            refine ⟨3662253908500846074607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1250049334101622126799189 3662253908500846074607)
            ·
              rfl

theorem cell22_866564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 10].length) (baseStart_866564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866564 prefixEnd_866564 := by exact prefixLift 866564
  have htrace : WordTrace (prefixWord ++ tailWord_866564) baseStart_866564 baseEnd_866564 := by
    simpa [prefixWord, tailWord_866564, baseEnd_866564] using wordTrace_append hprefix tailTrace_866564
  have hstable : (prefixWord ++ tailWord_866564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866564).length < 2 ^ (prefixWord ++ tailWord_866564).sum := by decide
  have hdescent : baseEnd_866564 < baseStart_866564 := by decide
  rcases family_descends (prefixWord ++ tailWord_866564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866568 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_866568 : Nat := 118140960795 + 866568 * 2 ^ 59
def prefixEnd_866568 : Nat := 4983230072969 + 3 ^ 40 * 866568 * 2
def baseEnd_866568 : Nat := 296643935870313854943155

theorem tailTrace_866568 : CollatzResearch.WordTrace tailWord_866568 prefixEnd_866568 296643935870313854943155 := by
  unfold tailWord_866568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803165762289804438392179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21070887683053072584522905 15803165762289804438392179)
  ·
    refine ⟨23704748643434706657588269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15803165762289804438392179 23704748643434706657588269)
    ·
      refine ⟨8889280741288014996595601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23704748643434706657588269 8889280741288014996595601)
      ·
        refine ⟨6666960555966011247446701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889280741288014996595601 6666960555966011247446701)
        ·
          refine ⟨2500110208487254217792513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6666960555966011247446701 2500110208487254217792513)
          ·
            refine ⟨1875082656365440663344385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500110208487254217792513 1875082656365440663344385)
            ·
              refine ⟨1406311992274080497508289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875082656365440663344385 1406311992274080497508289)
              ·
                refine ⟨1054733994205560373131217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406311992274080497508289 1054733994205560373131217)
                ·
                  refine ⟨791050495654170279848413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054733994205560373131217 791050495654170279848413)
                  ·
                    refine ⟨296643935870313854943155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791050495654170279848413 296643935870313854943155)
                    ·
                      rfl

theorem cell22_866568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_866568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866568 prefixEnd_866568 := by exact prefixLift 866568
  have htrace : WordTrace (prefixWord ++ tailWord_866568) baseStart_866568 baseEnd_866568 := by
    simpa [prefixWord, tailWord_866568, baseEnd_866568] using wordTrace_append hprefix tailTrace_866568
  have hstable : (prefixWord ++ tailWord_866568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866568).length < 2 ^ (prefixWord ++ tailWord_866568).sum := by decide
  have hdescent : baseEnd_866568 < baseStart_866568 := by decide
  rcases family_descends (prefixWord ++ tailWord_866568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866579 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 7, 3]
def baseStart_866579 : Nat := 118140960795 + 866579 * 2 ^ 59
def prefixEnd_866579 : Nat := 4983230072969 + 3 ^ 40 * 866579 * 2
def baseEnd_866579 : Nat := 296647701395113492918121

theorem tailTrace_866579 : CollatzResearch.WordTrace tailWord_866579 prefixEnd_866579 296647701395113492918121 := by
  unfold tailWord_866579
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606732727539757755434791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21071155151693171836956527 31606732727539757755434791)
  ·
    refine ⟨47410099091309636633152187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31606732727539757755434791 47410099091309636633152187)
    ·
      refine ⟨71115148636964454949728281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47410099091309636633152187 71115148636964454949728281)
      ·
        refine ⟨53336361477723341212296211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71115148636964454949728281 53336361477723341212296211)
        ·
          refine ⟨80004542216585011818444317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53336361477723341212296211 80004542216585011818444317)
          ·
            refine ⟨30001703331219379431916619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80004542216585011818444317 30001703331219379431916619)
            ·
              refine ⟨45002554996829069147874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30001703331219379431916619 45002554996829069147874929)
              ·
                refine ⟨33751916247621801860906197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45002554996829069147874929 33751916247621801860906197)
                ·
                  refine ⟨791060537053635981114989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 33751916247621801860906197 791060537053635981114989)
                  ·
                    refine ⟨296647701395113492918121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791060537053635981114989 296647701395113492918121)
                    ·
                      rfl

theorem cell22_866579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].length) (baseStart_866579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866579 prefixEnd_866579 := by exact prefixLift 866579
  have htrace : WordTrace (prefixWord ++ tailWord_866579) baseStart_866579 baseEnd_866579 := by
    simpa [prefixWord, tailWord_866579, baseEnd_866579] using wordTrace_append hprefix tailTrace_866579
  have hstable : (prefixWord ++ tailWord_866579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866579).length < 2 ^ (prefixWord ++ tailWord_866579).sum := by decide
  have hdescent : baseEnd_866579 < baseStart_866579 := by decide
  rcases family_descends (prefixWord ++ tailWord_866579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866596 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_866596 : Nat := 118140960795 + 866596 * 2 ^ 59
def prefixEnd_866596 : Nat := 4983230072969 + 3 ^ 40 * 866596 * 2
def baseEnd_866596 : Nat := 296653520842531115243069

theorem tailTrace_866596 : CollatzResearch.WordTrace tailWord_866596 prefixEnd_866596 296653520842531115243069 := by
  unfold tailWord_866596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803676384239084829401821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21071568512318779772535761 15803676384239084829401821)
  ·
    refine ⟨5926378644089656811025683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15803676384239084829401821 5926378644089656811025683)
    ·
      refine ⟨8889567966134485216538525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926378644089656811025683 8889567966134485216538525)
      ·
        refine ⟨3333587987300431956201947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8889567966134485216538525 3333587987300431956201947)
        ·
          refine ⟨5000381980950647934302921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333587987300431956201947 5000381980950647934302921)
          ·
            refine ⟨3750286485712985950727191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000381980950647934302921 3750286485712985950727191)
            ·
              refine ⟨5625429728569478926090787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750286485712985950727191 5625429728569478926090787)
              ·
                refine ⟨8438144592854218389136181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625429728569478926090787 8438144592854218389136181)
                ·
                  refine ⟨791076055580082973981517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8438144592854218389136181 791076055580082973981517)
                  ·
                    refine ⟨296653520842531115243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791076055580082973981517 296653520842531115243069)
                    ·
                      rfl

theorem cell22_866596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_866596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866596 prefixEnd_866596 := by exact prefixLift 866596
  have htrace : WordTrace (prefixWord ++ tailWord_866596) baseStart_866596 baseEnd_866596 := by
    simpa [prefixWord, tailWord_866596, baseEnd_866596] using wordTrace_append hprefix tailTrace_866596
  have hstable : (prefixWord ++ tailWord_866596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866596).length < 2 ^ (prefixWord ++ tailWord_866596).sum := by decide
  have hdescent : baseEnd_866596 < baseStart_866596 := by decide
  rcases family_descends (prefixWord ++ tailWord_866596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866600 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_866600 : Nat := 118140960795 + 866600 * 2 ^ 59
def prefixEnd_866600 : Nat := 4983230072969 + 3 ^ 40 * 866600 * 2
def baseEnd_866600 : Nat := 296654890124276438143057

theorem tailTrace_866600 : CollatzResearch.WordTrace tailWord_866600 prefixEnd_866600 296654890124276438143057 := by
  unfold tailWord_866600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803749330231839170974627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21071665773642452227966169 15803749330231839170974627)
  ·
    refine ⟨23705623995347758756461941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15803749330231839170974627 23705623995347758756461941)
    ·
      refine ⟨2222402249563852383418307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23705623995347758756461941 2222402249563852383418307)
      ·
        refine ⟨3333603374345778575127461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222402249563852383418307 3333603374345778575127461)
        ·
          refine ⟨625050632689833482836399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3333603374345778575127461 625050632689833482836399)
          ·
            refine ⟨937575949034750224254599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625050632689833482836399 937575949034750224254599)
            ·
              refine ⟨1406363923552125336381899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937575949034750224254599 1406363923552125336381899)
              ·
                refine ⟨2109545885328188004572849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406363923552125336381899 2109545885328188004572849)
                ·
                  refine ⟨1582159413996141003429637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2109545885328188004572849 1582159413996141003429637)
                  ·
                    refine ⟨296654890124276438143057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1582159413996141003429637 296654890124276438143057)
                    ·
                      rfl

theorem cell22_866600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_866600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866600 prefixEnd_866600 := by exact prefixLift 866600
  have htrace : WordTrace (prefixWord ++ tailWord_866600) baseStart_866600 baseEnd_866600 := by
    simpa [prefixWord, tailWord_866600, baseEnd_866600] using wordTrace_append hprefix tailTrace_866600
  have hstable : (prefixWord ++ tailWord_866600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866600).length < 2 ^ (prefixWord ++ tailWord_866600).sum := by decide
  have hdescent : baseEnd_866600 < baseStart_866600 := by decide
  rcases family_descends (prefixWord ++ tailWord_866600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866639 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_866639 : Nat := 118140960795 + 866639 * 2 ^ 59
def prefixEnd_866639 : Nat := 4983230072969 + 3 ^ 40 * 866639 * 2
def baseEnd_866639 : Nat := 296668240621293336417937

theorem tailTrace_866639 : CollatzResearch.WordTrace tailWord_866639 prefixEnd_866639 296668240621293336417937 := by
  unfold tailWord_866639
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608921107322388002618971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21072614071548258668412647 31608921107322388002618971)
  ·
    refine ⟨47413381660983582003928457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31608921107322388002618971 47413381660983582003928457)
    ·
      refine ⟨35560036245737686502946343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47413381660983582003928457 35560036245737686502946343)
      ·
        refine ⟨53340054368606529754419515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35560036245737686502946343 53340054368606529754419515)
        ·
          refine ⟨80010081552909794631629273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53340054368606529754419515 80010081552909794631629273)
          ·
            refine ⟨60007561164682345973721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80010081552909794631629273 60007561164682345973721955)
            ·
              refine ⟨90011341747023518960582933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60007561164682345973721955 90011341747023518960582933)
              ·
                refine ⟨4219281644391727451277325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90011341747023518960582933 4219281644391727451277325)
                ·
                  refine ⟨1582230616646897794228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4219281644391727451277325 1582230616646897794228997)
                  ·
                    refine ⟨296668240621293336417937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1582230616646897794228997 296668240621293336417937)
                    ·
                      rfl

theorem cell22_866639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_866639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866639 prefixEnd_866639 := by exact prefixLift 866639
  have htrace : WordTrace (prefixWord ++ tailWord_866639) baseStart_866639 baseEnd_866639 := by
    simpa [prefixWord, tailWord_866639, baseEnd_866639] using wordTrace_append hprefix tailTrace_866639
  have hstable : (prefixWord ++ tailWord_866639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866639).length < 2 ^ (prefixWord ++ tailWord_866639).sum := by decide
  have hdescent : baseEnd_866639 < baseStart_866639 := by decide
  rcases family_descends (prefixWord ++ tailWord_866639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866671 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 4]
def baseStart_866671 : Nat := 118140960795 + 866671 * 2 ^ 59
def prefixEnd_866671 : Nat := 4983230072969 + 3 ^ 40 * 866671 * 2
def baseEnd_866671 : Nat := 98893064958418639872613

theorem tailTrace_866671 : CollatzResearch.WordTrace tailWord_866671 prefixEnd_866671 98893064958418639872613 := by
  unfold tailWord_866671
  simp only [CollatzResearch.WordTrace]
  refine ⟨31610088243206457467783867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21073392162137638311855911 31610088243206457467783867)
  ·
    refine ⟨47415132364809686201675801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31610088243206457467783867 47415132364809686201675801)
    ·
      refine ⟨35561349273607264651256851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47415132364809686201675801 35561349273607264651256851)
      ·
        refine ⟨53342023910410896976885277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35561349273607264651256851 53342023910410896976885277)
        ·
          refine ⟨20003258966404086366331979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53342023910410896976885277 20003258966404086366331979)
          ·
            refine ⟨30004888449606129549497969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20003258966404086366331979 30004888449606129549497969)
            ·
              refine ⟨22503666337204597162123477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30004888449606129549497969 22503666337204597162123477)
              ·
                refine ⟨527429679778232745987269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22503666337204597162123477 527429679778232745987269)
                ·
                  refine ⟨98893064958418639872613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527429679778232745987269 98893064958418639872613)
                  ·
                    rfl

theorem cell22_866671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 4].length) (baseStart_866671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866671 prefixEnd_866671 := by exact prefixLift 866671
  have htrace : WordTrace (prefixWord ++ tailWord_866671) baseStart_866671 baseEnd_866671 := by
    simpa [prefixWord, tailWord_866671, baseEnd_866671] using wordTrace_append hprefix tailTrace_866671
  have hstable : (prefixWord ++ tailWord_866671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866671).length < 2 ^ (prefixWord ++ tailWord_866671).sum := by decide
  have hdescent : baseEnd_866671 < baseStart_866671 := by decide
  rcases family_descends (prefixWord ++ tailWord_866671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866684 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_866684 : Nat := 118140960795 + 866684 * 2 ^ 59
def prefixEnd_866684 : Nat := 4983230072969 + 3 ^ 40 * 866684 * 2
def baseEnd_866684 : Nat := 296683645040928219042799

theorem tailTrace_866684 : CollatzResearch.WordTrace tailWord_866684 prefixEnd_866684 296683645040928219042799 := by
  unfold tailWord_866684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805281196079680344003553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21073708261439573792004737 15805281196079680344003553)
  ·
    refine ⟨11853960897059760258002665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805281196079680344003553 11853960897059760258002665)
    ·
      refine ⟨8890470672794820193501999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11853960897059760258002665 8890470672794820193501999)
      ·
        refine ⟨13335706009192230290252999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890470672794820193501999 13335706009192230290252999)
        ·
          refine ⟨20003559013788345435379499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335706009192230290252999 20003559013788345435379499)
          ·
            refine ⟨30005338520682518153069249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20003559013788345435379499 30005338520682518153069249)
            ·
              refine ⟨22504003890511888614801937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30005338520682518153069249 22504003890511888614801937)
              ·
                refine ⟨16878002917883916461101453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22504003890511888614801937 16878002917883916461101453)
                ·
                  refine ⟨6329251094206468672913045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16878002917883916461101453 6329251094206468672913045)
                  ·
                    refine ⟨296683645040928219042799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6329251094206468672913045 296683645040928219042799)
                    ·
                      rfl

theorem cell22_866684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_866684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866684 prefixEnd_866684 := by exact prefixLift 866684
  have htrace : WordTrace (prefixWord ++ tailWord_866684) baseStart_866684 baseEnd_866684 := by
    simpa [prefixWord, tailWord_866684, baseEnd_866684] using wordTrace_append hprefix tailTrace_866684
  have hstable : (prefixWord ++ tailWord_866684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866684).length < 2 ^ (prefixWord ++ tailWord_866684).sum := by decide
  have hdescent : baseEnd_866684 < baseStart_866684 := by decide
  rcases family_descends (prefixWord ++ tailWord_866684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866699 : List Nat := [1, 1, 1, 1, 4, 4, 1, 9]
def baseStart_866699 : Nat := 118140960795 + 866699 * 2 ^ 59
def prefixEnd_866699 : Nat := 4983230072969 + 3 ^ 40 * 866699 * 2
def baseEnd_866699 : Nat := 32965419983052575546417

theorem tailTrace_866699 : CollatzResearch.WordTrace tailWord_866699 prefixEnd_866699 32965419983052575546417 := by
  unfold tailWord_866699
  simp only [CollatzResearch.WordTrace]
  refine ⟨31611109487105018249803151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074072991403345499868767 31611109487105018249803151)
  ·
    refine ⟨47416664230657527374704727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31611109487105018249803151 47416664230657527374704727)
    ·
      refine ⟨71124996345986291062057091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47416664230657527374704727 71124996345986291062057091)
      ·
        refine ⟨106687494518979436593085637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71124996345986291062057091 106687494518979436593085637)
        ·
          refine ⟨20003905222308644361203557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106687494518979436593085637 20003905222308644361203557)
          ·
            refine ⟨3750732229182870817725667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20003905222308644361203557 3750732229182870817725667)
            ·
              refine ⟨5626098343774306226588501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750732229182870817725667 5626098343774306226588501)
              ·
                refine ⟨32965419983052575546417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5626098343774306226588501 32965419983052575546417)
                ·
                  rfl

theorem cell22_866699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_866699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866699 prefixEnd_866699 := by exact prefixLift 866699
  have htrace : WordTrace (prefixWord ++ tailWord_866699) baseStart_866699 baseEnd_866699 := by
    simpa [prefixWord, tailWord_866699, baseEnd_866699] using wordTrace_append hprefix tailTrace_866699
  have hstable : (prefixWord ++ tailWord_866699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866699).length < 2 ^ (prefixWord ++ tailWord_866699).sum := by decide
  have hdescent : baseEnd_866699 < baseStart_866699 := by decide
  rcases family_descends (prefixWord ++ tailWord_866699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866729 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_866729 : Nat := 118140960795 + 866729 * 2 ^ 59
def prefixEnd_866729 : Nat := 4983230072969 + 3 ^ 40 * 866729 * 2
def baseEnd_866729 : Nat := 296699049460563101667661

theorem tailTrace_866729 : CollatzResearch.WordTrace tailWord_866729 prefixEnd_866729 296699049460563101667661 := by
  unfold tailWord_866729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612203676996333373395241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074802451330888915596827 31612203676996333373395241)
  ·
    refine ⟨23709152757747250030046431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31612203676996333373395241 23709152757747250030046431)
    ·
      refine ⟨35563729136620875045069647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23709152757747250030046431 35563729136620875045069647)
      ·
        refine ⟨53345593704931312567604471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35563729136620875045069647 53345593704931312567604471)
        ·
          refine ⟨80018390557396968851406707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53345593704931312567604471 80018390557396968851406707)
          ·
            refine ⟨120027585836095453277110061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80018390557396968851406707 120027585836095453277110061)
            ·
              refine ⟨45010344688535794978916273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120027585836095453277110061 45010344688535794978916273)
              ·
                refine ⟨33757758516401846234187205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45010344688535794978916273 33757758516401846234187205)
                ·
                  refine ⟨6329579721825346168910101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33757758516401846234187205 6329579721825346168910101)
                  ·
                    refine ⟨296699049460563101667661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6329579721825346168910101 296699049460563101667661)
                    ·
                      rfl

theorem cell22_866729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_866729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866729 prefixEnd_866729 := by exact prefixLift 866729
  have htrace : WordTrace (prefixWord ++ tailWord_866729) baseStart_866729 baseEnd_866729 := by
    simpa [prefixWord, tailWord_866729, baseEnd_866729] using wordTrace_append hprefix tailTrace_866729
  have hstable : (prefixWord ++ tailWord_866729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866729).length < 2 ^ (prefixWord ++ tailWord_866729).sum := by decide
  have hdescent : baseEnd_866729 < baseStart_866729 := by decide
  rcases family_descends (prefixWord ++ tailWord_866729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866733 : List Nat := [1, 5, 2, 2, 3, 9]
def baseStart_866733 : Nat := 118140960795 + 866733 * 2 ^ 59
def prefixEnd_866733 : Nat := 4983230072969 + 3 ^ 40 * 866733 * 2
def baseEnd_866733 : Nat := 3662968132621091661329

theorem tailTrace_866733 : CollatzResearch.WordTrace tailWord_866733 prefixEnd_866733 3662968132621091661329 := by
  unfold tailWord_866733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612349568981842056540853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074899712654561371027235 31612349568981842056540853)
  ·
    refine ⟨2963657772092047692800705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31612349568981842056540853 2963657772092047692800705)
    ·
      refine ⟨2222743329069035769600529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2963657772092047692800705 2222743329069035769600529)
      ·
        refine ⟨1667057496801776827200397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222743329069035769600529 1667057496801776827200397)
        ·
          refine ⟨625146561300666310200149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1667057496801776827200397 625146561300666310200149)
          ·
            refine ⟨3662968132621091661329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 625146561300666310200149 3662968132621091661329)
            ·
              rfl

theorem cell22_866733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 9].length) (baseStart_866733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866733 prefixEnd_866733 := by exact prefixLift 866733
  have htrace : WordTrace (prefixWord ++ tailWord_866733) baseStart_866733 baseEnd_866733 := by
    simpa [prefixWord, tailWord_866733, baseEnd_866733] using wordTrace_append hprefix tailTrace_866733
  have hstable : (prefixWord ++ tailWord_866733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866733).length < 2 ^ (prefixWord ++ tailWord_866733).sum := by decide
  have hdescent : baseEnd_866733 < baseStart_866733 := by decide
  rcases family_descends (prefixWord ++ tailWord_866733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866761 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 5]
def baseStart_866761 : Nat := 118140960795 + 866761 * 2 ^ 59
def prefixEnd_866761 : Nat := 4983230072969 + 3 ^ 40 * 866761 * 2
def baseEnd_866761 : Nat := 98903334571508561622521

theorem tailTrace_866761 : CollatzResearch.WordTrace tailWord_866761 prefixEnd_866761 98903334571508561622521 := by
  unfold tailWord_866761
  simp only [CollatzResearch.WordTrace]
  refine ⟨31613370812880402838560137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075580541920268559040091 31613370812880402838560137)
  ·
    refine ⟨23710028109660302128920103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31613370812880402838560137 23710028109660302128920103)
    ·
      refine ⟨35565042164490453193380155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23710028109660302128920103 35565042164490453193380155)
      ·
        refine ⟨53347563246735679790070233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35565042164490453193380155 53347563246735679790070233)
        ·
          refine ⟨40010672435051759842552675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53347563246735679790070233 40010672435051759842552675)
          ·
            refine ⟨60016008652577639763829013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40010672435051759842552675 60016008652577639763829013)
            ·
              refine ⟨2813250405589576863929485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60016008652577639763829013 2813250405589576863929485)
              ·
                refine ⟨1054968902096091323973557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2813250405589576863929485 1054968902096091323973557)
                ·
                  refine ⟨98903334571508561622521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1054968902096091323973557 98903334571508561622521)
                  ·
                    rfl

theorem cell22_866761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_866761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866761 prefixEnd_866761 := by exact prefixLift 866761
  have htrace : WordTrace (prefixWord ++ tailWord_866761) baseStart_866761 baseEnd_866761 := by
    simpa [prefixWord, tailWord_866761, baseEnd_866761] using wordTrace_append hprefix tailTrace_866761
  have hstable : (prefixWord ++ tailWord_866761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866761).length < 2 ^ (prefixWord ++ tailWord_866761).sum := by decide
  have hdescent : baseEnd_866761 < baseStart_866761 := by decide
  rcases family_descends (prefixWord ++ tailWord_866761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866840 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_866840 : Nat := 118140960795 + 866840 * 2 ^ 59
def prefixEnd_866840 : Nat := 4983230072969 + 3 ^ 40 * 866840 * 2
def baseEnd_866840 : Nat := 98912349009665270714107

theorem tailTrace_866840 : CollatzResearch.WordTrace tailWord_866840 prefixEnd_866840 98912349009665270714107 := by
  unfold tailWord_866840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808126089797099665342987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21077501453062799553790649 15808126089797099665342987)
  ·
    refine ⟨23712189134695649498014481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15808126089797099665342987 23712189134695649498014481)
    ·
      refine ⟨17784141851021737123510861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23712189134695649498014481 17784141851021737123510861)
      ·
        refine ⟨6669053194133151421316573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17784141851021737123510861 6669053194133151421316573)
        ·
          refine ⟨2500894947799931782993715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6669053194133151421316573 2500894947799931782993715)
          ·
            refine ⟨3751342421699897674490573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500894947799931782993715 3751342421699897674490573)
            ·
              refine ⟨1406753408137461627933965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751342421699897674490573 1406753408137461627933965)
              ·
                refine ⟨527532528051548110475237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406753408137461627933965 527532528051548110475237)
                ·
                  refine ⟨98912349009665270714107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527532528051548110475237 98912349009665270714107)
                  ·
                    rfl

theorem cell22_866840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_866840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866840 prefixEnd_866840 := by exact prefixLift 866840
  have htrace : WordTrace (prefixWord ++ tailWord_866840) baseStart_866840 baseEnd_866840 := by
    simpa [prefixWord, tailWord_866840, baseEnd_866840] using wordTrace_append hprefix tailTrace_866840
  have hstable : (prefixWord ++ tailWord_866840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866840).length < 2 ^ (prefixWord ++ tailWord_866840).sum := by decide
  have hdescent : baseEnd_866840 < baseStart_866840 := by decide
  rcases family_descends (prefixWord ++ tailWord_866840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866851 : List Nat := [1, 1, 1, 4, 4, 1, 10]
def baseStart_866851 : Nat := 118140960795 + 866851 * 2 ^ 59
def prefixEnd_866851 : Nat := 4983230072969 + 3 ^ 40 * 866851 * 2
def baseEnd_866851 : Nat := 10990400464955387041381

theorem tailTrace_866851 : CollatzResearch.WordTrace tailWord_866851 prefixEnd_866851 10990400464955387041381 := by
  unfold tailWord_866851
  simp only [CollatzResearch.WordTrace]
  refine ⟨31616653382554348209336407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21077768921702898806224271 31616653382554348209336407)
  ·
    refine ⟨47424980073831522314004611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31616653382554348209336407 47424980073831522314004611)
    ·
      refine ⟨71137470110747283471006917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47424980073831522314004611 71137470110747283471006917)
      ·
        refine ⟨13338275645765115650813797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71137470110747283471006917 13338275645765115650813797)
        ·
          refine ⟨2500926683580959184527587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13338275645765115650813797 2500926683580959184527587)
          ·
            refine ⟨3751390025371438776791381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500926683580959184527587 3751390025371438776791381)
            ·
              refine ⟨10990400464955387041381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3751390025371438776791381 10990400464955387041381)
              ·
                rfl

theorem cell22_866851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 10].length) (baseStart_866851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866851 prefixEnd_866851 := by exact prefixLift 866851
  have htrace : WordTrace (prefixWord ++ tailWord_866851) baseStart_866851 baseEnd_866851 := by
    simpa [prefixWord, tailWord_866851, baseEnd_866851] using wordTrace_append hprefix tailTrace_866851
  have hstable : (prefixWord ++ tailWord_866851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866851).length < 2 ^ (prefixWord ++ tailWord_866851).sum := by decide
  have hdescent : baseEnd_866851 < baseStart_866851 := by decide
  rcases family_descends (prefixWord ++ tailWord_866851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866883 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 3, 3]
def baseStart_866883 : Nat := 118140960795 + 866883 * 2 ^ 59
def prefixEnd_866883 : Nat := 4983230072969 + 3 ^ 40 * 866883 * 2
def baseEnd_866883 : Nat := 296751766807758033317189

theorem tailTrace_866883 : CollatzResearch.WordTrace tailWord_866883 prefixEnd_866883 296751766807758033317189 := by
  unfold tailWord_866883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31617820518438417674501303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21078547012292278449667535 31617820518438417674501303)
  ·
    refine ⟨47426730777657626511751955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31617820518438417674501303 47426730777657626511751955)
    ·
      refine ⟨71140096166486439767627933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47426730777657626511751955 71140096166486439767627933)
      ·
        refine ⟨26677536062432414912860475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71140096166486439767627933 26677536062432414912860475)
        ·
          refine ⟨40016304093648622369290713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26677536062432414912860475 40016304093648622369290713)
          ·
            refine ⟨30012228070236466776968035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40016304093648622369290713 30012228070236466776968035)
            ·
              refine ⟨45018342105354700165452053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30012228070236466776968035 45018342105354700165452053)
              ·
                refine ⟨2110234786188501570255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45018342105354700165452053 2110234786188501570255565)
                ·
                  refine ⟨791338044820688088845837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2110234786188501570255565 791338044820688088845837)
                  ·
                    refine ⟨296751766807758033317189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791338044820688088845837 296751766807758033317189)
                    ·
                      rfl

theorem cell22_866883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].length) (baseStart_866883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866883 prefixEnd_866883 := by exact prefixLift 866883
  have htrace : WordTrace (prefixWord ++ tailWord_866883) baseStart_866883 baseEnd_866883 := by
    simpa [prefixWord, tailWord_866883, baseEnd_866883] using wordTrace_append hprefix tailTrace_866883
  have hstable : (prefixWord ++ tailWord_866883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866883).length < 2 ^ (prefixWord ++ tailWord_866883).sum := by decide
  have hdescent : baseEnd_866883 < baseStart_866883 := by decide
  rcases family_descends (prefixWord ++ tailWord_866883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866896 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_866896 : Nat := 118140960795 + 866896 * 2 ^ 59
def prefixEnd_866896 : Nat := 4983230072969 + 3 ^ 40 * 866896 * 2
def baseEnd_866896 : Nat := 98918738991143444247383

theorem tailTrace_866896 : CollatzResearch.WordTrace tailWord_866896 prefixEnd_866896 98918738991143444247383 := by
  unfold tailWord_866896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809147333695660447362271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21078863111594213929816361 15809147333695660447362271)
  ·
    refine ⟨23713721000543490671043407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15809147333695660447362271 23713721000543490671043407)
    ·
      refine ⟨35570581500815236006565111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23713721000543490671043407 35570581500815236006565111)
      ·
        refine ⟨53355872251222854009847667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35570581500815236006565111 53355872251222854009847667)
        ·
          refine ⟨80033808376834281014771501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53355872251222854009847667 80033808376834281014771501)
          ·
            refine ⟨30012678141312855380539313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80033808376834281014771501 30012678141312855380539313)
            ·
              refine ⟨22509508605984641535404485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30012678141312855380539313 22509508605984641535404485)
              ·
                refine ⟨4220532863622120287888341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22509508605984641535404485 4220532863622120287888341)
                ·
                  refine ⟨98918738991143444247383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4220532863622120287888341 98918738991143444247383)
                  ·
                    rfl

theorem cell22_866896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_866896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866896 prefixEnd_866896 := by exact prefixLift 866896
  have htrace : WordTrace (prefixWord ++ tailWord_866896) baseStart_866896 baseEnd_866896 := by
    simpa [prefixWord, tailWord_866896, baseEnd_866896] using wordTrace_append hprefix tailTrace_866896
  have hstable : (prefixWord ++ tailWord_866896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866896).length < 2 ^ (prefixWord ++ tailWord_866896).sum := by decide
  have hdescent : baseEnd_866896 < baseStart_866896 := by decide
  rcases family_descends (prefixWord ++ tailWord_866896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866911 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_866911 : Nat := 118140960795 + 866911 * 2 ^ 59
def prefixEnd_866911 : Nat := 4983230072969 + 3 ^ 40 * 866911 * 2
def baseEnd_866911 : Nat := 296761351779975293617103

theorem tailTrace_866911 : CollatzResearch.WordTrace tailWord_866911 prefixEnd_866911 296761351779975293617103 := by
  unfold tailWord_866911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31618841762336978456520587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21079227841557985637680391 31618841762336978456520587)
  ·
    refine ⟨47428262643505467684780881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31618841762336978456520587 47428262643505467684780881)
    ·
      refine ⟨35571196982629100763585661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47428262643505467684780881 35571196982629100763585661)
      ·
        refine ⟨13339198868485912786344623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35571196982629100763585661 13339198868485912786344623)
        ·
          refine ⟨20008798302728869179516935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339198868485912786344623 20008798302728869179516935)
          ·
            refine ⟨30013197454093303769275403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20008798302728869179516935 30013197454093303769275403)
            ·
              refine ⟨45019796181139955653913105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30013197454093303769275403 45019796181139955653913105)
              ·
                refine ⟨33764847135854966740434829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45019796181139955653913105 33764847135854966740434829)
                ·
                  refine ⟨12661817675945612527663061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33764847135854966740434829 12661817675945612527663061)
                  ·
                    refine ⟨296761351779975293617103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12661817675945612527663061 296761351779975293617103)
                    ·
                      rfl

theorem cell22_866911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_866911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866911 prefixEnd_866911 := by exact prefixLift 866911
  have htrace : WordTrace (prefixWord ++ tailWord_866911) baseStart_866911 baseEnd_866911 := by
    simpa [prefixWord, tailWord_866911, baseEnd_866911] using wordTrace_append hprefix tailTrace_866911
  have hstable : (prefixWord ++ tailWord_866911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866911).length < 2 ^ (prefixWord ++ tailWord_866911).sum := by decide
  have hdescent : baseEnd_866911 < baseStart_866911 := by decide
  rcases family_descends (prefixWord ++ tailWord_866911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866913 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 5]
def baseStart_866913 : Nat := 118140960795 + 866913 * 2 ^ 59
def prefixEnd_866913 : Nat := 4983230072969 + 3 ^ 40 * 866913 * 2
def baseEnd_866913 : Nat := 98920678806949318355699

theorem tailTrace_866913 : CollatzResearch.WordTrace tailWord_866913 prefixEnd_866913 98920678806949318355699 := by
  unfold tailWord_866913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31618914708329732798093393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21079276472219821865395595 31618914708329732798093393)
  ·
    refine ⟨23714186031247299598570045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31618914708329732798093393 23714186031247299598570045)
    ·
      refine ⟨8892819761717737349463767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23714186031247299598570045 8892819761717737349463767)
      ·
        refine ⟨13339229642576606024195651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8892819761717737349463767 13339229642576606024195651)
        ·
          refine ⟨20008844463864909036293477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339229642576606024195651 20008844463864909036293477)
          ·
            refine ⟨3751658336974670444305027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20008844463864909036293477 3751658336974670444305027)
            ·
              refine ⟨5627487505462005666457541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751658336974670444305027 5627487505462005666457541)
              ·
                refine ⟨1055153907274126062460789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5627487505462005666457541 1055153907274126062460789)
                ·
                  refine ⟨98920678806949318355699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1055153907274126062460789 98920678806949318355699)
                  ·
                    rfl

theorem cell22_866913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_866913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866913 prefixEnd_866913 := by exact prefixLift 866913
  have htrace : WordTrace (prefixWord ++ tailWord_866913) baseStart_866913 baseEnd_866913 := by
    simpa [prefixWord, tailWord_866913, baseEnd_866913] using wordTrace_append hprefix tailTrace_866913
  have hstable : (prefixWord ++ tailWord_866913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866913).length < 2 ^ (prefixWord ++ tailWord_866913).sum := by decide
  have hdescent : baseEnd_866913 < baseStart_866913 := by decide
  rcases family_descends (prefixWord ++ tailWord_866913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866958 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_866958 : Nat := 118140960795 + 866958 * 2 ^ 59
def prefixEnd_866958 : Nat := 4983230072969 + 3 ^ 40 * 866958 * 2
def baseEnd_866958 : Nat := 98925813613494279230653

theorem tailTrace_866958 : CollatzResearch.WordTrace tailWord_866958 prefixEnd_866958 98925813613494279230653 := by
  unfold tailWord_866958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952569499145838185435191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21080370662111136988987685 3952569499145838185435191)
  ·
    refine ⟨5928854248718757278152787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3952569499145838185435191 5928854248718757278152787)
    ·
      refine ⟨8893281373078135917229181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928854248718757278152787 8893281373078135917229181)
      ·
        refine ⟨3334980514904300968960943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8893281373078135917229181 3334980514904300968960943)
        ·
          refine ⟨5002470772356451453441415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334980514904300968960943 5002470772356451453441415)
          ·
            refine ⟨7503706158534677180162123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002470772356451453441415 7503706158534677180162123)
            ·
              refine ⟨11255559237802015770243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503706158534677180162123 11255559237802015770243185)
              ·
                refine ⟨8441669428351511827682389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11255559237802015770243185 8441669428351511827682389)
                ·
                  refine ⟨98925813613494279230653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8441669428351511827682389 98925813613494279230653)
                  ·
                    rfl

theorem cell22_866958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_866958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866958 prefixEnd_866958 := by exact prefixLift 866958
  have htrace : WordTrace (prefixWord ++ tailWord_866958) baseStart_866958 baseEnd_866958 := by
    simpa [prefixWord, tailWord_866958, baseEnd_866958] using wordTrace_append hprefix tailTrace_866958
  have hstable : (prefixWord ++ tailWord_866958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866958).length < 2 ^ (prefixWord ++ tailWord_866958).sum := by decide
  have hdescent : baseEnd_866958 < baseStart_866958 := by decide
  rcases family_descends (prefixWord ++ tailWord_866958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866973 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_866973 : Nat := 118140960795 + 866973 * 2 ^ 59
def prefixEnd_866973 : Nat := 4983230072969 + 3 ^ 40 * 866973 * 2
def baseEnd_866973 : Nat := 296782575647027798566913

theorem tailTrace_866973 : CollatzResearch.WordTrace tailWord_866973 prefixEnd_866973 296782575647027798566913 := by
  unfold tailWord_866973
  simp only [CollatzResearch.WordTrace]
  refine ⟨31621103088112363045277573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21080735392074908696851715 31621103088112363045277573)
  ·
    refine ⟨5928956829021068070989545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31621103088112363045277573 5928956829021068070989545)
    ·
      refine ⟨4446717621765801053242159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5928956829021068070989545 4446717621765801053242159)
      ·
        refine ⟨6670076432648701579863239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446717621765801053242159 6670076432648701579863239)
        ·
          refine ⟨10005114648973052369794859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670076432648701579863239 10005114648973052369794859)
          ·
            refine ⟨15007671973459578554692289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005114648973052369794859 15007671973459578554692289)
            ·
              refine ⟨11255753980094683916019217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15007671973459578554692289 11255753980094683916019217)
              ·
                refine ⟨8441815485071012937014413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11255753980094683916019217 8441815485071012937014413)
                ·
                  refine ⟨3165680806901629851380405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8441815485071012937014413 3165680806901629851380405)
                  ·
                    refine ⟨296782575647027798566913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3165680806901629851380405 296782575647027798566913)
                    ·
                      rfl

theorem cell22_866973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_866973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_866973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_866973 prefixEnd_866973 := by exact prefixLift 866973
  have htrace : WordTrace (prefixWord ++ tailWord_866973) baseStart_866973 baseEnd_866973 := by
    simpa [prefixWord, tailWord_866973, baseEnd_866973] using wordTrace_append hprefix tailTrace_866973
  have hstable : (prefixWord ++ tailWord_866973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866973).length < 2 ^ (prefixWord ++ tailWord_866973).sum := by decide
  have hdescent : baseEnd_866973 < baseStart_866973 := by decide
  rcases family_descends (prefixWord ++ tailWord_866973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867020 : List Nat := [2, 2, 1, 5, 1, 3, 8]
def baseStart_867020 : Nat := 118140960795 + 867020 * 2 ^ 59
def prefixEnd_867020 : Nat := 4983230072969 + 3 ^ 40 * 867020 * 2
def baseEnd_867020 : Nat := 10992543137316123801547

theorem tailTrace_867020 : CollatzResearch.WordTrace tailWord_867020 prefixEnd_867020 10992543137316123801547 := by
  unfold tailWord_867020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811408659471045036119257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21081878212628060048159009 15811408659471045036119257)
  ·
    refine ⟨11858556494603283777089443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15811408659471045036119257 11858556494603283777089443)
    ·
      refine ⟨17787834741904925665634165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858556494603283777089443 17787834741904925665634165)
      ·
        refine ⟨1667609507053586781153203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17787834741904925665634165 1667609507053586781153203)
        ·
          refine ⟨2501414260580380171729805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667609507053586781153203 2501414260580380171729805)
          ·
            refine ⟨938030347717642564398677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2501414260580380171729805 938030347717642564398677)
            ·
              refine ⟨10992543137316123801547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 938030347717642564398677 10992543137316123801547)
              ·
                rfl

theorem cell22_867020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 8].length) (baseStart_867020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867020 prefixEnd_867020 := by exact prefixLift 867020
  have htrace : WordTrace (prefixWord ++ tailWord_867020) baseStart_867020 baseEnd_867020 := by
    simpa [prefixWord, tailWord_867020, baseEnd_867020] using wordTrace_append hprefix tailTrace_867020
  have hstable : (prefixWord ++ tailWord_867020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867020).length < 2 ^ (prefixWord ++ tailWord_867020).sum := by decide
  have hdescent : baseEnd_867020 < baseStart_867020 := by decide
  rcases family_descends (prefixWord ++ tailWord_867020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867033 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_867033 : Nat := 118140960795 + 867033 * 2 ^ 59
def prefixEnd_867033 : Nat := 4983230072969 + 3 ^ 40 * 867033 * 2
def baseEnd_867033 : Nat := 296803114873207642066729

theorem tailTrace_867033 : CollatzResearch.WordTrace tailWord_867033 prefixEnd_867033 296803114873207642066729 := by
  unfold tailWord_867033
  simp only [CollatzResearch.WordTrace]
  refine ⟨31623291467894993292461753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21082194311929995528307835 31623291467894993292461753)
  ·
    refine ⟨23717468600921244969346315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31623291467894993292461753 23717468600921244969346315)
    ·
      refine ⟨35576202901381867454019473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23717468600921244969346315 35576202901381867454019473)
      ·
        refine ⟨26682152176036400590514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35576202901381867454019473 26682152176036400590514605)
        ·
          refine ⟨10005807066013650221442977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26682152176036400590514605 10005807066013650221442977)
          ·
            refine ⟨7504355299510237666082233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10005807066013650221442977 7504355299510237666082233)
            ·
              refine ⟨5628266474632678249561675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504355299510237666082233 5628266474632678249561675)
              ·
                refine ⟨8442399711949017374342513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628266474632678249561675 8442399711949017374342513)
                ·
                  refine ⟨6331799783961763030756885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8442399711949017374342513 6331799783961763030756885)
                  ·
                    refine ⟨296803114873207642066729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6331799783961763030756885 296803114873207642066729)
                    ·
                      rfl

theorem cell22_867033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_867033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867033 prefixEnd_867033 := by exact prefixLift 867033
  have htrace : WordTrace (prefixWord ++ tailWord_867033) baseStart_867033 baseEnd_867033 := by
    simpa [prefixWord, tailWord_867033, baseEnd_867033] using wordTrace_append hprefix tailTrace_867033
  have hstable : (prefixWord ++ tailWord_867033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867033).length < 2 ^ (prefixWord ++ tailWord_867033).sum := by decide
  have hdescent : baseEnd_867033 < baseStart_867033 := by decide
  rcases family_descends (prefixWord ++ tailWord_867033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867063 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_867063 : Nat := 118140960795 + 867063 * 2 ^ 59
def prefixEnd_867063 : Nat := 4983230072969 + 3 ^ 40 * 867063 * 2
def baseEnd_867063 : Nat := 296813384486297563816637

theorem tailTrace_867063 : CollatzResearch.WordTrace tailWord_867063 prefixEnd_867063 296813384486297563816637 := by
  unfold tailWord_867063
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624385657786308416053843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21082923771857538944035895 31624385657786308416053843)
  ·
    refine ⟨47436578486679462624080765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31624385657786308416053843 47436578486679462624080765)
    ·
      refine ⟨17788716932504798484030287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47436578486679462624080765 17788716932504798484030287)
      ·
        refine ⟨26683075398757197726045431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788716932504798484030287 26683075398757197726045431)
        ·
          refine ⟨40024613098135796589068147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26683075398757197726045431 40024613098135796589068147)
          ·
            refine ⟨60036919647203694883602221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40024613098135796589068147 60036919647203694883602221)
            ·
              refine ⟨22513844867701385581350833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60036919647203694883602221 22513844867701385581350833)
              ·
                refine ⟨16885383650776039186013125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22513844867701385581350833 16885383650776039186013125)
                ·
                  refine ⟨3166009434520507347377461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16885383650776039186013125 3166009434520507347377461)
                  ·
                    refine ⟨296813384486297563816637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3166009434520507347377461 296813384486297563816637)
                    ·
                      rfl

theorem cell22_867063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_867063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867063 prefixEnd_867063 := by exact prefixLift 867063
  have htrace : WordTrace (prefixWord ++ tailWord_867063) baseStart_867063 baseEnd_867063 := by
    simpa [prefixWord, tailWord_867063, baseEnd_867063] using wordTrace_append hprefix tailTrace_867063
  have hstable : (prefixWord ++ tailWord_867063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867063).length < 2 ^ (prefixWord ++ tailWord_867063).sum := by decide
  have hdescent : baseEnd_867063 < baseStart_867063 := by decide
  rcases family_descends (prefixWord ++ tailWord_867063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867112 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_867112 : Nat := 118140960795 + 867112 * 2 ^ 59
def prefixEnd_867112 : Nat := 4983230072969 + 3 ^ 40 * 867112 * 2
def baseEnd_867112 : Nat := 296830158187677769341487

theorem tailTrace_867112 : CollatzResearch.WordTrace tailWord_867112 prefixEnd_867112 296830158187677769341487 := by
  unfold tailWord_867112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813086417304394892293795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21084115223072526523058393 15813086417304394892293795)
  ·
    refine ⟨23719629625956592338440693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15813086417304394892293795 23719629625956592338440693)
    ·
      refine ⟨2223715277433430531728815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23719629625956592338440693 2223715277433430531728815)
      ·
        refine ⟨3335572916150145797593223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223715277433430531728815 3335572916150145797593223)
        ·
          refine ⟨5003359374225218696389835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335572916150145797593223 5003359374225218696389835)
          ·
            refine ⟨7505039061337828044584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003359374225218696389835 7505039061337828044584753)
            ·
              refine ⟨5628779296003371033438565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505039061337828044584753 5628779296003371033438565)
              ·
                refine ⟨1055396118000632068769731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5628779296003371033438565 1055396118000632068769731)
                ·
                  refine ⟨1583094177000948103154597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055396118000632068769731 1583094177000948103154597)
                  ·
                    refine ⟨296830158187677769341487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583094177000948103154597 296830158187677769341487)
                    ·
                      rfl

theorem cell22_867112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_867112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867112 prefixEnd_867112 := by exact prefixLift 867112
  have htrace : WordTrace (prefixWord ++ tailWord_867112) baseStart_867112 baseEnd_867112 := by
    simpa [prefixWord, tailWord_867112, baseEnd_867112] using wordTrace_append hprefix tailTrace_867112
  have hstable : (prefixWord ++ tailWord_867112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867112).length < 2 ^ (prefixWord ++ tailWord_867112).sum := by decide
  have hdescent : baseEnd_867112 < baseStart_867112 := by decide
  rcases family_descends (prefixWord ++ tailWord_867112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867127 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 4]
def baseStart_867127 : Nat := 118140960795 + 867127 * 2 ^ 59
def prefixEnd_867127 : Nat := 4983230072969 + 3 ^ 40 * 867127 * 2
def baseEnd_867127 : Nat := 98945097664740910072147

theorem tailTrace_867127 : CollatzResearch.WordTrace tailWord_867127 prefixEnd_867127 98945097664740910072147 := by
  unfold tailWord_867127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626719929554447346383635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21084479953036298230922423 31626719929554447346383635)
  ·
    refine ⟨47440079894331671019575453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31626719929554447346383635 47440079894331671019575453)
    ·
      refine ⟨17790029960374376632340795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47440079894331671019575453 17790029960374376632340795)
      ·
        refine ⟨26685044940561564948511193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17790029960374376632340795 26685044940561564948511193)
        ·
          refine ⟨20013783705421173711383395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26685044940561564948511193 20013783705421173711383395)
          ·
            refine ⟨30020675558131760567075093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20013783705421173711383395 30020675558131760567075093)
            ·
              refine ⟨1407219166787426276581645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30020675558131760567075093 1407219166787426276581645)
              ·
                refine ⟨527707187545284853718117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407219166787426276581645 527707187545284853718117)
                ·
                  refine ⟨98945097664740910072147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527707187545284853718117 98945097664740910072147)
                  ·
                    rfl

theorem cell22_867127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 4].length) (baseStart_867127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867127 prefixEnd_867127 := by exact prefixLift 867127
  have htrace : WordTrace (prefixWord ++ tailWord_867127) baseStart_867127 baseEnd_867127 := by
    simpa [prefixWord, tailWord_867127, baseEnd_867127] using wordTrace_append hprefix tailTrace_867127
  have hstable : (prefixWord ++ tailWord_867127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867127).length < 2 ^ (prefixWord ++ tailWord_867127).sum := by decide
  have hdescent : baseEnd_867127 < baseStart_867127 := by decide
  rcases family_descends (prefixWord ++ tailWord_867127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867172 : List Nat := [2, 3, 1, 1, 4, 1, 4, 6]
def baseStart_867172 : Nat := 118140960795 + 867172 * 2 ^ 59
def prefixEnd_867172 : Nat := 4983230072969 + 3 ^ 40 * 867172 * 2
def baseEnd_867172 : Nat := 32983410823761956982367

theorem tailTrace_867172 : CollatzResearch.WordTrace tailWord_867172 prefixEnd_867172 32983410823761956982367 := by
  unfold tailWord_867172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814180607195710015885885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21085574142927613354514513 15814180607195710015885885)
  ·
    refine ⟨5930317727698391255957207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15814180607195710015885885 5930317727698391255957207)
    ·
      refine ⟨8895476591547586883935811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5930317727698391255957207 8895476591547586883935811)
      ·
        refine ⟨13343214887321380325903717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895476591547586883935811 13343214887321380325903717)
        ·
          refine ⟨2501852791372758811106947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13343214887321380325903717 2501852791372758811106947)
          ·
            refine ⟨3752779187059138216660421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501852791372758811106947 3752779187059138216660421)
            ·
              refine ⟨703646097573588415623829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3752779187059138216660421 703646097573588415623829)
              ·
                refine ⟨32983410823761956982367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 703646097573588415623829 32983410823761956982367)
                ·
                  rfl

theorem cell22_867172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_867172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867172 prefixEnd_867172 := by exact prefixLift 867172
  have htrace : WordTrace (prefixWord ++ tailWord_867172) baseStart_867172 baseEnd_867172 := by
    simpa [prefixWord, tailWord_867172, baseEnd_867172] using wordTrace_append hprefix tailTrace_867172
  have hstable : (prefixWord ++ tailWord_867172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867172).length < 2 ^ (prefixWord ++ tailWord_867172).sum := by decide
  have hdescent : baseEnd_867172 < baseStart_867172 := by decide
  rcases family_descends (prefixWord ++ tailWord_867172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867262 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_867262 : Nat := 118140960795 + 867262 * 2 ^ 59
def prefixEnd_867262 : Nat := 4983230072969 + 3 ^ 40 * 867262 * 2
def baseEnd_867262 : Nat := 98960502084375792697009

theorem tailTrace_867262 : CollatzResearch.WordTrace tailWord_867262 prefixEnd_867262 98960502084375792697009 := by
  unfold tailWord_867262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953955473008170675318505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21087762522710243601698693 3953955473008170675318505)
  ·
    refine ⟨2965466604756128006488879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3953955473008170675318505 2965466604756128006488879)
    ·
      refine ⟨4448199907134192009733319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965466604756128006488879 4448199907134192009733319)
      ·
        refine ⟨6672299860701288014599979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448199907134192009733319 6672299860701288014599979)
        ·
          refine ⟨10008449791051932021899969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672299860701288014599979 10008449791051932021899969)
          ·
            refine ⟨7506337343288949016424977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10008449791051932021899969 7506337343288949016424977)
            ·
              refine ⟨5629753007466711762318733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7506337343288949016424977 5629753007466711762318733)
              ·
                refine ⟨2111157377800016910869525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629753007466711762318733 2111157377800016910869525)
                ·
                  refine ⟨98960502084375792697009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2111157377800016910869525 98960502084375792697009)
                  ·
                    rfl

theorem cell22_867262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_867262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867262 prefixEnd_867262 := by exact prefixLift 867262
  have htrace : WordTrace (prefixWord ++ tailWord_867262) baseStart_867262 baseEnd_867262 := by
    simpa [prefixWord, tailWord_867262, baseEnd_867262] using wordTrace_append hprefix tailTrace_867262
  have hstable : (prefixWord ++ tailWord_867262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867262).length < 2 ^ (prefixWord ++ tailWord_867262).sum := by decide
  have hdescent : baseEnd_867262 < baseStart_867262 := by decide
  rcases family_descends (prefixWord ++ tailWord_867262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867298 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_867298 : Nat := 118140960795 + 867298 * 2 ^ 59
def prefixEnd_867298 : Nat := 4983230072969 + 3 ^ 40 * 867298 * 2
def baseEnd_867298 : Nat := 296893829788835284190917

theorem tailTrace_867298 : CollatzResearch.WordTrace tailWord_867298 prefixEnd_867298 296893829788835284190917 := by
  unfold tailWord_867298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908239202983735887714637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21088637874623295700572365 7908239202983735887714637)
  ·
    refine ⟨2965589701118900957892989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7908239202983735887714637 2965589701118900957892989)
    ·
      refine ⟨1112096137919587859209871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2965589701118900957892989 1112096137919587859209871)
      ·
        refine ⟨1668144206879381788814807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112096137919587859209871 1668144206879381788814807)
        ·
          refine ⟨2502216310319072683222211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668144206879381788814807 2502216310319072683222211)
          ·
            refine ⟨3753324465478609024833317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502216310319072683222211 3753324465478609024833317)
            ·
              refine ⟨703748337277239192156247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3753324465478609024833317 703748337277239192156247)
              ·
                refine ⟨1055622505915858788234371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703748337277239192156247 1055622505915858788234371)
                ·
                  refine ⟨1583433758873788182351557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055622505915858788234371 1583433758873788182351557)
                  ·
                    refine ⟨296893829788835284190917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583433758873788182351557 296893829788835284190917)
                    ·
                      rfl

theorem cell22_867298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_867298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867298 prefixEnd_867298 := by exact prefixLift 867298
  have htrace : WordTrace (prefixWord ++ tailWord_867298) baseStart_867298 baseEnd_867298 := by
    simpa [prefixWord, tailWord_867298, baseEnd_867298] using wordTrace_append hprefix tailTrace_867298
  have hstable : (prefixWord ++ tailWord_867298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867298).length < 2 ^ (prefixWord ++ tailWord_867298).sum := by decide
  have hdescent : baseEnd_867298 < baseStart_867298 := by decide
  rcases family_descends (prefixWord ++ tailWord_867298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867305 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_867305 : Nat := 118140960795 + 867305 * 2 ^ 59
def prefixEnd_867305 : Nat := 4983230072969 + 3 ^ 40 * 867305 * 2
def baseEnd_867305 : Nat := 296896226031889599265895

theorem tailTrace_867305 : CollatzResearch.WordTrace tailWord_867305 prefixEnd_867305 296896226031889599265895 := by
  unfold tailWord_867305
  simp only [CollatzResearch.WordTrace]
  refine ⟨31633212122909583746363369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21088808081939722497575579 31633212122909583746363369)
  ·
    refine ⟨23724909092182187809772527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31633212122909583746363369 23724909092182187809772527)
    ·
      refine ⟨35587363638273281714658791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23724909092182187809772527 35587363638273281714658791)
      ·
        refine ⟨53381045457409922571988187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35587363638273281714658791 53381045457409922571988187)
        ·
          refine ⟨80071568186114883857982281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53381045457409922571988187 80071568186114883857982281)
          ·
            refine ⟨60053676139586162893486711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80071568186114883857982281 60053676139586162893486711)
            ·
              refine ⟨90080514209379244340230067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60053676139586162893486711 90080514209379244340230067)
              ·
                refine ⟨135120771314068866510345101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90080514209379244340230067 135120771314068866510345101)
                ·
                  refine ⟨50670289242775824941379413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135120771314068866510345101 50670289242775824941379413)
                  ·
                    refine ⟨296896226031889599265895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50670289242775824941379413 296896226031889599265895)
                    ·
                      rfl

theorem cell22_867305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_867305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867305 prefixEnd_867305 := by exact prefixLift 867305
  have htrace : WordTrace (prefixWord ++ tailWord_867305) baseStart_867305 baseEnd_867305 := by
    simpa [prefixWord, tailWord_867305, baseEnd_867305] using wordTrace_append hprefix tailTrace_867305
  have hstable : (prefixWord ++ tailWord_867305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867305).length < 2 ^ (prefixWord ++ tailWord_867305).sum := by decide
  have hdescent : baseEnd_867305 < baseStart_867305 := by decide
  rcases family_descends (prefixWord ++ tailWord_867305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867311 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 2, 3]
def baseStart_867311 : Nat := 118140960795 + 867311 * 2 ^ 59
def prefixEnd_867311 : Nat := 4983230072969 + 3 ^ 40 * 867311 * 2
def baseEnd_867311 : Nat := 296898279954507583615877

theorem tailTrace_867311 : CollatzResearch.WordTrace tailWord_867311 prefixEnd_867311 296898279954507583615877 := by
  unfold tailWord_867311
  simp only [CollatzResearch.WordTrace]
  refine ⟨31633430960887846771081787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21088953973925231180721191 31633430960887846771081787)
  ·
    refine ⟨47450146441331770156622681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31633430960887846771081787 47450146441331770156622681)
    ·
      refine ⟨35587609830998827617467011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47450146441331770156622681 35587609830998827617467011)
      ·
        refine ⟨53381414746498241426200517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35587609830998827617467011 53381414746498241426200517)
        ·
          refine ⟨10009015264968420267412597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53381414746498241426200517 10009015264968420267412597)
          ·
            refine ⟨938345181090789400069931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10009015264968420267412597 938345181090789400069931)
            ·
              refine ⟨1407517771636184100104897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938345181090789400069931 1407517771636184100104897)
              ·
                refine ⟨1055638328727138075078673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407517771636184100104897 1055638328727138075078673)
                ·
                  refine ⟨791728746545353556309005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055638328727138075078673 791728746545353556309005)
                  ·
                    refine ⟨296898279954507583615877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791728746545353556309005 296898279954507583615877)
                    ·
                      rfl

theorem cell22_867311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_867311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867311 prefixEnd_867311 := by exact prefixLift 867311
  have htrace : WordTrace (prefixWord ++ tailWord_867311) baseStart_867311 baseEnd_867311 := by
    simpa [prefixWord, tailWord_867311, baseEnd_867311] using wordTrace_append hprefix tailTrace_867311
  have hstable : (prefixWord ++ tailWord_867311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867311).length < 2 ^ (prefixWord ++ tailWord_867311).sum := by decide
  have hdescent : baseEnd_867311 < baseStart_867311 := by decide
  rcases family_descends (prefixWord ++ tailWord_867311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867339 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 3, 3]
def baseStart_867339 : Nat := 118140960795 + 867339 * 2 ^ 59
def prefixEnd_867339 : Nat := 4983230072969 + 3 ^ 40 * 867339 * 2
def baseEnd_867339 : Nat := 296907864926724843915791

theorem tailTrace_867339 : CollatzResearch.WordTrace tailWord_867339 prefixEnd_867339 296907864926724843915791 := by
  unfold tailWord_867339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31634452204786407553101071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21089634803190938368734047 31634452204786407553101071)
  ·
    refine ⟨47451678307179611329651607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31634452204786407553101071 47451678307179611329651607)
    ·
      refine ⟨71177517460769416994477411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47451678307179611329651607 71177517460769416994477411)
      ·
        refine ⟨106766276191154125491716117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71177517460769416994477411 106766276191154125491716117)
        ·
          refine ⟨5004669196460349632424193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106766276191154125491716117 5004669196460349632424193)
          ·
            refine ⟨3753501897345262224318145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5004669196460349632424193 3753501897345262224318145)
            ·
              refine ⟨2815126423008946668238609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753501897345262224318145 2815126423008946668238609)
              ·
                refine ⟨2111344817256710001178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815126423008946668238609 2111344817256710001178957)
                ·
                  refine ⟨791754306471266250442109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2111344817256710001178957 791754306471266250442109)
                  ·
                    refine ⟨296907864926724843915791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791754306471266250442109 296907864926724843915791)
                    ·
                      rfl

theorem cell22_867339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].length) (baseStart_867339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867339 prefixEnd_867339 := by exact prefixLift 867339
  have htrace : WordTrace (prefixWord ++ tailWord_867339) baseStart_867339 baseEnd_867339 := by
    simpa [prefixWord, tailWord_867339, baseEnd_867339] using wordTrace_append hprefix tailTrace_867339
  have hstable : (prefixWord ++ tailWord_867339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867339).length < 2 ^ (prefixWord ++ tailWord_867339).sum := by decide
  have hdescent : baseEnd_867339 < baseStart_867339 := by decide
  rcases family_descends (prefixWord ++ tailWord_867339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867352 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_867352 : Nat := 118140960795 + 867352 * 2 ^ 59
def prefixEnd_867352 : Nat := 4983230072969 + 3 ^ 40 * 867352 * 2
def baseEnd_867352 : Nat := 98970771697465714446917

theorem tailTrace_867352 : CollatzResearch.WordTrace tailWord_867352 prefixEnd_867352 98970771697465714446917 := by
  unfold tailWord_867352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15817463176869655386662155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21089950902492873848882873 15817463176869655386662155)
  ·
    refine ⟨23726194765304483079993233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15817463176869655386662155 23726194765304483079993233)
    ·
      refine ⟨17794646073978362309994925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23726194765304483079993233 17794646073978362309994925)
      ·
        refine ⟨6672992277741885866248097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17794646073978362309994925 6672992277741885866248097)
        ·
          refine ⟨5004744208306414399686073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672992277741885866248097 5004744208306414399686073)
          ·
            refine ⟨3753558156229810799764555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5004744208306414399686073 3753558156229810799764555)
            ·
              refine ⟨5630337234344716199646833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753558156229810799764555 5630337234344716199646833)
              ·
                refine ⟨4222752925758537149735125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5630337234344716199646833 4222752925758537149735125)
                ·
                  refine ⟨98970771697465714446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4222752925758537149735125 98970771697465714446917)
                  ·
                    rfl

theorem cell22_867352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_867352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867352 prefixEnd_867352 := by exact prefixLift 867352
  have htrace : WordTrace (prefixWord ++ tailWord_867352) baseStart_867352 baseEnd_867352 := by
    simpa [prefixWord, tailWord_867352, baseEnd_867352] using wordTrace_append hprefix tailTrace_867352
  have hstable : (prefixWord ++ tailWord_867352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867352).length < 2 ^ (prefixWord ++ tailWord_867352).sum := by decide
  have hdescent : baseEnd_867352 < baseStart_867352 := by decide
  rcases family_descends (prefixWord ++ tailWord_867352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867397 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 6]
def baseStart_867397 : Nat := 118140960795 + 867397 * 2 ^ 59
def prefixEnd_867397 : Nat := 4983230072969 + 3 ^ 40 * 867397 * 2
def baseEnd_867397 : Nat := 98975906504010675321871

theorem tailTrace_867397 : CollatzResearch.WordTrace tailWord_867397 prefixEnd_867397 98975906504010675321871 := by
  unfold tailWord_867397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31636567638576283458712445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091045092384188972474963 31636567638576283458712445)
  ·
    refine ⟨11863712864466106297017167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31636567638576283458712445 11863712864466106297017167)
    ·
      refine ⟨17795569296699159445525751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11863712864466106297017167 17795569296699159445525751)
      ·
        refine ⟨26693353945048739168288627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17795569296699159445525751 26693353945048739168288627)
        ·
          refine ⟨40040030917573108752432941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26693353945048739168288627 40040030917573108752432941)
          ·
            refine ⟨15015011594089915782162353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40040030917573108752432941 15015011594089915782162353)
            ·
              refine ⟨11261258695567436836621765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15015011594089915782162353 11261258695567436836621765)
              ·
                refine ⟨2111486005418894406866581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11261258695567436836621765 2111486005418894406866581)
                ·
                  refine ⟨98975906504010675321871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2111486005418894406866581 98975906504010675321871)
                  ·
                    rfl

theorem cell22_867397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_867397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867397 prefixEnd_867397 := by exact prefixLift 867397
  have htrace : WordTrace (prefixWord ++ tailWord_867397) baseStart_867397 baseEnd_867397 := by
    simpa [prefixWord, tailWord_867397, baseEnd_867397] using wordTrace_append hprefix tailTrace_867397
  have hstable : (prefixWord ++ tailWord_867397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867397).length < 2 ^ (prefixWord ++ tailWord_867397).sum := by decide
  have hdescent : baseEnd_867397 < baseStart_867397 := by decide
  rcases family_descends (prefixWord ++ tailWord_867397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867399 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_867399 : Nat := 118140960795 + 867399 * 2 ^ 59
def prefixEnd_867399 : Nat := 4983230072969 + 3 ^ 40 * 867399 * 2
def baseEnd_867399 : Nat := 296928404152904687415607

theorem tailTrace_867399 : CollatzResearch.WordTrace tailWord_867399 prefixEnd_867399 296928404152904687415607 := by
  unfold tailWord_867399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31636640584569037800285251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091093723046025200190167 31636640584569037800285251)
  ·
    refine ⟨47454960876853556700427877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31636640584569037800285251 47454960876853556700427877)
    ·
      refine ⟨8897805164410041881330227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47454960876853556700427877 8897805164410041881330227)
      ·
        refine ⟨13346707746615062821995341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897805164410041881330227 13346707746615062821995341)
        ·
          refine ⟨5005015404980648558248253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13346707746615062821995341 5005015404980648558248253)
          ·
            refine ⟨1876880776867743209343095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5005015404980648558248253 1876880776867743209343095)
            ·
              refine ⟨2815321165301614814014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876880776867743209343095 2815321165301614814014643)
              ·
                refine ⟨4222981747952422221021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815321165301614814014643 4222981747952422221021965)
                ·
                  refine ⟨1583618155482158332883237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4222981747952422221021965 1583618155482158332883237)
                  ·
                    refine ⟨296928404152904687415607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583618155482158332883237 296928404152904687415607)
                    ·
                      rfl

theorem cell22_867399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_867399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867399 prefixEnd_867399 := by exact prefixLift 867399
  have htrace : WordTrace (prefixWord ++ tailWord_867399) baseStart_867399 baseEnd_867399 := by
    simpa [prefixWord, tailWord_867399, baseEnd_867399] using wordTrace_append hprefix tailTrace_867399
  have hstable : (prefixWord ++ tailWord_867399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867399).length < 2 ^ (prefixWord ++ tailWord_867399).sum := by decide
  have hdescent : baseEnd_867399 < baseStart_867399 := by decide
  rcases family_descends (prefixWord ++ tailWord_867399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867416 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_867416 : Nat := 118140960795 + 867416 * 2 ^ 59
def prefixEnd_867416 : Nat := 4983230072969 + 3 ^ 40 * 867416 * 2
def baseEnd_867416 : Nat := 296934223600322309740555

theorem tailTrace_867416 : CollatzResearch.WordTrace tailWord_867416 prefixEnd_867416 296934223600322309740555 := by
  unfold tailWord_867416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818630312753724851827051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21091507083671633135769401 15818630312753724851827051)
  ·
    refine ⟨23727945469130587277740577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818630312753724851827051 23727945469130587277740577)
    ·
      refine ⟨17795959101847940458305433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23727945469130587277740577 17795959101847940458305433)
      ·
        refine ⟨13346969326385955343729075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17795959101847940458305433 13346969326385955343729075)
        ·
          refine ⟨20020453989578933015593613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346969326385955343729075 20020453989578933015593613)
          ·
            refine ⟨7507670246092099880847605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20020453989578933015593613 7507670246092099880847605)
            ·
              refine ⟨703844085571134363829463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7507670246092099880847605 703844085571134363829463)
              ·
                refine ⟨1055766128356701545744195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703844085571134363829463 1055766128356701545744195)
                ·
                  refine ⟨1583649192535052318616293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055766128356701545744195 1583649192535052318616293)
                  ·
                    refine ⟨296934223600322309740555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583649192535052318616293 296934223600322309740555)
                    ·
                      rfl

theorem cell22_867416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_867416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867416 prefixEnd_867416 := by exact prefixLift 867416
  have htrace : WordTrace (prefixWord ++ tailWord_867416) baseStart_867416 baseEnd_867416 := by
    simpa [prefixWord, tailWord_867416, baseEnd_867416] using wordTrace_append hprefix tailTrace_867416
  have hstable : (prefixWord ++ tailWord_867416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867416).length < 2 ^ (prefixWord ++ tailWord_867416).sum := by decide
  have hdescent : baseEnd_867416 < baseStart_867416 := by decide
  rcases family_descends (prefixWord ++ tailWord_867416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867427 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_867427 : Nat := 118140960795 + 867427 * 2 ^ 59
def prefixEnd_867427 : Nat := 4983230072969 + 3 ^ 40 * 867427 * 2
def baseEnd_867427 : Nat := 296937989125121947715521

theorem tailTrace_867427 : CollatzResearch.WordTrace tailWord_867427 prefixEnd_867427 296937989125121947715521 := by
  unfold tailWord_867427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637661828467598582304535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091774552311732388203023 31637661828467598582304535)
  ·
    refine ⟨47456492742701397873456803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31637661828467598582304535 47456492742701397873456803)
    ·
      refine ⟨71184739114052096810185205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456492742701397873456803 71184739114052096810185205)
      ·
        refine ⟨6673569291942384075954863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71184739114052096810185205 6673569291942384075954863)
        ·
          refine ⟨10010353937913576113932295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673569291942384075954863 10010353937913576113932295)
          ·
            refine ⟨15015530906870364170898443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010353937913576113932295 15015530906870364170898443)
            ·
              refine ⟨22523296360305546256347665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015530906870364170898443 22523296360305546256347665)
              ·
                refine ⟨16892472270229159692260749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523296360305546256347665 16892472270229159692260749)
                ·
                  refine ⟨6334677101335934884597781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16892472270229159692260749 6334677101335934884597781)
                  ·
                    refine ⟨296937989125121947715521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6334677101335934884597781 296937989125121947715521)
                    ·
                      rfl

theorem cell22_867427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_867427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867427 prefixEnd_867427 := by exact prefixLift 867427
  have htrace : WordTrace (prefixWord ++ tailWord_867427) baseStart_867427 baseEnd_867427 := by
    simpa [prefixWord, tailWord_867427, baseEnd_867427] using wordTrace_append hprefix tailTrace_867427
  have hstable : (prefixWord ++ tailWord_867427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867427).length < 2 ^ (prefixWord ++ tailWord_867427).sum := by decide
  have hdescent : baseEnd_867427 < baseStart_867427 := by decide
  rcases family_descends (prefixWord ++ tailWord_867427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867431 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 4]
def baseStart_867431 : Nat := 118140960795 + 867431 * 2 ^ 59
def prefixEnd_867431 : Nat := 4983230072969 + 3 ^ 40 * 867431 * 2
def baseEnd_867431 : Nat := 98979786135622423538503

theorem tailTrace_867431 : CollatzResearch.WordTrace tailWord_867431 prefixEnd_867431 98979786135622423538503 := by
  unfold tailWord_867431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637807720453107265450147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091871813635404843633431 31637807720453107265450147)
  ·
    refine ⟨47456711580679660898175221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31637807720453107265450147 47456711580679660898175221)
    ·
      refine ⟨4449066710688718209203927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47456711580679660898175221 4449066710688718209203927)
      ·
        refine ⟨6673600066033077313805891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449066710688718209203927 6673600066033077313805891)
        ·
          refine ⟨10010400099049615970708837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673600066033077313805891 10010400099049615970708837)
          ·
            refine ⟨1876950018571802994507907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10010400099049615970708837 1876950018571802994507907)
            ·
              refine ⟨2815425027857704491761861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876950018571802994507907 2815425027857704491761861)
              ·
                refine ⟨527892192723319592205349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2815425027857704491761861 527892192723319592205349)
                ·
                  refine ⟨98979786135622423538503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527892192723319592205349 98979786135622423538503)
                  ·
                    rfl

theorem cell22_867431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 4].length) (baseStart_867431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867431 prefixEnd_867431 := by exact prefixLift 867431
  have htrace : WordTrace (prefixWord ++ tailWord_867431) baseStart_867431 baseEnd_867431 := by
    simpa [prefixWord, tailWord_867431, baseEnd_867431] using wordTrace_append hprefix tailTrace_867431
  have hstable : (prefixWord ++ tailWord_867431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867431).length < 2 ^ (prefixWord ++ tailWord_867431).sum := by decide
  have hdescent : baseEnd_867431 < baseStart_867431 := by decide
  rcases family_descends (prefixWord ++ tailWord_867431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867446 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_867446 : Nat := 118140960795 + 867446 * 2 ^ 59
def prefixEnd_867446 : Nat := 4983230072969 + 3 ^ 40 * 867446 * 2
def baseEnd_867446 : Nat := 296944493213412231490463

theorem tailTrace_867446 : CollatzResearch.WordTrace tailWord_867446 prefixEnd_867446 296944493213412231490463 := by
  unfold tailWord_867446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977397175962422801702887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21092236543599176551497461 1977397175962422801702887)
  ·
    refine ⟨2966095763943634202554331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1977397175962422801702887 2966095763943634202554331)
    ·
      refine ⟨4449143645915451303831497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966095763943634202554331 4449143645915451303831497)
      ·
        refine ⟨3336857734436588477873623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449143645915451303831497 3336857734436588477873623)
        ·
          refine ⟨5005286601654882716810435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336857734436588477873623 5005286601654882716810435)
          ·
            refine ⟨7507929902482324075215653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005286601654882716810435 7507929902482324075215653)
            ·
              refine ⟨1407736856715435764102935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7507929902482324075215653 1407736856715435764102935)
              ·
                refine ⟨2111605285073153646154403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407736856715435764102935 2111605285073153646154403)
                ·
                  refine ⟨3167407927609730469231605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111605285073153646154403 3167407927609730469231605)
                  ·
                    refine ⟨296944493213412231490463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3167407927609730469231605 296944493213412231490463)
                    ·
                      rfl

theorem cell22_867446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_867446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867446 prefixEnd_867446 := by exact prefixLift 867446
  have htrace : WordTrace (prefixWord ++ tailWord_867446) baseStart_867446 baseEnd_867446 := by
    simpa [prefixWord, tailWord_867446, baseEnd_867446] using wordTrace_append hprefix tailTrace_867446
  have hstable : (prefixWord ++ tailWord_867446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867446).length < 2 ^ (prefixWord ++ tailWord_867446).sum := by decide
  have hdescent : baseEnd_867446 < baseStart_867446 := by decide
  rcases family_descends (prefixWord ++ tailWord_867446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867459 : List Nat := [1, 1, 1, 3, 3, 2, 5, 6]
def baseStart_867459 : Nat := 118140960795 + 867459 * 2 ^ 59
def prefixEnd_867459 : Nat := 4983230072969 + 3 ^ 40 * 867459 * 2
def baseEnd_867459 : Nat := 32994327042120503435047

theorem tailTrace_867459 : CollatzResearch.WordTrace tailWord_867459 prefixEnd_867459 32994327042120503435047 := by
  unfold tailWord_867459
  simp only [CollatzResearch.WordTrace]
  refine ⟨31638828964351668047469431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21092552642901112031646287 31638828964351668047469431)
  ·
    refine ⟨47458243446527502071204147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31638828964351668047469431 47458243446527502071204147)
    ·
      refine ⟨71187365169791253106806221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47458243446527502071204147 71187365169791253106806221)
      ·
        refine ⟨26695261938671719915052333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71187365169791253106806221 26695261938671719915052333)
        ·
          refine ⟨10010723227001894968144625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26695261938671719915052333 10010723227001894968144625)
          ·
            refine ⟨7508042420251421226108469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10010723227001894968144625 7508042420251421226108469)
            ·
              refine ⟨703878976898570739947669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7508042420251421226108469 703878976898570739947669)
              ·
                refine ⟨32994327042120503435047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 703878976898570739947669 32994327042120503435047)
                ·
                  rfl

theorem cell22_867459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 6].length) (baseStart_867459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867459 prefixEnd_867459 := by exact prefixLift 867459
  have htrace : WordTrace (prefixWord ++ tailWord_867459) baseStart_867459 baseEnd_867459 := by
    simpa [prefixWord, tailWord_867459, baseEnd_867459] using wordTrace_append hprefix tailTrace_867459
  have hstable : (prefixWord ++ tailWord_867459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867459).length < 2 ^ (prefixWord ++ tailWord_867459).sum := by decide
  have hdescent : baseEnd_867459 < baseStart_867459 := by decide
  rcases family_descends (prefixWord ++ tailWord_867459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867472 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_867472 : Nat := 118140960795 + 867472 * 2 ^ 59
def prefixEnd_867472 : Nat := 4983230072969 + 3 ^ 40 * 867472 * 2
def baseEnd_867472 : Nat := 296953393544756830340383

theorem tailTrace_867472 : CollatzResearch.WordTrace tailWord_867472 prefixEnd_867472 296953393544756830340383 := by
  unfold tailWord_867472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15819651556652285633846335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21092868742203047511795113 15819651556652285633846335)
  ·
    refine ⟨23729477334978428450769503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15819651556652285633846335 23729477334978428450769503)
    ·
      refine ⟨35594216002467642676154255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23729477334978428450769503 35594216002467642676154255)
      ·
        refine ⟨53391324003701464014231383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35594216002467642676154255 53391324003701464014231383)
        ·
          refine ⟨80086986005552196021347075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53391324003701464014231383 80086986005552196021347075)
          ·
            refine ⟨120130479008328294032020613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80086986005552196021347075 120130479008328294032020613)
            ·
              refine ⟨22524464814061555131003865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120130479008328294032020613 22524464814061555131003865)
              ·
                refine ⟨16893348610546166348252899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524464814061555131003865 16893348610546166348252899)
                ·
                  refine ⟨25340022915819249522379349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16893348610546166348252899 25340022915819249522379349)
                  ·
                    refine ⟨296953393544756830340383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25340022915819249522379349 296953393544756830340383)
                    ·
                      rfl

theorem cell22_867472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_867472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867472 prefixEnd_867472 := by exact prefixLift 867472
  have htrace : WordTrace (prefixWord ++ tailWord_867472) baseStart_867472 baseEnd_867472 := by
    simpa [prefixWord, tailWord_867472, baseEnd_867472] using wordTrace_append hprefix tailTrace_867472
  have hstable : (prefixWord ++ tailWord_867472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867472).length < 2 ^ (prefixWord ++ tailWord_867472).sum := by decide
  have hdescent : baseEnd_867472 < baseStart_867472 := by decide
  rcases family_descends (prefixWord ++ tailWord_867472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867521 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 7]
def baseStart_867521 : Nat := 118140960795 + 867521 * 2 ^ 59
def prefixEnd_867521 : Nat := 4983230072969 + 3 ^ 40 * 867521 * 2
def baseEnd_867521 : Nat := 98990055748712345288411

theorem tailTrace_867521 : CollatzResearch.WordTrace tailWord_867521 prefixEnd_867521 98990055748712345288411 := by
  unfold tailWord_867521
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641090290127052636226417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21094060193418035090817611 31641090290127052636226417)
  ·
    refine ⟨23730817717595289477169813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31641090290127052636226417 23730817717595289477169813)
    ·
      refine ⟨1112382080512279194242335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23730817717595289477169813 1112382080512279194242335)
      ·
        refine ⟨1668573120768418791363503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112382080512279194242335 1668573120768418791363503)
        ·
          refine ⟨2502859681152628187045255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668573120768418791363503 2502859681152628187045255)
          ·
            refine ⟨3754289521728942280567883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502859681152628187045255 3754289521728942280567883)
            ·
              refine ⟨5631434282593413420851825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754289521728942280567883 5631434282593413420851825)
              ·
                refine ⟨4223575711945060065638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5631434282593413420851825 4223575711945060065638869)
                ·
                  refine ⟨98990055748712345288411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4223575711945060065638869 98990055748712345288411)
                  ·
                    rfl

theorem cell22_867521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_867521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867521 prefixEnd_867521 := by exact prefixLift 867521
  have htrace : WordTrace (prefixWord ++ tailWord_867521) baseStart_867521 baseEnd_867521 := by
    simpa [prefixWord, tailWord_867521, baseEnd_867521] using wordTrace_append hprefix tailTrace_867521
  have hstable : (prefixWord ++ tailWord_867521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867521).length < 2 ^ (prefixWord ++ tailWord_867521).sum := by decide
  have hdescent : baseEnd_867521 < baseStart_867521 := by decide
  rcases family_descends (prefixWord ++ tailWord_867521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867542 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_867542 : Nat := 118140960795 + 867542 * 2 ^ 59
def prefixEnd_867542 : Nat := 4983230072969 + 3 ^ 40 * 867542 * 2
def baseEnd_867542 : Nat := 296977355975299981090169

theorem tailTrace_867542 : CollatzResearch.WordTrace tailWord_867542 prefixEnd_867542 296977355975299981090169 := by
  unfold tailWord_867542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977616013940685826421305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21094570815367315481827253 1977616013940685826421305)
  ·
    refine ⟨1483212010455514369815979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1977616013940685826421305 1483212010455514369815979)
    ·
      refine ⟨2224818015683271554723969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483212010455514369815979 2224818015683271554723969)
      ·
        refine ⟨1668613511762453666042977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224818015683271554723969 1668613511762453666042977)
        ·
          refine ⟨1251460133821840249532233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668613511762453666042977 1251460133821840249532233)
          ·
            refine ⟨938595100366380187149175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251460133821840249532233 938595100366380187149175)
            ·
              refine ⟨1407892650549570280723763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938595100366380187149175 1407892650549570280723763)
              ·
                refine ⟨2111838975824355421085645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407892650549570280723763 2111838975824355421085645)
                ·
                  refine ⟨791939615934133282907117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2111838975824355421085645 791939615934133282907117)
                  ·
                    refine ⟨296977355975299981090169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791939615934133282907117 296977355975299981090169)
                    ·
                      rfl

theorem cell22_867542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_867542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867542 prefixEnd_867542 := by exact prefixLift 867542
  have htrace : WordTrace (prefixWord ++ tailWord_867542) baseStart_867542 baseEnd_867542 := by
    simpa [prefixWord, tailWord_867542, baseEnd_867542] using wordTrace_append hprefix tailTrace_867542
  have hstable : (prefixWord ++ tailWord_867542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867542).length < 2 ^ (prefixWord ++ tailWord_867542).sum := by decide
  have hdescent : baseEnd_867542 < baseStart_867542 := by decide
  rcases family_descends (prefixWord ++ tailWord_867542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867596 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_867596 : Nat := 118140960795 + 867596 * 2 ^ 59
def prefixEnd_867596 : Nat := 4983230072969 + 3 ^ 40 * 867596 * 2
def baseEnd_867596 : Nat := 296995841278861840240003

theorem tailTrace_867596 : CollatzResearch.WordTrace tailWord_867596 prefixEnd_867596 296995841278861840240003 := by
  unfold tailWord_867596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821912882427670222603321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21095883843236893630137761 15821912882427670222603321)
  ·
    refine ⟨11866434661820752666952491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15821912882427670222603321 11866434661820752666952491)
    ·
      refine ⟨17799651992731129000428737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866434661820752666952491 17799651992731129000428737)
      ·
        refine ⟨13349738994548346750321553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17799651992731129000428737 13349738994548346750321553)
        ·
          refine ⟨10012304245911260062741165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13349738994548346750321553 10012304245911260062741165)
          ·
            refine ⟨3754614092216722523527937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10012304245911260062741165 3754614092216722523527937)
            ·
              refine ⟨2815960569162541892645953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754614092216722523527937 2815960569162541892645953)
              ·
                refine ⟨2111970426871906419484465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815960569162541892645953 2111970426871906419484465)
                ·
                  refine ⟨1583977820153929814613349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111970426871906419484465 1583977820153929814613349)
                  ·
                    refine ⟨296995841278861840240003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1583977820153929814613349 296995841278861840240003)
                    ·
                      rfl

theorem cell22_867596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_867596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867596 prefixEnd_867596 := by exact prefixLift 867596
  have htrace : WordTrace (prefixWord ++ tailWord_867596) baseStart_867596 baseEnd_867596 := by
    simpa [prefixWord, tailWord_867596, baseEnd_867596] using wordTrace_append hprefix tailTrace_867596
  have hstable : (prefixWord ++ tailWord_867596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867596).length < 2 ^ (prefixWord ++ tailWord_867596).sum := by decide
  have hdescent : baseEnd_867596 < baseStart_867596 := by decide
  rcases family_descends (prefixWord ++ tailWord_867596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867598 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_867598 : Nat := 118140960795 + 867598 * 2 ^ 59
def prefixEnd_867598 : Nat := 4983230072969 + 3 ^ 40 * 867598 * 2
def baseEnd_867598 : Nat := 296996525919734501689997

theorem tailTrace_867598 : CollatzResearch.WordTrace tailWord_867598 prefixEnd_867598 296996525919734501689997 := by
  unfold tailWord_867598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955487338856011848347431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21095932473898729857852965 3955487338856011848347431)
  ·
    refine ⟨5933231008284017772521147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3955487338856011848347431 5933231008284017772521147)
    ·
      refine ⟨8899846512426026658781721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5933231008284017772521147 8899846512426026658781721)
      ·
        refine ⟨6674884884319519994086291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8899846512426026658781721 6674884884319519994086291)
        ·
          refine ⟨10012327326479279991129437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674884884319519994086291 10012327326479279991129437)
          ·
            refine ⟨3754622747429729996673539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10012327326479279991129437 3754622747429729996673539)
            ·
              refine ⟨5631934121144594995010309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754622747429729996673539 5631934121144594995010309)
              ·
                refine ⟨1055987647714611561564433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5631934121144594995010309 1055987647714611561564433)
                ·
                  refine ⟨791990735785958671173325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055987647714611561564433 791990735785958671173325)
                  ·
                    refine ⟨296996525919734501689997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791990735785958671173325 296996525919734501689997)
                    ·
                      rfl

theorem cell22_867598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_867598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867598 prefixEnd_867598 := by exact prefixLift 867598
  have htrace : WordTrace (prefixWord ++ tailWord_867598) baseStart_867598 baseEnd_867598 := by
    simpa [prefixWord, tailWord_867598, baseEnd_867598] using wordTrace_append hprefix tailTrace_867598
  have hstable : (prefixWord ++ tailWord_867598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867598).length < 2 ^ (prefixWord ++ tailWord_867598).sum := by decide
  have hdescent : baseEnd_867598 < baseStart_867598 := by decide
  rcases family_descends (prefixWord ++ tailWord_867598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867660 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_867660 : Nat := 118140960795 + 867660 * 2 ^ 59
def prefixEnd_867660 : Nat := 4983230072969 + 3 ^ 40 * 867660 * 2
def baseEnd_867660 : Nat := 297017749786787006639807

theorem tailTrace_867660 : CollatzResearch.WordTrace tailWord_867660 prefixEnd_867660 297017749786787006639807 := by
  unfold tailWord_867660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823080018311739687768217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21097440024415652917024289 15823080018311739687768217)
  ·
    refine ⟨11867310013733804765826163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15823080018311739687768217 11867310013733804765826163)
    ·
      refine ⟨17800965020600707148739245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867310013733804765826163 17800965020600707148739245)
      ·
        refine ⟨6675361882725265180777217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17800965020600707148739245 6675361882725265180777217)
        ·
          refine ⟨5006521412043948885582913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675361882725265180777217 5006521412043948885582913)
          ·
            refine ⟨3754891059032961664187185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006521412043948885582913 3754891059032961664187185)
            ·
              refine ⟨2816168294274721248140389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754891059032961664187185 2816168294274721248140389)
              ·
                refine ⟨528031555176510234026323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2816168294274721248140389 528031555176510234026323)
                ·
                  refine ⟨792047332764765351039485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528031555176510234026323 792047332764765351039485)
                  ·
                    refine ⟨297017749786787006639807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792047332764765351039485 297017749786787006639807)
                    ·
                      rfl

theorem cell22_867660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_867660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867660 prefixEnd_867660 := by exact prefixLift 867660
  have htrace : WordTrace (prefixWord ++ tailWord_867660) baseStart_867660 baseEnd_867660 := by
    simpa [prefixWord, tailWord_867660, baseEnd_867660] using wordTrace_append hprefix tailTrace_867660
  have hstable : (prefixWord ++ tailWord_867660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867660).length < 2 ^ (prefixWord ++ tailWord_867660).sum := by decide
  have hdescent : baseEnd_867660 < baseStart_867660 := by decide
  rcases family_descends (prefixWord ++ tailWord_867660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867671 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_867671 : Nat := 118140960795 + 867671 * 2 ^ 59
def prefixEnd_867671 : Nat := 4983230072969 + 3 ^ 40 * 867671 * 2
def baseEnd_867671 : Nat := 297021515311586644614773

theorem tailTrace_867671 : CollatzResearch.WordTrace tailWord_867671 prefixEnd_867671 297021515311586644614773 := by
  unfold tailWord_867671
  simp only [CollatzResearch.WordTrace]
  refine ⟨31646561239583628254186867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21097707493055752169457911 31646561239583628254186867)
  ·
    refine ⟨47469841859375442381280301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31646561239583628254186867 47469841859375442381280301)
    ·
      refine ⟨17801190697265790892980113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47469841859375442381280301 17801190697265790892980113)
      ·
        refine ⟨13350893022949343169735085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17801190697265790892980113 13350893022949343169735085)
        ·
          refine ⟨5006584883606003688650657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13350893022949343169735085 5006584883606003688650657)
          ·
            refine ⟨3754938662704502766487993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006584883606003688650657 3754938662704502766487993)
            ·
              refine ⟨2816203997028377074865995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754938662704502766487993 2816203997028377074865995)
              ·
                refine ⟨4224305995542565612298993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816203997028377074865995 4224305995542565612298993)
                ·
                  refine ⟨3168229496656924209224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224305995542565612298993 3168229496656924209224245)
                  ·
                    refine ⟨297021515311586644614773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3168229496656924209224245 297021515311586644614773)
                    ·
                      rfl

theorem cell22_867671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_867671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867671 prefixEnd_867671 := by exact prefixLift 867671
  have htrace : WordTrace (prefixWord ++ tailWord_867671) baseStart_867671 baseEnd_867671 := by
    simpa [prefixWord, tailWord_867671, baseEnd_867671] using wordTrace_append hprefix tailTrace_867671
  have hstable : (prefixWord ++ tailWord_867671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867671).length < 2 ^ (prefixWord ++ tailWord_867671).sum := by decide
  have hdescent : baseEnd_867671 < baseStart_867671 := by decide
  rcases family_descends (prefixWord ++ tailWord_867671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867769 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 4]
def baseStart_867769 : Nat := 118140960795 + 867769 * 2 ^ 59
def prefixEnd_867769 : Nat := 4983230072969 + 3 ^ 40 * 867769 * 2
def baseEnd_867769 : Nat := 99018354238115685221491

theorem tailTrace_867769 : CollatzResearch.WordTrace tailWord_867769 prefixEnd_867769 99018354238115685221491 := by
  unfold tailWord_867769
  simp only [CollatzResearch.WordTrace]
  refine ⟨31650135593228590991254361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21100090395485727327502907 31650135593228590991254361)
  ·
    refine ⟨23737601694921443243440771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31650135593228590991254361 23737601694921443243440771)
    ·
      refine ⟨35606402542382164865161157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23737601694921443243440771 35606402542382164865161157)
      ·
        refine ⟨6676200476696655912217717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35606402542382164865161157 6676200476696655912217717)
        ·
          refine ⟨625893794690311491770411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6676200476696655912217717 625893794690311491770411)
          ·
            refine ⟨938840692035467237655617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625893794690311491770411 938840692035467237655617)
            ·
              refine ⟨704130519026600428241713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938840692035467237655617 704130519026600428241713)
              ·
                refine ⟨528097889269950321181285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704130519026600428241713 528097889269950321181285)
                ·
                  refine ⟨99018354238115685221491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528097889269950321181285 99018354238115685221491)
                  ·
                    rfl

theorem cell22_867769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_867769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867769 prefixEnd_867769 := by exact prefixLift 867769
  have htrace : WordTrace (prefixWord ++ tailWord_867769) baseStart_867769 baseEnd_867769 := by
    simpa [prefixWord, tailWord_867769, baseEnd_867769] using wordTrace_append hprefix tailTrace_867769
  have hstable : (prefixWord ++ tailWord_867769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867769).length < 2 ^ (prefixWord ++ tailWord_867769).sum := by decide
  have hdescent : baseEnd_867769 < baseStart_867769 := by decide
  rcases family_descends (prefixWord ++ tailWord_867769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867776 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_867776 : Nat := 118140960795 + 867776 * 2 ^ 59
def prefixEnd_867776 : Nat := 4983230072969 + 3 ^ 40 * 867776 * 2
def baseEnd_867776 : Nat := 297057458957401370739451

theorem tailTrace_867776 : CollatzResearch.WordTrace tailWord_867776 prefixEnd_867776 297057458957401370739451 := by
  unfold tailWord_867776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825195452101615593379591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21100260602802154124506121 15825195452101615593379591)
  ·
    refine ⟨23737793178152423390069387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825195452101615593379591 23737793178152423390069387)
    ·
      refine ⟨35606689767228635085104081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23737793178152423390069387 35606689767228635085104081)
      ·
        refine ⟨26705017325421476313828061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35606689767228635085104081 26705017325421476313828061)
        ·
          refine ⟨10014381497033053617685523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26705017325421476313828061 10014381497033053617685523)
          ·
            refine ⟨15021572245549580426528285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014381497033053617685523 15021572245549580426528285)
            ·
              refine ⟨5633089592081092659948107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15021572245549580426528285 5633089592081092659948107)
              ·
                refine ⟨8449634388121638989922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633089592081092659948107 8449634388121638989922161)
                ·
                  refine ⟨6337225791091229242441621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8449634388121638989922161 6337225791091229242441621)
                  ·
                    refine ⟨297057458957401370739451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6337225791091229242441621 297057458957401370739451)
                    ·
                      rfl

theorem cell22_867776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_867776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867776 prefixEnd_867776 := by exact prefixLift 867776
  have htrace : WordTrace (prefixWord ++ tailWord_867776) baseStart_867776 baseEnd_867776 := by
    simpa [prefixWord, tailWord_867776, baseEnd_867776] using wordTrace_append hprefix tailTrace_867776
  have hstable : (prefixWord ++ tailWord_867776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867776).length < 2 ^ (prefixWord ++ tailWord_867776).sum := by decide
  have hdescent : baseEnd_867776 < baseStart_867776 := by decide
  rcases family_descends (prefixWord ++ tailWord_867776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867780 : List Nat := [2, 3, 3, 2, 1, 3, 1, 7]
def baseStart_867780 : Nat := 118140960795 + 867780 * 2 ^ 59
def prefixEnd_867780 : Nat := 4983230072969 + 3 ^ 40 * 867780 * 2
def baseEnd_867780 : Nat := 33006536471016299293271

theorem tailTrace_867780 : CollatzResearch.WordTrace tailWord_867780 prefixEnd_867780 33006536471016299293271 := by
  unfold tailWord_867780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825268398094369934952397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21100357864125826579936529 15825268398094369934952397)
  ·
    refine ⟨5934475649285388725607149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15825268398094369934952397 5934475649285388725607149)
    ·
      refine ⟨2225428368482020772102681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5934475649285388725607149 2225428368482020772102681)
      ·
        refine ⟨1669071276361515579077011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225428368482020772102681 1669071276361515579077011)
        ·
          refine ⟨2503606914542273368615517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669071276361515579077011 2503606914542273368615517)
          ·
            refine ⟨938852592953352513230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2503606914542273368615517 938852592953352513230819)
            ·
              refine ⟨1408278889430028769846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938852592953352513230819 1408278889430028769846229)
              ·
                refine ⟨33006536471016299293271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1408278889430028769846229 33006536471016299293271)
                ·
                  rfl

theorem cell22_867780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_867780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867780 prefixEnd_867780 := by exact prefixLift 867780
  have htrace : WordTrace (prefixWord ++ tailWord_867780) baseStart_867780 baseEnd_867780 := by
    simpa [prefixWord, tailWord_867780, baseEnd_867780] using wordTrace_append hprefix tailTrace_867780
  have hstable : (prefixWord ++ tailWord_867780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867780).length < 2 ^ (prefixWord ++ tailWord_867780).sum := by decide
  have hdescent : baseEnd_867780 < baseStart_867780 := by decide
  rcases family_descends (prefixWord ++ tailWord_867780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867825 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 5]
def baseStart_867825 : Nat := 118140960795 + 867825 * 2 ^ 59
def prefixEnd_867825 : Nat := 4983230072969 + 3 ^ 40 * 867825 * 2
def baseEnd_867825 : Nat := 99024744219593858754767

theorem tailTrace_867825 : CollatzResearch.WordTrace tailWord_867825 prefixEnd_867825 99024744219593858754767 := by
  unfold tailWord_867825
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652178081025712555292929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21101452054017141703528619 31652178081025712555292929)
  ·
    refine ⟨23739133560769284416469697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31652178081025712555292929 23739133560769284416469697)
    ·
      refine ⟨17804350170576963312352273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23739133560769284416469697 17804350170576963312352273)
      ·
        refine ⟨13353262627932722484264205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804350170576963312352273 13353262627932722484264205)
        ·
          refine ⟨5007473485474770931599077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13353262627932722484264205 5007473485474770931599077)
          ·
            refine ⟨938901278526519549674827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5007473485474770931599077 938901278526519549674827)
            ·
              refine ⟨1408351917789779324512241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938901278526519549674827 1408351917789779324512241)
              ·
                refine ⟨1056263938342334493384181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408351917789779324512241 1056263938342334493384181)
                ·
                  refine ⟨99024744219593858754767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056263938342334493384181 99024744219593858754767)
                  ·
                    rfl

theorem cell22_867825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_867825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867825 prefixEnd_867825 := by exact prefixLift 867825
  have htrace : WordTrace (prefixWord ++ tailWord_867825) baseStart_867825 baseEnd_867825 := by
    simpa [prefixWord, tailWord_867825, baseEnd_867825] using wordTrace_append hprefix tailTrace_867825
  have hstable : (prefixWord ++ tailWord_867825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867825).length < 2 ^ (prefixWord ++ tailWord_867825).sum := by decide
  have hdescent : baseEnd_867825 < baseStart_867825 := by decide
  rcases family_descends (prefixWord ++ tailWord_867825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867829 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_867829 : Nat := 118140960795 + 867829 * 2 ^ 59
def prefixEnd_867829 : Nat := 4983230072969 + 3 ^ 40 * 867829 * 2
def baseEnd_867829 : Nat := 297075601940526899164289

theorem tailTrace_867829 : CollatzResearch.WordTrace tailWord_867829 prefixEnd_867829 297075601940526899164289 := by
  unfold tailWord_867829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652323973011221238438541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21101549315340814158959027 31652323973011221238438541)
  ·
    refine ⟨11869621489879207964414453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31652323973011221238438541 11869621489879207964414453)
    ·
      refine ⟨1112777014676175746663855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11869621489879207964414453 1112777014676175746663855)
      ·
        refine ⟨1669165522014263619995783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112777014676175746663855 1669165522014263619995783)
        ·
          refine ⟨2503748283021395429993675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669165522014263619995783 2503748283021395429993675)
          ·
            refine ⟨3755622424532093144990513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503748283021395429993675 3755622424532093144990513)
            ·
              refine ⟨2816716818399069858742885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755622424532093144990513 2816716818399069858742885)
              ·
                refine ⟨528134403449825598514291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2816716818399069858742885 528134403449825598514291)
                ·
                  refine ⟨792201605174738397771437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528134403449825598514291 792201605174738397771437)
                  ·
                    refine ⟨297075601940526899164289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792201605174738397771437 297075601940526899164289)
                    ·
                      rfl

theorem cell22_867829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_867829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867829 prefixEnd_867829 := by exact prefixLift 867829
  have htrace : WordTrace (prefixWord ++ tailWord_867829) baseStart_867829 baseEnd_867829 := by
    simpa [prefixWord, tailWord_867829, baseEnd_867829] using wordTrace_append hprefix tailTrace_867829
  have hstable : (prefixWord ++ tailWord_867829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867829).length < 2 ^ (prefixWord ++ tailWord_867829).sum := by decide
  have hdescent : baseEnd_867829 < baseStart_867829 := by decide
  rcases family_descends (prefixWord ++ tailWord_867829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867868 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_867868 : Nat := 118140960795 + 867868 * 2 ^ 59
def prefixEnd_867868 : Nat := 4983230072969 + 3 ^ 40 * 867868 * 2
def baseEnd_867868 : Nat := 297088952437543797439169

theorem tailTrace_867868 : CollatzResearch.WordTrace tailWord_867868 prefixEnd_867868 297088952437543797439169 := by
  unfold tailWord_867868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826873209934965449554129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21102497613246620599405505 15826873209934965449554129)
  ·
    refine ⟨11870154907451224087165597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15826873209934965449554129 11870154907451224087165597)
    ·
      refine ⟨4451308090294209032687099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11870154907451224087165597 4451308090294209032687099)
      ·
        refine ⟨6676962135441313549030649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451308090294209032687099 6676962135441313549030649)
        ·
          refine ⟨5007721601580985161772987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676962135441313549030649 5007721601580985161772987)
          ·
            refine ⟨7511582402371477742659481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007721601580985161772987 7511582402371477742659481)
            ·
              refine ⟨5633686801778608306994611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7511582402371477742659481 5633686801778608306994611)
              ·
                refine ⟨8450530202667912460491917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633686801778608306994611 8450530202667912460491917)
                ·
                  refine ⟨3168948826000467172684469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8450530202667912460491917 3168948826000467172684469)
                  ·
                    refine ⟨297088952437543797439169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3168948826000467172684469 297088952437543797439169)
                    ·
                      rfl

theorem cell22_867868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_867868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867868 prefixEnd_867868 := by exact prefixLift 867868
  have htrace : WordTrace (prefixWord ++ tailWord_867868) baseStart_867868 baseEnd_867868 := by
    simpa [prefixWord, tailWord_867868, baseEnd_867868] using wordTrace_append hprefix tailTrace_867868
  have hstable : (prefixWord ++ tailWord_867868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867868).length < 2 ^ (prefixWord ++ tailWord_867868).sum := by decide
  have hdescent : baseEnd_867868 < baseStart_867868 := by decide
  rcases family_descends (prefixWord ++ tailWord_867868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867898 : List Nat := [3, 1, 1, 1, 3, 2, 4, 7]
def baseStart_867898 : Nat := 118140960795 + 867898 * 2 ^ 59
def prefixEnd_867898 : Nat := 4983230072969 + 3 ^ 40 * 867898 * 2
def baseEnd_867898 : Nat := 33011024672292635465453

theorem tailTrace_867898 : CollatzResearch.WordTrace tailWord_867898 prefixEnd_867898 33011024672292635465453 := by
  unfold tailWord_867898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913710152440311505675087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21103227073174164015133565 7913710152440311505675087)
  ·
    refine ⟨11870565228660467258512631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7913710152440311505675087 11870565228660467258512631)
    ·
      refine ⟨17805847842990700887768947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11870565228660467258512631 17805847842990700887768947)
      ·
        refine ⟨26708771764486051331653421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17805847842990700887768947 26708771764486051331653421)
        ·
          refine ⟨10015789411682269249370033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26708771764486051331653421 10015789411682269249370033)
          ·
            refine ⟨7511842058761701937027525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10015789411682269249370033 7511842058761701937027525)
            ·
              refine ⟨1408470386017819113192661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7511842058761701937027525 1408470386017819113192661)
              ·
                refine ⟨33011024672292635465453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1408470386017819113192661 33011024672292635465453)
                ·
                  rfl

theorem cell22_867898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_867898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867898 prefixEnd_867898 := by exact prefixLift 867898
  have htrace : WordTrace (prefixWord ++ tailWord_867898) baseStart_867898 baseEnd_867898 := by
    simpa [prefixWord, tailWord_867898, baseEnd_867898] using wordTrace_append hprefix tailTrace_867898
  have hstable : (prefixWord ++ tailWord_867898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867898).length < 2 ^ (prefixWord ++ tailWord_867898).sum := by decide
  have hdescent : baseEnd_867898 < baseStart_867898 := by decide
  rcases family_descends (prefixWord ++ tailWord_867898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867943 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 7]
def baseStart_867943 : Nat := 118140960795 + 867943 * 2 ^ 59
def prefixEnd_867943 : Nat := 4983230072969 + 3 ^ 40 * 867943 * 2
def baseEnd_867943 : Nat := 99038208823422867271313

theorem tailTrace_867943 : CollatzResearch.WordTrace tailWord_867943 prefixEnd_867943 99038208823422867271313 := by
  unfold tailWord_867943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31656481894598218708088483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21104321263065479138725655 31656481894598218708088483)
  ·
    refine ⟨47484722841897328062132725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31656481894598218708088483 47484722841897328062132725)
    ·
      refine ⟨4451692766427874505824943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47484722841897328062132725 4451692766427874505824943)
      ·
        refine ⟨6677539149641811758737415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451692766427874505824943 6677539149641811758737415)
        ·
          refine ⟨10016308724462717638106123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677539149641811758737415 10016308724462717638106123)
          ·
            refine ⟨15024463086694076457159185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016308724462717638106123 15024463086694076457159185)
            ·
              refine ⟨11268347315020557342869389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024463086694076457159185 11268347315020557342869389)
              ·
                refine ⟨4225630243132709003576021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11268347315020557342869389 4225630243132709003576021)
                ·
                  refine ⟨99038208823422867271313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4225630243132709003576021 99038208823422867271313)
                  ·
                    rfl

theorem cell22_867943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_867943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_867943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_867943 prefixEnd_867943 := by exact prefixLift 867943
  have htrace : WordTrace (prefixWord ++ tailWord_867943) baseStart_867943 baseEnd_867943 := by
    simpa [prefixWord, tailWord_867943, baseEnd_867943] using wordTrace_append hprefix tailTrace_867943
  have hstable : (prefixWord ++ tailWord_867943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867943).length < 2 ^ (prefixWord ++ tailWord_867943).sum := by decide
  have hdescent : baseEnd_867943 < baseStart_867943 := by decide
  rcases family_descends (prefixWord ++ tailWord_867943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868050 : List Nat := [3, 2, 2, 2, 2, 1, 10]
def baseStart_868050 : Nat := 118140960795 + 868050 * 2 ^ 59
def prefixEnd_868050 : Nat := 4983230072969 + 3 ^ 40 * 868050 * 2
def baseEnd_868050 : Nat := 11005602028035407014393

theorem tailTrace_868050 : CollatzResearch.WordTrace tailWord_868050 prefixEnd_868050 11005602028035407014393 := by
  unfold tailWord_868050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915096126302643995558401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21106923003473717321489069 7915096126302643995558401)
  ·
    refine ⟨5936322094726982996668801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7915096126302643995558401 5936322094726982996668801)
    ·
      refine ⟨4452241571045237247501601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936322094726982996668801 4452241571045237247501601)
      ·
        refine ⟨3339181178283927935626201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4452241571045237247501601 3339181178283927935626201)
        ·
          refine ⟨2504385883712945951719651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3339181178283927935626201 2504385883712945951719651)
          ·
            refine ⟨3756578825569418927579477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504385883712945951719651 3756578825569418927579477)
            ·
              refine ⟨11005602028035407014393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3756578825569418927579477 11005602028035407014393)
              ·
                rfl

theorem cell22_868050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 10].length) (baseStart_868050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868050 prefixEnd_868050 := by exact prefixLift 868050
  have htrace : WordTrace (prefixWord ++ tailWord_868050) baseStart_868050 baseEnd_868050 := by
    simpa [prefixWord, tailWord_868050, baseEnd_868050] using wordTrace_append hprefix tailTrace_868050
  have hstable : (prefixWord ++ tailWord_868050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868050).length < 2 ^ (prefixWord ++ tailWord_868050).sum := by decide
  have hdescent : baseEnd_868050 < baseStart_868050 := by decide
  rcases family_descends (prefixWord ++ tailWord_868050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868052 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_868052 : Nat := 118140960795 + 868052 * 2 ^ 59
def prefixEnd_868052 : Nat := 4983230072969 + 3 ^ 40 * 868052 * 2
def baseEnd_868052 : Nat := 297151939397828650838605

theorem tailTrace_868052 : CollatzResearch.WordTrace tailWord_868052 prefixEnd_868052 297151939397828650838605 := by
  unfold tailWord_868052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830228725601665161903205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21106971634135553549204273 15830228725601665161903205)
  ·
    refine ⟨2968167886050312217856851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15830228725601665161903205 2968167886050312217856851)
    ·
      refine ⟨4452251829075468326785277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968167886050312217856851 4452251829075468326785277)
      ·
        refine ⟨1669594435903300622544479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4452251829075468326785277 1669594435903300622544479)
        ·
          refine ⟨2504391653854950933816719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669594435903300622544479 2504391653854950933816719)
          ·
            refine ⟨3756587480782426400725079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504391653854950933816719 3756587480782426400725079)
            ·
              refine ⟨5634881221173639601087619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756587480782426400725079 5634881221173639601087619)
              ·
                refine ⟨8452321831760459401631429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634881221173639601087619 8452321831760459401631429)
                ·
                  refine ⟨1584810343455086137805893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8452321831760459401631429 1584810343455086137805893)
                  ·
                    refine ⟨297151939397828650838605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584810343455086137805893 297151939397828650838605)
                    ·
                      rfl

theorem cell22_868052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_868052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868052 prefixEnd_868052 := by exact prefixLift 868052
  have htrace : WordTrace (prefixWord ++ tailWord_868052) baseStart_868052 baseEnd_868052 := by
    simpa [prefixWord, tailWord_868052, baseEnd_868052] using wordTrace_append hprefix tailTrace_868052
  have hstable : (prefixWord ++ tailWord_868052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868052).length < 2 ^ (prefixWord ++ tailWord_868052).sum := by decide
  have hdescent : baseEnd_868052 < baseStart_868052 := by decide
  rcases family_descends (prefixWord ++ tailWord_868052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868067 : List Nat := [1, 1, 1, 7, 2, 1, 2, 7]
def baseStart_868067 : Nat := 118140960795 + 868067 * 2 ^ 59
def prefixEnd_868067 : Nat := 4983230072969 + 3 ^ 40 * 868067 * 2
def baseEnd_868067 : Nat := 33017452689374845745951

theorem tailTrace_868067 : CollatzResearch.WordTrace tailWord_868067 prefixEnd_868067 33017452689374845745951 := by
  unfold tailWord_868067
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661004546148987885602455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107336364099325257068303 31661004546148987885602455)
  ·
    refine ⟨47491506819223481828403683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31661004546148987885602455 47491506819223481828403683)
    ·
      refine ⟨71237260228835222742605525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47491506819223481828403683 71237260228835222742605525)
      ·
        refine ⟨1669623286613325533029817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 71237260228835222742605525 1669623286613325533029817)
        ·
          refine ⟨1252217464959994149772363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669623286613325533029817 1252217464959994149772363)
          ·
            refine ⟨1878326197439991224658545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252217464959994149772363 1878326197439991224658545)
            ·
              refine ⟨1408744648079993418493909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878326197439991224658545 1408744648079993418493909)
              ·
                refine ⟨33017452689374845745951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1408744648079993418493909 33017452689374845745951)
                ·
                  rfl

theorem cell22_868067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 7].length) (baseStart_868067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868067 prefixEnd_868067 := by exact prefixLift 868067
  have htrace : WordTrace (prefixWord ++ tailWord_868067) baseStart_868067 baseEnd_868067 := by
    simpa [prefixWord, tailWord_868067, baseEnd_868067] using wordTrace_append hprefix tailTrace_868067
  have hstable : (prefixWord ++ tailWord_868067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868067).length < 2 ^ (prefixWord ++ tailWord_868067).sum := by decide
  have hdescent : baseEnd_868067 < baseStart_868067 := by decide
  rcases family_descends (prefixWord ++ tailWord_868067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868071 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 2, 3]
def baseStart_868071 : Nat := 118140960795 + 868071 * 2 ^ 59
def prefixEnd_868071 : Nat := 4983230072969 + 3 ^ 40 * 868071 * 2
def baseEnd_868071 : Nat := 297158443486118934613547

theorem tailTrace_868071 : CollatzResearch.WordTrace tailWord_868071 prefixEnd_868071 297158443486118934613547 := by
  unfold tailWord_868071
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661150438134496568748067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107433625422997712498711 31661150438134496568748067)
  ·
    refine ⟨47491725657201744853122101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31661150438134496568748067 47491725657201744853122101)
    ·
      refine ⟨4452349280362663579980197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47491725657201744853122101 4452349280362663579980197)
      ·
        refine ⟨834815490067999421246287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4452349280362663579980197 834815490067999421246287)
        ·
          refine ⟨1252223235101999131869431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834815490067999421246287 1252223235101999131869431)
          ·
            refine ⟨1878334852652998697804147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252223235101999131869431 1878334852652998697804147)
            ·
              refine ⟨2817502278979498046706221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878334852652998697804147 2817502278979498046706221)
              ·
                refine ⟨1056563354617311767514833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817502278979498046706221 1056563354617311767514833)
                ·
                  refine ⟨792422515962983825636125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056563354617311767514833 792422515962983825636125)
                  ·
                    refine ⟨297158443486118934613547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792422515962983825636125 297158443486118934613547)
                    ·
                      rfl

theorem cell22_868071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_868071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868071 prefixEnd_868071 := by exact prefixLift 868071
  have htrace : WordTrace (prefixWord ++ tailWord_868071) baseStart_868071 baseEnd_868071 := by
    simpa [prefixWord, tailWord_868071, baseEnd_868071] using wordTrace_append hprefix tailTrace_868071
  have hstable : (prefixWord ++ tailWord_868071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868071).length < 2 ^ (prefixWord ++ tailWord_868071).sum := by decide
  have hdescent : baseEnd_868071 < baseStart_868071 := by decide
  rcases family_descends (prefixWord ++ tailWord_868071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868082 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_868082 : Nat := 118140960795 + 868082 * 2 ^ 59
def prefixEnd_868082 : Nat := 4983230072969 + 3 ^ 40 * 868082 * 2
def baseEnd_868082 : Nat := 297162209010918572588513

theorem tailTrace_868082 : CollatzResearch.WordTrace tailWord_868082 prefixEnd_868082 297162209010918572588513 := by
  unfold tailWord_868082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915387910273661361849625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21107701094063096964932333 7915387910273661361849625)
  ·
    refine ⟨5936540932705246021387219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7915387910273661361849625 5936540932705246021387219)
    ·
      refine ⟨8904811399057869032080829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936540932705246021387219 8904811399057869032080829)
      ·
        refine ⟨3339304274646700887030311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8904811399057869032080829 3339304274646700887030311)
        ·
          refine ⟨5008956411970051330545467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339304274646700887030311 5008956411970051330545467)
          ·
            refine ⟨7513434617955076995818201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008956411970051330545467 7513434617955076995818201)
            ·
              refine ⟨5635075963466307746863651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513434617955076995818201 5635075963466307746863651)
              ·
                refine ⟨8452613945199461620295477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635075963466307746863651 8452613945199461620295477)
                ·
                  refine ⟨792432557362449526902701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8452613945199461620295477 792432557362449526902701)
                  ·
                    refine ⟨297162209010918572588513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792432557362449526902701 297162209010918572588513)
                    ·
                      rfl

theorem cell22_868082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_868082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868082 prefixEnd_868082 := by exact prefixLift 868082
  have htrace : WordTrace (prefixWord ++ tailWord_868082) baseStart_868082 baseEnd_868082 := by
    simpa [prefixWord, tailWord_868082, baseEnd_868082] using wordTrace_append hprefix tailTrace_868082
  have hstable : (prefixWord ++ tailWord_868082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868082).length < 2 ^ (prefixWord ++ tailWord_868082).sum := by decide
  have hdescent : baseEnd_868082 < baseStart_868082 := by decide
  rcases family_descends (prefixWord ++ tailWord_868082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868084 : List Nat := [2, 6, 1, 1, 1, 1, 2, 8]
def baseStart_868084 : Nat := 118140960795 + 868084 * 2 ^ 59
def prefixEnd_868084 : Nat := 4983230072969 + 3 ^ 40 * 868084 * 2
def baseEnd_868084 : Nat := 33018099294643470448723

theorem tailTrace_868084 : CollatzResearch.WordTrace tailWord_868084 prefixEnd_868084 33018099294643470448723 := by
  unfold tailWord_868084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830812293543699894485653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21107749724724933192647537 15830812293543699894485653)
  ·
    refine ⟨742069326259860932554015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15830812293543699894485653 742069326259860932554015)
    ·
      refine ⟨1113103989389791398831023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742069326259860932554015 1113103989389791398831023)
      ·
        refine ⟨1669655984084687098246535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113103989389791398831023 1669655984084687098246535)
        ·
          refine ⟨2504483976127030647369803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669655984084687098246535 2504483976127030647369803)
          ·
            refine ⟨3756725964190545971054705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504483976127030647369803 3756725964190545971054705)
            ·
              refine ⟨2817544473142909478291029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756725964190545971054705 2817544473142909478291029)
              ·
                refine ⟨33018099294643470448723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2817544473142909478291029 33018099294643470448723)
                ·
                  rfl

theorem cell22_868084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_868084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868084 prefixEnd_868084 := by exact prefixLift 868084
  have htrace : WordTrace (prefixWord ++ tailWord_868084) baseStart_868084 baseEnd_868084 := by
    simpa [prefixWord, tailWord_868084, baseEnd_868084] using wordTrace_append hprefix tailTrace_868084
  have hstable : (prefixWord ++ tailWord_868084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868084).length < 2 ^ (prefixWord ++ tailWord_868084).sum := by decide
  have hdescent : baseEnd_868084 < baseStart_868084 := by decide
  rcases family_descends (prefixWord ++ tailWord_868084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868140 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_868140 : Nat := 118140960795 + 868140 * 2 ^ 59
def prefixEnd_868140 : Nat := 4983230072969 + 3 ^ 40 * 868140 * 2
def baseEnd_868140 : Nat := 99060687865408584879445

theorem tailTrace_868140 : CollatzResearch.WordTrace tailWord_868140 prefixEnd_868140 99060687865408584879445 := by
  unfold tailWord_868140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15831833537442260676504937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21109111383256347568673249 15831833537442260676504937)
  ·
    refine ⟨11873875153081695507378703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15831833537442260676504937 11873875153081695507378703)
    ·
      refine ⟨17810812729622543261068055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11873875153081695507378703 17810812729622543261068055)
      ·
        refine ⟨26716219094433814891602083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17810812729622543261068055 26716219094433814891602083)
        ·
          refine ⟨40074328641650722337403125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26716219094433814891602083 40074328641650722337403125)
          ·
            refine ⟨3756968310154755219131543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40074328641650722337403125 3756968310154755219131543)
            ·
              refine ⟨5635452465232132828697315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756968310154755219131543 5635452465232132828697315)
              ·
                refine ⟨8453178697848199243045973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635452465232132828697315 8453178697848199243045973)
                ·
                  refine ⟨99060687865408584879445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8453178697848199243045973 99060687865408584879445)
                  ·
                    rfl

theorem cell22_868140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_868140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868140 prefixEnd_868140 := by exact prefixLift 868140
  have htrace : WordTrace (prefixWord ++ tailWord_868140) baseStart_868140 baseEnd_868140 := by
    simpa [prefixWord, tailWord_868140, baseEnd_868140] using wordTrace_append hprefix tailTrace_868140
  have hstable : (prefixWord ++ tailWord_868140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868140).length < 2 ^ (prefixWord ++ tailWord_868140).sum := by decide
  have hdescent : baseEnd_868140 < baseStart_868140 := by decide
  rcases family_descends (prefixWord ++ tailWord_868140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868159 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 1, 4]
def baseStart_868159 : Nat := 118140960795 + 868159 * 2 ^ 59
def prefixEnd_868159 : Nat := 4983230072969 + 3 ^ 40 * 868159 * 2
def baseEnd_868159 : Nat := 297188567684516038413277

theorem tailTrace_868159 : CollatzResearch.WordTrace tailWord_868159 prefixEnd_868159 297188567684516038413277 := by
  unfold tailWord_868159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31664360061815687597951531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21109573374543791731967687 31664360061815687597951531)
  ·
    refine ⟨47496540092723531396927297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31664360061815687597951531 47496540092723531396927297)
    ·
      refine ⟨35622405069542648547695473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47496540092723531396927297 35622405069542648547695473)
      ·
        refine ⟨26716803802156986410771605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35622405069542648547695473 26716803802156986410771605)
        ·
          refine ⟨1252350178226108738004919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26716803802156986410771605 1252350178226108738004919)
          ·
            refine ⟨1878525267339163107007379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252350178226108738004919 1878525267339163107007379)
            ·
              refine ⟨2817787901008744660511069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878525267339163107007379 2817787901008744660511069)
              ·
                refine ⟨1056670462878279247691651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817787901008744660511069 1056670462878279247691651)
                ·
                  refine ⟨1585005694317418871537477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056670462878279247691651 1585005694317418871537477)
                  ·
                    refine ⟨297188567684516038413277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1585005694317418871537477 297188567684516038413277)
                    ·
                      rfl

theorem cell22_868159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_868159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868159 prefixEnd_868159 := by exact prefixLift 868159
  have htrace : WordTrace (prefixWord ++ tailWord_868159) baseStart_868159 baseEnd_868159 := by
    simpa [prefixWord, tailWord_868159, baseEnd_868159] using wordTrace_append hprefix tailTrace_868159
  have hstable : (prefixWord ++ tailWord_868159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868159).length < 2 ^ (prefixWord ++ tailWord_868159).sum := by decide
  have hdescent : baseEnd_868159 < baseStart_868159 := by decide
  rcases family_descends (prefixWord ++ tailWord_868159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868185 : List Nat := [1, 2, 1, 2, 2, 3, 2, 9]
def baseStart_868185 : Nat := 118140960795 + 868185 * 2 ^ 59
def prefixEnd_868185 : Nat := 4983230072969 + 3 ^ 40 * 868185 * 2
def baseEnd_868185 : Nat := 33021940890651181918133

theorem tailTrace_868185 : CollatzResearch.WordTrace tailWord_868185 prefixEnd_868185 33021940890651181918133 := by
  unfold tailWord_868185
  simp only [CollatzResearch.WordTrace]
  refine ⟨31665308359721494038398009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21110205573147662692265339 31665308359721494038398009)
  ·
    refine ⟨23748981269791120528798507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31665308359721494038398009 23748981269791120528798507)
    ·
      refine ⟨35623471904686680793197761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748981269791120528798507 35623471904686680793197761)
      ·
        refine ⟨26717603928515010594898321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35623471904686680793197761 26717603928515010594898321)
        ·
          refine ⟨20038202946386257946173741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26717603928515010594898321 20038202946386257946173741)
          ·
            refine ⟨7514326104894846729815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20038202946386257946173741 7514326104894846729815153)
            ·
              refine ⟨5635744578671135047361365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7514326104894846729815153 5635744578671135047361365)
              ·
                refine ⟨33021940890651181918133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5635744578671135047361365 33021940890651181918133)
                ·
                  rfl

theorem cell22_868185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 9].length) (baseStart_868185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868185 prefixEnd_868185 := by exact prefixLift 868185
  have htrace : WordTrace (prefixWord ++ tailWord_868185) baseStart_868185 baseEnd_868185 := by
    simpa [prefixWord, tailWord_868185, baseEnd_868185] using wordTrace_append hprefix tailTrace_868185
  have hstable : (prefixWord ++ tailWord_868185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868185).length < 2 ^ (prefixWord ++ tailWord_868185).sum := by decide
  have hdescent : baseEnd_868185 < baseStart_868185 := by decide
  rcases family_descends (prefixWord ++ tailWord_868185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868215 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_868215 : Nat := 118140960795 + 868215 * 2 ^ 59
def prefixEnd_868215 : Nat := 4983230072969 + 3 ^ 40 * 868215 * 2
def baseEnd_868215 : Nat := 297207737628950559013105

theorem tailTrace_868215 : CollatzResearch.WordTrace tailWord_868215 prefixEnd_868215 297207737628950559013105 := by
  unfold tailWord_868215
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666402549612809161990099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21110935033075206107993399 31666402549612809161990099)
  ·
    refine ⟨47499603824419213742985149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31666402549612809161990099 47499603824419213742985149)
    ·
      refine ⟨17812351434157205153619431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47499603824419213742985149 17812351434157205153619431)
      ·
        refine ⟨26718527151235807730429147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812351434157205153619431 26718527151235807730429147)
        ·
          refine ⟨40077790726853711595643721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26718527151235807730429147 40077790726853711595643721)
          ·
            refine ⟨30058343045140283696732791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40077790726853711595643721 30058343045140283696732791)
            ·
              refine ⟨45087514567710425545099187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30058343045140283696732791 45087514567710425545099187)
              ·
                refine ⟨67631271851565638317648781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45087514567710425545099187 67631271851565638317648781)
                ·
                  refine ⟨25361726944337114369118293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67631271851565638317648781 25361726944337114369118293)
                  ·
                    refine ⟨297207737628950559013105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25361726944337114369118293 297207737628950559013105)
                    ·
                      rfl

theorem cell22_868215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_868215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868215 prefixEnd_868215 := by exact prefixLift 868215
  have htrace : WordTrace (prefixWord ++ tailWord_868215) baseStart_868215 baseEnd_868215 := by
    simpa [prefixWord, tailWord_868215, baseEnd_868215] using wordTrace_append hprefix tailTrace_868215
  have hstable : (prefixWord ++ tailWord_868215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868215).length < 2 ^ (prefixWord ++ tailWord_868215).sum := by decide
  have hdescent : baseEnd_868215 < baseStart_868215 := by decide
  rcases family_descends (prefixWord ++ tailWord_868215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868285 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_868285 : Nat := 118140960795 + 868285 * 2 ^ 59
def prefixEnd_868285 : Nat := 4983230072969 + 3 ^ 40 * 868285 * 2
def baseEnd_868285 : Nat := 297231700059493709762891

theorem tailTrace_868285 : CollatzResearch.WordTrace tailWord_868285 prefixEnd_868285 297231700059493709762891 := by
  unfold tailWord_868285
  simp only [CollatzResearch.WordTrace]
  refine ⟨31668955659359211117038309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21112637106239474078025539 31668955659359211117038309)
  ·
    refine ⟨5937929186129852084444683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31668955659359211117038309 5937929186129852084444683)
    ·
      refine ⟨8906893779194778126667025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937929186129852084444683 8906893779194778126667025)
      ·
        refine ⟨6680170334396083595000269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906893779194778126667025 6680170334396083595000269)
        ·
          refine ⟨2505063875398531348125101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6680170334396083595000269 2505063875398531348125101)
          ·
            refine ⟨939398953274449255546913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2505063875398531348125101 939398953274449255546913)
            ·
              refine ⟨704549214955836941660185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939398953274449255546913 704549214955836941660185)
              ·
                refine ⟨528411911216877706245139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704549214955836941660185 528411911216877706245139)
                ·
                  refine ⟨792617866825316559367709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528411911216877706245139 792617866825316559367709)
                  ·
                    refine ⟨297231700059493709762891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792617866825316559367709 297231700059493709762891)
                    ·
                      rfl

theorem cell22_868285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_868285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868285 prefixEnd_868285 := by exact prefixLift 868285
  have htrace : WordTrace (prefixWord ++ tailWord_868285) baseStart_868285 baseEnd_868285 := by
    simpa [prefixWord, tailWord_868285, baseEnd_868285] using wordTrace_append hprefix tailTrace_868285
  have hstable : (prefixWord ++ tailWord_868285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868285).length < 2 ^ (prefixWord ++ tailWord_868285).sum := by decide
  have hdescent : baseEnd_868285 < baseStart_868285 := by decide
  rcases family_descends (prefixWord ++ tailWord_868285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868309 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 6]
def baseStart_868309 : Nat := 118140960795 + 868309 * 2 ^ 59
def prefixEnd_868309 : Nat := 4983230072969 + 3 ^ 40 * 868309 * 2
def baseEnd_868309 : Nat := 99079971916655215720939

theorem tailTrace_868309 : CollatzResearch.WordTrace tailWord_868309 prefixEnd_868309 99079971916655215720939 := by
  unfold tailWord_868309
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669831011272263215911981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21113220674181508810607987 31669831011272263215911981)
  ·
    refine ⟨11876186629227098705966993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31669831011272263215911981 11876186629227098705966993)
    ·
      refine ⟨8907139971920324029475245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11876186629227098705966993 8907139971920324029475245)
      ·
        refine ⟨3340177489470121511053217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8907139971920324029475245 3340177489470121511053217)
        ·
          refine ⟨2505133117102591133289913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340177489470121511053217 2505133117102591133289913)
          ·
            refine ⟨1878849837826943349967435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505133117102591133289913 1878849837826943349967435)
            ·
              refine ⟨2818274756740415024951153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878849837826943349967435 2818274756740415024951153)
              ·
                refine ⟨2113706067555311268713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818274756740415024951153 2113706067555311268713365)
                ·
                  refine ⟨99079971916655215720939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2113706067555311268713365 99079971916655215720939)
                  ·
                    rfl

theorem cell22_868309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_868309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868309 prefixEnd_868309 := by exact prefixLift 868309
  have htrace : WordTrace (prefixWord ++ tailWord_868309) baseStart_868309 baseEnd_868309 := by
    simpa [prefixWord, tailWord_868309, baseEnd_868309] using wordTrace_append hprefix tailTrace_868309
  have hstable : (prefixWord ++ tailWord_868309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868309).length < 2 ^ (prefixWord ++ tailWord_868309).sum := by decide
  have hdescent : baseEnd_868309 < baseStart_868309 := by decide
  rcases family_descends (prefixWord ++ tailWord_868309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868324 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_868324 : Nat := 118140960795 + 868324 * 2 ^ 59
def prefixEnd_868324 : Nat := 4983230072969 + 3 ^ 40 * 868324 * 2
def baseEnd_868324 : Nat := 297245050556510608037771

theorem tailTrace_868324 : CollatzResearch.WordTrace tailWord_868324 prefixEnd_868324 297245050556510608037771 := by
  unfold tailWord_868324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835189053108960388854013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21113585404145280518472017 15835189053108960388854013)
  ·
    refine ⟨5938195894915860145820255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15835189053108960388854013 5938195894915860145820255)
    ·
      refine ⟨8907293842373790218730383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938195894915860145820255 8907293842373790218730383)
      ·
        refine ⟨13360940763560685328095575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907293842373790218730383 13360940763560685328095575)
        ·
          refine ⟨20041411145341027992143363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360940763560685328095575 20041411145341027992143363)
          ·
            refine ⟨30062116718011541988215045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20041411145341027992143363 30062116718011541988215045)
            ·
              refine ⟨5636646884627164122790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30062116718011541988215045 5636646884627164122790321)
              ·
                refine ⟨4227485163470373092092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636646884627164122790321 4227485163470373092092741)
                ·
                  refine ⟨792653468150694954767389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4227485163470373092092741 792653468150694954767389)
                  ·
                    refine ⟨297245050556510608037771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792653468150694954767389 297245050556510608037771)
                    ·
                      rfl

theorem cell22_868324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_868324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868324 prefixEnd_868324 := by exact prefixLift 868324
  have htrace : WordTrace (prefixWord ++ tailWord_868324) baseStart_868324 baseEnd_868324 := by
    simpa [prefixWord, tailWord_868324, baseEnd_868324] using wordTrace_append hprefix tailTrace_868324
  have hstable : (prefixWord ++ tailWord_868324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868324).length < 2 ^ (prefixWord ++ tailWord_868324).sum := by decide
  have hdescent : baseEnd_868324 < baseStart_868324 := by decide
  rcases family_descends (prefixWord ++ tailWord_868324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868416 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_868416 : Nat := 118140960795 + 868416 * 2 ^ 59
def prefixEnd_868416 : Nat := 4983230072969 + 3 ^ 40 * 868416 * 2
def baseEnd_868416 : Nat := 99092181345551011579163

theorem tailTrace_868416 : CollatzResearch.WordTrace tailWord_868416 prefixEnd_868416 99092181345551011579163 := by
  unfold tailWord_868416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836866810942310245028551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21115822414589746993371401 15836866810942310245028551)
  ·
    refine ⟨23755300216413465367542827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15836866810942310245028551 23755300216413465367542827)
    ·
      refine ⟨35632950324620198051314241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23755300216413465367542827 35632950324620198051314241)
      ·
        refine ⟨26724712743465148538485681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35632950324620198051314241 26724712743465148538485681)
        ·
          refine ⟨20043534557598861403864261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26724712743465148538485681 20043534557598861403864261)
          ·
            refine ⟨3758162729549786513224549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20043534557598861403864261 3758162729549786513224549)
            ·
              refine ⟨704655511790584971229603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3758162729549786513224549 704655511790584971229603)
              ·
                refine ⟨1056983267685877456844405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704655511790584971229603 1056983267685877456844405)
                ·
                  refine ⟨99092181345551011579163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056983267685877456844405 99092181345551011579163)
                  ·
                    rfl

theorem cell22_868416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_868416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868416 prefixEnd_868416 := by exact prefixLift 868416
  have htrace : WordTrace (prefixWord ++ tailWord_868416) baseStart_868416 baseEnd_868416 := by
    simpa [prefixWord, tailWord_868416, baseEnd_868416] using wordTrace_append hprefix tailTrace_868416
  have hstable : (prefixWord ++ tailWord_868416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868416).length < 2 ^ (prefixWord ++ tailWord_868416).sum := by decide
  have hdescent : baseEnd_868416 < baseStart_868416 := by decide
  rcases family_descends (prefixWord ++ tailWord_868416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868476 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_868476 : Nat := 118140960795 + 868476 * 2 ^ 59
def prefixEnd_868476 : Nat := 4983230072969 + 3 ^ 40 * 868476 * 2
def baseEnd_868476 : Nat := 297297083262832878237305

theorem tailTrace_868476 : CollatzResearch.WordTrace tailWord_868476 prefixEnd_868476 297297083262832878237305 := by
  unfold tailWord_868476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15837961000833625368620641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21117281334444833824827521 15837961000833625368620641)
  ·
    refine ⟨11878470750625219026465481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15837961000833625368620641 11878470750625219026465481)
    ·
      refine ⟨8908853062968914269849111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11878470750625219026465481 8908853062968914269849111)
      ·
        refine ⟨13363279594453371404773667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908853062968914269849111 13363279594453371404773667)
        ·
          refine ⟨20044919391680057107160501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13363279594453371404773667 20044919391680057107160501)
          ·
            refine ⟨1879211192970005353796297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20044919391680057107160501 1879211192970005353796297)
            ·
              refine ⟨1409408394727504015347223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879211192970005353796297 1409408394727504015347223)
              ·
                refine ⟨2114112592091256023020835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409408394727504015347223 2114112592091256023020835)
                ·
                  refine ⟨3171168888136884034531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114112592091256023020835 3171168888136884034531253)
                  ·
                    refine ⟨297297083262832878237305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3171168888136884034531253 297297083262832878237305)
                    ·
                      rfl

theorem cell22_868476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_868476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868476 prefixEnd_868476 := by exact prefixLift 868476
  have htrace : WordTrace (prefixWord ++ tailWord_868476) baseStart_868476 baseEnd_868476 := by
    simpa [prefixWord, tailWord_868476, baseEnd_868476] using wordTrace_append hprefix tailTrace_868476
  have hstable : (prefixWord ++ tailWord_868476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868476).length < 2 ^ (prefixWord ++ tailWord_868476).sum := by decide
  have hdescent : baseEnd_868476 < baseStart_868476 := by decide
  rcases family_descends (prefixWord ++ tailWord_868476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868506 : List Nat := [3, 1, 1, 5, 2, 1, 9]
def baseStart_868506 : Nat := 118140960795 + 868506 * 2 ^ 59
def prefixEnd_868506 : Nat := 4983230072969 + 3 ^ 40 * 868506 * 2
def baseEnd_868506 : Nat := 11011383439848992592119

theorem tailTrace_868506 : CollatzResearch.WordTrace tailWord_868506 prefixEnd_868506 11011383439848992592119 := by
  unfold tailWord_868506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919254047889641465208343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21118010794372377240555581 7919254047889641465208343)
  ·
    refine ⟨11878881071834462197812515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7919254047889641465208343 11878881071834462197812515)
    ·
      refine ⟨17818321607751693296718773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878881071834462197812515 17818321607751693296718773)
      ·
        refine ⟨1670467650726721246567385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17818321607751693296718773 1670467650726721246567385)
        ·
          refine ⟨1252850738045040934925539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670467650726721246567385 1252850738045040934925539)
          ·
            refine ⟨1879276107067561402388309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252850738045040934925539 1879276107067561402388309)
            ·
              refine ⟨11011383439848992592119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1879276107067561402388309 11011383439848992592119)
              ·
                rfl

theorem cell22_868506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 9].length) (baseStart_868506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868506 prefixEnd_868506 := by exact prefixLift 868506
  have htrace : WordTrace (prefixWord ++ tailWord_868506) baseStart_868506 baseEnd_868506 := by
    simpa [prefixWord, tailWord_868506, baseEnd_868506] using wordTrace_append hprefix tailTrace_868506
  have hstable : (prefixWord ++ tailWord_868506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868506).length < 2 ^ (prefixWord ++ tailWord_868506).sum := by decide
  have hdescent : baseEnd_868506 < baseStart_868506 := by decide
  rcases family_descends (prefixWord ++ tailWord_868506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868510 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_868510 : Nat := 118140960795 + 868510 * 2 ^ 59
def prefixEnd_868510 : Nat := 4983230072969 + 3 ^ 40 * 868510 * 2
def baseEnd_868510 : Nat := 297308722157668122887201

theorem tailTrace_868510 : CollatzResearch.WordTrace tailWord_868510 prefixEnd_868510 297308722157668122887201 := by
  unfold tailWord_868510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959645260443009317997373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21118108055696049695985989 3959645260443009317997373)
  ·
    refine ⟨1484866972666128494249015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3959645260443009317997373 1484866972666128494249015)
    ·
      refine ⟨2227300458999192741373523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484866972666128494249015 2227300458999192741373523)
      ·
        refine ⟨3340950688498789112060285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227300458999192741373523 3340950688498789112060285)
        ·
          refine ⟨1252856508187045917022607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3340950688498789112060285 1252856508187045917022607)
          ·
            refine ⟨1879284762280568875533911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252856508187045917022607 1879284762280568875533911)
            ·
              refine ⟨2818927143420853313300867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879284762280568875533911 2818927143420853313300867)
              ·
                refine ⟨4228390715131279969951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818927143420853313300867 4228390715131279969951301)
                ·
                  refine ⟨792823259087114994365869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4228390715131279969951301 792823259087114994365869)
                  ·
                    refine ⟨297308722157668122887201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792823259087114994365869 297308722157668122887201)
                    ·
                      rfl

theorem cell22_868510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_868510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868510 prefixEnd_868510 := by exact prefixLift 868510
  have htrace : WordTrace (prefixWord ++ tailWord_868510) baseStart_868510 baseEnd_868510 := by
    simpa [prefixWord, tailWord_868510, baseEnd_868510] using wordTrace_append hprefix tailTrace_868510
  have hstable : (prefixWord ++ tailWord_868510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868510).length < 2 ^ (prefixWord ++ tailWord_868510).sum := by decide
  have hdescent : baseEnd_868510 < baseStart_868510 := by decide
  rcases family_descends (prefixWord ++ tailWord_868510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868540 : List Nat := [2, 2, 2, 3, 4, 1, 2, 6]
def baseStart_868540 : Nat := 118140960795 + 868540 * 2 ^ 59
def prefixEnd_868540 : Nat := 4983230072969 + 3 ^ 40 * 868540 * 2
def baseEnd_868540 : Nat := 33035443530084227181901

theorem tailTrace_868540 : CollatzResearch.WordTrace tailWord_868540 prefixEnd_868540 33035443530084227181901 := by
  unfold tailWord_868540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839128136717694833785537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21118837515623593111714049 15839128136717694833785537)
  ·
    refine ⟨11879346102538271125339153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15839128136717694833785537 11879346102538271125339153)
    ·
      refine ⟨8909509576903703344004365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11879346102538271125339153 8909509576903703344004365)
      ·
        refine ⟨3341066091338888754001637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8909509576903703344004365 3341066091338888754001637)
        ·
          refine ⟨626449892126041641375307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3341066091338888754001637 626449892126041641375307)
          ·
            refine ⟨939674838189062462062961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626449892126041641375307 939674838189062462062961)
            ·
              refine ⟨704756128641796846547221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939674838189062462062961 704756128641796846547221)
              ·
                refine ⟨33035443530084227181901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 704756128641796846547221 33035443530084227181901)
                ·
                  rfl

theorem cell22_868540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_868540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868540 prefixEnd_868540 := by exact prefixLift 868540
  have htrace : WordTrace (prefixWord ++ tailWord_868540) baseStart_868540 baseEnd_868540 := by
    simpa [prefixWord, tailWord_868540, baseEnd_868540] using wordTrace_append hprefix tailTrace_868540
  have hstable : (prefixWord ++ tailWord_868540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868540).length < 2 ^ (prefixWord ++ tailWord_868540).sum := by decide
  have hdescent : baseEnd_868540 < baseStart_868540 := by decide
  rcases family_descends (prefixWord ++ tailWord_868540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868549 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_868549 : Nat := 118140960795 + 868549 * 2 ^ 59
def prefixEnd_868549 : Nat := 4983230072969 + 3 ^ 40 * 868549 * 2
def baseEnd_868549 : Nat := 297322072654685021162081

theorem tailTrace_868549 : CollatzResearch.WordTrace tailWord_868549 prefixEnd_868549 297322072654685021162081 := by
  unfold tailWord_868549
  simp only [CollatzResearch.WordTrace]
  refine ⟨31678584530402784204648701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21119056353601856136432467 31678584530402784204648701)
  ·
    refine ⟨11879469198901044076743263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31678584530402784204648701 11879469198901044076743263)
    ·
      refine ⟨17819203798351566115114895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879469198901044076743263 17819203798351566115114895)
      ·
        refine ⟨26728805697527349172672343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17819203798351566115114895 26728805697527349172672343)
        ·
          refine ⟨40093208546291023759008515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26728805697527349172672343 40093208546291023759008515)
          ·
            refine ⟨60139812819436535638512773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40093208546291023759008515 60139812819436535638512773)
            ·
              refine ⟨11276214903644350432221145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60139812819436535638512773 11276214903644350432221145)
              ·
                refine ⟨8457161177733262824165859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11276214903644350432221145 8457161177733262824165859)
                ·
                  refine ⟨12685741766599894236248789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457161177733262824165859 12685741766599894236248789)
                  ·
                    refine ⟨297322072654685021162081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12685741766599894236248789 297322072654685021162081)
                    ·
                      rfl

theorem cell22_868549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_868549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868549 prefixEnd_868549 := by exact prefixLift 868549
  have htrace : WordTrace (prefixWord ++ tailWord_868549) baseStart_868549 baseEnd_868549 := by
    simpa [prefixWord, tailWord_868549, baseEnd_868549] using wordTrace_append hprefix tailTrace_868549
  have hstable : (prefixWord ++ tailWord_868549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868549).length < 2 ^ (prefixWord ++ tailWord_868549).sum := by decide
  have hdescent : baseEnd_868549 < baseStart_868549 := by decide
  rcases family_descends (prefixWord ++ tailWord_868549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868578 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_868578 : Nat := 118140960795 + 868578 * 2 ^ 59
def prefixEnd_868578 : Nat := 4983230072969 + 3 ^ 40 * 868578 * 2
def baseEnd_868578 : Nat := 297331999947338612186993

theorem tailTrace_868578 : CollatzResearch.WordTrace tailWord_868578 prefixEnd_868578 297331999947338612186993 := by
  unfold tailWord_868578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919910561824430539363597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21119761498198481438302925 7919910561824430539363597)
  ·
    refine ⟨2969966460684161452261349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7919910561824430539363597 2969966460684161452261349)
    ·
      refine ⟨556868711378280272299003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2969966460684161452261349 556868711378280272299003)
      ·
        refine ⟨835303067067420408448505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556868711378280272299003 835303067067420408448505)
        ·
          refine ⟨626477300300565306336379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835303067067420408448505 626477300300565306336379)
          ·
            refine ⟨939715950450847959504569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626477300300565306336379 939715950450847959504569)
            ·
              refine ⟨704786962838135969628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939715950450847959504569 704786962838135969628427)
              ·
                refine ⟨1057180444257203954442641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704786962838135969628427 1057180444257203954442641)
                ·
                  refine ⟨792885333192902965831981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057180444257203954442641 792885333192902965831981)
                  ·
                    refine ⟨297331999947338612186993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792885333192902965831981 297331999947338612186993)
                    ·
                      rfl

theorem cell22_868578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_868578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868578 prefixEnd_868578 := by exact prefixLift 868578
  have htrace : WordTrace (prefixWord ++ tailWord_868578) baseStart_868578 baseEnd_868578 := by
    simpa [prefixWord, tailWord_868578, baseEnd_868578] using wordTrace_append hprefix tailTrace_868578
  have hstable : (prefixWord ++ tailWord_868578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868578).length < 2 ^ (prefixWord ++ tailWord_868578).sum := by decide
  have hdescent : baseEnd_868578 < baseStart_868578 := by decide
  rcases family_descends (prefixWord ++ tailWord_868578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868611 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_868611 : Nat := 118140960795 + 868611 * 2 ^ 59
def prefixEnd_868611 : Nat := 4983230072969 + 3 ^ 40 * 868611 * 2
def baseEnd_868611 : Nat := 297343296521737526111891

theorem tailTrace_868611 : CollatzResearch.WordTrace tailWord_868611 prefixEnd_868611 297343296521737526111891 := by
  unfold tailWord_868611
  simp only [CollatzResearch.WordTrace]
  refine ⟨31680845856178168793405687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21120563904118779195603791 31680845856178168793405687)
  ·
    refine ⟨47521268784267253190108531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31680845856178168793405687 47521268784267253190108531)
    ·
      refine ⟨71281903176400879785162797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47521268784267253190108531 71281903176400879785162797)
      ·
        refine ⟨26730713691150329919436049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71281903176400879785162797 26730713691150329919436049)
        ·
          refine ⟨20048035268362747439577037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26730713691150329919436049 20048035268362747439577037)
          ·
            refine ⟨7518013225636030289841389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20048035268362747439577037 7518013225636030289841389)
            ·
              refine ⟨2819254959613511358690521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518013225636030289841389 2819254959613511358690521)
              ·
                refine ⟨2114441219710133519017891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819254959613511358690521 2114441219710133519017891)
                ·
                  refine ⟨3171661829565200278526837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114441219710133519017891 3171661829565200278526837)
                  ·
                    refine ⟨297343296521737526111891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3171661829565200278526837 297343296521737526111891)
                    ·
                      rfl

theorem cell22_868611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_868611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868611 prefixEnd_868611 := by exact prefixLift 868611
  have htrace : WordTrace (prefixWord ++ tailWord_868611) baseStart_868611 baseEnd_868611 := by
    simpa [prefixWord, tailWord_868611, baseEnd_868611] using wordTrace_append hprefix tailTrace_868611
  have hstable : (prefixWord ++ tailWord_868611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868611).length < 2 ^ (prefixWord ++ tailWord_868611).sum := by decide
  have hdescent : baseEnd_868611 < baseStart_868611 := by decide
  rcases family_descends (prefixWord ++ tailWord_868611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868641 : List Nat := [1, 2, 3, 2, 1, 1, 5, 7]
def baseStart_868641 : Nat := 118140960795 + 868641 * 2 ^ 59
def prefixEnd_868641 : Nat := 4983230072969 + 3 ^ 40 * 868641 * 2
def baseEnd_868641 : Nat := 33039285126091938651311

theorem tailTrace_868641 : CollatzResearch.WordTrace tailWord_868641 prefixEnd_868641 33039285126091938651311 := by
  unfold tailWord_868641
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681940046069483916997777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121293364046322611331851 31681940046069483916997777)
  ·
    refine ⟨23761455034552112937748333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31681940046069483916997777 23761455034552112937748333)
    ·
      refine ⟨8910545637957042351655625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23761455034552112937748333 8910545637957042351655625)
      ·
        refine ⟨6682909228467781763741719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8910545637957042351655625 6682909228467781763741719)
        ·
          refine ⟨10024363842701672645612579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682909228467781763741719 10024363842701672645612579)
          ·
            refine ⟨15036545764052508968418869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024363842701672645612579 15036545764052508968418869)
            ·
              refine ⟨1409676165379922715789269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15036545764052508968418869 1409676165379922715789269)
              ·
                refine ⟨33039285126091938651311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1409676165379922715789269 33039285126091938651311)
                ·
                  rfl

theorem cell22_868641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 7].length) (baseStart_868641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868641 prefixEnd_868641 := by exact prefixLift 868641
  have htrace : WordTrace (prefixWord ++ tailWord_868641) baseStart_868641 baseEnd_868641 := by
    simpa [prefixWord, tailWord_868641, baseEnd_868641] using wordTrace_append hprefix tailTrace_868641
  have hstable : (prefixWord ++ tailWord_868641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868641).length < 2 ^ (prefixWord ++ tailWord_868641).sum := by decide
  have hdescent : baseEnd_868641 < baseStart_868641 := by decide
  rcases family_descends (prefixWord ++ tailWord_868641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868647 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 6]
def baseStart_868647 : Nat := 118140960795 + 868647 * 2 ^ 59
def prefixEnd_868647 : Nat := 4983230072969 + 3 ^ 40 * 868647 * 2
def baseEnd_868647 : Nat := 99118540019148477403927

theorem tailTrace_868647 : CollatzResearch.WordTrace tailWord_868647 prefixEnd_868647 99118540019148477403927 := by
  unfold tailWord_868647
  simp only [CollatzResearch.WordTrace]
  refine ⟨31682158884047746941716195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121439256031831294477463 31682158884047746941716195)
  ·
    refine ⟨47523238326071620412574293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31682158884047746941716195 47523238326071620412574293)
    ·
      refine ⟨556912949133651801709855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 47523238326071620412574293 556912949133651801709855)
      ·
        refine ⟨835369423700477702564783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556912949133651801709855 835369423700477702564783)
        ·
          refine ⟨1253054135550716553847175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835369423700477702564783 1253054135550716553847175)
          ·
            refine ⟨1879581203326074830770763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253054135550716553847175 1879581203326074830770763)
            ·
              refine ⟨2819371804989112246156145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879581203326074830770763 2819371804989112246156145)
              ·
                refine ⟨2114528853741834184617109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819371804989112246156145 2114528853741834184617109)
                ·
                  refine ⟨99118540019148477403927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2114528853741834184617109 99118540019148477403927)
                  ·
                    rfl

theorem cell22_868647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 6].length) (baseStart_868647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868647 prefixEnd_868647 := by exact prefixLift 868647
  have htrace : WordTrace (prefixWord ++ tailWord_868647) baseStart_868647 baseEnd_868647 := by
    simpa [prefixWord, tailWord_868647, baseEnd_868647] using wordTrace_append hprefix tailTrace_868647
  have hstable : (prefixWord ++ tailWord_868647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868647).length < 2 ^ (prefixWord ++ tailWord_868647).sum := by decide
  have hdescent : baseEnd_868647 < baseStart_868647 := by decide
  rcases family_descends (prefixWord ++ tailWord_868647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868660 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_868660 : Nat := 118140960795 + 868660 * 2 ^ 59
def prefixEnd_868660 : Nat := 4983230072969 + 3 ^ 40 * 868660 * 2
def baseEnd_868660 : Nat := 297360070223117731636741

theorem tailTrace_868660 : CollatzResearch.WordTrace tailWord_868660 prefixEnd_868660 297360070223117731636741 := by
  unfold tailWord_868660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841316516500325080969717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21121755355333766774626289 15841316516500325080969717)
  ·
    refine ⟨1485123423421905476340911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15841316516500325080969717 1485123423421905476340911)
    ·
      refine ⟨2227685135132858214511367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485123423421905476340911 2227685135132858214511367)
      ·
        refine ⟨3341527702699287321767051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227685135132858214511367 3341527702699287321767051)
        ·
          refine ⟨5012291554048930982650577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341527702699287321767051 5012291554048930982650577)
          ·
            refine ⟨3759218665536698236987933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5012291554048930982650577 3759218665536698236987933)
            ·
              refine ⟨1409706999576261838870475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3759218665536698236987933 1409706999576261838870475)
              ·
                refine ⟨2114560499364392758305713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409706999576261838870475 2114560499364392758305713)
                ·
                  refine ⟨1585920374523294568729285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114560499364392758305713 1585920374523294568729285)
                  ·
                    refine ⟨297360070223117731636741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1585920374523294568729285 297360070223117731636741)
                    ·
                      rfl

theorem cell22_868660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_868660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868660 prefixEnd_868660 := by exact prefixLift 868660
  have htrace : WordTrace (prefixWord ++ tailWord_868660) baseStart_868660 baseEnd_868660 := by
    simpa [prefixWord, tailWord_868660, baseEnd_868660] using wordTrace_append hprefix tailTrace_868660
  have hstable : (prefixWord ++ tailWord_868660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868660).length < 2 ^ (prefixWord ++ tailWord_868660).sum := by decide
  have hdescent : baseEnd_868660 < baseStart_868660 := by decide
  rcases family_descends (prefixWord ++ tailWord_868660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868748 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_868748 : Nat := 118140960795 + 868748 * 2 ^ 59
def prefixEnd_868748 : Nat := 4983230072969 + 3 ^ 40 * 868748 * 2
def baseEnd_868748 : Nat := 99130064807171611812157

theorem tailTrace_868748 : CollatzResearch.WordTrace tailWord_868748 prefixEnd_868748 99130064807171611812157 := by
  unfold tailWord_868748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842921328340920595571449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21123895104454560794095265 15842921328340920595571449)
  ·
    refine ⟨11882190996255690446678587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15842921328340920595571449 11882190996255690446678587)
    ·
      refine ⟨17823286494383535670017881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882190996255690446678587 17823286494383535670017881)
      ·
        refine ⟨13367464870787651752513411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17823286494383535670017881 13367464870787651752513411)
        ·
          refine ⟨20051197306181477628770117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367464870787651752513411 20051197306181477628770117)
          ·
            refine ⟨3759599494909027055394397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20051197306181477628770117 3759599494909027055394397)
            ·
              refine ⟨1409849810590885145772899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3759599494909027055394397 1409849810590885145772899)
              ·
                refine ⟨2114774715886327718659349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409849810590885145772899 2114774715886327718659349)
                ·
                  refine ⟨99130064807171611812157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2114774715886327718659349 99130064807171611812157)
                  ·
                    rfl

theorem cell22_868748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_868748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868748 prefixEnd_868748 := by exact prefixLift 868748
  have htrace : WordTrace (prefixWord ++ tailWord_868748) baseStart_868748 baseEnd_868748 := by
    simpa [prefixWord, tailWord_868748, baseEnd_868748] using wordTrace_append hprefix tailTrace_868748
  have hstable : (prefixWord ++ tailWord_868748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868748).length < 2 ^ (prefixWord ++ tailWord_868748).sum := by decide
  have hdescent : baseEnd_868748 < baseStart_868748 := by decide
  rcases family_descends (prefixWord ++ tailWord_868748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868797 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_868797 : Nat := 118140960795 + 868797 * 2 ^ 59
def prefixEnd_868797 : Nat := 4983230072969 + 3 ^ 40 * 868797 * 2
def baseEnd_868797 : Nat := 297406968122895040961321

theorem tailTrace_868797 : CollatzResearch.WordTrace tailWord_868797 prefixEnd_868797 297406968122895040961321 := by
  unfold tailWord_868797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687629833504322559676645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21125086555669548373117763 31687629833504322559676645)
  ·
    refine ⟨5941430593782060479939371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31687629833504322559676645 5941430593782060479939371)
    ·
      refine ⟨8912145890673090719909057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5941430593782060479939371 8912145890673090719909057)
      ·
        refine ⟨6684109418004818039931793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912145890673090719909057 6684109418004818039931793)
        ·
          refine ⟨5013082063503613529948845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684109418004818039931793 5013082063503613529948845)
          ·
            refine ⟨1879905773813855073730817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5013082063503613529948845 1879905773813855073730817)
            ·
              refine ⟨1409929330360391305298113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879905773813855073730817 1409929330360391305298113)
              ·
                refine ⟨1057446997770293478973585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409929330360391305298113 1057446997770293478973585)
                ·
                  refine ⟨793085248327720109230189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057446997770293478973585 793085248327720109230189)
                  ·
                    refine ⟨297406968122895040961321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793085248327720109230189 297406968122895040961321)
                    ·
                      rfl

theorem cell22_868797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_868797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868797 prefixEnd_868797 := by exact prefixLift 868797
  have htrace : WordTrace (prefixWord ++ tailWord_868797) baseStart_868797 baseEnd_868797 := by
    simpa [prefixWord, tailWord_868797, baseEnd_868797] using wordTrace_append hprefix tailTrace_868797
  have hstable : (prefixWord ++ tailWord_868797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868797).length < 2 ^ (prefixWord ++ tailWord_868797).sum := by decide
  have hdescent : baseEnd_868797 < baseStart_868797 := by decide
  rcases family_descends (prefixWord ++ tailWord_868797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868825 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_868825 : Nat := 118140960795 + 868825 * 2 ^ 59
def prefixEnd_868825 : Nat := 4983230072969 + 3 ^ 40 * 868825 * 2
def baseEnd_868825 : Nat := 297416553095112301261235

theorem tailTrace_868825 : CollatzResearch.WordTrace tailWord_868825 prefixEnd_868825 297416553095112301261235 := by
  unfold tailWord_868825
  simp only [CollatzResearch.WordTrace]
  refine ⟨31688651077402883341695929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21125767384935255561130619 31688651077402883341695929)
  ·
    refine ⟨23766488308052162506271947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31688651077402883341695929 23766488308052162506271947)
    ·
      refine ⟨35649732462078243759407921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23766488308052162506271947 35649732462078243759407921)
      ·
        refine ⟨26737299346558682819555941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35649732462078243759407921 26737299346558682819555941)
        ·
          refine ⟨5013243627479753028666739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26737299346558682819555941 5013243627479753028666739)
          ·
            refine ⟨7519865441219629543000109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013243627479753028666739 7519865441219629543000109)
            ·
              refine ⟨2819949540457361078625041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7519865441219629543000109 2819949540457361078625041)
              ·
                refine ⟨2114962155343020808968781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819949540457361078625041 2114962155343020808968781)
                ·
                  refine ⟨793110808253632803363293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2114962155343020808968781 793110808253632803363293)
                  ·
                    refine ⟨297416553095112301261235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793110808253632803363293 297416553095112301261235)
                    ·
                      rfl

theorem cell22_868825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_868825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868825 prefixEnd_868825 := by exact prefixLift 868825
  have htrace : WordTrace (prefixWord ++ tailWord_868825) baseStart_868825 baseEnd_868825 := by
    simpa [prefixWord, tailWord_868825, baseEnd_868825] using wordTrace_append hprefix tailTrace_868825
  have hstable : (prefixWord ++ tailWord_868825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868825).length < 2 ^ (prefixWord ++ tailWord_868825).sum := by decide
  have hdescent : baseEnd_868825 < baseStart_868825 := by decide
  rcases family_descends (prefixWord ++ tailWord_868825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868883 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 6]
def baseStart_868883 : Nat := 118140960795 + 868883 * 2 ^ 59
def prefixEnd_868883 : Nat := 4983230072969 + 3 ^ 40 * 868883 * 2
def baseEnd_868883 : Nat := 99145469226806494437019

theorem tailTrace_868883 : CollatzResearch.WordTrace tailWord_868883 prefixEnd_868883 99145469226806494437019 := by
  unfold tailWord_868883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31690766511192759247307303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21127177674128506164871535 31690766511192759247307303)
  ·
    refine ⟨47536149766789138870960955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31690766511192759247307303 47536149766789138870960955)
    ·
      refine ⟨71304224650183708306441433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47536149766789138870960955 71304224650183708306441433)
      ·
        refine ⟨53478168487637781229831075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71304224650183708306441433 53478168487637781229831075)
        ·
          refine ⟨80217252731456671844746613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53478168487637781229831075 80217252731456671844746613)
          ·
            refine ⟨7520367443574062985444995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80217252731456671844746613 7520367443574062985444995)
            ·
              refine ⟨11280551165361094478167493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520367443574062985444995 11280551165361094478167493)
              ·
                refine ⟨2115103343505205214656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11280551165361094478167493 2115103343505205214656405)
                ·
                  refine ⟨99145469226806494437019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2115103343505205214656405 99145469226806494437019)
                  ·
                    rfl

theorem cell22_868883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_868883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868883 prefixEnd_868883 := by exact prefixLift 868883
  have htrace : WordTrace (prefixWord ++ tailWord_868883) baseStart_868883 baseEnd_868883 := by
    simpa [prefixWord, tailWord_868883, baseEnd_868883] using wordTrace_append hprefix tailTrace_868883
  have hstable : (prefixWord ++ tailWord_868883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868883).length < 2 ^ (prefixWord ++ tailWord_868883).sum := by decide
  have hdescent : baseEnd_868883 < baseStart_868883 := by decide
  rcases family_descends (prefixWord ++ tailWord_868883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868915 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 4, 3]
def baseStart_868915 : Nat := 118140960795 + 868915 * 2 ^ 59
def prefixEnd_868915 : Nat := 4983230072969 + 3 ^ 40 * 868915 * 2
def baseEnd_868915 : Nat := 297447361934382066510959

theorem tailTrace_868915 : CollatzResearch.WordTrace tailWord_868915 prefixEnd_868915 297447361934382066510959 := by
  unfold tailWord_868915
  simp only [CollatzResearch.WordTrace]
  refine ⟨31691933647076828712472199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21127955764717885808314799 31691933647076828712472199)
  ·
    refine ⟨47537900470615243068708299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31691933647076828712472199 47537900470615243068708299)
    ·
      refine ⟨71306850705922864603062449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47537900470615243068708299 71306850705922864603062449)
      ·
        refine ⟨53480138029442148452296837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71306850705922864603062449 53480138029442148452296837)
        ·
          refine ⟨10027525880520402834805657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53480138029442148452296837 10027525880520402834805657)
          ·
            refine ⟨7520644410390302126104243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10027525880520402834805657 7520644410390302126104243)
            ·
              refine ⟨11280966615585453189156365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520644410390302126104243 11280966615585453189156365)
              ·
                refine ⟨4230362480844544945933637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11280966615585453189156365 4230362480844544945933637)
                ·
                  refine ⟨793192965158352177362557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4230362480844544945933637 793192965158352177362557)
                  ·
                    refine ⟨297447361934382066510959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793192965158352177362557 297447361934382066510959)
                    ·
                      rfl

theorem cell22_868915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].length) (baseStart_868915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868915 prefixEnd_868915 := by exact prefixLift 868915
  have htrace : WordTrace (prefixWord ++ tailWord_868915) baseStart_868915 baseEnd_868915 := by
    simpa [prefixWord, tailWord_868915, baseEnd_868915] using wordTrace_append hprefix tailTrace_868915
  have hstable : (prefixWord ++ tailWord_868915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868915).length < 2 ^ (prefixWord ++ tailWord_868915).sum := by decide
  have hdescent : baseEnd_868915 < baseStart_868915 := by decide
  rcases family_descends (prefixWord ++ tailWord_868915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868928 : List Nat := [2, 1, 1, 2, 2, 2, 3, 9]
def baseStart_868928 : Nat := 118140960795 + 868928 * 2 ^ 59
def prefixEnd_868928 : Nat := 4983230072969 + 3 ^ 40 * 868928 * 2
def baseEnd_868928 : Nat := 33050201344450485103991

theorem tailTrace_868928 : CollatzResearch.WordTrace tailWord_868928 prefixEnd_868928 33050201344450485103991 := by
  unfold tailWord_868928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846203898014865966347719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21128271864019821288463625 15846203898014865966347719)
  ·
    refine ⟨23769305847022298949521579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846203898014865966347719 23769305847022298949521579)
    ·
      refine ⟨35653958770533448424282369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23769305847022298949521579 35653958770533448424282369)
      ·
        refine ⟨26740469077900086318211777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35653958770533448424282369 26740469077900086318211777)
        ·
          refine ⟨20055351808425064738658833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26740469077900086318211777 20055351808425064738658833)
          ·
            refine ⟨15041513856318798553994125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20055351808425064738658833 15041513856318798553994125)
            ·
              refine ⟨5640567696119549457747797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15041513856318798553994125 5640567696119549457747797)
              ·
                refine ⟨33050201344450485103991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5640567696119549457747797 33050201344450485103991)
                ·
                  rfl

theorem cell22_868928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_868928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868928 prefixEnd_868928 := by exact prefixLift 868928
  have htrace : WordTrace (prefixWord ++ tailWord_868928) baseStart_868928 baseEnd_868928 := by
    simpa [prefixWord, tailWord_868928, baseEnd_868928] using wordTrace_append hprefix tailTrace_868928
  have hstable : (prefixWord ++ tailWord_868928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868928).length < 2 ^ (prefixWord ++ tailWord_868928).sum := by decide
  have hdescent : baseEnd_868928 < baseStart_868928 := by decide
  rcases family_descends (prefixWord ++ tailWord_868928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868943 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_868943 : Nat := 118140960795 + 868943 * 2 ^ 59
def prefixEnd_868943 : Nat := 4983230072969 + 3 ^ 40 * 868943 * 2
def baseEnd_868943 : Nat := 297456946906599326810873

theorem tailTrace_868943 : CollatzResearch.WordTrace tailWord_868943 prefixEnd_868943 297456946906599326810873 := by
  unfold tailWord_868943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692954890975389494491483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21128636593983592996327655 31692954890975389494491483)
  ·
    refine ⟨47539432336463084241737225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31692954890975389494491483 47539432336463084241737225)
    ·
      refine ⟨35654574252347313181302919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47539432336463084241737225 35654574252347313181302919)
      ·
        refine ⟨53481861378520969771954379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35654574252347313181302919 53481861378520969771954379)
        ·
          refine ⟨80222792067781454657931569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53481861378520969771954379 80222792067781454657931569)
          ·
            refine ⟨60167094050836090993448677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80222792067781454657931569 60167094050836090993448677)
            ·
              refine ⟨11281330134531767061271627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60167094050836090993448677 11281330134531767061271627)
              ·
                refine ⟨16921995201797650591907441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281330134531767061271627 16921995201797650591907441)
                ·
                  refine ⟨12691496401348237943930581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16921995201797650591907441 12691496401348237943930581)
                  ·
                    refine ⟨297456946906599326810873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12691496401348237943930581 297456946906599326810873)
                    ·
                      rfl

theorem cell22_868943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_868943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868943 prefixEnd_868943 := by exact prefixLift 868943
  have htrace : WordTrace (prefixWord ++ tailWord_868943) baseStart_868943 baseEnd_868943 := by
    simpa [prefixWord, tailWord_868943, baseEnd_868943] using wordTrace_append hprefix tailTrace_868943
  have hstable : (prefixWord ++ tailWord_868943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868943).length < 2 ^ (prefixWord ++ tailWord_868943).sum := by decide
  have hdescent : baseEnd_868943 < baseStart_868943 := by decide
  rcases family_descends (prefixWord ++ tailWord_868943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868962 : List Nat := [3, 3, 2, 3, 1, 10]
def baseStart_868962 : Nat := 118140960795 + 868962 * 2 ^ 59
def prefixEnd_868962 : Nat := 4983230072969 + 3 ^ 40 * 868962 * 2
def baseEnd_868962 : Nat := 3672388283887526056615

theorem tailTrace_868962 : CollatzResearch.WordTrace tailWord_868962 prefixEnd_868962 3672388283887526056615 := by
  unfold tailWord_868962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923411969476638934858285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21129098585271037159622093 7923411969476638934858285)
  ·
    refine ⟨2971279488553739600571857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7923411969476638934858285 2971279488553739600571857)
    ·
      refine ⟨2228459616415304700428893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2971279488553739600571857 2228459616415304700428893)
      ·
        refine ⟨835672356155739262660835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228459616415304700428893 835672356155739262660835)
        ·
          refine ⟨1253508534233608893991253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835672356155739262660835 1253508534233608893991253)
          ·
            refine ⟨3672388283887526056615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1253508534233608893991253 3672388283887526056615)
            ·
              rfl

theorem cell22_868962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 10].length) (baseStart_868962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868962 prefixEnd_868962 := by exact prefixLift 868962
  have htrace : WordTrace (prefixWord ++ tailWord_868962) baseStart_868962 baseEnd_868962 := by
    simpa [prefixWord, tailWord_868962, baseEnd_868962] using wordTrace_append hprefix tailTrace_868962
  have hstable : (prefixWord ++ tailWord_868962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868962).length < 2 ^ (prefixWord ++ tailWord_868962).sum := by decide
  have hdescent : baseEnd_868962 < baseStart_868962 := by decide
  rcases family_descends (prefixWord ++ tailWord_868962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868968 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_868968 : Nat := 118140960795 + 868968 * 2 ^ 59
def prefixEnd_868968 : Nat := 4983230072969 + 3 ^ 40 * 868968 * 2
def baseEnd_868968 : Nat := 99155168305835864978599

theorem tailTrace_868968 : CollatzResearch.WordTrace tailWord_868968 prefixEnd_868968 99155168305835864978599 := by
  unfold tailWord_868968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846933357942409382075779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21129244477256545842767705 15846933357942409382075779)
  ·
    refine ⟨23770400036913614073113669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846933357942409382075779 23770400036913614073113669)
    ·
      refine ⟨4456950006921302638708813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23770400036913614073113669 4456950006921302638708813)
      ·
        refine ⟨1671356252595488489515805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4456950006921302638708813 1671356252595488489515805)
        ·
          refine ⟨626758594723308183568427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1671356252595488489515805 626758594723308183568427)
          ·
            refine ⟨940137892084962275352641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626758594723308183568427 940137892084962275352641)
            ·
              refine ⟨705103419063721706514481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940137892084962275352641 705103419063721706514481)
              ·
                refine ⟨528827564297791279885861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705103419063721706514481 528827564297791279885861)
                ·
                  refine ⟨99155168305835864978599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528827564297791279885861 99155168305835864978599)
                  ·
                    rfl

theorem cell22_868968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_868968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_868968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_868968 prefixEnd_868968 := by exact prefixLift 868968
  have htrace : WordTrace (prefixWord ++ tailWord_868968) baseStart_868968 baseEnd_868968 := by
    simpa [prefixWord, tailWord_868968, baseEnd_868968] using wordTrace_append hprefix tailTrace_868968
  have hstable : (prefixWord ++ tailWord_868968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868968).length < 2 ^ (prefixWord ++ tailWord_868968).sum := by decide
  have hdescent : baseEnd_868968 < baseStart_868968 := by decide
  rcases family_descends (prefixWord ++ tailWord_868968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869022 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_869022 : Nat := 118140960795 + 869022 * 2 ^ 59
def prefixEnd_869022 : Nat := 4983230072969 + 3 ^ 40 * 869022 * 2
def baseEnd_869022 : Nat := 297483990221069454085631

theorem tailTrace_869022 : CollatzResearch.WordTrace tailWord_869022 prefixEnd_869022 297483990221069454085631 := by
  unfold tailWord_869022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961979532211148248327165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21130557505126123991078213 3961979532211148248327165)
  ·
    refine ⟨1485742324579180593122687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3961979532211148248327165 1485742324579180593122687)
    ·
      refine ⟨2228613486868770889684031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485742324579180593122687 2228613486868770889684031)
      ·
        refine ⟨3342920230303156334526047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228613486868770889684031 3342920230303156334526047)
        ·
          refine ⟨5014380345454734501789071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342920230303156334526047 5014380345454734501789071)
          ·
            refine ⟨7521570518182101752683607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014380345454734501789071 7521570518182101752683607)
            ·
              refine ⟨11282355777273152629025411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521570518182101752683607 11282355777273152629025411)
              ·
                refine ⟨16923533665909728943538117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282355777273152629025411 16923533665909728943538117)
                ·
                  refine ⟨3173162562358074176913397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16923533665909728943538117 3173162562358074176913397)
                  ·
                    refine ⟨297483990221069454085631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3173162562358074176913397 297483990221069454085631)
                    ·
                      rfl

theorem cell22_869022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_869022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869022 prefixEnd_869022 := by exact prefixLift 869022
  have htrace : WordTrace (prefixWord ++ tailWord_869022) baseStart_869022 baseEnd_869022 := by
    simpa [prefixWord, tailWord_869022, baseEnd_869022] using wordTrace_append hprefix tailTrace_869022
  have hstable : (prefixWord ++ tailWord_869022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869022).length < 2 ^ (prefixWord ++ tailWord_869022).sum := by decide
  have hdescent : baseEnd_869022 < baseStart_869022 := by decide
  rcases family_descends (prefixWord ++ tailWord_869022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869024 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_869024 : Nat := 118140960795 + 869024 * 2 ^ 59
def prefixEnd_869024 : Nat := 4983230072969 + 3 ^ 40 * 869024 * 2
def baseEnd_869024 : Nat := 99161558287314038511875

theorem tailTrace_869024 : CollatzResearch.WordTrace tailWord_869024 prefixEnd_869024 99161558287314038511875 := by
  unfold tailWord_869024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847954601840970164095063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21130606135787960218793417 15847954601840970164095063)
  ·
    refine ⟨23771931902761455246142595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15847954601840970164095063 23771931902761455246142595)
    ·
      refine ⟨35657897854142182869213893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23771931902761455246142595 35657897854142182869213893)
      ·
        refine ⟨6685855847651659287977605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35657897854142182869213893 6685855847651659287977605)
        ·
          refine ⟨1253597971434686116495801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6685855847651659287977605 1253597971434686116495801)
          ·
            refine ⟨940198478576014587371851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253597971434686116495801 940198478576014587371851)
            ·
              refine ⟨1410297717864021881057777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940198478576014587371851 1410297717864021881057777)
              ·
                refine ⟨1057723288398016410793333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410297717864021881057777 1057723288398016410793333)
                ·
                  refine ⟨99161558287314038511875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057723288398016410793333 99161558287314038511875)
                  ·
                    rfl

theorem cell22_869024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_869024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869024 prefixEnd_869024 := by exact prefixLift 869024
  have htrace : WordTrace (prefixWord ++ tailWord_869024) baseStart_869024 baseEnd_869024 := by
    simpa [prefixWord, tailWord_869024, baseEnd_869024] using wordTrace_append hprefix tailTrace_869024
  have hstable : (prefixWord ++ tailWord_869024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869024).length < 2 ^ (prefixWord ++ tailWord_869024).sum := by decide
  have hdescent : baseEnd_869024 < baseStart_869024 := by decide
  rcases family_descends (prefixWord ++ tailWord_869024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869041 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 5]
def baseStart_869041 : Nat := 118140960795 + 869041 * 2 ^ 59
def prefixEnd_869041 : Nat := 4983230072969 + 3 ^ 40 * 869041 * 2
def baseEnd_869041 : Nat := 99163498103119912620191

theorem tailTrace_869041 : CollatzResearch.WordTrace tailWord_869041 prefixEnd_869041 99163498103119912620191 := by
  unfold tailWord_869041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31696529244620352231558977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21131019496413568154372651 31696529244620352231558977)
  ·
    refine ⟨23772396933465264173669233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31696529244620352231558977 23772396933465264173669233)
    ·
      refine ⟨17829297700098948130251925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23772396933465264173669233 17829297700098948130251925)
      ·
        refine ⟨835748329692138193605559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17829297700098948130251925 835748329692138193605559)
        ·
          refine ⟨1253622494538207290408339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835748329692138193605559 1253622494538207290408339)
          ·
            refine ⟨1880433741807310935612509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253622494538207290408339 1880433741807310935612509)
            ·
              refine ⟨705162653177741600854691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880433741807310935612509 705162653177741600854691)
              ·
                refine ⟨1057743979766612401282037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705162653177741600854691 1057743979766612401282037)
                ·
                  refine ⟨99163498103119912620191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057743979766612401282037 99163498103119912620191)
                  ·
                    rfl

theorem cell22_869041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_869041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869041 prefixEnd_869041 := by exact prefixLift 869041
  have htrace : WordTrace (prefixWord ++ tailWord_869041) baseStart_869041 baseEnd_869041 := by
    simpa [prefixWord, tailWord_869041, baseEnd_869041] using wordTrace_append hprefix tailTrace_869041
  have hstable : (prefixWord ++ tailWord_869041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869041).length < 2 ^ (prefixWord ++ tailWord_869041).sum := by decide
  have hdescent : baseEnd_869041 < baseStart_869041 := by decide
  rcases family_descends (prefixWord ++ tailWord_869041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
