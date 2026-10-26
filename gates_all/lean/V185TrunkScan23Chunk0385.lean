import V185TrunkScan23Chunk0384

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2276044 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2276044 : Nat := 118140960795 + 2276044 * 2 ^ 59
def prefixEnd_2276044 : Nat := 4983230072969 + 3 ^ 40 * 2276044 * 2
def baseEnd_2276044 : Nat := 1168704562781998201082671

theorem tailTrace_2276044 : CollatzResearch.WordTrace tailWord_2276044 prefixEnd_2276044 1168704562781998201082671 := by
  unfold tailWord_2276044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41507072283144390106469593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55342763044192520141959457 41507072283144390106469593)
  ·
    refine ⟨31130304212358292579852195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41507072283144390106469593 31130304212358292579852195)
    ·
      refine ⟨46695456318537438869778293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31130304212358292579852195 46695456318537438869778293)
      ·
        refine ⟨4377699029862884894041715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46695456318537438869778293 4377699029862884894041715)
        ·
          refine ⟨6566548544794327341062573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377699029862884894041715 6566548544794327341062573)
          ·
            refine ⟨2462455704297872752898465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6566548544794327341062573 2462455704297872752898465)
            ·
              refine ⟨1846841778223404564673849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462455704297872752898465 1846841778223404564673849)
              ·
                refine ⟨1385131333667553423505387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846841778223404564673849 1385131333667553423505387)
                ·
                  refine ⟨2077697000501330135258081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385131333667553423505387 2077697000501330135258081)
                  ·
                    refine ⟨1558272750375997601443561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2077697000501330135258081 1558272750375997601443561)
                    ·
                      refine ⟨1168704562781998201082671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558272750375997601443561 1168704562781998201082671)
                      ·
                        rfl

theorem cell23_2276044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2276044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276044 prefixEnd_2276044 := by exact prefixLift 2276044
  have htrace : WordTrace (prefixWord ++ tailWord_2276044) baseStart_2276044 baseEnd_2276044 := by
    simpa [prefixWord, tailWord_2276044, baseEnd_2276044] using wordTrace_append hprefix tailTrace_2276044
  have hstable : (prefixWord ++ tailWord_2276044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276044).length < 2 ^ (prefixWord ++ tailWord_2276044).sum := by decide
  have hdescent : baseEnd_2276044 < baseStart_2276044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276060 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2276060 : Nat := 118140960795 + 2276060 * 2 ^ 59
def prefixEnd_2276060 : Nat := 4983230072969 + 3 ^ 40 * 2276060 * 2
def baseEnd_2276060 : Nat := 1168712778472470138482597

theorem tailTrace_2276060 : CollatzResearch.WordTrace tailWord_2276060 prefixEnd_2276060 1168712778472470138482597 := by
  unfold tailWord_2276060
  simp only [CollatzResearch.WordTrace]
  refine ⟨41507364067115407472760817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55343152089487209963681089 41507364067115407472760817)
  ·
    refine ⟨31130523050336555604570613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41507364067115407472760817 31130523050336555604570613)
    ·
      refine ⟨2918486535969052087928495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31130523050336555604570613 2918486535969052087928495)
      ·
        refine ⟨4377729803953578131892743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918486535969052087928495 4377729803953578131892743)
        ·
          refine ⟨6566594705930367197839115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377729803953578131892743 6566594705930367197839115)
          ·
            refine ⟨9849892058895550796758673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566594705930367197839115 9849892058895550796758673)
            ·
              refine ⟨7387419044171663097569005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849892058895550796758673 7387419044171663097569005)
              ·
                refine ⟨2770282141564373661588377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7387419044171663097569005 2770282141564373661588377)
                ·
                  refine ⟨2077711606173280246191283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770282141564373661588377 2077711606173280246191283)
                  ·
                    refine ⟨3116567409259920369286925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2077711606173280246191283 3116567409259920369286925)
                    ·
                      refine ⟨1168712778472470138482597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116567409259920369286925 1168712778472470138482597)
                      ·
                        rfl

theorem cell23_2276060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2276060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276060 prefixEnd_2276060 := by exact prefixLift 2276060
  have htrace : WordTrace (prefixWord ++ tailWord_2276060) baseStart_2276060 baseEnd_2276060 := by
    simpa [prefixWord, tailWord_2276060, baseEnd_2276060] using wordTrace_append hprefix tailTrace_2276060
  have hstable : (prefixWord ++ tailWord_2276060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276060).length < 2 ^ (prefixWord ++ tailWord_2276060).sum := by decide
  have hdescent : baseEnd_2276060 < baseStart_2276060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276106 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_2276106 : Nat := 118140960795 + 2276106 * 2 ^ 59
def prefixEnd_2276106 : Nat := 4983230072969 + 3 ^ 40 * 2276106 * 2
def baseEnd_2276106 : Nat := 129859599842508550945265

theorem tailTrace_2276106 : CollatzResearch.WordTrace tailWord_2276106 prefixEnd_2276106 129859599842508550945265 := by
  unfold tailWord_2276106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20754101473016041200424043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55344270594709443201130781 20754101473016041200424043)
  ·
    refine ⟨31131152209524061800636065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20754101473016041200424043 31131152209524061800636065)
    ·
      refine ⟨23348364157143046350477049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31131152209524061800636065 23348364157143046350477049)
      ·
        refine ⟨17511273117857284762857787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23348364157143046350477049 17511273117857284762857787)
        ·
          refine ⟨26266909676785927144286681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17511273117857284762857787 26266909676785927144286681)
          ·
            refine ⟨19700182257589445358215011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26266909676785927144286681 19700182257589445358215011)
            ·
              refine ⟨29550273386384168037322517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19700182257589445358215011 29550273386384168037322517)
              ·
                refine ⟨1385169064986757876749493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29550273386384168037322517 1385169064986757876749493)
                ·
                  refine ⟨129859599842508550945265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385169064986757876749493 129859599842508550945265)
                  ·
                    rfl

theorem cell23_2276106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_2276106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276106 prefixEnd_2276106 := by exact prefixLift 2276106
  have htrace : WordTrace (prefixWord ++ tailWord_2276106) baseStart_2276106 baseEnd_2276106 := by
    simpa [prefixWord, tailWord_2276106, baseEnd_2276106] using wordTrace_append hprefix tailTrace_2276106
  have hstable : (prefixWord ++ tailWord_2276106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276106).length < 2 ^ (prefixWord ++ tailWord_2276106).sum := by decide
  have hdescent : baseEnd_2276106 < baseStart_2276106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276136 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2276136 : Nat := 118140960795 + 2276136 * 2 ^ 59
def prefixEnd_2276136 : Nat := 4983230072969 + 3 ^ 40 * 2276136 * 2
def baseEnd_2276136 : Nat := 389583934334070613710749

theorem tailTrace_2276136 : CollatzResearch.WordTrace tailWord_2276136 prefixEnd_2276136 389583934334070613710749 := by
  unfold tailWord_2276136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41508750040977739962644131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55345000054636986616858841 41508750040977739962644131)
  ·
    refine ⟨62263125061466609943966197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41508750040977739962644131 62263125061466609943966197)
    ·
      refine ⟨5837167974512494682246831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62263125061466609943966197 5837167974512494682246831)
      ·
        refine ⟨8755751961768742023370247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837167974512494682246831 8755751961768742023370247)
        ·
          refine ⟨13133627942653113035055371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755751961768742023370247 13133627942653113035055371)
          ·
            refine ⟨19700441913979669552583057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13133627942653113035055371 19700441913979669552583057)
            ·
              refine ⟨14775331435484752164437293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19700441913979669552583057 14775331435484752164437293)
              ·
                refine ⟨5540749288306782061663985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14775331435484752164437293 5540749288306782061663985)
                ·
                  refine ⟨4155561966230086546247989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540749288306782061663985 4155561966230086546247989)
                  ·
                    refine ⟨389583934334070613710749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4155561966230086546247989 389583934334070613710749)
                    ·
                      rfl

theorem cell23_2276136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2276136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276136 prefixEnd_2276136 := by exact prefixLift 2276136
  have htrace : WordTrace (prefixWord ++ tailWord_2276136) baseStart_2276136 baseEnd_2276136 := by
    simpa [prefixWord, tailWord_2276136, baseEnd_2276136] using wordTrace_append hprefix tailTrace_2276136
  have hstable : (prefixWord ++ tailWord_2276136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276136).length < 2 ^ (prefixWord ++ tailWord_2276136).sum := by decide
  have hdescent : baseEnd_2276136 < baseStart_2276136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276213 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 6]
def baseStart_2276213 : Nat := 118140960795 + 2276213 * 2 ^ 59
def prefixEnd_2276213 : Nat := 4983230072969 + 3 ^ 40 * 2276213 * 2
def baseEnd_2276213 : Nat := 129865704556956448874377

theorem tailTrace_2276213 : CollatzResearch.WordTrace tailWord_2276213 prefixEnd_2276213 129865704556956448874377 := by
  unfold tailWord_2276213
  simp only [CollatzResearch.WordTrace]
  refine ⟨83020308502676522075841293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55346872335117681383894195 83020308502676522075841293)
  ·
    refine ⟨31132615688503695778440485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83020308502676522075841293 31132615688503695778440485)
    ·
      refine ⟨5837365441594442958457591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31132615688503695778440485 5837365441594442958457591)
      ·
        refine ⟨8756048162391664437686387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837365441594442958457591 8756048162391664437686387)
        ·
          refine ⟨13134072243587496656529581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756048162391664437686387 13134072243587496656529581)
          ·
            refine ⟨4925277091345311246198593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13134072243587496656529581 4925277091345311246198593)
            ·
              refine ⟨3693957818508983434648945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925277091345311246198593 3693957818508983434648945)
              ·
                refine ⟨2770468363881737575986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693957818508983434648945 2770468363881737575986709)
                ·
                  refine ⟨129865704556956448874377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2770468363881737575986709 129865704556956448874377)
                  ·
                    rfl

theorem cell23_2276213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_2276213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276213 prefixEnd_2276213 := by exact prefixLift 2276213
  have htrace : WordTrace (prefixWord ++ tailWord_2276213) baseStart_2276213 baseEnd_2276213 := by
    simpa [prefixWord, tailWord_2276213, baseEnd_2276213] using wordTrace_append hprefix tailTrace_2276213
  have hstable : (prefixWord ++ tailWord_2276213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276213).length < 2 ^ (prefixWord ++ tailWord_2276213).sum := by decide
  have hdescent : baseEnd_2276213 < baseStart_2276213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276217 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 1, 4]
def baseStart_2276217 : Nat := 118140960795 + 2276217 * 2 ^ 59
def prefixEnd_2276217 : Nat := 4983230072969 + 3 ^ 40 * 2276217 * 2
def baseEnd_2276217 : Nat := 389597798311742008073125

theorem tailTrace_2276217 : CollatzResearch.WordTrace tailWord_2276217 prefixEnd_2276217 389597798311742008073125 := by
  unfold tailWord_2276217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83020454394662030758986905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55346969596441353839324603 83020454394662030758986905)
  ·
    refine ⟨62265340795996523069240179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83020454394662030758986905 62265340795996523069240179)
    ·
      refine ⟨93398011193994784603860269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62265340795996523069240179 93398011193994784603860269)
      ·
        refine ⟨35024254197748044226447601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93398011193994784603860269 35024254197748044226447601)
        ·
          refine ⟨26268190648311033169835701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35024254197748044226447601 26268190648311033169835701)
          ·
            refine ⟨2462642873279159359672097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26268190648311033169835701 2462642873279159359672097)
            ·
              refine ⟨1846982154959369519754073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462642873279159359672097 1846982154959369519754073)
              ·
                refine ⟨1385236616219527139815555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846982154959369519754073 1385236616219527139815555)
                ·
                  refine ⟨2077854924329290709723333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385236616219527139815555 2077854924329290709723333)
                  ·
                    refine ⟨389597798311742008073125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077854924329290709723333 389597798311742008073125)
                    ·
                      rfl

theorem cell23_2276217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_2276217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276217 prefixEnd_2276217 := by exact prefixLift 2276217
  have htrace : WordTrace (prefixWord ++ tailWord_2276217) baseStart_2276217 baseEnd_2276217 := by
    simpa [prefixWord, tailWord_2276217, baseEnd_2276217] using wordTrace_append hprefix tailTrace_2276217
  have hstable : (prefixWord ++ tailWord_2276217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276217).length < 2 ^ (prefixWord ++ tailWord_2276217).sum := by decide
  have hdescent : baseEnd_2276217 < baseStart_2276217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276250 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2276250 : Nat := 118140960795 + 2276250 * 2 ^ 59
def prefixEnd_2276250 : Nat := 4983230072969 + 3 ^ 40 * 2276250 * 2
def baseEnd_2276250 : Nat := 1168810339796824395106723

theorem tailTrace_2276250 : CollatzResearch.WordTrace tailWord_2276250 prefixEnd_2276250 1168810339796824395106723 := by
  unfold tailWord_2276250
  simp only [CollatzResearch.WordTrace]
  refine ⟨20755414500885619348734551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55347772002361651596625469 20755414500885619348734551)
  ·
    refine ⟨31133121751328429023101827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20755414500885619348734551 31133121751328429023101827)
    ·
      refine ⟨46699682626992643534652741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31133121751328429023101827 46699682626992643534652741)
      ·
        refine ⟨8756190492561120662747389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46699682626992643534652741 8756190492561120662747389)
        ·
          refine ⟨3283571434710420248530271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8756190492561120662747389 3283571434710420248530271)
          ·
            refine ⟨4925357152065630372795407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283571434710420248530271 4925357152065630372795407)
            ·
              refine ⟨7388035728098445559193111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925357152065630372795407 7388035728098445559193111)
              ·
                refine ⟨11082053592147668338789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388035728098445559193111 11082053592147668338789667)
                ·
                  refine ⟨16623080388221502508184501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082053592147668338789667 16623080388221502508184501)
                  ·
                    refine ⟨1558413786395765860142297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16623080388221502508184501 1558413786395765860142297)
                    ·
                      refine ⟨1168810339796824395106723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558413786395765860142297 1168810339796824395106723)
                      ·
                        rfl

theorem cell23_2276250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2276250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276250 prefixEnd_2276250 := by exact prefixLift 2276250
  have htrace : WordTrace (prefixWord ++ tailWord_2276250) baseStart_2276250 baseEnd_2276250 := by
    simpa [prefixWord, tailWord_2276250, baseEnd_2276250] using wordTrace_append hprefix tailTrace_2276250
  have hstable : (prefixWord ++ tailWord_2276250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276250).length < 2 ^ (prefixWord ++ tailWord_2276250).sum := by decide
  have hdescent : baseEnd_2276250 < baseStart_2276250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276256 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_2276256 : Nat := 118140960795 + 2276256 * 2 ^ 59
def prefixEnd_2276256 : Nat := 4983230072969 + 3 ^ 40 * 2276256 * 2
def baseEnd_2276256 : Nat := 389604473560250457210565

theorem tailTrace_2276256 : CollatzResearch.WordTrace tailWord_2276256 prefixEnd_2276256 389604473560250457210565 := by
  unfold tailWord_2276256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41510938420760370209828311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55347917894347160279771081 41510938420760370209828311)
  ·
    refine ⟨62266407631140555314742467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41510938420760370209828311 62266407631140555314742467)
    ·
      refine ⟨93399611446710832972113701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62266407631140555314742467 93399611446710832972113701)
      ·
        refine ⟨17512427146258281182271319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93399611446710832972113701 17512427146258281182271319)
        ·
          refine ⟨26268640719387421773406979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17512427146258281182271319 26268640719387421773406979)
          ·
            refine ⟨39402961079081132660110469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26268640719387421773406979 39402961079081132660110469)
            ·
              refine ⟨7388055202327712373770713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39402961079081132660110469 7388055202327712373770713)
              ·
                refine ⟨5541041401745784280328035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7388055202327712373770713 5541041401745784280328035)
                ·
                  refine ⟨8311562102618676420492053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541041401745784280328035 8311562102618676420492053)
                  ·
                    refine ⟨389604473560250457210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8311562102618676420492053 389604473560250457210565)
                    ·
                      rfl

theorem cell23_2276256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_2276256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276256 prefixEnd_2276256 := by exact prefixLift 2276256
  have htrace : WordTrace (prefixWord ++ tailWord_2276256) baseStart_2276256 baseEnd_2276256 := by
    simpa [prefixWord, tailWord_2276256, baseEnd_2276256] using wordTrace_append hprefix tailTrace_2276256
  have hstable : (prefixWord ++ tailWord_2276256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276256).length < 2 ^ (prefixWord ++ tailWord_2276256).sum := by decide
  have hdescent : baseEnd_2276256 < baseStart_2276256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276257 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2276257 : Nat := 118140960795 + 2276257 * 2 ^ 59
def prefixEnd_2276257 : Nat := 4983230072969 + 3 ^ 40 * 2276257 * 2
def baseEnd_2276257 : Nat := 1168813934161405867719191

theorem tailTrace_2276257 : CollatzResearch.WordTrace tailWord_2276257 prefixEnd_2276257 1168813934161405867719191 := by
  unfold tailWord_2276257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83021913314517117590443025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55347942209678078393628683 83021913314517117590443025)
  ·
    refine ⟨62266434985887838192832269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83021913314517117590443025 62266434985887838192832269)
    ·
      refine ⟨23349913119707939322312101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62266434985887838192832269 23349913119707939322312101)
      ·
        refine ⟨4378108709945238622933519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23349913119707939322312101 4378108709945238622933519)
        ·
          refine ⟨6567163064917857934400279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378108709945238622933519 6567163064917857934400279)
          ·
            refine ⟨9850744597376786901600419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567163064917857934400279 9850744597376786901600419)
            ·
              refine ⟨14776116896065180352400629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850744597376786901600419 14776116896065180352400629)
              ·
                refine ⟨1385260959006110658037559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14776116896065180352400629 1385260959006110658037559)
                ·
                  refine ⟨2077891438509165987056339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385260959006110658037559 2077891438509165987056339)
                  ·
                    refine ⟨3116837157763748980584509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2077891438509165987056339 3116837157763748980584509)
                    ·
                      refine ⟨1168813934161405867719191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116837157763748980584509 1168813934161405867719191)
                      ·
                        rfl

theorem cell23_2276257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2276257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276257 prefixEnd_2276257 := by exact prefixLift 2276257
  have htrace : WordTrace (prefixWord ++ tailWord_2276257) baseStart_2276257 baseEnd_2276257 := by
    simpa [prefixWord, tailWord_2276257, baseEnd_2276257] using wordTrace_append hprefix tailTrace_2276257
  have hstable : (prefixWord ++ tailWord_2276257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276257).length < 2 ^ (prefixWord ++ tailWord_2276257).sum := by decide
  have hdescent : baseEnd_2276257 < baseStart_2276257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276280 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_2276280 : Nat := 118140960795 + 2276280 * 2 ^ 59
def prefixEnd_2276280 : Nat := 4983230072969 + 3 ^ 40 * 2276280 * 2
def baseEnd_2276280 : Nat := 1168825744216459277731585

theorem tailTrace_2276280 : CollatzResearch.WordTrace tailWord_2276280 prefixEnd_2276280 1168825744216459277731585 := by
  unfold tailWord_2276280
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511376096716896259265147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55348501462289195012353529 41511376096716896259265147)
  ·
    refine ⟨62267064145075344388897721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41511376096716896259265147 62267064145075344388897721)
    ·
      refine ⟨46700298108806508291673291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62267064145075344388897721 46700298108806508291673291)
      ·
        refine ⟨70050447163209762437509937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46700298108806508291673291 70050447163209762437509937)
        ·
          refine ⟨52537835372407321828132453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70050447163209762437509937 52537835372407321828132453)
          ·
            refine ⟨9850844132326372842774835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52537835372407321828132453 9850844132326372842774835)
            ·
              refine ⟨14776266198489559264162253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850844132326372842774835 14776266198489559264162253)
              ·
                refine ⟨5541099824433584724060845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14776266198489559264162253 5541099824433584724060845)
                ·
                  refine ⟨2077912434162594271522817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5541099824433584724060845 2077912434162594271522817)
                  ·
                    refine ⟨1558434325621945703642113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2077912434162594271522817 1558434325621945703642113)
                    ·
                      refine ⟨1168825744216459277731585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558434325621945703642113 1168825744216459277731585)
                      ·
                        rfl

theorem cell23_2276280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_2276280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276280 prefixEnd_2276280 := by exact prefixLift 2276280
  have htrace : WordTrace (prefixWord ++ tailWord_2276280) baseStart_2276280 baseEnd_2276280 := by
    simpa [prefixWord, tailWord_2276280, baseEnd_2276280] using wordTrace_append hprefix tailTrace_2276280
  have hstable : (prefixWord ++ tailWord_2276280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276280).length < 2 ^ (prefixWord ++ tailWord_2276280).sum := by decide
  have hdescent : baseEnd_2276280 < baseStart_2276280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276286 : List Nat := [4, 2, 1, 1, 1, 2, 2, 10]
def baseStart_2276286 : Nat := 118140960795 + 2276286 * 2 ^ 59
def prefixEnd_2276286 : Nat := 4983230072969 + 3 ^ 40 * 2276286 * 2
def baseEnd_2276286 : Nat := 43289956485199490898391

theorem tailTrace_2276286 : CollatzResearch.WordTrace tailWord_2276286 prefixEnd_2276286 43289956485199490898391 := by
  unfold tailWord_2276286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377871378926506942906089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55348647354274703695499141 10377871378926506942906089)
  ·
    refine ⟨7783403534194880207179567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10377871378926506942906089 7783403534194880207179567)
    ·
      refine ⟨11675105301292320310769351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783403534194880207179567 11675105301292320310769351)
      ·
        refine ⟨17512657951938480466154027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675105301292320310769351 17512657951938480466154027)
        ·
          refine ⟨26268986927907720699231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17512657951938480466154027 26268986927907720699231041)
          ·
            refine ⟨19701740195930790524423281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26268986927907720699231041 19701740195930790524423281)
            ·
              refine ⟨14776305146948092893317461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701740195930790524423281 14776305146948092893317461)
              ·
                refine ⟨43289956485199490898391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14776305146948092893317461 43289956485199490898391)
                ·
                  rfl

theorem cell23_2276286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_2276286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276286 prefixEnd_2276286 := by exact prefixLift 2276286
  have htrace : WordTrace (prefixWord ++ tailWord_2276286) baseStart_2276286 baseEnd_2276286 := by
    simpa [prefixWord, tailWord_2276286, baseEnd_2276286] using wordTrace_append hprefix tailTrace_2276286
  have hstable : (prefixWord ++ tailWord_2276286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276286).length < 2 ^ (prefixWord ++ tailWord_2276286).sum := by decide
  have hdescent : baseEnd_2276286 < baseStart_2276286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276300 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2276300 : Nat := 118140960795 + 2276300 * 2 ^ 59
def prefixEnd_2276300 : Nat := 4983230072969 + 3 ^ 40 * 2276300 * 2
def baseEnd_2276300 : Nat := 1168836013829549199481493

theorem tailTrace_2276300 : CollatzResearch.WordTrace tailWord_2276300 prefixEnd_2276300 1168836013829549199481493 := by
  unfold tailWord_2276300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511740826680667967129177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55348987768907557289505569 41511740826680667967129177)
  ·
    refine ⟨31133805620010500975346883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41511740826680667967129177 31133805620010500975346883)
    ·
      refine ⟨46700708430015751463020325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31133805620010500975346883 46700708430015751463020325)
      ·
        refine ⟨8756382830627953399316311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46700708430015751463020325 8756382830627953399316311)
        ·
          refine ⟨13134574245941930098974467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756382830627953399316311 13134574245941930098974467)
          ·
            refine ⟨19701861368912895148461701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134574245941930098974467 19701861368912895148461701)
            ·
              refine ⟨3694099006671167840336569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19701861368912895148461701 3694099006671167840336569)
              ·
                refine ⟨2770574255003375880252427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694099006671167840336569 2770574255003375880252427)
                ·
                  refine ⟨4155861382505063820378641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770574255003375880252427 4155861382505063820378641)
                  ·
                    refine ⟨3116896036878797865283981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155861382505063820378641 3116896036878797865283981)
                    ·
                      refine ⟨1168836013829549199481493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116896036878797865283981 1168836013829549199481493)
                      ·
                        rfl

theorem cell23_2276300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2276300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276300 prefixEnd_2276300 := by exact prefixLift 2276300
  have htrace : WordTrace (prefixWord ++ tailWord_2276300) baseStart_2276300 baseEnd_2276300 := by
    simpa [prefixWord, tailWord_2276300, baseEnd_2276300] using wordTrace_append hprefix tailTrace_2276300
  have hstable : (prefixWord ++ tailWord_2276300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276300).length < 2 ^ (prefixWord ++ tailWord_2276300).sum := by decide
  have hdescent : baseEnd_2276300 < baseStart_2276300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276303 : List Nat := [1, 1, 2, 1, 1, 8, 2, 7]
def baseStart_2276303 : Nat := 118140960795 + 2276303 * 2 ^ 59
def prefixEnd_2276303 : Nat := 4983230072969 + 3 ^ 40 * 2276303 * 2
def baseEnd_2276303 : Nat := 43290279787833803249777

theorem tailTrace_2276303 : CollatzResearch.WordTrace tailWord_2276303 prefixEnd_2276303 43290279787833803249777 := by
  unfold tailWord_2276303
  simp only [CollatzResearch.WordTrace]
  refine ⟨83023591072350467446617563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55349060714900311631078375 83023591072350467446617563)
  ·
    refine ⟨124535386608525701169926345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83023591072350467446617563 124535386608525701169926345)
    ·
      refine ⟨93401539956394275877444759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124535386608525701169926345 93401539956394275877444759)
      ·
        refine ⟨140102309934591413816167139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93401539956394275877444759 140102309934591413816167139)
        ·
          refine ⟨210153464901887120724250709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140102309934591413816167139 210153464901887120724250709)
          ·
            refine ⟨2462735916818989695987313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 210153464901887120724250709 2462735916818989695987313)
            ·
              refine ⟨1847051937614242271990485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462735916818989695987313 1847051937614242271990485)
              ·
                refine ⟨43290279787833803249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1847051937614242271990485 43290279787833803249777)
                ·
                  rfl

theorem cell23_2276303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 7].length) (baseStart_2276303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276303 prefixEnd_2276303 := by exact prefixLift 2276303
  have htrace : WordTrace (prefixWord ++ tailWord_2276303) baseStart_2276303 baseEnd_2276303 := by
    simpa [prefixWord, tailWord_2276303, baseEnd_2276303] using wordTrace_append hprefix tailTrace_2276303
  have hstable : (prefixWord ++ tailWord_2276303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276303).length < 2 ^ (prefixWord ++ tailWord_2276303).sum := by decide
  have hdescent : baseEnd_2276303 < baseStart_2276303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276314 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_2276314 : Nat := 118140960795 + 2276314 * 2 ^ 59
def prefixEnd_2276314 : Nat := 4983230072969 + 3 ^ 40 * 2276314 * 2
def baseEnd_2276314 : Nat := 1168843202558712144706429

theorem tailTrace_2276314 : CollatzResearch.WordTrace tailWord_2276314 prefixEnd_2276314 1168843202558712144706429 := by
  unfold tailWord_2276314
  simp only [CollatzResearch.WordTrace]
  refine ⟨20755998068827654081316999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55349328183540410883511997 20755998068827654081316999)
  ·
    refine ⟨31133997103241481121975499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20755998068827654081316999 31133997103241481121975499)
    ·
      refine ⟨46700995654862221682963249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31133997103241481121975499 46700995654862221682963249)
      ·
        refine ⟨35025746741146666262222437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46700995654862221682963249 35025746741146666262222437)
        ·
          refine ⟨6567327513964999924166707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35025746741146666262222437 6567327513964999924166707)
          ·
            refine ⟨9850991270947499886250061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567327513964999924166707 9850991270947499886250061)
            ·
              refine ⟨3694121726605312457343773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9850991270947499886250061 3694121726605312457343773)
              ·
                refine ⟨1385295647476992171503915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3694121726605312457343773 1385295647476992171503915)
                ·
                  refine ⟨2077943471215488257255873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385295647476992171503915 2077943471215488257255873)
                  ·
                    refine ⟨1558457603411616192941905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2077943471215488257255873 1558457603411616192941905)
                    ·
                      refine ⟨1168843202558712144706429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558457603411616192941905 1168843202558712144706429)
                      ·
                        rfl

theorem cell23_2276314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_2276314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276314 prefixEnd_2276314 := by exact prefixLift 2276314
  have htrace : WordTrace (prefixWord ++ tailWord_2276314) baseStart_2276314 baseEnd_2276314 := by
    simpa [prefixWord, tailWord_2276314, baseEnd_2276314] using wordTrace_append hprefix tailTrace_2276314
  have hstable : (prefixWord ++ tailWord_2276314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276314).length < 2 ^ (prefixWord ++ tailWord_2276314).sum := by decide
  have hdescent : baseEnd_2276314 < baseStart_2276314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276330 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2276330 : Nat := 118140960795 + 2276330 * 2 ^ 59
def prefixEnd_2276330 : Nat := 4983230072969 + 3 ^ 40 * 2276330 * 2
def baseEnd_2276330 : Nat := 1168851418249184082106355

theorem tailTrace_2276330 : CollatzResearch.WordTrace tailWord_2276330 prefixEnd_2276330 1168851418249184082106355 := by
  unfold tailWord_2276330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756143960813162764462611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55349717228835100705233629 20756143960813162764462611)
  ·
    refine ⟨31134215941219744146693917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20756143960813162764462611 31134215941219744146693917)
    ·
      refine ⟨11675330977957404055010219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31134215941219744146693917 11675330977957404055010219)
      ·
        refine ⟨17512996466936106082515329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675330977957404055010219 17512996466936106082515329)
        ·
          refine ⟨13134747350202079561886497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17512996466936106082515329 13134747350202079561886497)
          ·
            refine ⟨9851060512651559671414873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13134747350202079561886497 9851060512651559671414873)
            ·
              refine ⟨7388295384488669753561155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851060512651559671414873 7388295384488669753561155)
              ·
                refine ⟨11082443076733004630341733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388295384488669753561155 11082443076733004630341733)
                ·
                  refine ⟨2077958076887438368189075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11082443076733004630341733 2077958076887438368189075)
                  ·
                    refine ⟨3116937115331157552283613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2077958076887438368189075 3116937115331157552283613)
                    ·
                      refine ⟨1168851418249184082106355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3116937115331157552283613 1168851418249184082106355)
                      ·
                        rfl

theorem cell23_2276330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2276330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276330 prefixEnd_2276330 := by exact prefixLift 2276330
  have htrace : WordTrace (prefixWord ++ tailWord_2276330) baseStart_2276330 baseEnd_2276330 := by
    simpa [prefixWord, tailWord_2276330, baseEnd_2276330] using wordTrace_append hprefix tailTrace_2276330
  have hstable : (prefixWord ++ tailWord_2276330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276330).length < 2 ^ (prefixWord ++ tailWord_2276330).sum := by decide
  have hdescent : baseEnd_2276330 < baseStart_2276330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276336 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_2276336 : Nat := 118140960795 + 2276336 * 2 ^ 59
def prefixEnd_2276336 : Nat := 4983230072969 + 3 ^ 40 * 2276336 * 2
def baseEnd_2276336 : Nat := 1168854499133111058631327

theorem tailTrace_2276336 : CollatzResearch.WordTrace tailWord_2276336 prefixEnd_2276336 1168854499133111058631327 := by
  unfold tailWord_2276336
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512397340615457041284431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55349863120820609388379241 41512397340615457041284431)
  ·
    refine ⟨62268596010923185561926647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41512397340615457041284431 62268596010923185561926647)
    ·
      refine ⟨93402894016384778342889971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62268596010923185561926647 93402894016384778342889971)
      ·
        refine ⟨140104341024577167514334957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93402894016384778342889971 140104341024577167514334957)
        ·
          refine ⟨52539127884216437817875609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140104341024577167514334957 52539127884216437817875609)
          ·
            refine ⟨39404345913162328363406707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52539127884216437817875609 39404345913162328363406707)
            ·
              refine ⟨59106518869743492545110061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39404345913162328363406707 59106518869743492545110061)
              ·
                refine ⟨22164944576153809704416273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59106518869743492545110061 22164944576153809704416273)
                ·
                  refine ⟨16623708432115357278312205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22164944576153809704416273 16623708432115357278312205)
                  ·
                    refine ⟨6233890662043258979367077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16623708432115357278312205 6233890662043258979367077)
                    ·
                      refine ⟨1168854499133111058631327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6233890662043258979367077 1168854499133111058631327)
                      ·
                        rfl

theorem cell23_2276336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_2276336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276336 prefixEnd_2276336 := by exact prefixLift 2276336
  have htrace : WordTrace (prefixWord ++ tailWord_2276336) baseStart_2276336 baseEnd_2276336 := by
    simpa [prefixWord, tailWord_2276336, baseEnd_2276336] using wordTrace_append hprefix tailTrace_2276336
  have hstable : (prefixWord ++ tailWord_2276336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276336).length < 2 ^ (prefixWord ++ tailWord_2276336).sum := by decide
  have hdescent : baseEnd_2276336 < baseStart_2276336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276341 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2276341 : Nat := 118140960795 + 2276341 * 2 ^ 59
def prefixEnd_2276341 : Nat := 4983230072969 + 3 ^ 40 * 2276341 * 2
def baseEnd_2276341 : Nat := 389619022178794513022935

theorem tailTrace_2276341 : CollatzResearch.WordTrace tailWord_2276341 prefixEnd_2276341 389619022178794513022935 := by
  unfold tailWord_2276341
  simp only [CollatzResearch.WordTrace]
  refine ⟨83024977046212799936500877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55349984697475199957667251 83024977046212799936500877)
  ·
    refine ⟨31134366392329799976187829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83024977046212799936500877 31134366392329799976187829)
    ·
      refine ⟨2918846849280918747767609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31134366392329799976187829 2918846849280918747767609)
      ·
        refine ⟨2189135136960689060825707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2918846849280918747767609 2189135136960689060825707)
        ·
          refine ⟨3283702705441033591238561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189135136960689060825707 3283702705441033591238561)
          ·
            refine ⟨2462777029080775193428921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283702705441033591238561 2462777029080775193428921)
            ·
              refine ⟨1847082771810581395071691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462777029080775193428921 1847082771810581395071691)
              ·
                refine ⟨2770624157715872092607537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847082771810581395071691 2770624157715872092607537)
                ·
                  refine ⟨2077968118286904069455653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770624157715872092607537 2077968118286904069455653)
                  ·
                    refine ⟨389619022178794513022935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077968118286904069455653 389619022178794513022935)
                    ·
                      rfl

theorem cell23_2276341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2276341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276341 prefixEnd_2276341 := by exact prefixLift 2276341
  have htrace : WordTrace (prefixWord ++ tailWord_2276341) baseStart_2276341 baseEnd_2276341 := by
    simpa [prefixWord, tailWord_2276341, baseEnd_2276341] using wordTrace_append hprefix tailTrace_2276341
  have hstable : (prefixWord ++ tailWord_2276341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276341).length < 2 ^ (prefixWord ++ tailWord_2276341).sum := by decide
  have hdescent : baseEnd_2276341 < baseStart_2276341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276346 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_2276346 : Nat := 118140960795 + 2276346 * 2 ^ 59
def prefixEnd_2276346 : Nat := 4983230072969 + 3 ^ 40 * 2276346 * 2
def baseEnd_2276346 : Nat := 389619877979885339835427

theorem tailTrace_2276346 : CollatzResearch.WordTrace tailWord_2276346 prefixEnd_2276346 389619877979885339835427 := by
  unfold tailWord_2276346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756289852798671447608223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55350106274129790526955261 20756289852798671447608223)
  ·
    refine ⟨31134434779198007171412335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20756289852798671447608223 31134434779198007171412335)
    ·
      refine ⟨46701652168797010757118503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31134434779198007171412335 46701652168797010757118503)
      ·
        refine ⟨70052478253195516135677755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46701652168797010757118503 70052478253195516135677755)
        ·
          refine ⟨105078717379793274203516633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70052478253195516135677755 105078717379793274203516633)
          ·
            refine ⟨78809038034844955652637475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105078717379793274203516633 78809038034844955652637475)
            ·
              refine ⟨118213557052267433478956213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78809038034844955652637475 118213557052267433478956213)
              ·
                refine ⟨11082520973650071888652145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118213557052267433478956213 11082520973650071888652145)
                ·
                  refine ⟨8311890730237553916489109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11082520973650071888652145 8311890730237553916489109)
                  ·
                    refine ⟨389619877979885339835427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8311890730237553916489109 389619877979885339835427)
                    ·
                      rfl

theorem cell23_2276346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_2276346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276346 prefixEnd_2276346 := by exact prefixLift 2276346
  have htrace : WordTrace (prefixWord ++ tailWord_2276346) baseStart_2276346 baseEnd_2276346 := by
    simpa [prefixWord, tailWord_2276346, baseEnd_2276346] using wordTrace_append hprefix tailTrace_2276346
  have hstable : (prefixWord ++ tailWord_2276346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276346).length < 2 ^ (prefixWord ++ tailWord_2276346).sum := by decide
  have hdescent : baseEnd_2276346 < baseStart_2276346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276373 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2276373 : Nat := 118140960795 + 2276373 * 2 ^ 59
def prefixEnd_2276373 : Nat := 4983230072969 + 3 ^ 40 * 2276373 * 2
def baseEnd_2276373 : Nat := 1168873497917327413868657

theorem tailTrace_2276373 : CollatzResearch.WordTrace tailWord_2276373 prefixEnd_2276373 1168873497917327413868657 := by
  unfold tailWord_2276373
  simp only [CollatzResearch.WordTrace]
  refine ⟨83026144182096869401665773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55350762788064579601110515 83026144182096869401665773)
  ·
    refine ⟨31134804068286326025624665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83026144182096869401665773 31134804068286326025624665)
    ·
      refine ⟨23351103051214744519218499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31134804068286326025624665 23351103051214744519218499)
      ·
        refine ⟨35026654576822116778827749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23351103051214744519218499 35026654576822116778827749)
        ·
          refine ⟨6567497733154146896030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35026654576822116778827749 6567497733154146896030203)
          ·
            refine ⟨9851246599731220344045305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567497733154146896030203 9851246599731220344045305)
            ·
              refine ⟨7388434949798415258033979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851246599731220344045305 7388434949798415258033979)
              ·
                refine ⟨11082652424697622887050969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388434949798415258033979 11082652424697622887050969)
                ·
                  refine ⟨8311989318523217165288227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11082652424697622887050969 8311989318523217165288227)
                  ·
                    refine ⟨12467983977784825747932341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8311989318523217165288227 12467983977784825747932341)
                    ·
                      refine ⟨1168873497917327413868657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12467983977784825747932341 1168873497917327413868657)
                      ·
                        rfl

theorem cell23_2276373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2276373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276373 prefixEnd_2276373 := by exact prefixLift 2276373
  have htrace : WordTrace (prefixWord ++ tailWord_2276373) baseStart_2276373 baseEnd_2276373 := by
    simpa [prefixWord, tailWord_2276373, baseEnd_2276373] using wordTrace_append hprefix tailTrace_2276373
  have hstable : (prefixWord ++ tailWord_2276373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276373).length < 2 ^ (prefixWord ++ tailWord_2276373).sum := by decide
  have hdescent : baseEnd_2276373 < baseStart_2276373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276387 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 2, 2, 2]
def baseStart_2276387 : Nat := 118140960795 + 2276387 * 2 ^ 59
def prefixEnd_2276387 : Nat := 4983230072969 + 3 ^ 40 * 2276387 * 2
def baseEnd_2276387 : Nat := 1168880686646490359093593

theorem tailTrace_2276387 : CollatzResearch.WordTrace tailWord_2276387 prefixEnd_2276387 1168880686646490359093593 := by
  unfold tailWord_2276387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83026654804046149792675415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55351103202697433195116943 83026654804046149792675415)
  ·
    refine ⟨124539982206069224689013123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83026654804046149792675415 124539982206069224689013123)
    ·
      refine ⟨186809973309103837033519685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124539982206069224689013123 186809973309103837033519685)
      ·
        refine ⟨35026869995456969443784941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186809973309103837033519685 35026869995456969443784941)
        ·
          refine ⟨13135076248296363541419353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35026869995456969443784941 13135076248296363541419353)
          ·
            refine ⟨9851307186222272656064515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13135076248296363541419353 9851307186222272656064515)
            ·
              refine ⟨14776960779333408984096773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851307186222272656064515 14776960779333408984096773)
              ·
                refine ⟨2770680146125014184518145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14776960779333408984096773 2770680146125014184518145)
                ·
                  refine ⟨2078010109593760638388609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770680146125014184518145 2078010109593760638388609)
                  ·
                    refine ⟨1558507582195320478791457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078010109593760638388609 1558507582195320478791457)
                    ·
                      refine ⟨1168880686646490359093593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558507582195320478791457 1168880686646490359093593)
                      ·
                        rfl

theorem cell23_2276387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_2276387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276387 prefixEnd_2276387 := by exact prefixLift 2276387
  have htrace : WordTrace (prefixWord ++ tailWord_2276387) baseStart_2276387 baseEnd_2276387 := by
    simpa [prefixWord, tailWord_2276387, baseEnd_2276387] using wordTrace_append hprefix tailTrace_2276387
  have hstable : (prefixWord ++ tailWord_2276387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276387).length < 2 ^ (prefixWord ++ tailWord_2276387).sum := by decide
  have hdescent : baseEnd_2276387 < baseStart_2276387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276404 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2276404 : Nat := 118140960795 + 2276404 * 2 ^ 59
def prefixEnd_2276404 : Nat := 4983230072969 + 3 ^ 40 * 2276404 * 2
def baseEnd_2276404 : Nat := 1168889415817616792581015

theorem tailTrace_2276404 : CollatzResearch.WordTrace tailWord_2276404 prefixEnd_2276404 1168889415817616792581015 := by
  unfold tailWord_2276404
  simp only [CollatzResearch.WordTrace]
  refine ⟨41513637422492280848022133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55351516563323041130696177 41513637422492280848022133)
  ·
    refine ⟨3891903508358651329502075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41513637422492280848022133 3891903508358651329502075)
    ·
      refine ⟨5837855262537976994253113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891903508358651329502075 5837855262537976994253113)
      ·
        refine ⟨4378391446903482745689835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5837855262537976994253113 4378391446903482745689835)
        ·
          refine ⟨6567587170355224118534753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378391446903482745689835 6567587170355224118534753)
          ·
            refine ⟨4925690377766418088901065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6567587170355224118534753 4925690377766418088901065)
            ·
              refine ⟨3694267783324813566675799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925690377766418088901065 3694267783324813566675799)
              ·
                refine ⟨5541401674987220350013699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694267783324813566675799 5541401674987220350013699)
                ·
                  refine ⟨8312102512480830525020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541401674987220350013699 8312102512480830525020549)
                  ·
                    refine ⟨1558519221090155723441353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8312102512480830525020549 1558519221090155723441353)
                    ·
                      refine ⟨1168889415817616792581015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558519221090155723441353 1168889415817616792581015)
                      ·
                        rfl

theorem cell23_2276404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2276404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276404 prefixEnd_2276404 := by exact prefixLift 2276404
  have htrace : WordTrace (prefixWord ++ tailWord_2276404) baseStart_2276404 baseEnd_2276404 := by
    simpa [prefixWord, tailWord_2276404, baseEnd_2276404] using wordTrace_append hprefix tailTrace_2276404
  have hstable : (prefixWord ++ tailWord_2276404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276404).length < 2 ^ (prefixWord ++ tailWord_2276404).sum := by decide
  have hdescent : baseEnd_2276404 < baseStart_2276404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276423 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 7]
def baseStart_2276423 : Nat := 118140960795 + 2276423 * 2 ^ 59
def prefixEnd_2276423 : Nat := 4983230072969 + 3 ^ 40 * 2276423 * 2
def baseEnd_2276423 : Nat := 389633057316684072747809

theorem tailTrace_2276423 : CollatzResearch.WordTrace tailWord_2276423 prefixEnd_2276423 389633057316684072747809 := by
  unfold tailWord_2276423
  simp only [CollatzResearch.WordTrace]
  refine ⟨83027967831915727940985923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55351978554610485293990615 83027967831915727940985923)
  ·
    refine ⟨124541951747873591911478885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83027967831915727940985923 124541951747873591911478885)
    ·
      refine ⟨23351615952726298483402291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124541951747873591911478885 23351615952726298483402291)
      ·
        refine ⟨35027423929089447725103437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23351615952726298483402291 35027423929089447725103437)
        ·
          refine ⟨13135283973408542896913789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35027423929089447725103437 13135283973408542896913789)
          ·
            refine ⟨4925731490028203586342671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13135283973408542896913789 4925731490028203586342671)
            ·
              refine ⟨7388597235042305379514007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925731490028203586342671 7388597235042305379514007)
              ·
                refine ⟨11082895852563458069271011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388597235042305379514007 11082895852563458069271011)
                ·
                  refine ⟨16624343778845187103906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082895852563458069271011 16624343778845187103906517)
                  ·
                    refine ⟨389633057316684072747809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16624343778845187103906517 389633057316684072747809)
                    ·
                      rfl

theorem cell23_2276423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_2276423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276423 prefixEnd_2276423 := by exact prefixLift 2276423
  have htrace : WordTrace (prefixWord ++ tailWord_2276423) baseStart_2276423 baseEnd_2276423 := by
    simpa [prefixWord, tailWord_2276423, baseEnd_2276423] using wordTrace_append hprefix tailTrace_2276423
  have hstable : (prefixWord ++ tailWord_2276423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276423).length < 2 ^ (prefixWord ++ tailWord_2276423).sum := by decide
  have hdescent : baseEnd_2276423 < baseStart_2276423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276460 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_2276460 : Nat := 118140960795 + 2276460 * 2 ^ 59
def prefixEnd_2276460 : Nat := 4983230072969 + 3 ^ 40 * 2276460 * 2
def baseEnd_2276460 : Nat := 1168918170734268573480757

theorem tailTrace_2276460 : CollatzResearch.WordTrace tailWord_2276460 prefixEnd_2276460 1168918170734268573480757 := by
  unfold tailWord_2276460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41514658666390841630041417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55352878221854455506721889 41514658666390841630041417)
  ·
    refine ⟨31135993999793131222531063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41514658666390841630041417 31135993999793131222531063)
    ·
      refine ⟨46703990999689696833796595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31135993999793131222531063 46703990999689696833796595)
      ·
        refine ⟨70055986499534545250694893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46703990999689696833796595 70055986499534545250694893)
        ·
          refine ⟨26270994937325454469010585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70055986499534545250694893 26270994937325454469010585)
          ·
            refine ⟨19703246202994090851757939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26270994937325454469010585 19703246202994090851757939)
            ·
              refine ⟨29554869304491136277636909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19703246202994090851757939 29554869304491136277636909)
              ·
                refine ⟨11083075989184176104113841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29554869304491136277636909 11083075989184176104113841)
                ·
                  refine ⟨8312306991888132078085381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11083075989184176104113841 8312306991888132078085381)
                  ·
                    refine ⟨1558557560979024764641009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8312306991888132078085381 1558557560979024764641009)
                    ·
                      refine ⟨1168918170734268573480757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558557560979024764641009 1168918170734268573480757)
                      ·
                        rfl

theorem cell23_2276460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_2276460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276460 prefixEnd_2276460 := by exact prefixLift 2276460
  have htrace : WordTrace (prefixWord ++ tailWord_2276460) baseStart_2276460 baseEnd_2276460 := by
    simpa [prefixWord, tailWord_2276460, baseEnd_2276460] using wordTrace_append hprefix tailTrace_2276460
  have hstable : (prefixWord ++ tailWord_2276460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276460).length < 2 ^ (prefixWord ++ tailWord_2276460).sum := by decide
  have hdescent : baseEnd_2276460 < baseStart_2276460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276463 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_2276463 : Nat := 118140960795 + 2276463 * 2 ^ 59
def prefixEnd_2276463 : Nat := 4983230072969 + 3 ^ 40 * 2276463 * 2
def baseEnd_2276463 : Nat := 1168919711176232061743243

theorem tailTrace_2276463 : CollatzResearch.WordTrace tailWord_2276463 prefixEnd_2276463 1168919711176232061743243 := by
  unfold tailWord_2276463
  simp only [CollatzResearch.WordTrace]
  refine ⟨83029426751770814772442043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55352951167847209848294695 83029426751770814772442043)
  ·
    refine ⟨124544140127656222158663065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83029426751770814772442043 124544140127656222158663065)
    ·
      refine ⟨93408105095742166618997299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124544140127656222158663065 93408105095742166618997299)
      ·
        refine ⟨140112157643613249928495949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93408105095742166618997299 140112157643613249928495949)
        ·
          refine ⟨52542059116354968723185981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140112157643613249928495949 52542059116354968723185981)
          ·
            refine ⟨19703272168633113271194743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52542059116354968723185981 19703272168633113271194743)
            ·
              refine ⟨29554908252949669906792115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19703272168633113271194743 29554908252949669906792115)
              ·
                refine ⟨44332362379424504860188173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29554908252949669906792115 44332362379424504860188173)
                ·
                  refine ⟨16624635892284189322570565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44332362379424504860188173 16624635892284189322570565)
                  ·
                    refine ⟨3117119229803285497981981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16624635892284189322570565 3117119229803285497981981)
                    ·
                      refine ⟨1168919711176232061743243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117119229803285497981981 1168919711176232061743243)
                      ·
                        rfl

theorem cell23_2276463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_2276463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276463 prefixEnd_2276463 := by exact prefixLift 2276463
  have htrace : WordTrace (prefixWord ++ tailWord_2276463) baseStart_2276463 baseEnd_2276463 := by
    simpa [prefixWord, tailWord_2276463, baseEnd_2276463] using wordTrace_append hprefix tailTrace_2276463
  have hstable : (prefixWord ++ tailWord_2276463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276463).length < 2 ^ (prefixWord ++ tailWord_2276463).sum := by decide
  have hdescent : baseEnd_2276463 < baseStart_2276463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276478 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2276478 : Nat := 118140960795 + 2276478 * 2 ^ 59
def prefixEnd_2276478 : Nat := 4983230072969 + 3 ^ 40 * 2276478 * 2
def baseEnd_2276478 : Nat := 129880823709561055895075

theorem tailTrace_2276478 : CollatzResearch.WordTrace tailWord_2276478 prefixEnd_2276478 129880823709561055895075 := by
  unfold tailWord_2276478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378746730839559041779761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55353315897810981556158725 10378746730839559041779761)
  ·
    refine ⟨7784060048129669281334821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10378746730839559041779761 7784060048129669281334821)
    ·
      refine ⟨1459511259024312990250279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7784060048129669281334821 1459511259024312990250279)
      ·
        refine ⟨2189266888536469485375419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459511259024312990250279 2189266888536469485375419)
        ·
          refine ⟨3283900332804704228063129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189266888536469485375419 3283900332804704228063129)
          ·
            refine ⟨2462925249603528171047347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283900332804704228063129 2462925249603528171047347)
            ·
              refine ⟨3694387874405292256571021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462925249603528171047347 3694387874405292256571021)
              ·
                refine ⟨1385395452901984596214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3694387874405292256571021 1385395452901984596214133)
                ·
                  refine ⟨129880823709561055895075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385395452901984596214133 129880823709561055895075)
                  ·
                    rfl

theorem cell23_2276478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2276478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276478 prefixEnd_2276478 := by exact prefixLift 2276478
  have htrace : WordTrace (prefixWord ++ tailWord_2276478) baseStart_2276478 baseEnd_2276478 := by
    simpa [prefixWord, tailWord_2276478, baseEnd_2276478] using wordTrace_append hprefix tailTrace_2276478
  have hstable : (prefixWord ++ tailWord_2276478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276478).length < 2 ^ (prefixWord ++ tailWord_2276478).sum := by decide
  have hdescent : baseEnd_2276478 < baseStart_2276478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276517 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 6]
def baseStart_2276517 : Nat := 118140960795 + 2276517 * 2 ^ 59
def prefixEnd_2276517 : Nat := 4983230072969 + 3 ^ 40 * 2276517 * 2
def baseEnd_2276517 : Nat := 129883048792397205607555

theorem tailTrace_2276517 : CollatzResearch.WordTrace tailWord_2276517 prefixEnd_2276517 129883048792397205607555 := by
  unfold tailWord_2276517
  simp only [CollatzResearch.WordTrace]
  refine ⟨83031396293575181994907805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55354264195716787996605203 83031396293575181994907805)
  ·
    refine ⟨31136773610090693248090427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83031396293575181994907805 31136773610090693248090427)
    ·
      refine ⟨46705160415136039872135641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31136773610090693248090427 46705160415136039872135641)
      ·
        refine ⟨35028870311352029904101731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46705160415136039872135641 35028870311352029904101731)
        ·
          refine ⟨52543305467028044856152597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35028870311352029904101731 52543305467028044856152597)
          ·
            refine ⟨2462967443766939602632153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52543305467028044856152597 2462967443766939602632153)
            ·
              refine ⟨1847225582825204701974115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462967443766939602632153 1847225582825204701974115)
              ·
                refine ⟨2770838374237807052961173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847225582825204701974115 2770838374237807052961173)
                ·
                  refine ⟨129883048792397205607555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2770838374237807052961173 129883048792397205607555)
                  ·
                    rfl

theorem cell23_2276517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_2276517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276517 prefixEnd_2276517 := by exact prefixLift 2276517
  have htrace : WordTrace (prefixWord ++ tailWord_2276517) baseStart_2276517 baseEnd_2276517 := by
    simpa [prefixWord, tailWord_2276517, baseEnd_2276517] using wordTrace_append hprefix tailTrace_2276517
  have hstable : (prefixWord ++ tailWord_2276517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276517).length < 2 ^ (prefixWord ++ tailWord_2276517).sum := by decide
  have hdescent : baseEnd_2276517 < baseStart_2276517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276530 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2276530 : Nat := 118140960795 + 2276530 * 2 ^ 59
def prefixEnd_2276530 : Nat := 4983230072969 + 3 ^ 40 * 2276530 * 2
def baseEnd_2276530 : Nat := 389651371460027766535145

theorem tailTrace_2276530 : CollatzResearch.WordTrace tailWord_2276530 prefixEnd_2276530 389651371460027766535145 := by
  unfold tailWord_2276530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20757967610632021303782761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55354580295018723476754029 20757967610632021303782761)
  ·
    refine ⟨15568475707974015977837071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20757967610632021303782761 15568475707974015977837071)
    ·
      refine ⟨23352713561961023966755607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15568475707974015977837071 23352713561961023966755607)
      ·
        refine ⟨35029070342941535950133411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23352713561961023966755607 35029070342941535950133411)
        ·
          refine ⟨52543605514412303925200117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35029070342941535950133411 52543605514412303925200117)
          ·
            refine ⟨4925963016976153492987511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52543605514412303925200117 4925963016976153492987511)
            ·
              refine ⟨7388944525464230239481267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925963016976153492987511 7388944525464230239481267)
              ·
                refine ⟨11083416788196345359221901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388944525464230239481267 11083416788196345359221901)
                ·
                  refine ⟨4156281295573629509708213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11083416788196345359221901 4156281295573629509708213)
                  ·
                    refine ⟨389651371460027766535145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4156281295573629509708213 389651371460027766535145)
                    ·
                      rfl

theorem cell23_2276530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2276530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276530 prefixEnd_2276530 := by exact prefixLift 2276530
  have htrace : WordTrace (prefixWord ++ tailWord_2276530) baseStart_2276530 baseEnd_2276530 := by
    simpa [prefixWord, tailWord_2276530, baseEnd_2276530] using wordTrace_append hprefix tailTrace_2276530
  have hstable : (prefixWord ++ tailWord_2276530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276530).length < 2 ^ (prefixWord ++ tailWord_2276530).sum := by decide
  have hdescent : baseEnd_2276530 < baseStart_2276530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276537 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2276537 : Nat := 118140960795 + 2276537 * 2 ^ 59
def prefixEnd_2276537 : Nat := 4983230072969 + 3 ^ 40 * 2276537 * 2
def baseEnd_2276537 : Nat := 1168957708744664772217903

theorem tailTrace_2276537 : CollatzResearch.WordTrace tailWord_2276537 prefixEnd_2276537 1168957708744664772217903 := by
  unfold tailWord_2276537
  simp only [CollatzResearch.WordTrace]
  refine ⟨83032125753502725410635865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55354750502335150273757243 83032125753502725410635865)
  ·
    refine ⟨62274094315127044057976899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83032125753502725410635865 62274094315127044057976899)
    ·
      refine ⟨93411141472690566086965349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62274094315127044057976899 93411141472690566086965349)
      ·
        refine ⟨17514589026129481141306003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93411141472690566086965349 17514589026129481141306003)
        ·
          refine ⟨26271883539194221711959005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17514589026129481141306003 26271883539194221711959005)
          ·
            refine ⟨9851956327197833141984627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26271883539194221711959005 9851956327197833141984627)
            ·
              refine ⟨14777934490796749712976941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851956327197833141984627 14777934490796749712976941)
              ·
                refine ⟨5541725434048781142366353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14777934490796749712976941 5541725434048781142366353)
                ·
                  refine ⟨4156294075536585856774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541725434048781142366353 4156294075536585856774765)
                  ·
                    refine ⟨1558610278326219696290537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4156294075536585856774765 1558610278326219696290537)
                    ·
                      refine ⟨1168957708744664772217903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558610278326219696290537 1168957708744664772217903)
                      ·
                        rfl

theorem cell23_2276537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2276537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276537 prefixEnd_2276537 := by exact prefixLift 2276537
  have htrace : WordTrace (prefixWord ++ tailWord_2276537) baseStart_2276537 baseEnd_2276537 := by
    simpa [prefixWord, tailWord_2276537, baseEnd_2276537] using wordTrace_append hprefix tailTrace_2276537
  have hstable : (prefixWord ++ tailWord_2276537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276537).length < 2 ^ (prefixWord ++ tailWord_2276537).sum := by decide
  have hdescent : baseEnd_2276537 < baseStart_2276537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276543 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 6]
def baseStart_2276543 : Nat := 118140960795 + 2276543 * 2 ^ 59
def prefixEnd_2276543 : Nat := 4983230072969 + 3 ^ 40 * 2276543 * 2
def baseEnd_2276543 : Nat := 389653596542863916247625

theorem tailTrace_2276543 : CollatzResearch.WordTrace tailWord_2276543 prefixEnd_2276543 389653596542863916247625 := by
  unfold tailWord_2276543
  simp only [CollatzResearch.WordTrace]
  refine ⟨83032344591480988435354283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55354896394320658956902855 83032344591480988435354283)
  ·
    refine ⟨124548516887221482653031425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83032344591480988435354283 124548516887221482653031425)
    ·
      refine ⟨93411387665416111989773569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124548516887221482653031425 93411387665416111989773569)
      ·
        refine ⟨70058540749062083992330177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93411387665416111989773569 70058540749062083992330177)
        ·
          refine ⟨52543905561796562994247633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70058540749062083992330177 52543905561796562994247633)
          ·
            refine ⟨39407929171347422245685725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52543905561796562994247633 39407929171347422245685725)
            ·
              refine ⟨14777973439255283342132147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39407929171347422245685725 14777973439255283342132147)
              ·
                refine ⟨22166960158882925013198221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14777973439255283342132147 22166960158882925013198221)
                ·
                  refine ⟨8312610059581096879949333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22166960158882925013198221 8312610059581096879949333)
                  ·
                    refine ⟨389653596542863916247625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8312610059581096879949333 389653596542863916247625)
                    ·
                      rfl

theorem cell23_2276543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_2276543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276543 prefixEnd_2276543 := by exact prefixLift 2276543
  have htrace : WordTrace (prefixWord ++ tailWord_2276543) baseStart_2276543 baseEnd_2276543 := by
    simpa [prefixWord, tailWord_2276543, baseEnd_2276543] using wordTrace_append hprefix tailTrace_2276543
  have hstable : (prefixWord ++ tailWord_2276543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276543).length < 2 ^ (prefixWord ++ tailWord_2276543).sum := by decide
  have hdescent : baseEnd_2276543 < baseStart_2276543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276577 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2276577 : Nat := 118140960795 + 2276577 * 2 ^ 59
def prefixEnd_2276577 : Nat := 4983230072969 + 3 ^ 40 * 2276577 * 2
def baseEnd_2276577 : Nat := 389659415990281538572573

theorem tailTrace_2276577 : CollatzResearch.WordTrace tailWord_2276577 prefixEnd_2276577 389659415990281538572573 := by
  unfold tailWord_2276577
  simp only [CollatzResearch.WordTrace]
  refine ⟨83033584673357812242091985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55355723115571874828061323 83033584673357812242091985)
  ·
    refine ⟨62275188505018359181568989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83033584673357812242091985 62275188505018359181568989)
    ·
      refine ⟨23353195689381884693088371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62275188505018359181568989 23353195689381884693088371)
      ·
        refine ⟨35029793534072827039632557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23353195689381884693088371 35029793534072827039632557)
        ·
          refine ⟨13136172575277310139862209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35029793534072827039632557 13136172575277310139862209)
          ·
            refine ⟨9852129431457982604896657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13136172575277310139862209 9852129431457982604896657)
            ·
              refine ⟨7389097073593486953672493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9852129431457982604896657 7389097073593486953672493)
              ·
                refine ⟨2770911402597557607627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7389097073593486953672493 2770911402597557607627185)
                ·
                  refine ⟨2078183551948168205720389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770911402597557607627185 2078183551948168205720389)
                  ·
                    refine ⟨389659415990281538572573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078183551948168205720389 389659415990281538572573)
                    ·
                      rfl

theorem cell23_2276577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2276577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276577 prefixEnd_2276577 := by exact prefixLift 2276577
  have htrace : WordTrace (prefixWord ++ tailWord_2276577) baseStart_2276577 baseEnd_2276577 := by
    simpa [prefixWord, tailWord_2276577, baseEnd_2276577] using wordTrace_append hprefix tailTrace_2276577
  have hstable : (prefixWord ++ tailWord_2276577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276577).length < 2 ^ (prefixWord ++ tailWord_2276577).sum := by decide
  have hdescent : baseEnd_2276577 < baseStart_2276577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276580 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_2276580 : Nat := 118140960795 + 2276580 * 2 ^ 59
def prefixEnd_2276580 : Nat := 4983230072969 + 3 ^ 40 * 2276580 * 2
def baseEnd_2276580 : Nat := 1168979788412808103980205

theorem tailTrace_2276580 : CollatzResearch.WordTrace tailWord_2276580 prefixEnd_2276580 1168979788412808103980205 := by
  unfold tailWord_2276580
  simp only [CollatzResearch.WordTrace]
  refine ⟨41516847046173471877225597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55355796061564629169634129 41516847046173471877225597)
  ·
    refine ⟨15568817642315051953959599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41516847046173471877225597 15568817642315051953959599)
    ·
      refine ⟨23353226463472577930939399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15568817642315051953959599 23353226463472577930939399)
      ·
        refine ⟨35029839695208866896409099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23353226463472577930939399 35029839695208866896409099)
        ·
          refine ⟨52544759542813300344613649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35029839695208866896409099 52544759542813300344613649)
          ·
            refine ⟨39408569657109975258460237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52544759542813300344613649 39408569657109975258460237)
            ·
              refine ⟨14778213621416240721922589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39408569657109975258460237 14778213621416240721922589)
              ·
                refine ⟨5541830108031090270720971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14778213621416240721922589 5541830108031090270720971)
                ·
                  refine ⟨8312745162046635406081457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541830108031090270720971 8312745162046635406081457)
                  ·
                    refine ⟨6234558871534976554561093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8312745162046635406081457 6234558871534976554561093)
                    ·
                      refine ⟨1168979788412808103980205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6234558871534976554561093 1168979788412808103980205)
                      ·
                        rfl

theorem cell23_2276580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_2276580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276580 prefixEnd_2276580 := by exact prefixLift 2276580
  have htrace : WordTrace (prefixWord ++ tailWord_2276580) baseStart_2276580 baseEnd_2276580 := by
    simpa [prefixWord, tailWord_2276580, baseEnd_2276580] using wordTrace_append hprefix tailTrace_2276580
  have hstable : (prefixWord ++ tailWord_2276580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276580).length < 2 ^ (prefixWord ++ tailWord_2276580).sum := by decide
  have hdescent : baseEnd_2276580 < baseStart_2276580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276584 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2276584 : Nat := 118140960795 + 2276584 * 2 ^ 59
def prefixEnd_2276584 : Nat := 4983230072969 + 3 ^ 40 * 2276584 * 2
def baseEnd_2276584 : Nat := 1168981842335426088330187

theorem tailTrace_2276584 : CollatzResearch.WordTrace tailWord_2276584 prefixEnd_2276584 1168981842335426088330187 := by
  unfold tailWord_2276584
  simp only [CollatzResearch.WordTrace]
  refine ⟨41516919992166226218798403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55355893322888301625064537 41516919992166226218798403)
  ·
    refine ⟨62275379988249339328197605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41516919992166226218798403 62275379988249339328197605)
    ·
      refine ⟨11676633747796751124037051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62275379988249339328197605 11676633747796751124037051)
      ·
        refine ⟨17514950621695126686055577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11676633747796751124037051 17514950621695126686055577)
        ·
          refine ⟨13136212966271345014541683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17514950621695126686055577 13136212966271345014541683)
          ·
            refine ⟨19704319449407017521812525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13136212966271345014541683 19704319449407017521812525)
            ·
              refine ⟨7389119793527631570679697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19704319449407017521812525 7389119793527631570679697)
              ·
                refine ⟨5541839845145723678009773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389119793527631570679697 5541839845145723678009773)
                ·
                  refine ⟨2078189941929646379253665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5541839845145723678009773 2078189941929646379253665)
                  ·
                    refine ⟨1558642456447234784440249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078189941929646379253665 1558642456447234784440249)
                    ·
                      refine ⟨1168981842335426088330187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558642456447234784440249 1168981842335426088330187)
                      ·
                        rfl

theorem cell23_2276584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2276584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276584 prefixEnd_2276584 := by exact prefixLift 2276584
  have htrace : WordTrace (prefixWord ++ tailWord_2276584) baseStart_2276584 baseEnd_2276584 := by
    simpa [prefixWord, tailWord_2276584, baseEnd_2276584] using wordTrace_append hprefix tailTrace_2276584
  have hstable : (prefixWord ++ tailWord_2276584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276584).length < 2 ^ (prefixWord ++ tailWord_2276584).sum := by decide
  have hdescent : baseEnd_2276584 < baseStart_2276584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276601 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 1, 2, 2]
def baseStart_2276601 : Nat := 118140960795 + 2276601 * 2 ^ 59
def prefixEnd_2276601 : Nat := 4983230072969 + 3 ^ 40 * 2276601 * 2
def baseEnd_2276601 : Nat := 1168990571506552521817609

theorem tailTrace_2276601 : CollatzResearch.WordTrace tailWord_2276601 prefixEnd_2276601 1168990571506552521817609 := by
  unfold tailWord_2276601
  simp only [CollatzResearch.WordTrace]
  refine ⟨83034460025270864340965657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55356306683513909560643771 83034460025270864340965657)
  ·
    refine ⟨62275845018953148255724243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83034460025270864340965657 62275845018953148255724243)
    ·
      refine ⟨93413767528429722383586365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62275845018953148255724243 93413767528429722383586365)
      ·
        refine ⟨35030162823161145893844887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93413767528429722383586365 35030162823161145893844887)
        ·
          refine ⟨52545244234741718840767331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35030162823161145893844887 52545244234741718840767331)
          ·
            refine ⟨78817866352112578261150997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52545244234741718840767331 78817866352112578261150997)
            ·
              refine ⟨3694587485255277105991453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78817866352112578261150997 3694587485255277105991453)
              ·
                refine ⟨1385470306970728914746795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3694587485255277105991453 1385470306970728914746795)
                ·
                  refine ⟨2078205460456093372120193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385470306970728914746795 2078205460456093372120193)
                  ·
                    refine ⟨1558654095342070029090145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078205460456093372120193 1558654095342070029090145)
                    ·
                      refine ⟨1168990571506552521817609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558654095342070029090145 1168990571506552521817609)
                      ·
                        rfl

theorem cell23_2276601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_2276601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276601 prefixEnd_2276601 := by exact prefixLift 2276601
  have htrace : WordTrace (prefixWord ++ tailWord_2276601) baseStart_2276601 baseEnd_2276601 := by
    simpa [prefixWord, tailWord_2276601, baseEnd_2276601] using wordTrace_append hprefix tailTrace_2276601
  have hstable : (prefixWord ++ tailWord_2276601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276601).length < 2 ^ (prefixWord ++ tailWord_2276601).sum := by decide
  have hdescent : baseEnd_2276601 < baseStart_2276601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276604 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_2276604 : Nat := 118140960795 + 2276604 * 2 ^ 59
def prefixEnd_2276604 : Nat := 4983230072969 + 3 ^ 40 * 2276604 * 2
def baseEnd_2276604 : Nat := 1168992111948516010080095

theorem tailTrace_2276604 : CollatzResearch.WordTrace tailWord_2276604 prefixEnd_2276604 1168992111948516010080095 := by
  unfold tailWord_2276604
  simp only [CollatzResearch.WordTrace]
  refine ⟨41517284722129997926662433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55356379629506663902216577 41517284722129997926662433)
  ·
    refine ⟨31137963541597498444996825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41517284722129997926662433 31137963541597498444996825)
    ·
      refine ⟨23353472656198123833747619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31137963541597498444996825 23353472656198123833747619)
      ·
        refine ⟨35030208984297185750621429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23353472656198123833747619 35030208984297185750621429)
        ·
          refine ⟨3284082092277861164120759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35030208984297185750621429 3284082092277861164120759)
          ·
            refine ⟨4926123138416791746181139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284082092277861164120759 4926123138416791746181139)
            ·
              refine ⟨7389184707625187619271709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926123138416791746181139 7389184707625187619271709)
              ·
                refine ⟨2770944265359445357226891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7389184707625187619271709 2770944265359445357226891)
                ·
                  refine ⟨4156416398039168035840337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770944265359445357226891 4156416398039168035840337)
                  ·
                    refine ⟨3117312298529376026880253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4156416398039168035840337 3117312298529376026880253)
                    ·
                      refine ⟨1168992111948516010080095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117312298529376026880253 1168992111948516010080095)
                      ·
                        rfl

theorem cell23_2276604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_2276604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276604 prefixEnd_2276604 := by exact prefixLift 2276604
  have htrace : WordTrace (prefixWord ++ tailWord_2276604) baseStart_2276604 baseEnd_2276604 := by
    simpa [prefixWord, tailWord_2276604, baseEnd_2276604] using wordTrace_append hprefix tailTrace_2276604
  have hstable : (prefixWord ++ tailWord_2276604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276604).length < 2 ^ (prefixWord ++ tailWord_2276604).sum := by decide
  have hdescent : baseEnd_2276604 < baseStart_2276604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276617 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_2276617 : Nat := 118140960795 + 2276617 * 2 ^ 59
def prefixEnd_2276617 : Nat := 4983230072969 + 3 ^ 40 * 2276617 * 2
def baseEnd_2276617 : Nat := 1168998787197024459217535

theorem tailTrace_2276617 : CollatzResearch.WordTrace tailWord_2276617 prefixEnd_2276617 1168998787197024459217535 := by
  unfold tailWord_2276617
  simp only [CollatzResearch.WordTrace]
  refine ⟨83035043593212899073548105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55356695728808599382365403 83035043593212899073548105)
  ·
    refine ⟨62276282694909674305161079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83035043593212899073548105 62276282694909674305161079)
    ·
      refine ⟨93414424042364511457741619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62276282694909674305161079 93414424042364511457741619)
      ·
        refine ⟨140121636063546767186612429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93414424042364511457741619 140121636063546767186612429)
        ·
          refine ⟨52545613523830037694979661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140121636063546767186612429 52545613523830037694979661)
          ·
            refine ⟨19704605071436264135617373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52545613523830037694979661 19704605071436264135617373)
            ·
              refine ⟨7389226901788599050856515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19704605071436264135617373 7389226901788599050856515)
              ·
                refine ⟨11083840352682898576284773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389226901788599050856515 11083840352682898576284773)
                ·
                  refine ⟨2078220066128043483053395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11083840352682898576284773 2078220066128043483053395)
                  ·
                    refine ⟨3117330099192065224580093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2078220066128043483053395 3117330099192065224580093)
                    ·
                      refine ⟨1168998787197024459217535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117330099192065224580093 1168998787197024459217535)
                      ·
                        rfl

theorem cell23_2276617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_2276617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276617 prefixEnd_2276617 := by exact prefixLift 2276617
  have htrace : WordTrace (prefixWord ++ tailWord_2276617) baseStart_2276617 baseEnd_2276617 := by
    simpa [prefixWord, tailWord_2276617, baseEnd_2276617] using wordTrace_append hprefix tailTrace_2276617
  have hstable : (prefixWord ++ tailWord_2276617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276617).length < 2 ^ (prefixWord ++ tailWord_2276617).sum := by decide
  have hdescent : baseEnd_2276617 < baseStart_2276617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276634 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2276634 : Nat := 118140960795 + 2276634 * 2 ^ 59
def prefixEnd_2276634 : Nat := 4983230072969 + 3 ^ 40 * 2276634 * 2
def baseEnd_2276634 : Nat := 1169007516368150892704957

theorem tailTrace_2276634 : CollatzResearch.WordTrace tailWord_2276634 prefixEnd_2276634 1169007516368150892704957 := by
  unfold tailWord_2276634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20758915908537827744229239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55357109089434207317944637 20758915908537827744229239)
  ·
    refine ⟨31138373862806741616343859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20758915908537827744229239 31138373862806741616343859)
    ·
      refine ⟨46707560794210112424515789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31138373862806741616343859 46707560794210112424515789)
      ·
        refine ⟨17515335297828792159193421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46707560794210112424515789 17515335297828792159193421)
        ·
          refine ⟨6568250736685797059697533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17515335297828792159193421 6568250736685797059697533)
          ·
            refine ⟨2463094026257173897386575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6568250736685797059697533 2463094026257173897386575)
            ·
              refine ⟨3694641039385760846079863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463094026257173897386575 3694641039385760846079863)
              ·
                refine ⟨5541961559078641269119795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694641039385760846079863 5541961559078641269119795)
                ·
                  refine ⟨8312942338617961903679693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541961559078641269119795 8312942338617961903679693)
                  ·
                    refine ⟨3117353376981735713879885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8312942338617961903679693 3117353376981735713879885)
                    ·
                      refine ⟨1169007516368150892704957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117353376981735713879885 1169007516368150892704957)
                      ·
                        rfl

theorem cell23_2276634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2276634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276634 prefixEnd_2276634 := by exact prefixLift 2276634
  have htrace : WordTrace (prefixWord ++ tailWord_2276634) baseStart_2276634 baseEnd_2276634 := by
    simpa [prefixWord, tailWord_2276634, baseEnd_2276634] using wordTrace_append hprefix tailTrace_2276634
  have hstable : (prefixWord ++ tailWord_2276634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276634).length < 2 ^ (prefixWord ++ tailWord_2276634).sum := by decide
  have hdescent : baseEnd_2276634 < baseStart_2276634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276638 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2276638 : Nat := 118140960795 + 2276638 * 2 ^ 59
def prefixEnd_2276638 : Nat := 4983230072969 + 3 ^ 40 * 2276638 * 2
def baseEnd_2276638 : Nat := 1169009570290768877054939

theorem tailTrace_2276638 : CollatzResearch.WordTrace tailWord_2276638 prefixEnd_2276638 1169009570290768877054939 := by
  unfold tailWord_2276638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379476190767102457507821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55357206350757879773375045 10379476190767102457507821)
  ·
    refine ⟨3892303571537663421565433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10379476190767102457507821 3892303571537663421565433)
    ·
      refine ⟨2919227678653247566174075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3892303571537663421565433 2919227678653247566174075)
      ·
        refine ⟨4378841517979871349261113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919227678653247566174075 4378841517979871349261113)
        ·
          refine ⟨3284131138484903511945835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4378841517979871349261113 3284131138484903511945835)
          ·
            refine ⟨4926196707727355267918753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284131138484903511945835 4926196707727355267918753)
            ·
              refine ⟨3694647530795516450939065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926196707727355267918753 3694647530795516450939065)
              ·
                refine ⟨2770985648096637338204299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694647530795516450939065 2770985648096637338204299)
                ·
                  refine ⟨4156478472144956007306449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770985648096637338204299 4156478472144956007306449)
                  ·
                    refine ⟨3117358854108717005479837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4156478472144956007306449 3117358854108717005479837)
                    ·
                      refine ⟨1169009570290768877054939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117358854108717005479837 1169009570290768877054939)
                      ·
                        rfl

theorem cell23_2276638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2276638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276638 prefixEnd_2276638 := by exact prefixLift 2276638
  have htrace : WordTrace (prefixWord ++ tailWord_2276638) baseStart_2276638 baseEnd_2276638 := by
    simpa [prefixWord, tailWord_2276638, baseEnd_2276638] using wordTrace_append hprefix tailTrace_2276638
  have hstable : (prefixWord ++ tailWord_2276638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276638).length < 2 ^ (prefixWord ++ tailWord_2276638).sum := by decide
  have hdescent : baseEnd_2276638 < baseStart_2276638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276720 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_2276720 : Nat := 118140960795 + 2276720 * 2 ^ 59
def prefixEnd_2276720 : Nat := 4983230072969 + 3 ^ 40 * 2276720 * 2
def baseEnd_2276720 : Nat := 1169051675704437556229561

theorem tailTrace_2276720 : CollatzResearch.WordTrace tailWord_2276720 prefixEnd_2276720 1169051675704437556229561 := by
  unfold tailWord_2276720
  simp only [CollatzResearch.WordTrace]
  refine ⟨41519400155919873832273807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55359200207893165109698409 41519400155919873832273807)
  ·
    refine ⟨62279100233879810748410711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41519400155919873832273807 62279100233879810748410711)
    ·
      refine ⟨93418650350819716122616067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62279100233879810748410711 93418650350819716122616067)
      ·
        refine ⟨140127975526229574183924101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93418650350819716122616067 140127975526229574183924101)
        ·
          refine ⟨26273995411168045159485769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140127975526229574183924101 26273995411168045159485769)
          ·
            refine ⟨19705496558376033869614327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26273995411168045159485769 19705496558376033869614327)
            ·
              refine ⟨29558244837564050804421491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19705496558376033869614327 29558244837564050804421491)
              ·
                refine ⟨44337367256346076206632237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29558244837564050804421491 44337367256346076206632237)
                ·
                  refine ⟨16626512721129778577487089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44337367256346076206632237 16626512721129778577487089)
                  ·
                    refine ⟨12469884540847333933115317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16626512721129778577487089 12469884540847333933115317)
                    ·
                      refine ⟨1169051675704437556229561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12469884540847333933115317 1169051675704437556229561)
                      ·
                        rfl

theorem cell23_2276720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_2276720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276720 prefixEnd_2276720 := by exact prefixLift 2276720
  have htrace : WordTrace (prefixWord ++ tailWord_2276720) baseStart_2276720 baseEnd_2276720 := by
    simpa [prefixWord, tailWord_2276720, baseEnd_2276720] using wordTrace_append hprefix tailTrace_2276720
  have hstable : (prefixWord ++ tailWord_2276720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276720).length < 2 ^ (prefixWord ++ tailWord_2276720).sum := by decide
  have hdescent : baseEnd_2276720 < baseStart_2276720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276757 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2276757 : Nat := 118140960795 + 2276757 * 2 ^ 59
def prefixEnd_2276757 : Nat := 4983230072969 + 3 ^ 40 * 2276757 * 2
def baseEnd_2276757 : Nat := 389690224829551303822297

theorem tailTrace_2276757 : CollatzResearch.WordTrace tailWord_2276757 prefixEnd_2276757 389690224829551303822297 := by
  unfold tailWord_2276757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83040149812705702983644525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55360099875137135322429683 83040149812705702983644525)
  ·
    refine ⟨31140056179764638618866697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83040149812705702983644525 31140056179764638618866697)
    ·
      refine ⟨23355042134823478964150023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31140056179764638618866697 23355042134823478964150023)
      ·
        refine ⟨35032563202235218446225035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23355042134823478964150023 35032563202235218446225035)
        ·
          refine ⟨52548844803352827669337553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35032563202235218446225035 52548844803352827669337553)
          ·
            refine ⟨39411633602514620752003165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52548844803352827669337553 39411633602514620752003165)
            ·
              refine ⟨14779362600942982782001187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39411633602514620752003165 14779362600942982782001187)
              ·
                refine ⟨22169043901414474173001781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14779362600942982782001187 22169043901414474173001781)
                ·
                  refine ⟨2078347865757606953718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22169043901414474173001781 2078347865757606953718917)
                  ·
                    refine ⟨389690224829551303822297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078347865757606953718917 389690224829551303822297)
                    ·
                      rfl

theorem cell23_2276757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2276757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276757 prefixEnd_2276757 := by exact prefixLift 2276757
  have htrace : WordTrace (prefixWord ++ tailWord_2276757) baseStart_2276757 baseEnd_2276757 := by
    simpa [prefixWord, tailWord_2276757, baseEnd_2276757] using wordTrace_append hprefix tailTrace_2276757
  have hstable : (prefixWord ++ tailWord_2276757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276757).length < 2 ^ (prefixWord ++ tailWord_2276757).sum := by decide
  have hdescent : baseEnd_2276757 < baseStart_2276757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276781 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2276781 : Nat := 118140960795 + 2276781 * 2 ^ 59
def prefixEnd_2276781 : Nat := 4983230072969 + 3 ^ 40 * 2276781 * 2
def baseEnd_2276781 : Nat := 1169082998024361817566781

theorem tailTrace_2276781 : CollatzResearch.WordTrace tailWord_2276781 prefixEnd_2276781 1169082998024361817566781 := by
  unfold tailWord_2276781
  simp only [CollatzResearch.WordTrace]
  refine ⟨83041025164618755082518197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55360683443079170055012131 83041025164618755082518197)
  ·
    refine ⟨7785096109183008288986081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83041025164618755082518197 7785096109183008288986081)
    ·
      refine ⟨5838822081887256216739561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7785096109183008288986081 5838822081887256216739561)
      ·
        refine ⟨4379116561415442162554671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5838822081887256216739561 4379116561415442162554671)
        ·
          refine ⟨6568674842123163243832007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379116561415442162554671 6568674842123163243832007)
          ·
            refine ⟨9853012263184744865748011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568674842123163243832007 9853012263184744865748011)
            ·
              refine ⟨14779518394777117298622017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9853012263184744865748011 14779518394777117298622017)
              ·
                refine ⟨11084638796082837973966513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14779518394777117298622017 11084638796082837973966513)
                ·
                  refine ⟨8313479097062128480474885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11084638796082837973966513 8313479097062128480474885)
                  ·
                    refine ⟨1558777330699149090089041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8313479097062128480474885 1558777330699149090089041)
                    ·
                      refine ⟨1169082998024361817566781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558777330699149090089041 1169082998024361817566781)
                      ·
                        rfl

theorem cell23_2276781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2276781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276781 prefixEnd_2276781 := by exact prefixLift 2276781
  have htrace : WordTrace (prefixWord ++ tailWord_2276781) baseStart_2276781 baseEnd_2276781 := by
    simpa [prefixWord, tailWord_2276781, baseEnd_2276781] using wordTrace_append hprefix tailTrace_2276781
  have hstable : (prefixWord ++ tailWord_2276781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276781).length < 2 ^ (prefixWord ++ tailWord_2276781).sum := by decide
  have hdescent : baseEnd_2276781 < baseStart_2276781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276824 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_2276824 : Nat := 118140960795 + 2276824 * 2 ^ 59
def prefixEnd_2276824 : Nat := 4983230072969 + 3 ^ 40 * 2276824 * 2
def baseEnd_2276824 : Nat := 1169105077692505149329083

theorem tailTrace_2276824 : CollatzResearch.WordTrace tailWord_2276824 prefixEnd_2276824 1169105077692505149329083 := by
  unfold tailWord_2276824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41521296751731486713166763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55361729002308648950889017 41521296751731486713166763)
  ·
    refine ⟨62281945127597230069750145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41521296751731486713166763 62281945127597230069750145)
    ·
      refine ⟨46711458845697922552312609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62281945127597230069750145 46711458845697922552312609)
      ·
        refine ⟨35033594134273441914234457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46711458845697922552312609 35033594134273441914234457)
        ·
          refine ⟨26275195600705081435675843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35033594134273441914234457 26275195600705081435675843)
          ·
            refine ⟨39412793401057622153513765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26275195600705081435675843 39412793401057622153513765)
            ·
              refine ⟨7389898762698304153783831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39412793401057622153513765 7389898762698304153783831)
              ·
                refine ⟨11084848144047456230675747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389898762698304153783831 11084848144047456230675747)
                ·
                  refine ⟨16627272216071184346013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11084848144047456230675747 16627272216071184346013621)
                  ·
                    refine ⟨1558806770256673532438777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16627272216071184346013621 1558806770256673532438777)
                    ·
                      refine ⟨1169105077692505149329083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558806770256673532438777 1169105077692505149329083)
                      ·
                        rfl

theorem cell23_2276824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_2276824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276824 prefixEnd_2276824 := by exact prefixLift 2276824
  have htrace : WordTrace (prefixWord ++ tailWord_2276824) baseStart_2276824 baseEnd_2276824 := by
    simpa [prefixWord, tailWord_2276824, baseEnd_2276824] using wordTrace_append hprefix tailTrace_2276824
  have hstable : (prefixWord ++ tailWord_2276824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276824).length < 2 ^ (prefixWord ++ tailWord_2276824).sum := by decide
  have hdescent : baseEnd_2276824 < baseStart_2276824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276857 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2276857 : Nat := 118140960795 + 2276857 * 2 ^ 59
def prefixEnd_2276857 : Nat := 4983230072969 + 3 ^ 40 * 2276857 * 2
def baseEnd_2276857 : Nat := 1169122022554103520216431

theorem tailTrace_2276857 : CollatzResearch.WordTrace tailWord_2276857 prefixEnd_2276857 1169122022554103520216431 := by
  unfold tailWord_2276857
  simp only [CollatzResearch.WordTrace]
  refine ⟨83043797112343420062284825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55362531408228946708189883 83043797112343420062284825)
  ·
    refine ⟨62282847834257565046713619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83043797112343420062284825 62282847834257565046713619)
    ·
      refine ⟨93424271751386347570070429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62282847834257565046713619 93424271751386347570070429)
      ·
        refine ⟨35034101906769880338776411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93424271751386347570070429 35034101906769880338776411)
        ·
          refine ⟨52551152860154820508164617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35034101906769880338776411 52551152860154820508164617)
          ·
            refine ⟨39413364645116115381123463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52551152860154820508164617 39413364645116115381123463)
            ·
              refine ⟨59120046967674173071685195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39413364645116115381123463 59120046967674173071685195)
              ·
                refine ⟨88680070451511259607527793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59120046967674173071685195 88680070451511259607527793)
                ·
                  refine ⟨66510052838633444705645845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88680070451511259607527793 66510052838633444705645845)
                  ·
                    refine ⟨3117658726810942720577149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66510052838633444705645845 3117658726810942720577149)
                    ·
                      refine ⟨1169122022554103520216431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117658726810942720577149 1169122022554103520216431)
                      ·
                        rfl

theorem cell23_2276857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2276857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276857 prefixEnd_2276857 := by exact prefixLift 2276857
  have htrace : WordTrace (prefixWord ++ tailWord_2276857) baseStart_2276857 baseEnd_2276857 := by
    simpa [prefixWord, tailWord_2276857, baseEnd_2276857] using wordTrace_append hprefix tailTrace_2276857
  have hstable : (prefixWord ++ tailWord_2276857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276857).length < 2 ^ (prefixWord ++ tailWord_2276857).sum := by decide
  have hdescent : baseEnd_2276857 < baseStart_2276857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276868 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_2276868 : Nat := 118140960795 + 2276868 * 2 ^ 59
def prefixEnd_2276868 : Nat := 4983230072969 + 3 ^ 40 * 2276868 * 2
def baseEnd_2276868 : Nat := 389709223613767659059627

theorem tailTrace_2276868 : CollatzResearch.WordTrace tailWord_2276868 prefixEnd_2276868 389709223613767659059627 := by
  unfold tailWord_2276868
  simp only [CollatzResearch.WordTrace]
  refine ⟨41522099157651784470467629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55362798876869045960623505 41522099157651784470467629)
  ·
    refine ⟨15570787184119419176425361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41522099157651784470467629 15570787184119419176425361)
    ·
      refine ⟨11678090388089564382319021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15570787184119419176425361 11678090388089564382319021)
      ·
        refine ⟨4379283895533586643369633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11678090388089564382319021 4379283895533586643369633)
        ·
          refine ⟨3284462921650189982527225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4379283895533586643369633 3284462921650189982527225)
          ·
            refine ⟨2463347191237642486895419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284462921650189982527225 2463347191237642486895419)
            ·
              refine ⟨3695020786856463730343129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463347191237642486895419 3695020786856463730343129)
              ·
                refine ⟨2771265590142347797757347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695020786856463730343129 2771265590142347797757347)
                ·
                  refine ⟨4156898385213521696636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771265590142347797757347 4156898385213521696636021)
                  ·
                    refine ⟨389709223613767659059627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4156898385213521696636021 389709223613767659059627)
                    ·
                      rfl

theorem cell23_2276868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_2276868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276868 prefixEnd_2276868 := by exact prefixLift 2276868
  have htrace : WordTrace (prefixWord ++ tailWord_2276868) baseStart_2276868 baseEnd_2276868 := by
    simpa [prefixWord, tailWord_2276868, baseEnd_2276868] using wordTrace_append hprefix tailTrace_2276868
  have hstable : (prefixWord ++ tailWord_2276868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276868).length < 2 ^ (prefixWord ++ tailWord_2276868).sum := by decide
  have hdescent : baseEnd_2276868 < baseStart_2276868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276871 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2276871 : Nat := 118140960795 + 2276871 * 2 ^ 59
def prefixEnd_2276871 : Nat := 4983230072969 + 3 ^ 40 * 2276871 * 2
def baseEnd_2276871 : Nat := 1169129211283266465441367

theorem tailTrace_2276871 : CollatzResearch.WordTrace tailWord_2276871 prefixEnd_2276871 1169129211283266465441367 := by
  unfold tailWord_2276871
  simp only [CollatzResearch.WordTrace]
  refine ⟨83044307734292700453294467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55362871822861800302196311 83044307734292700453294467)
  ·
    refine ⟨124566461601439050679941701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83044307734292700453294467 124566461601439050679941701)
    ·
      refine ⟨23356211550269822002489069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124566461601439050679941701 23356211550269822002489069)
      ·
        refine ⟨8758579331351183250933401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23356211550269822002489069 8758579331351183250933401)
        ·
          refine ⟨6568934498513387438200051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8758579331351183250933401 6568934498513387438200051)
          ·
            refine ⟨9853401747770081157300077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568934498513387438200051 9853401747770081157300077)
            ·
              refine ⟨3695025655413780433987529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9853401747770081157300077 3695025655413780433987529)
              ·
                refine ⟨2771269241560335325490647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695025655413780433987529 2771269241560335325490647)
                ·
                  refine ⟨4156903862340502988235971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771269241560335325490647 4156903862340502988235971)
                  ·
                    refine ⟨6235355793510754482353957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4156903862340502988235971 6235355793510754482353957)
                    ·
                      refine ⟨1169129211283266465441367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6235355793510754482353957 1169129211283266465441367)
                      ·
                        rfl

theorem cell23_2276871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2276871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276871 prefixEnd_2276871 := by exact prefixLift 2276871
  have htrace : WordTrace (prefixWord ++ tailWord_2276871) baseStart_2276871 baseEnd_2276871 := by
    simpa [prefixWord, tailWord_2276871, baseEnd_2276871] using wordTrace_append hprefix tailTrace_2276871
  have hstable : (prefixWord ++ tailWord_2276871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276871).length < 2 ^ (prefixWord ++ tailWord_2276871).sum := by decide
  have hdescent : baseEnd_2276871 < baseStart_2276871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276888 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2276888 : Nat := 118140960795 + 2276888 * 2 ^ 59
def prefixEnd_2276888 : Nat := 4983230072969 + 3 ^ 40 * 2276888 * 2
def baseEnd_2276888 : Nat := 1169137940454392898928789

theorem tailTrace_2276888 : CollatzResearch.WordTrace tailWord_2276888 prefixEnd_2276888 1169137940454392898928789 := by
  unfold tailWord_2276888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41522463887615556178331659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55363285183487408237775545 41522463887615556178331659)
  ·
    refine ⟨62283695831423334267497489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41522463887615556178331659 62283695831423334267497489)
    ·
      refine ⟨46712771873567500700623117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62283695831423334267497489 46712771873567500700623117)
      ·
        refine ⟨17517289452587812762733669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46712771873567500700623117 17517289452587812762733669)
        ·
          refine ⟨3284491772360214893012563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17517289452587812762733669 3284491772360214893012563)
          ·
            refine ⟨4926737658540322339518845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284491772360214893012563 4926737658540322339518845)
            ·
              refine ⟨1847526621952620877319567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4926737658540322339518845 1847526621952620877319567)
              ·
                refine ⟨2771289932928931315979351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847526621952620877319567 2771289932928931315979351)
                ·
                  refine ⟨4156934899393396973969027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771289932928931315979351 4156934899393396973969027)
                  ·
                    refine ⟨6235402349090095460953541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4156934899393396973969027 6235402349090095460953541)
                    ·
                      refine ⟨1169137940454392898928789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6235402349090095460953541 1169137940454392898928789)
                      ·
                        rfl

theorem cell23_2276888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2276888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276888 prefixEnd_2276888 := by exact prefixLift 2276888
  have htrace : WordTrace (prefixWord ++ tailWord_2276888) baseStart_2276888 baseEnd_2276888 := by
    simpa [prefixWord, tailWord_2276888, baseEnd_2276888] using wordTrace_append hprefix tailTrace_2276888
  have hstable : (prefixWord ++ tailWord_2276888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276888).length < 2 ^ (prefixWord ++ tailWord_2276888).sum := by decide
  have hdescent : baseEnd_2276888 < baseStart_2276888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276918 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2276918 : Nat := 118140960795 + 2276918 * 2 ^ 59
def prefixEnd_2276918 : Nat := 4983230072969 + 3 ^ 40 * 2276918 * 2
def baseEnd_2276918 : Nat := 1169153344874027781553651

theorem tailTrace_2276918 : CollatzResearch.WordTrace tailWord_2276918 prefixEnd_2276918 1169153344874027781553651 := by
  unfold tailWord_2276918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190376372820151717515963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55364014643414951653503605 5190376372820151717515963)
  ·
    refine ⟨7785564559230227576273945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190376372820151717515963 7785564559230227576273945)
    ·
      refine ⟨5839173419422670682205459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7785564559230227576273945 5839173419422670682205459)
      ·
        refine ⟨8758760129134006023308189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839173419422670682205459 8758760129134006023308189)
        ·
          refine ⟨3284535048425252258740571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8758760129134006023308189 3284535048425252258740571)
          ·
            refine ⟨4926802572637878388110857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284535048425252258740571 4926802572637878388110857)
            ·
              refine ⟨3695101929478408791083143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926802572637878388110857 3695101929478408791083143)
              ·
                refine ⟨5542652894217613186624715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695101929478408791083143 5542652894217613186624715)
                ·
                  refine ⟨8313979341326419779937073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542652894217613186624715 8313979341326419779937073)
                  ·
                    refine ⟨6235484505994814834952805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8313979341326419779937073 6235484505994814834952805)
                    ·
                      refine ⟨1169153344874027781553651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6235484505994814834952805 1169153344874027781553651)
                      ·
                        rfl

theorem cell23_2276918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2276918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276918 prefixEnd_2276918 := by exact prefixLift 2276918
  have htrace : WordTrace (prefixWord ++ tailWord_2276918) baseStart_2276918 baseEnd_2276918 := by
    simpa [prefixWord, tailWord_2276918, baseEnd_2276918] using wordTrace_append hprefix tailTrace_2276918
  have hstable : (prefixWord ++ tailWord_2276918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276918).length < 2 ^ (prefixWord ++ tailWord_2276918).sum := by decide
  have hdescent : baseEnd_2276918 < baseStart_2276918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276921 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2276921 : Nat := 118140960795 + 2276921 * 2 ^ 59
def prefixEnd_2276921 : Nat := 4983230072969 + 3 ^ 40 * 2276921 * 2
def baseEnd_2276921 : Nat := 1169154885315991269816137

theorem tailTrace_2276921 : CollatzResearch.WordTrace tailWord_2276921 prefixEnd_2276921 1169154885315991269816137 := by
  unfold tailWord_2276921
  simp only [CollatzResearch.WordTrace]
  refine ⟨83046131384111558992614617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55364087589407705995076411 83046131384111558992614617)
  ·
    refine ⟨62284598538083669244460963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83046131384111558992614617 62284598538083669244460963)
    ·
      refine ⟨93426897807125503866691445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62284598538083669244460963 93426897807125503866691445)
      ·
        refine ⟨8758771669418015987502323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93426897807125503866691445 8758771669418015987502323)
        ·
          refine ⟨13138157504127023981253485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8758771669418015987502323 13138157504127023981253485)
          ·
            refine ⟨4926809064047633992970057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13138157504127023981253485 4926809064047633992970057)
            ·
              refine ⟨3695106798035725494727543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926809064047633992970057 3695106798035725494727543)
              ·
                refine ⟨5542660197053588242091315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695106798035725494727543 5542660197053588242091315)
                ·
                  refine ⟨8313990295580382363136973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542660197053588242091315 8313990295580382363136973)
                  ·
                    refine ⟨3117746360842643386176365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8313990295580382363136973 3117746360842643386176365)
                    ·
                      refine ⟨1169154885315991269816137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3117746360842643386176365 1169154885315991269816137)
                      ·
                        rfl

theorem cell23_2276921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2276921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276921 prefixEnd_2276921 := by exact prefixLift 2276921
  have htrace : WordTrace (prefixWord ++ tailWord_2276921) baseStart_2276921 baseEnd_2276921 := by
    simpa [prefixWord, tailWord_2276921, baseEnd_2276921] using wordTrace_append hprefix tailTrace_2276921
  have hstable : (prefixWord ++ tailWord_2276921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276921).length < 2 ^ (prefixWord ++ tailWord_2276921).sum := by decide
  have hdescent : baseEnd_2276921 < baseStart_2276921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276948 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_2276948 : Nat := 118140960795 + 2276948 * 2 ^ 59
def prefixEnd_2276948 : Nat := 4983230072969 + 3 ^ 40 * 2276948 * 2
def baseEnd_2276948 : Nat := 1169168749293662664178513

theorem tailTrace_2276948 : CollatzResearch.WordTrace tailWord_2276948 prefixEnd_2276948 1169168749293662664178513 := by
  unfold tailWord_2276948
  simp only [CollatzResearch.WordTrace]
  refine ⟨41523558077506871301923749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55364744103342495069231665 41523558077506871301923749)
  ·
    refine ⟨7785667139532538369110703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41523558077506871301923749 7785667139532538369110703)
    ·
      refine ⟨11678500709298807553666055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7785667139532538369110703 11678500709298807553666055)
      ·
        refine ⟨17517751063948211330499083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11678500709298807553666055 17517751063948211330499083)
        ·
          refine ⟨26276626595922316995748625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17517751063948211330499083 26276626595922316995748625)
          ·
            refine ⟨19707469946941737746811469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26276626595922316995748625 19707469946941737746811469)
            ·
              refine ⟨7390301230103151655054301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19707469946941737746811469 7390301230103151655054301)
              ·
                refine ⟨2771362961288681870645363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7390301230103151655054301 2771362961288681870645363)
                ·
                  refine ⟨4157044441933022805968045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771362961288681870645363 4157044441933022805968045)
                  ·
                    refine ⟨1558891665724883552238017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4157044441933022805968045 1558891665724883552238017)
                    ·
                      refine ⟨1169168749293662664178513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558891665724883552238017 1169168749293662664178513)
                      ·
                        rfl

theorem cell23_2276948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_2276948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276948 prefixEnd_2276948 := by exact prefixLift 2276948
  have htrace : WordTrace (prefixWord ++ tailWord_2276948) baseStart_2276948 baseEnd_2276948 := by
    simpa [prefixWord, tailWord_2276948, baseEnd_2276948] using wordTrace_append hprefix tailTrace_2276948
  have hstable : (prefixWord ++ tailWord_2276948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276948).length < 2 ^ (prefixWord ++ tailWord_2276948).sum := by decide
  have hdescent : baseEnd_2276948 < baseStart_2276948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276977 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2276977 : Nat := 118140960795 + 2276977 * 2 ^ 59
def prefixEnd_2276977 : Nat := 4983230072969 + 3 ^ 40 * 2276977 * 2
def baseEnd_2276977 : Nat := 1169183640232643050715879

theorem tailTrace_2276977 : CollatzResearch.WordTrace tailWord_2276977 prefixEnd_2276977 1169183640232643050715879 := by
  unfold tailWord_2276977
  simp only [CollatzResearch.WordTrace]
  refine ⟨83048173871908680556653185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55365449247939120371102123 83048173871908680556653185)
  ·
    refine ⟨62286130403931510417489889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83048173871908680556653185 62286130403931510417489889)
    ·
      refine ⟨46714597802948632813117417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62286130403931510417489889 46714597802948632813117417)
      ·
        refine ⟨35035948352211474609838063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46714597802948632813117417 35035948352211474609838063)
        ·
          refine ⟨52553922528317211914757095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35035948352211474609838063 52553922528317211914757095)
          ·
            refine ⟨78830883792475817872135643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52553922528317211914757095 78830883792475817872135643)
            ·
              refine ⟨118246325688713726808203465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78830883792475817872135643 118246325688713726808203465)
              ·
                refine ⟨88684744266535295106152599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118246325688713726808203465 88684744266535295106152599)
                ·
                  refine ⟨133027116399802942659228899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88684744266535295106152599 133027116399802942659228899)
                  ·
                    refine ⟨199540674599704413988843349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133027116399802942659228899 199540674599704413988843349)
                    ·
                      refine ⟨1169183640232643050715879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 199540674599704413988843349 1169183640232643050715879)
                      ·
                        rfl

theorem cell23_2276977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2276977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276977 prefixEnd_2276977 := by exact prefixLift 2276977
  have htrace : WordTrace (prefixWord ++ tailWord_2276977) baseStart_2276977 baseEnd_2276977 := by
    simpa [prefixWord, tailWord_2276977, baseEnd_2276977] using wordTrace_append hprefix tailTrace_2276977
  have hstable : (prefixWord ++ tailWord_2276977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276977).length < 2 ^ (prefixWord ++ tailWord_2276977).sum := by decide
  have hdescent : baseEnd_2276977 < baseStart_2276977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2276978 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2276978 : Nat := 118140960795 + 2276978 * 2 ^ 59
def prefixEnd_2276978 : Nat := 4983230072969 + 3 ^ 40 * 2276978 * 2
def baseEnd_2276978 : Nat := 1169184153713297546803375

theorem tailTrace_2276978 : CollatzResearch.WordTrace tailWord_2276978 prefixEnd_2276978 1169184153713297546803375 := by
  unfold tailWord_2276978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762052586226264431859897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55365473563270038484959725 20762052586226264431859897)
  ·
    refine ⟨15571539439669698323894923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20762052586226264431859897 15571539439669698323894923)
    ·
      refine ⟨23357309159504547485842385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15571539439669698323894923 23357309159504547485842385)
      ·
        refine ⟨17517981869628410614381789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23357309159504547485842385 17517981869628410614381789)
        ·
          refine ⟨6569243201110653980393171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17517981869628410614381789 6569243201110653980393171)
          ·
            refine ⟨9853864801665980970589757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6569243201110653980393171 9853864801665980970589757)
            ·
              refine ⟨3695199300624742863971159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9853864801665980970589757 3695199300624742863971159)
              ·
                refine ⟨5542798950937114295956739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695199300624742863971159 5542798950937114295956739)
                ·
                  refine ⟨8314198426405671443935109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542798950937114295956739 8314198426405671443935109)
                  ·
                    refine ⟨1558912204951063395737833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8314198426405671443935109 1558912204951063395737833)
                    ·
                      refine ⟨1169184153713297546803375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558912204951063395737833 1169184153713297546803375)
                      ·
                        rfl

theorem cell23_2276978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2276978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2276978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2276978 prefixEnd_2276978 := by exact prefixLift 2276978
  have htrace : WordTrace (prefixWord ++ tailWord_2276978) baseStart_2276978 baseEnd_2276978 := by
    simpa [prefixWord, tailWord_2276978, baseEnd_2276978] using wordTrace_append hprefix tailTrace_2276978
  have hstable : (prefixWord ++ tailWord_2276978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2276978).length < 2 ^ (prefixWord ++ tailWord_2276978).sum := by decide
  have hdescent : baseEnd_2276978 < baseStart_2276978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2276978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277001 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 5]
def baseStart_2277001 : Nat := 118140960795 + 2277001 * 2 ^ 59
def prefixEnd_2277001 : Nat := 4983230072969 + 3 ^ 40 * 2277001 * 2
def baseEnd_2277001 : Nat := 129910662640927884090641

theorem tailTrace_2277001 : CollatzResearch.WordTrace tailWord_2277001 prefixEnd_2277001 129910662640927884090641 := by
  unfold tailWord_2277001
  simp only [CollatzResearch.WordTrace]
  refine ⟨83049049223821732655526857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55366032815881155103684571 83049049223821732655526857)
  ·
    refine ⟨62286786917866299491645143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83049049223821732655526857 62286786917866299491645143)
    ·
      refine ⟨93430180376799449237467715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62286786917866299491645143 93430180376799449237467715)
      ·
        refine ⟨140145270565199173856201573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93430180376799449237467715 140145270565199173856201573)
        ·
          refine ⟨26277238230974845098037795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140145270565199173856201573 26277238230974845098037795)
          ·
            refine ⟨39415857346462267647056693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26277238230974845098037795 39415857346462267647056693)
            ·
              refine ⟨3695236626230837591911565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39415857346462267647056693 3695236626230837591911565)
              ·
                refine ⟨1385713734836564096966837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3695236626230837591911565 1385713734836564096966837)
                ·
                  refine ⟨129910662640927884090641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385713734836564096966837 129910662640927884090641)
                  ·
                    rfl

theorem cell23_2277001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 5].length) (baseStart_2277001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277001 prefixEnd_2277001 := by exact prefixLift 2277001
  have htrace : WordTrace (prefixWord ++ tailWord_2277001) baseStart_2277001 baseEnd_2277001 := by
    simpa [prefixWord, tailWord_2277001, baseEnd_2277001] using wordTrace_append hprefix tailTrace_2277001
  have hstable : (prefixWord ++ tailWord_2277001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277001).length < 2 ^ (prefixWord ++ tailWord_2277001).sum := by decide
  have hdescent : baseEnd_2277001 < baseStart_2277001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277021 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_2277021 : Nat := 118140960795 + 2277021 * 2 ^ 59
def prefixEnd_2277021 : Nat := 4983230072969 + 3 ^ 40 * 2277021 * 2
def baseEnd_2277021 : Nat := 1169206233381440878565677

theorem tailTrace_2277021 : CollatzResearch.WordTrace tailWord_2277021 prefixEnd_2277021 1169206233381440878565677 := by
  unfold tailWord_2277021
  simp only [CollatzResearch.WordTrace]
  refine ⟨83049778683749276071254917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55366519122499517380836611 83049778683749276071254917)
  ·
    refine ⟨15571833503202989263360297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83049778683749276071254917 15571833503202989263360297)
    ·
      refine ⟨11678875127402241947520223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15571833503202989263360297 11678875127402241947520223)
      ·
        refine ⟨17518312691103362921280335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11678875127402241947520223 17518312691103362921280335)
        ·
          refine ⟨26277469036655044381920503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17518312691103362921280335 26277469036655044381920503)
          ·
            refine ⟨39416203554982566572880755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26277469036655044381920503 39416203554982566572880755)
            ·
              refine ⟨59124305332473849859321133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39416203554982566572880755 59124305332473849859321133)
              ·
                refine ⟨22171614499677693697245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59124305332473849859321133 22171614499677693697245425)
                ·
                  refine ⟨16628710874758270272934069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22171614499677693697245425 16628710874758270272934069)
                  ·
                    refine ⟨1558941644508587838087569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16628710874758270272934069 1558941644508587838087569)
                    ·
                      refine ⟨1169206233381440878565677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1558941644508587838087569 1169206233381440878565677)
                      ·
                        rfl

theorem cell23_2277021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_2277021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277021 prefixEnd_2277021 := by exact prefixLift 2277021
  have htrace : WordTrace (prefixWord ++ tailWord_2277021) baseStart_2277021 baseEnd_2277021 := by
    simpa [prefixWord, tailWord_2277021, baseEnd_2277021] using wordTrace_append hprefix tailTrace_2277021
  have hstable : (prefixWord ++ tailWord_2277021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277021).length < 2 ^ (prefixWord ++ tailWord_2277021).sum := by decide
  have hdescent : baseEnd_2277021 < baseStart_2277021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277024 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2277024 : Nat := 118140960795 + 2277024 * 2 ^ 59
def prefixEnd_2277024 : Nat := 4983230072969 + 3 ^ 40 * 2277024 * 2
def baseEnd_2277024 : Nat := 1169207773823404366828163

theorem tailTrace_2277024 : CollatzResearch.WordTrace tailWord_2277024 prefixEnd_2277024 1169207773823404366828163 := by
  unfold tailWord_2277024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524944051369203791807063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55366592068492271722409417 41524944051369203791807063)
  ·
    refine ⟨62287416077053805687710595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41524944051369203791807063 62287416077053805687710595)
    ·
      refine ⟨93431124115580708531565893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62287416077053805687710595 93431124115580708531565893)
      ·
        refine ⟨17518335771671382849668605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93431124115580708531565893 17518335771671382849668605)
        ·
          refine ⟨6569375914376768568625727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17518335771671382849668605 6569375914376768568625727)
          ·
            refine ⟨9854063871565152852938591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6569375914376768568625727 9854063871565152852938591)
            ·
              refine ⟨14781095807347729279407887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9854063871565152852938591 14781095807347729279407887)
              ·
                refine ⟨22171643711021593919111831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781095807347729279407887 22171643711021593919111831)
                ·
                  refine ⟨33257465566532390878667747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22171643711021593919111831 33257465566532390878667747)
                  ·
                    refine ⟨49886198349798586318001621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33257465566532390878667747 49886198349798586318001621)
                    ·
                      refine ⟨1169207773823404366828163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49886198349798586318001621 1169207773823404366828163)
                      ·
                        rfl

theorem cell23_2277024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2277024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277024 prefixEnd_2277024 := by exact prefixLift 2277024
  have htrace : WordTrace (prefixWord ++ tailWord_2277024) baseStart_2277024 baseEnd_2277024 := by
    simpa [prefixWord, tailWord_2277024, baseEnd_2277024] using wordTrace_append hprefix tailTrace_2277024
  have hstable : (prefixWord ++ tailWord_2277024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277024).length < 2 ^ (prefixWord ++ tailWord_2277024).sum := by decide
  have hdescent : baseEnd_2277024 < baseStart_2277024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277064 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2277064 : Nat := 118140960795 + 2277064 * 2 ^ 59
def prefixEnd_2277064 : Nat := 4983230072969 + 3 ^ 40 * 2277064 * 2
def baseEnd_2277064 : Nat := 1169228313049584210327979

theorem tailTrace_2277064 : CollatzResearch.WordTrace tailWord_2277064 prefixEnd_2277064 1169228313049584210327979 := by
  unfold tailWord_2277064
  simp only [CollatzResearch.WordTrace]
  refine ⟨41525673511296747207535123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55367564681728996276713497 41525673511296747207535123)
  ·
    refine ⟨62288510266945120811302685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41525673511296747207535123 62288510266945120811302685)
    ·
      refine ⟨23358191350104420304238507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62288510266945120811302685 23358191350104420304238507)
      ·
        refine ⟨35037287025156630456357761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23358191350104420304238507 35037287025156630456357761)
        ·
          refine ⟨26277965268867472842268321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35037287025156630456357761 26277965268867472842268321)
          ·
            refine ⟨19708473951650604631701241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26277965268867472842268321 19708473951650604631701241)
            ·
              refine ⟨14781355463737953473775931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19708473951650604631701241 14781355463737953473775931)
              ·
                refine ⟨22172033195606930210663897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781355463737953473775931 22172033195606930210663897)
                ·
                  refine ⟨16629024896705197657997923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22172033195606930210663897 16629024896705197657997923)
                  ·
                    refine ⟨24943537345057796486996885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16629024896705197657997923 24943537345057796486996885)
                    ·
                      refine ⟨1169228313049584210327979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24943537345057796486996885 1169228313049584210327979)
                      ·
                        rfl

theorem cell23_2277064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2277064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277064 prefixEnd_2277064 := by exact prefixLift 2277064
  have htrace : WordTrace (prefixWord ++ tailWord_2277064) baseStart_2277064 baseEnd_2277064 := by
    simpa [prefixWord, tailWord_2277064, baseEnd_2277064] using wordTrace_append hprefix tailTrace_2277064
  have hstable : (prefixWord ++ tailWord_2277064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277064).length < 2 ^ (prefixWord ++ tailWord_2277064).sum := by decide
  have hdescent : baseEnd_2277064 < baseStart_2277064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277095 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 3, 4]
def baseStart_2277095 : Nat := 118140960795 + 2277095 * 2 ^ 59
def prefixEnd_2277095 : Nat := 4983230072969 + 3 ^ 40 * 2277095 * 2
def baseEnd_2277095 : Nat := 389748076983291196346779

theorem tailTrace_2277095 : CollatzResearch.WordTrace tailWord_2277095 prefixEnd_2277095 389748076983291196346779 := by
  unfold tailWord_2277095
  simp only [CollatzResearch.WordTrace]
  refine ⟨83052477685481186709448739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55368318456987457806299159 83052477685481186709448739)
  ·
    refine ⟨124578716528221780064173109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83052477685481186709448739 124578716528221780064173109)
    ·
      refine ⟨11679254674520791881016229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124578716528221780064173109 11679254674520791881016229)
      ·
        refine ⟨2189860251472648477690543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11679254674520791881016229 2189860251472648477690543)
        ·
          refine ⟨3284790377208972716535815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189860251472648477690543 3284790377208972716535815)
          ·
            refine ⟨4927185565813459074803723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284790377208972716535815 4927185565813459074803723)
            ·
              refine ⟨7390778348720188612205585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4927185565813459074803723 7390778348720188612205585)
              ·
                refine ⟨5543083761540141459154189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390778348720188612205585 5543083761540141459154189)
                ·
                  refine ⟨2078656410577553047182821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5543083761540141459154189 2078656410577553047182821)
                  ·
                    refine ⟨389748076983291196346779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078656410577553047182821 389748076983291196346779)
                    ·
                      rfl

theorem cell23_2277095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_2277095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277095 prefixEnd_2277095 := by exact prefixLift 2277095
  have htrace : WordTrace (prefixWord ++ tailWord_2277095) baseStart_2277095 baseEnd_2277095 := by
    simpa [prefixWord, tailWord_2277095, baseEnd_2277095] using wordTrace_append hprefix tailTrace_2277095
  have hstable : (prefixWord ++ tailWord_2277095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277095).length < 2 ^ (prefixWord ++ tailWord_2277095).sum := by decide
  have hdescent : baseEnd_2277095 < baseStart_2277095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277114 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_2277114 : Nat := 118140960795 + 2277114 * 2 ^ 59
def prefixEnd_2277114 : Nat := 4983230072969 + 3 ^ 40 * 2277114 * 2
def baseEnd_2277114 : Nat := 1169253987082309014702749

theorem tailTrace_2277114 : CollatzResearch.WordTrace tailWord_2277114 prefixEnd_2277114 1169253987082309014702749 := by
  unfold tailWord_2277114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20763292668103088238597599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55368780448274901969593597 20763292668103088238597599)
  ·
    refine ⟨31144939002154632357896399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20763292668103088238597599 31144939002154632357896399)
    ·
      refine ⟨46717408503231948536844599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31144939002154632357896399 46717408503231948536844599)
      ·
        refine ⟨70076112754847922805266899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46717408503231948536844599 70076112754847922805266899)
        ·
          refine ⟨105114169132271884207900349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70076112754847922805266899 105114169132271884207900349)
          ·
            refine ⟨39417813424601956577962631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105114169132271884207900349 39417813424601956577962631)
            ·
              refine ⟨59126720136902934866943947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39417813424601956577962631 59126720136902934866943947)
              ·
                refine ⟨88690080205354402300415921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59126720136902934866943947 88690080205354402300415921)
                ·
                  refine ⟨66517560154015801725311941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88690080205354402300415921 66517560154015801725311941)
                  ·
                    refine ⟨12472042528877962823495989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66517560154015801725311941 12472042528877962823495989)
                    ·
                      refine ⟨1169253987082309014702749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12472042528877962823495989 1169253987082309014702749)
                      ·
                        rfl

theorem cell23_2277114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_2277114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277114 prefixEnd_2277114 := by exact prefixLift 2277114
  have htrace : WordTrace (prefixWord ++ tailWord_2277114) baseStart_2277114 baseEnd_2277114 := by
    simpa [prefixWord, tailWord_2277114, baseEnd_2277114] using wordTrace_append hprefix tailTrace_2277114
  have hstable : (prefixWord ++ tailWord_2277114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277114).length < 2 ^ (prefixWord ++ tailWord_2277114).sum := by decide
  have hdescent : baseEnd_2277114 < baseStart_2277114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277128 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_2277128 : Nat := 118140960795 + 2277128 * 2 ^ 59
def prefixEnd_2277128 : Nat := 4983230072969 + 3 ^ 40 * 2277128 * 2
def baseEnd_2277128 : Nat := 1169261175811471959927685

theorem tailTrace_2277128 : CollatzResearch.WordTrace tailWord_2277128 prefixEnd_2277128 1169261175811471959927685 := by
  unfold tailWord_2277128
  simp only [CollatzResearch.WordTrace]
  refine ⟨41526840647180816672700019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55369120862907755563600025 41526840647180816672700019)
  ·
    refine ⟨62290260970771225009050029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41526840647180816672700019 62290260970771225009050029)
    ·
      refine ⟨23358847864039209378393761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62290260970771225009050029 23358847864039209378393761)
      ·
        refine ⟨17519135898029407033795321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23358847864039209378393761 17519135898029407033795321)
        ·
          refine ⟨13139351923522055275346491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17519135898029407033795321 13139351923522055275346491)
          ·
            refine ⟨19709027885283082913019737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13139351923522055275346491 19709027885283082913019737)
            ·
              refine ⟨14781770913962312184764803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19709027885283082913019737 14781770913962312184764803)
              ·
                refine ⟨22172656370943468277147205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781770913962312184764803 22172656370943468277147205)
                ·
                  refine ⟨4157373069551900301965101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22172656370943468277147205 4157373069551900301965101)
                  ·
                    refine ⟨1559014901081962613236913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4157373069551900301965101 1559014901081962613236913)
                    ·
                      refine ⟨1169261175811471959927685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559014901081962613236913 1169261175811471959927685)
                      ·
                        rfl

theorem cell23_2277128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_2277128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277128 prefixEnd_2277128 := by exact prefixLift 2277128
  have htrace : WordTrace (prefixWord ++ tailWord_2277128) baseStart_2277128 baseEnd_2277128 := by
    simpa [prefixWord, tailWord_2277128, baseEnd_2277128] using wordTrace_append hprefix tailTrace_2277128
  have hstable : (prefixWord ++ tailWord_2277128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277128).length < 2 ^ (prefixWord ++ tailWord_2277128).sum := by decide
  have hdescent : baseEnd_2277128 < baseStart_2277128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277178 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_2277178 : Nat := 118140960795 + 2277178 * 2 ^ 59
def prefixEnd_2277178 : Nat := 4983230072969 + 3 ^ 40 * 2277178 * 2
def baseEnd_2277178 : Nat := 1169286849844196764302455

theorem tailTrace_2277178 : CollatzResearch.WordTrace tailWord_2277178 prefixEnd_2277178 1169286849844196764302455 := by
  unfold tailWord_2277178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20763876236045122971180047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55370336629453661256480125 20763876236045122971180047)
  ·
    refine ⟨31145814354067684456770071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20763876236045122971180047 31145814354067684456770071)
    ·
      refine ⟨46718721531101526685155107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31145814354067684456770071 46718721531101526685155107)
      ·
        refine ⟨70078082296652290027732661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46718721531101526685155107 70078082296652290027732661)
        ·
          refine ⟨6569820215311152190099937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70078082296652290027732661 6569820215311152190099937)
          ·
            refine ⟨4927365161483364142574953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6569820215311152190099937 4927365161483364142574953)
            ·
              refine ⟨3695523871112523106931215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4927365161483364142574953 3695523871112523106931215)
              ·
                refine ⟨5543285806668784660396823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695523871112523106931215 5543285806668784660396823)
                ·
                  refine ⟨8314928710003176990595235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5543285806668784660396823 8314928710003176990595235)
                  ·
                    refine ⟨12472393065004765485892853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8314928710003176990595235 12472393065004765485892853)
                    ·
                      refine ⟨1169286849844196764302455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12472393065004765485892853 1169286849844196764302455)
                      ·
                        rfl

theorem cell23_2277178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_2277178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277178 prefixEnd_2277178 := by exact prefixLift 2277178
  have htrace : WordTrace (prefixWord ++ tailWord_2277178) baseStart_2277178 baseEnd_2277178 := by
    simpa [prefixWord, tailWord_2277178, baseEnd_2277178] using wordTrace_append hprefix tailTrace_2277178
  have hstable : (prefixWord ++ tailWord_2277178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277178).length < 2 ^ (prefixWord ++ tailWord_2277178).sum := by decide
  have hdescent : baseEnd_2277178 < baseStart_2277178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277181 : List Nat := [1, 4, 1, 4, 1, 1, 11]
def baseStart_2277181 : Nat := 118140960795 + 2277181 * 2 ^ 59
def prefixEnd_2277181 : Nat := 4983230072969 + 3 ^ 40 * 2277181 * 2
def baseEnd_2277181 : Nat := 14435659139335311760061

theorem tailTrace_2277181 : CollatzResearch.WordTrace tailWord_2277181 prefixEnd_2277181 14435659139335311760061 := by
  unfold tailWord_2277181
  simp only [CollatzResearch.WordTrace]
  refine ⟨83055614363169623397079397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55370409575446415598052931 83055614363169623397079397)
  ·
    refine ⟨15572927693094304386952387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83055614363169623397079397 15572927693094304386952387)
    ·
      refine ⟨23359391539641456580428581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572927693094304386952387 23359391539641456580428581)
      ·
        refine ⟨4379885913682773108830359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23359391539641456580428581 4379885913682773108830359)
        ·
          refine ⟨6569828870524159663245539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379885913682773108830359 6569828870524159663245539)
          ·
            refine ⟨9854743305786239494868309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6569828870524159663245539 9854743305786239494868309)
            ·
              refine ⟨14435659139335311760061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9854743305786239494868309 14435659139335311760061)
              ·
                rfl

theorem cell23_2277181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 11].length) (baseStart_2277181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277181 prefixEnd_2277181 := by exact prefixLift 2277181
  have htrace : WordTrace (prefixWord ++ tailWord_2277181) baseStart_2277181 baseEnd_2277181 := by
    simpa [prefixWord, tailWord_2277181, baseEnd_2277181] using wordTrace_append hprefix tailTrace_2277181
  have hstable : (prefixWord ++ tailWord_2277181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277181).length < 2 ^ (prefixWord ++ tailWord_2277181).sum := by decide
  have hdescent : baseEnd_2277181 < baseStart_2277181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277192 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_2277192 : Nat := 118140960795 + 2277192 * 2 ^ 59
def prefixEnd_2277192 : Nat := 4983230072969 + 3 ^ 40 * 2277192 * 2
def baseEnd_2277192 : Nat := 1169294038573359709527391

theorem tailTrace_2277192 : CollatzResearch.WordTrace tailWord_2277192 prefixEnd_2277192 1169294038573359709527391 := by
  unfold tailWord_2277192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41528007783064886137864915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55370677044086514850486553 41528007783064886137864915)
  ·
    refine ⟨62292011674597329206797373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41528007783064886137864915 62292011674597329206797373)
    ·
      refine ⟨23359504377973998452549015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62292011674597329206797373 23359504377973998452549015)
      ·
        refine ⟨35039256566960997678823523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23359504377973998452549015 35039256566960997678823523)
        ·
          refine ⟨52558884850441496518235285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35039256566960997678823523 52558884850441496518235285)
          ·
            refine ⟨2463697727364445149292279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52558884850441496518235285 2463697727364445149292279)
            ·
              refine ⟨3695546591046667723938419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463697727364445149292279 3695546591046667723938419)
              ·
                refine ⟨5543319886570001585907629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695546591046667723938419 5543319886570001585907629)
                ·
                  refine ⟨2078744957463750594715361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5543319886570001585907629 2078744957463750594715361)
                  ·
                    refine ⟨1559058718097812946036521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078744957463750594715361 1559058718097812946036521)
                    ·
                      refine ⟨1169294038573359709527391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559058718097812946036521 1169294038573359709527391)
                      ·
                        rfl

theorem cell23_2277192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_2277192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277192 prefixEnd_2277192 := by exact prefixLift 2277192
  have htrace : WordTrace (prefixWord ++ tailWord_2277192) baseStart_2277192 baseEnd_2277192 := by
    simpa [prefixWord, tailWord_2277192, baseEnd_2277192] using wordTrace_append hprefix tailTrace_2277192
  have hstable : (prefixWord ++ tailWord_2277192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277192).length < 2 ^ (prefixWord ++ tailWord_2277192).sum := by decide
  have hdescent : baseEnd_2277192 < baseStart_2277192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277202 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2277202 : Nat := 118140960795 + 2277202 * 2 ^ 59
def prefixEnd_2277202 : Nat := 4983230072969 + 3 ^ 40 * 2277202 * 2
def baseEnd_2277202 : Nat := 389766391126634890134115

theorem tailTrace_2277202 : CollatzResearch.WordTrace tailWord_2277202 prefixEnd_2277202 389766391126634890134115 := by
  unfold tailWord_2277202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20764095074023385995898465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55370920197395695989062573 20764095074023385995898465)
  ·
    refine ⟨15573071305517539496923849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20764095074023385995898465 15573071305517539496923849)
    ·
      refine ⟨11679803479138154622692887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15573071305517539496923849 11679803479138154622692887)
      ·
        refine ⟨17519705218707231934039331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11679803479138154622692887 17519705218707231934039331)
        ·
          refine ⟨26279557828060847901058997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17519705218707231934039331 26279557828060847901058997)
          ·
            refine ⟨2463708546380704490724281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26279557828060847901058997 2463708546380704490724281)
            ·
              refine ⟨1847781409785528368043211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2463708546380704490724281 1847781409785528368043211)
              ·
                refine ⟨2771672114678292552064817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847781409785528368043211 2771672114678292552064817)
                ·
                  refine ⟨2078754086008719414048613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2771672114678292552064817 2078754086008719414048613)
                  ·
                    refine ⟨389766391126634890134115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078754086008719414048613 389766391126634890134115)
                    ·
                      rfl

theorem cell23_2277202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2277202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277202 prefixEnd_2277202 := by exact prefixLift 2277202
  have htrace : WordTrace (prefixWord ++ tailWord_2277202) baseStart_2277202 baseEnd_2277202 := by
    simpa [prefixWord, tailWord_2277202, baseEnd_2277202] using wordTrace_append hprefix tailTrace_2277202
  have hstable : (prefixWord ++ tailWord_2277202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277202).length < 2 ^ (prefixWord ++ tailWord_2277202).sum := by decide
  have hdescent : baseEnd_2277202 < baseStart_2277202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277241 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_2277241 : Nat := 118140960795 + 2277241 * 2 ^ 59
def prefixEnd_2277241 : Nat := 4983230072969 + 3 ^ 40 * 2277241 * 2
def baseEnd_2277241 : Nat := 389773066375143339271555

theorem tailTrace_2277241 : CollatzResearch.WordTrace tailWord_2277241 prefixEnd_2277241 389773066375143339271555 := by
  unfold tailWord_2277241
  simp only [CollatzResearch.WordTrace]
  refine ⟨83057802742952253644263577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55371868495301502429509051 83057802742952253644263577)
  ·
    refine ⟨62293352057214190233197683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83057802742952253644263577 62293352057214190233197683)
    ·
      refine ⟨93440028085821285349796525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62293352057214190233197683 93440028085821285349796525)
      ·
        refine ⟨35040010532182982006173697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93440028085821285349796525 35040010532182982006173697)
        ·
          refine ⟨26280007899137236504630273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35040010532182982006173697 26280007899137236504630273)
          ·
            refine ⟨19710005924352927378472705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26280007899137236504630273 19710005924352927378472705)
            ·
              refine ⟨14782504443264695533854529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19710005924352927378472705 14782504443264695533854529)
              ·
                refine ⟨11086878332448521650390897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14782504443264695533854529 11086878332448521650390897)
                ·
                  refine ⟨8315158749336391237793173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11086878332448521650390897 8315158749336391237793173)
                  ·
                    refine ⟨389773066375143339271555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8315158749336391237793173 389773066375143339271555)
                    ·
                      rfl

theorem cell23_2277241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_2277241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277241 prefixEnd_2277241 := by exact prefixLift 2277241
  have htrace : WordTrace (prefixWord ++ tailWord_2277241) baseStart_2277241 baseEnd_2277241 := by
    simpa [prefixWord, tailWord_2277241, baseEnd_2277241] using wordTrace_append hprefix tailTrace_2277241
  have hstable : (prefixWord ++ tailWord_2277241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277241).length < 2 ^ (prefixWord ++ tailWord_2277241).sum := by decide
  have hdescent : baseEnd_2277241 < baseStart_2277241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277248 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2]
def baseStart_2277248 : Nat := 118140960795 + 2277248 * 2 ^ 59
def prefixEnd_2277248 : Nat := 4983230072969 + 3 ^ 40 * 2277248 * 2
def baseEnd_2277248 : Nat := 1169322793490011490427133

theorem tailTrace_2277248 : CollatzResearch.WordTrace tailWord_2277248 prefixEnd_2277248 1169322793490011490427133 := by
  unfold tailWord_2277248
  simp only [CollatzResearch.WordTrace]
  refine ⟨41529029026963446919884199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55372038702617929226512265 41529029026963446919884199)
  ·
    refine ⟨62293543540445170379826299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41529029026963446919884199 62293543540445170379826299)
    ·
      refine ⟨93440315310667755569739449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62293543540445170379826299 93440315310667755569739449)
      ·
        refine ⟨70080236483000816677304587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93440315310667755569739449 70080236483000816677304587)
        ·
          refine ⟨105120354724501225015956881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70080236483000816677304587 105120354724501225015956881)
          ·
            refine ⟨78840266043375918761967661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105120354724501225015956881 78840266043375918761967661)
            ·
              refine ⟨29565099766265969535737873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78840266043375918761967661 29565099766265969535737873)
              ·
                refine ⟨22173824824699477151803405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29565099766265969535737873 22173824824699477151803405)
                ·
                  refine ⟨8315184309262303931926277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22173824824699477151803405 8315184309262303931926277)
                  ·
                    refine ⟨1559097057986681987236177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8315184309262303931926277 1559097057986681987236177)
                    ·
                      refine ⟨1169322793490011490427133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559097057986681987236177 1169322793490011490427133)
                      ·
                        rfl

theorem cell23_2277248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_2277248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277248 prefixEnd_2277248 := by exact prefixLift 2277248
  have htrace : WordTrace (prefixWord ++ tailWord_2277248) baseStart_2277248 baseEnd_2277248 := by
    simpa [prefixWord, tailWord_2277248, baseEnd_2277248] using wordTrace_append hprefix tailTrace_2277248
  have hstable : (prefixWord ++ tailWord_2277248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277248).length < 2 ^ (prefixWord ++ tailWord_2277248).sum := by decide
  have hdescent : baseEnd_2277248 < baseStart_2277248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277271 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 9]
def baseStart_2277271 : Nat := 118140960795 + 2277271 * 2 ^ 59
def prefixEnd_2277271 : Nat := 4983230072969 + 3 ^ 40 * 2277271 * 2
def baseEnd_2277271 : Nat := 129926067060562766715503

theorem tailTrace_2277271 : CollatzResearch.WordTrace tailWord_2277271 prefixEnd_2277271 129926067060562766715503 := by
  unfold tailWord_2277271
  simp only [CollatzResearch.WordTrace]
  refine ⟨83058896932843568767855667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55372597955229045845237111 83058896932843568767855667)
  ·
    refine ⟨124588345399265353151783501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83058896932843568767855667 124588345399265353151783501)
    ·
      refine ⟨46720629524724507431918813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124588345399265353151783501 46720629524724507431918813)
      ·
        refine ⟨17520236071771690286969555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46720629524724507431918813 17520236071771690286969555)
        ·
          refine ⟨26280354107657535430454333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520236071771690286969555 26280354107657535430454333)
          ·
            refine ⟨9855132790371575786420375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26280354107657535430454333 9855132790371575786420375)
            ·
              refine ⟨14782699185557363679630563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855132790371575786420375 14782699185557363679630563)
              ·
                refine ⟨22174048778336045519445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14782699185557363679630563 22174048778336045519445845)
                ·
                  refine ⟨129926067060562766715503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22174048778336045519445845 129926067060562766715503)
                  ·
                    rfl

theorem cell23_2277271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 9].length) (baseStart_2277271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277271 prefixEnd_2277271 := by exact prefixLift 2277271
  have htrace : WordTrace (prefixWord ++ tailWord_2277271) baseStart_2277271 baseEnd_2277271 := by
    simpa [prefixWord, tailWord_2277271, baseEnd_2277271] using wordTrace_append hprefix tailTrace_2277271
  have hstable : (prefixWord ++ tailWord_2277271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277271).length < 2 ^ (prefixWord ++ tailWord_2277271).sum := by decide
  have hdescent : baseEnd_2277271 < baseStart_2277271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277311 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_2277311 : Nat := 118140960795 + 2277311 * 2 ^ 59
def prefixEnd_2277311 : Nat := 4983230072969 + 3 ^ 40 * 2277311 * 2
def baseEnd_2277311 : Nat := 1169355142771244743939343

theorem tailTrace_2277311 : CollatzResearch.WordTrace tailWord_2277311 prefixEnd_2277311 1169355142771244743939343 := by
  unfold tailWord_2277311
  simp only [CollatzResearch.WordTrace]
  refine ⟨83060355852698655599311787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55373570568465770399541191 83060355852698655599311787)
  ·
    refine ⟨124590533779047983398967681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83060355852698655599311787 124590533779047983398967681)
    ·
      refine ⟨93442900334285987549225761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124590533779047983398967681 93442900334285987549225761)
      ·
        refine ⟨70082175250714490661919321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93442900334285987549225761 70082175250714490661919321)
        ·
          refine ⟨52561631438035867996439491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70082175250714490661919321 52561631438035867996439491)
          ·
            refine ⟨78842447157053801994659237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52561631438035867996439491 78842447157053801994659237)
            ·
              refine ⟨14782958841947587873998607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78842447157053801994659237 14782958841947587873998607)
              ·
                refine ⟨22174438262921381810997911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14782958841947587873998607 22174438262921381810997911)
                ·
                  refine ⟨33261657394382072716496867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22174438262921381810997911 33261657394382072716496867)
                  ·
                    refine ⟨49892486091573109074745301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33261657394382072716496867 49892486091573109074745301)
                    ·
                      refine ⟨1169355142771244743939343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49892486091573109074745301 1169355142771244743939343)
                      ·
                        rfl

theorem cell23_2277311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_2277311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277311 prefixEnd_2277311 := by exact prefixLift 2277311
  have htrace : WordTrace (prefixWord ++ tailWord_2277311) baseStart_2277311 baseEnd_2277311 := by
    simpa [prefixWord, tailWord_2277311, baseEnd_2277311] using wordTrace_append hprefix tailTrace_2277311
  have hstable : (prefixWord ++ tailWord_2277311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277311).length < 2 ^ (prefixWord ++ tailWord_2277311).sum := by decide
  have hdescent : baseEnd_2277311 < baseStart_2277311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277412 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 6]
def baseStart_2277412 : Nat := 118140960795 + 2277412 * 2 ^ 59
def prefixEnd_2277412 : Nat := 4983230072969 + 3 ^ 40 * 2277412 * 2
def baseEnd_2277412 : Nat := 129934111590816538752931

theorem tailTrace_2277412 : CollatzResearch.WordTrace tailWord_2277412 prefixEnd_2277412 129934111590816538752931 := by
  unfold tailWord_2277412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41532019812666374924369245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55376026416888499899158993 41532019812666374924369245)
  ·
    refine ⟨15574507429749890596638467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41532019812666374924369245 15574507429749890596638467)
    ·
      refine ⟨23361761144624835894957701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15574507429749890596638467 23361761144624835894957701)
      ·
        refine ⟨4380330214617156730304569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23361761144624835894957701 4380330214617156730304569)
        ·
          refine ⟨3285247660962867547728427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4380330214617156730304569 3285247660962867547728427)
          ·
            refine ⟨4927871491444301321592641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285247660962867547728427 4927871491444301321592641)
            ·
              refine ⟨3695903618583225991194481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4927871491444301321592641 3695903618583225991194481)
              ·
                refine ⟨2771927713937419493395861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695903618583225991194481 2771927713937419493395861)
                ·
                  refine ⟨129934111590816538752931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2771927713937419493395861 129934111590816538752931)
                  ·
                    rfl

theorem cell23_2277412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_2277412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277412 prefixEnd_2277412 := by exact prefixLift 2277412
  have htrace : WordTrace (prefixWord ++ tailWord_2277412) baseStart_2277412 baseEnd_2277412 := by
    simpa [prefixWord, tailWord_2277412, baseEnd_2277412] using wordTrace_append hprefix tailTrace_2277412
  have hstable : (prefixWord ++ tailWord_2277412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277412).length < 2 ^ (prefixWord ++ tailWord_2277412).sum := by decide
  have hdescent : baseEnd_2277412 < baseStart_2277412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277416 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2277416 : Nat := 118140960795 + 2277416 * 2 ^ 59
def prefixEnd_2277416 : Nat := 4983230072969 + 3 ^ 40 * 2277416 * 2
def baseEnd_2277416 : Nat := 389803019413322277708787

theorem tailTrace_2277416 : CollatzResearch.WordTrace tailWord_2277416 prefixEnd_2277416 389803019413322277708787 := by
  unfold tailWord_2277416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41532092758659129265942051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55376123678212172354589401 41532092758659129265942051)
  ·
    refine ⟨62298139137988693898913077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41532092758659129265942051 62298139137988693898913077)
    ·
      refine ⟨5840450544186440053023101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62298139137988693898913077 5840450544186440053023101)
      ·
        refine ⟨2190168954069915019883663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5840450544186440053023101 2190168954069915019883663)
        ·
          refine ⟨3285253431104872529825495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190168954069915019883663 3285253431104872529825495)
          ·
            refine ⟨4927880146657308794738243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285253431104872529825495 4927880146657308794738243)
            ·
              refine ⟨7391820219985963192107365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4927880146657308794738243 7391820219985963192107365)
              ·
                refine ⟨1385966291247368098520131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7391820219985963192107365 1385966291247368098520131)
                ·
                  refine ⟨2078949436871052147780197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385966291247368098520131 2078949436871052147780197)
                  ·
                    refine ⟨389803019413322277708787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078949436871052147780197 389803019413322277708787)
                    ·
                      rfl

theorem cell23_2277416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2277416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277416 prefixEnd_2277416 := by exact prefixLift 2277416
  have htrace : WordTrace (prefixWord ++ tailWord_2277416) baseStart_2277416 baseEnd_2277416 := by
    simpa [prefixWord, tailWord_2277416, baseEnd_2277416] using wordTrace_append hprefix tailTrace_2277416
  have hstable : (prefixWord ++ tailWord_2277416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277416).length < 2 ^ (prefixWord ++ tailWord_2277416).sum := by decide
  have hdescent : baseEnd_2277416 < baseStart_2277416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277445 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_2277445 : Nat := 118140960795 + 2277445 * 2 ^ 59
def prefixEnd_2277445 : Nat := 4983230072969 + 3 ^ 40 * 2277445 * 2
def baseEnd_2277445 : Nat := 1169423949178947219663727

theorem tailTrace_2277445 : CollatzResearch.WordTrace tailWord_2277445 prefixEnd_2277445 1169423949178947219663727 := by
  unfold tailWord_2277445
  simp only [CollatzResearch.WordTrace]
  refine ⟨83065243234213196484689789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55376828822808797656459859 83065243234213196484689789)
  ·
    refine ⟨31149466212829948681758671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83065243234213196484689789 31149466212829948681758671)
    ·
      refine ⟨46724199319244923022638007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31149466212829948681758671 46724199319244923022638007)
      ·
        refine ⟨70086298978867384533957011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46724199319244923022638007 70086298978867384533957011)
        ·
          refine ⟨105129448468301076800935517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70086298978867384533957011 105129448468301076800935517)
          ·
            refine ⟨39423543175612903800350819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105129448468301076800935517 39423543175612903800350819)
            ·
              refine ⟨59135314763419355700526229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39423543175612903800350819 59135314763419355700526229)
              ·
                refine ⟨2771967879535282298462167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59135314763419355700526229 2771967879535282298462167)
                ·
                  refine ⟨4157951819302923447693251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771967879535282298462167 4157951819302923447693251)
                  ·
                    refine ⟨6236927728954385171539877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157951819302923447693251 6236927728954385171539877)
                    ·
                      refine ⟨1169423949178947219663727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6236927728954385171539877 1169423949178947219663727)
                      ·
                        rfl

theorem cell23_2277445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_2277445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277445 prefixEnd_2277445 := by exact prefixLift 2277445
  have htrace : WordTrace (prefixWord ++ tailWord_2277445) baseStart_2277445 baseEnd_2277445 := by
    simpa [prefixWord, tailWord_2277445, baseEnd_2277445] using wordTrace_append hprefix tailTrace_2277445
  have hstable : (prefixWord ++ tailWord_2277445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277445).length < 2 ^ (prefixWord ++ tailWord_2277445).sum := by decide
  have hdescent : baseEnd_2277445 < baseStart_2277445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277448 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2277448 : Nat := 118140960795 + 2277448 * 2 ^ 59
def prefixEnd_2277448 : Nat := 4983230072969 + 3 ^ 40 * 2277448 * 2
def baseEnd_2277448 : Nat := 1169425489620910707926213

theorem tailTrace_2277448 : CollatzResearch.WordTrace tailWord_2277448 prefixEnd_2277448 1169425489620910707926213 := by
  unfold tailWord_2277448
  simp only [CollatzResearch.WordTrace]
  refine ⟨41532676326601163998524499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55376901768801551998032665 41532676326601163998524499)
  ·
    refine ⟨62299014489901745997786749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41532676326601163998524499 62299014489901745997786749)
    ·
      refine ⟨23362130433713154749170031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62299014489901745997786749 23362130433713154749170031)
      ·
        refine ⟨35043195650569732123755047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23362130433713154749170031 35043195650569732123755047)
        ·
          refine ⟨52564793475854598185632571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35043195650569732123755047 52564793475854598185632571)
          ·
            refine ⟨78847190213781897278448857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52564793475854598185632571 78847190213781897278448857)
            ·
              refine ⟨59135392660336422958836643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78847190213781897278448857 59135392660336422958836643)
              ·
                refine ⟨88703088990504634438254965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59135392660336422958836643 88703088990504634438254965)
                ·
                  refine ⟨8315914592859809478586403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88703088990504634438254965 8315914592859809478586403)
                  ·
                    refine ⟨12473871889289714217879605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8315914592859809478586403 12473871889289714217879605)
                    ·
                      refine ⟨1169425489620910707926213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12473871889289714217879605 1169425489620910707926213)
                      ·
                        rfl

theorem cell23_2277448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2277448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277448 prefixEnd_2277448 := by exact prefixLift 2277448
  have htrace : WordTrace (prefixWord ++ tailWord_2277448) baseStart_2277448 baseEnd_2277448 := by
    simpa [prefixWord, tailWord_2277448, baseEnd_2277448] using wordTrace_append hprefix tailTrace_2277448
  have hstable : (prefixWord ++ tailWord_2277448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277448).length < 2 ^ (prefixWord ++ tailWord_2277448).sum := by decide
  have hdescent : baseEnd_2277448 < baseStart_2277448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277472 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_2277472 : Nat := 118140960795 + 2277472 * 2 ^ 59
def prefixEnd_2277472 : Nat := 4983230072969 + 3 ^ 40 * 2277472 * 2
def baseEnd_2277472 : Nat := 389812604385539538008701

theorem tailTrace_2277472 : CollatzResearch.WordTrace tailWord_2277472 prefixEnd_2277472 389812604385539538008701 := by
  unfold tailWord_2277472
  simp only [CollatzResearch.WordTrace]
  refine ⟨41533114002557690047961335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55377485336743586730615113 41533114002557690047961335)
  ·
    refine ⟨62299671003836535071942003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41533114002557690047961335 62299671003836535071942003)
    ·
      refine ⟨93449506505754802607913005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62299671003836535071942003 93449506505754802607913005)
      ·
        refine ⟨35043564939658050977967377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93449506505754802607913005 35043564939658050977967377)
        ·
          refine ⟨26282673704743538233475533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35043564939658050977967377 26282673704743538233475533)
          ·
            refine ⟨9856002639278826837553325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26282673704743538233475533 9856002639278826837553325)
            ·
              refine ⟨3696000989729560064082497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9856002639278826837553325 3696000989729560064082497)
              ·
                refine ⟨2772000742297170048061873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696000989729560064082497 2772000742297170048061873)
                ·
                  refine ⟨2079000556722877536046405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772000742297170048061873 2079000556722877536046405)
                  ·
                    refine ⟨389812604385539538008701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079000556722877536046405 389812604385539538008701)
                    ·
                      rfl

theorem cell23_2277472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_2277472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277472 prefixEnd_2277472 := by exact prefixLift 2277472
  have htrace : WordTrace (prefixWord ++ tailWord_2277472) baseStart_2277472 baseEnd_2277472 := by
    simpa [prefixWord, tailWord_2277472, baseEnd_2277472] using wordTrace_append hprefix tailTrace_2277472
  have hstable : (prefixWord ++ tailWord_2277472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277472).length < 2 ^ (prefixWord ++ tailWord_2277472).sum := by decide
  have hdescent : baseEnd_2277472 < baseStart_2277472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277479 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_2277479 : Nat := 118140960795 + 2277479 * 2 ^ 59
def prefixEnd_2277479 : Nat := 4983230072969 + 3 ^ 40 * 2277479 * 2
def baseEnd_2277479 : Nat := 1169441407521200086638571

theorem tailTrace_2277479 : CollatzResearch.WordTrace tailWord_2277479 prefixEnd_2277479 1169441407521200086638571 := by
  unfold tailWord_2277479
  simp only [CollatzResearch.WordTrace]
  refine ⟨83066483316090020291427491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55377655544060013527618327 83066483316090020291427491)
  ·
    refine ⟨124599724974135030437141237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83066483316090020291427491 124599724974135030437141237)
    ·
      refine ⟨11681224216325159103481991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124599724974135030437141237 11681224216325159103481991)
      ·
        refine ⟨17521836324487738655222987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681224216325159103481991 17521836324487738655222987)
        ·
          refine ⟨26282754486731607982834481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17521836324487738655222987 26282754486731607982834481)
          ·
            refine ⟨19712065865048705987125861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26282754486731607982834481 19712065865048705987125861)
            ·
              refine ⟨3696012349696632372586099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19712065865048705987125861 3696012349696632372586099)
              ·
                refine ⟨5544018524544948558879149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696012349696632372586099 5544018524544948558879149)
                ·
                  refine ⟨2079006946704355709579681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5544018524544948558879149 2079006946704355709579681)
                  ·
                    refine ⟨1559255210028266782184761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079006946704355709579681 1559255210028266782184761)
                    ·
                      refine ⟨1169441407521200086638571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559255210028266782184761 1169441407521200086638571)
                      ·
                        rfl

theorem cell23_2277479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_2277479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277479 prefixEnd_2277479 := by exact prefixLift 2277479
  have htrace : WordTrace (prefixWord ++ tailWord_2277479) baseStart_2277479 baseEnd_2277479 := by
    simpa [prefixWord, tailWord_2277479, baseEnd_2277479] using wordTrace_append hprefix tailTrace_2277479
  have hstable : (prefixWord ++ tailWord_2277479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277479).length < 2 ^ (prefixWord ++ tailWord_2277479).sum := by decide
  have hdescent : baseEnd_2277479 < baseStart_2277479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277482 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2277482 : Nat := 118140960795 + 2277482 * 2 ^ 59
def prefixEnd_2277482 : Nat := 4983230072969 + 3 ^ 40 * 2277482 * 2
def baseEnd_2277482 : Nat := 1169442947963163574901057

theorem tailTrace_2277482 : CollatzResearch.WordTrace tailWord_2277482 prefixEnd_2277482 1169442947963163574901057 := by
  unfold tailWord_2277482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766648183769787950946675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55377728490052767869191133 20766648183769787950946675)
  ·
    refine ⟨31149972275654681926420013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20766648183769787950946675 31149972275654681926420013)
    ·
      refine ⟨11681239603370505722407505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31149972275654681926420013 11681239603370505722407505)
      ·
        refine ⟨8760929702527879291805629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11681239603370505722407505 8760929702527879291805629)
        ·
          refine ⟨3285348638447954734427111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8760929702527879291805629 3285348638447954734427111)
          ·
            refine ⟨4928022957671932101640667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285348638447954734427111 4928022957671932101640667)
            ·
              refine ⟨7392034436507898152461001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928022957671932101640667 7392034436507898152461001)
              ·
                refine ⟨5544025827380923614345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7392034436507898152461001 5544025827380923614345751)
                ·
                  refine ⟨8316038741071385421518627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5544025827380923614345751 8316038741071385421518627)
                  ·
                    refine ⟨12474058111607078132277941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8316038741071385421518627 12474058111607078132277941)
                    ·
                      refine ⟨1169442947963163574901057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12474058111607078132277941 1169442947963163574901057)
                      ·
                        rfl

theorem cell23_2277482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2277482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277482 prefixEnd_2277482 := by exact prefixLift 2277482
  have htrace : WordTrace (prefixWord ++ tailWord_2277482) baseStart_2277482 baseEnd_2277482 := by
    simpa [prefixWord, tailWord_2277482, baseEnd_2277482] using wordTrace_append hprefix tailTrace_2277482
  have hstable : (prefixWord ++ tailWord_2277482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277482).length < 2 ^ (prefixWord ++ tailWord_2277482).sum := by decide
  have hdescent : baseEnd_2277482 < baseStart_2277482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277530 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2277530 : Nat := 118140960795 + 2277530 * 2 ^ 59
def prefixEnd_2277530 : Nat := 4983230072969 + 3 ^ 40 * 2277530 * 2
def baseEnd_2277530 : Nat := 1169467595034579387100837

theorem tailTrace_2277530 : CollatzResearch.WordTrace tailWord_2277530 prefixEnd_2277530 1169467595034579387100837 := by
  unfold tailWord_2277530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20767085859726314000383511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55378895625936837334356029 20767085859726314000383511)
  ·
    refine ⟨31150628789589471000575267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20767085859726314000383511 31150628789589471000575267)
    ·
      refine ⟨46725943184384206500862901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31150628789589471000575267 46725943184384206500862901)
      ·
        refine ⟨4380557173536019359455897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46725943184384206500862901 4380557173536019359455897)
        ·
          refine ⟨3285417880152014519591923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4380557173536019359455897 3285417880152014519591923)
          ·
            refine ⟨4928126820228021779387885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285417880152014519591923 4928126820228021779387885)
            ·
              refine ⟨1848047557585508167270457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4928126820228021779387885 1848047557585508167270457)
              ·
                refine ⟨1386035668189131125452843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848047557585508167270457 1386035668189131125452843)
                ·
                  refine ⟨2079053502283696688179265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386035668189131125452843 2079053502283696688179265)
                  ·
                    refine ⟨1559290126712772516134449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079053502283696688179265 1559290126712772516134449)
                    ·
                      refine ⟨1169467595034579387100837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559290126712772516134449 1169467595034579387100837)
                      ·
                        rfl

theorem cell23_2277530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2277530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277530 prefixEnd_2277530 := by exact prefixLift 2277530
  have htrace : WordTrace (prefixWord ++ tailWord_2277530) baseStart_2277530 baseEnd_2277530 := by
    simpa [prefixWord, tailWord_2277530, baseEnd_2277530] using wordTrace_append hprefix tailTrace_2277530
  have hstable : (prefixWord ++ tailWord_2277530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277530).length < 2 ^ (prefixWord ++ tailWord_2277530).sum := by decide
  have hdescent : baseEnd_2277530 < baseStart_2277530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277550 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2277550 : Nat := 118140960795 + 2277550 * 2 ^ 59
def prefixEnd_2277550 : Nat := 4983230072969 + 3 ^ 40 * 2277550 * 2
def baseEnd_2277550 : Nat := 1169477864647669308850745

theorem tailTrace_2277550 : CollatzResearch.WordTrace tailWord_2277550 prefixEnd_2277550 1169477864647669308850745 := by
  unfold tailWord_2277550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383634112354099927157763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55379381932555199611508069 10383634112354099927157763)
  ·
    refine ⟨15575451168531149890736645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10383634112354099927157763 15575451168531149890736645)
    ·
      refine ⟨2920397094099590604513121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15575451168531149890736645 2920397094099590604513121)
      ·
        refine ⟨2190297820574692953384841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920397094099590604513121 2190297820574692953384841)
        ·
          refine ⟨1642723365431019715038631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190297820574692953384841 1642723365431019715038631)
          ·
            refine ⟨2464085048146529572557947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642723365431019715038631 2464085048146529572557947)
            ·
              refine ⟨3696127572219794358836921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464085048146529572557947 3696127572219794358836921)
              ·
                refine ⟨2772095679164845769127691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696127572219794358836921 2772095679164845769127691)
                ·
                  refine ⟨4158143518747268653691537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772095679164845769127691 4158143518747268653691537)
                  ·
                    refine ⟨3118607639060451490268653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158143518747268653691537 3118607639060451490268653)
                    ·
                      refine ⟨1169477864647669308850745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3118607639060451490268653 1169477864647669308850745)
                      ·
                        rfl

theorem cell23_2277550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2277550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277550 prefixEnd_2277550 := by exact prefixLift 2277550
  have htrace : WordTrace (prefixWord ++ tailWord_2277550) baseStart_2277550 baseEnd_2277550 := by
    simpa [prefixWord, tailWord_2277550, baseEnd_2277550] using wordTrace_append hprefix tailTrace_2277550
  have hstable : (prefixWord ++ tailWord_2277550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277550).length < 2 ^ (prefixWord ++ tailWord_2277550).sum := by decide
  have hdescent : baseEnd_2277550 < baseStart_2277550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277565 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2277565 : Nat := 118140960795 + 2277565 * 2 ^ 59
def prefixEnd_2277565 : Nat := 4983230072969 + 3 ^ 40 * 2277565 * 2
def baseEnd_2277565 : Nat := 1169485566857486750163175

theorem tailTrace_2277565 : CollatzResearch.WordTrace tailWord_2277565 prefixEnd_2277565 1169485566857486750163175 := by
  unfold tailWord_2277565
  simp only [CollatzResearch.WordTrace]
  refine ⟨83069619993778456979058149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55379746662518971319372099 83069619993778456979058149)
  ·
    refine ⟨15575553748833460683573403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83069619993778456979058149 15575553748833460683573403)
    ·
      refine ⟨23363330623250191025360105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15575553748833460683573403 23363330623250191025360105)
      ·
        refine ⟨17522497967437643269020079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23363330623250191025360105 17522497967437643269020079)
        ·
          refine ⟨26283746951156464903530119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17522497967437643269020079 26283746951156464903530119)
          ·
            refine ⟨39425620426734697355295179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26283746951156464903530119 39425620426734697355295179)
            ·
              refine ⟨59138430640102046032942769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39425620426734697355295179 59138430640102046032942769)
              ·
                refine ⟨44353822980076534524707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59138430640102046032942769 44353822980076534524707077)
                ·
                  refine ⟨8316341808764350223382577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44353822980076534524707077 8316341808764350223382577)
                  ·
                    refine ⟨6237256356573262667536933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8316341808764350223382577 6237256356573262667536933)
                    ·
                      refine ⟨1169485566857486750163175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6237256356573262667536933 1169485566857486750163175)
                      ·
                        rfl

theorem cell23_2277565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2277565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277565 prefixEnd_2277565 := by exact prefixLift 2277565
  have htrace : WordTrace (prefixWord ++ tailWord_2277565) baseStart_2277565 baseEnd_2277565 := by
    simpa [prefixWord, tailWord_2277565, baseEnd_2277565] using wordTrace_append hprefix tailTrace_2277565
  have hstable : (prefixWord ++ tailWord_2277565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277565).length < 2 ^ (prefixWord ++ tailWord_2277565).sum := by decide
  have hdescent : baseEnd_2277565 < baseStart_2277565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277572 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2277572 : Nat := 118140960795 + 2277572 * 2 ^ 59
def prefixEnd_2277572 : Nat := 4983230072969 + 3 ^ 40 * 2277572 * 2
def baseEnd_2277572 : Nat := 1169489161222068222775643

theorem tailTrace_2277572 : CollatzResearch.WordTrace tailWord_2277572 prefixEnd_2277572 1169489161222068222775643 := by
  unfold tailWord_2277572
  simp only [CollatzResearch.WordTrace]
  refine ⟨41534937652376548587281485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55379916869835398116375313 41534937652376548587281485)
  ·
    refine ⟨15575601619641205720230557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41534937652376548587281485 15575601619641205720230557)
    ·
      refine ⟨5840850607365452145086459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15575601619641205720230557 5840850607365452145086459)
      ·
        refine ⟨8761275911048178217629689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840850607365452145086459 8761275911048178217629689)
        ·
          refine ⟨6570956933286133663222267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8761275911048178217629689 6570956933286133663222267)
          ·
            refine ⟨9856435399929200494833401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570956933286133663222267 9856435399929200494833401)
            ·
              refine ⟨7392326549946900371125051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9856435399929200494833401 7392326549946900371125051)
              ·
                refine ⟨11088489824920350556687577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7392326549946900371125051 11088489824920350556687577)
                ·
                  refine ⟨8316367368690262917515683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11088489824920350556687577 8316367368690262917515683)
                  ·
                    refine ⟨12474551053035394376273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8316367368690262917515683 12474551053035394376273525)
                    ·
                      refine ⟨1169489161222068222775643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12474551053035394376273525 1169489161222068222775643)
                      ·
                        rfl

theorem cell23_2277572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2277572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277572 prefixEnd_2277572 := by exact prefixLift 2277572
  have htrace : WordTrace (prefixWord ++ tailWord_2277572) baseStart_2277572 baseEnd_2277572 := by
    simpa [prefixWord, tailWord_2277572, baseEnd_2277572] using wordTrace_append hprefix tailTrace_2277572
  have hstable : (prefixWord ++ tailWord_2277572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277572).length < 2 ^ (prefixWord ++ tailWord_2277572).sum := by decide
  have hdescent : baseEnd_2277572 < baseStart_2277572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277586 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2277586 : Nat := 118140960795 + 2277586 * 2 ^ 59
def prefixEnd_2277586 : Nat := 4983230072969 + 3 ^ 40 * 2277586 * 2
def baseEnd_2277586 : Nat := 1169496349951231168000579

theorem tailTrace_2277586 : CollatzResearch.WordTrace tailWord_2277586 prefixEnd_2277586 1169496349951231168000579 := by
  unfold tailWord_2277586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20767596481675594391393153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55380257284468251710381741 20767596481675594391393153)
  ·
    refine ⟨15575697361256695793544865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20767596481675594391393153 15575697361256695793544865)
    ·
      refine ⟨11681773020942521845158649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15575697361256695793544865 11681773020942521845158649)
      ·
        refine ⟨8761329765706891383868987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11681773020942521845158649 8761329765706891383868987)
        ·
          refine ⟨13141994648560337075803481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8761329765706891383868987 13141994648560337075803481)
          ·
            refine ⟨9856495986420252806852611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13141994648560337075803481 9856495986420252806852611)
            ·
              refine ⟨14784743979630379210278917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9856495986420252806852611 14784743979630379210278917)
              ·
                refine ⟨2772139496180696101927297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14784743979630379210278917 2772139496180696101927297)
                ·
                  refine ⟨2079104622135522076445473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772139496180696101927297 2079104622135522076445473)
                  ·
                    refine ⟨1559328466601641557334105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079104622135522076445473 1559328466601641557334105)
                    ·
                      refine ⟨1169496349951231168000579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559328466601641557334105 1169496349951231168000579)
                      ·
                        rfl

theorem cell23_2277586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2277586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277586 prefixEnd_2277586 := by exact prefixLift 2277586
  have htrace : WordTrace (prefixWord ++ tailWord_2277586) baseStart_2277586 baseEnd_2277586 := by
    simpa [prefixWord, tailWord_2277586, baseEnd_2277586] using wordTrace_append hprefix tailTrace_2277586
  have hstable : (prefixWord ++ tailWord_2277586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277586).length < 2 ^ (prefixWord ++ tailWord_2277586).sum := by decide
  have hdescent : baseEnd_2277586 < baseStart_2277586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277612 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_2277612 : Nat := 118140960795 + 2277612 * 2 ^ 59
def prefixEnd_2277612 : Nat := 4983230072969 + 3 ^ 40 * 2277612 * 2
def baseEnd_2277612 : Nat := 1169509700448248066275459

theorem tailTrace_2277612 : CollatzResearch.WordTrace tailWord_2277612 prefixEnd_2277612 1169509700448248066275459 := by
  unfold tailWord_2277612
  simp only [CollatzResearch.WordTrace]
  refine ⟨41535667112304092003009545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55380889483072122670679393 41535667112304092003009545)
  ·
    refine ⟨31151750334228069002257159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41535667112304092003009545 31151750334228069002257159)
    ·
      refine ⟨46727625501342103503385739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31151750334228069002257159 46727625501342103503385739)
      ·
        refine ⟨70091438252013155255078609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46727625501342103503385739 70091438252013155255078609)
        ·
          refine ⟨52568578689009866441308957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70091438252013155255078609 52568578689009866441308957)
          ·
            refine ⟨19713217008378699915490859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52568578689009866441308957 19713217008378699915490859)
            ·
              refine ⟨29569825512568049873236289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19713217008378699915490859 29569825512568049873236289)
              ·
                refine ⟨22177369134426037404927217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29569825512568049873236289 22177369134426037404927217)
                ·
                  refine ⟨16633026850819528053695413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22177369134426037404927217 16633026850819528053695413)
                  ·
                    refine ⟨1559346267264330755033945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16633026850819528053695413 1559346267264330755033945)
                    ·
                      refine ⟨1169509700448248066275459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559346267264330755033945 1169509700448248066275459)
                      ·
                        rfl

theorem cell23_2277612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_2277612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277612 prefixEnd_2277612 := by exact prefixLift 2277612
  have htrace : WordTrace (prefixWord ++ tailWord_2277612) baseStart_2277612 baseEnd_2277612 := by
    simpa [prefixWord, tailWord_2277612, baseEnd_2277612] using wordTrace_append hprefix tailTrace_2277612
  have hstable : (prefixWord ++ tailWord_2277612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277612).length < 2 ^ (prefixWord ++ tailWord_2277612).sum := by decide
  have hdescent : baseEnd_2277612 < baseStart_2277612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277642 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2277642 : Nat := 118140960795 + 2277642 * 2 ^ 59
def prefixEnd_2277642 : Nat := 4983230072969 + 3 ^ 40 * 2277642 * 2
def baseEnd_2277642 : Nat := 1169525104867882948900321

theorem tailTrace_2277642 : CollatzResearch.WordTrace tailWord_2277642 prefixEnd_2277642 1169525104867882948900321 := by
  unfold tailWord_2277642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768107103624874782402795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55381618942999666086407453 20768107103624874782402795)
  ·
    refine ⟨31152160655437312173604193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20768107103624874782402795 31152160655437312173604193)
    ·
      refine ⟨23364120491577984130203145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31152160655437312173604193 23364120491577984130203145)
      ·
        refine ⟨17523090368683488097652359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23364120491577984130203145 17523090368683488097652359)
        ·
          refine ⟨26284635553025232146478539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17523090368683488097652359 26284635553025232146478539)
          ·
            refine ⟨39426953329537848219717809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26284635553025232146478539 39426953329537848219717809)
            ·
              refine ⟨29570214997153386164788357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39426953329537848219717809 29570214997153386164788357)
              ·
                refine ⟨5544415311966259905897817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29570214997153386164788357 5544415311966259905897817)
                ·
                  refine ⟨4158311483974694929423363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5544415311966259905897817 4158311483974694929423363)
                  ·
                    refine ⟨6237467225962042394135045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158311483974694929423363 6237467225962042394135045)
                    ·
                      refine ⟨1169525104867882948900321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6237467225962042394135045 1169525104867882948900321)
                      ·
                        rfl

theorem cell23_2277642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2277642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277642 prefixEnd_2277642 := by exact prefixLift 2277642
  have htrace : WordTrace (prefixWord ++ tailWord_2277642) baseStart_2277642 baseEnd_2277642 := by
    simpa [prefixWord, tailWord_2277642, baseEnd_2277642] using wordTrace_append hprefix tailTrace_2277642
  have hstable : (prefixWord ++ tailWord_2277642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277642).length < 2 ^ (prefixWord ++ tailWord_2277642).sum := by decide
  have hdescent : baseEnd_2277642 < baseStart_2277642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277705 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_2277705 : Nat := 118140960795 + 2277705 * 2 ^ 59
def prefixEnd_2277705 : Nat := 4983230072969 + 3 ^ 40 * 2277705 * 2
def baseEnd_2277705 : Nat := 1169557454149116202412531

theorem tailTrace_2277705 : CollatzResearch.WordTrace tailWord_2277705 prefixEnd_2277705 1169557454149116202412531 := by
  unfold tailWord_2277705
  simp only [CollatzResearch.WordTrace]
  refine ⟨83074726213271260889154569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55383150808847507259436379 83074726213271260889154569)
  ·
    refine ⟨62306044659953445666865927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83074726213271260889154569 62306044659953445666865927)
    ·
      refine ⟨93459066989930168500298891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62306044659953445666865927 93459066989930168500298891)
      ·
        refine ⟨140188600484895252750448337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93459066989930168500298891 140188600484895252750448337)
        ·
          refine ⟨105141450363671439562836253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140188600484895252750448337 105141450363671439562836253)
          ·
            refine ⟨39428043886376789836063595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105141450363671439562836253 39428043886376789836063595)
            ·
              refine ⟨59142065829565184754095393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39428043886376789836063595 59142065829565184754095393)
              ·
                refine ⟨44356549372173888565571545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59142065829565184754095393 44356549372173888565571545)
                ·
                  refine ⟨33267412029130416424178659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44356549372173888565571545 33267412029130416424178659)
                  ·
                    refine ⟨49901118043695624636267989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33267412029130416424178659 49901118043695624636267989)
                    ·
                      refine ⟨1169557454149116202412531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49901118043695624636267989 1169557454149116202412531)
                      ·
                        rfl

theorem cell23_2277705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_2277705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277705 prefixEnd_2277705 := by exact prefixLift 2277705
  have htrace : WordTrace (prefixWord ++ tailWord_2277705) baseStart_2277705 baseEnd_2277705 := by
    simpa [prefixWord, tailWord_2277705, baseEnd_2277705] using wordTrace_append hprefix tailTrace_2277705
  have hstable : (prefixWord ++ tailWord_2277705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277705).length < 2 ^ (prefixWord ++ tailWord_2277705).sum := by decide
  have hdescent : baseEnd_2277705 < baseStart_2277705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277716 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2277716 : Nat := 118140960795 + 2277716 * 2 ^ 59
def prefixEnd_2277716 : Nat := 4983230072969 + 3 ^ 40 * 2277716 * 2
def baseEnd_2277716 : Nat := 129951455826257295486109

theorem tailTrace_2277716 : CollatzResearch.WordTrace tailWord_2277716 prefixEnd_2277716 129951455826257295486109 := by
  unfold tailWord_2277716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41537563708115704883902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55383418277487606511870001 41537563708115704883902501)
  ·
    refine ⟨7788293195271694665731719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41537563708115704883902501 7788293195271694665731719)
    ·
      refine ⟨11682439792907541998597579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788293195271694665731719 11682439792907541998597579)
      ·
        refine ⟨17523659689361312997896369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11682439792907541998597579 17523659689361312997896369)
        ·
          refine ⟨13142744767020984748422277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17523659689361312997896369 13142744767020984748422277)
          ·
            refine ⟨2464264643816434640329177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13142744767020984748422277 2464264643816434640329177)
            ·
              refine ⟨1848198482862325980246883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464264643816434640329177 1848198482862325980246883)
              ·
                refine ⟨2772297724293488970370325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848198482862325980246883 2772297724293488970370325)
                ·
                  refine ⟨129951455826257295486109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2772297724293488970370325 129951455826257295486109)
                  ·
                    rfl

theorem cell23_2277716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2277716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277716 prefixEnd_2277716 := by exact prefixLift 2277716
  have htrace : WordTrace (prefixWord ++ tailWord_2277716) baseStart_2277716 baseEnd_2277716 := by
    simpa [prefixWord, tailWord_2277716, baseEnd_2277716] using wordTrace_append hprefix tailTrace_2277716
  have hstable : (prefixWord ++ tailWord_2277716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277716).length < 2 ^ (prefixWord ++ tailWord_2277716).sum := by decide
  have hdescent : baseEnd_2277716 < baseStart_2277716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277719 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_2277719 : Nat := 118140960795 + 2277719 * 2 ^ 59
def prefixEnd_2277719 : Nat := 4983230072969 + 3 ^ 40 * 2277719 * 2
def baseEnd_2277719 : Nat := 1169564642878279147637467

theorem tailTrace_2277719 : CollatzResearch.WordTrace tailWord_2277719 prefixEnd_2277719 1169564642878279147637467 := by
  unfold tailWord_2277719
  simp only [CollatzResearch.WordTrace]
  refine ⟨83075236835220541280164211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55383491223480360853442807 83075236835220541280164211)
  ·
    refine ⟨124612855252830811920246317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83075236835220541280164211 124612855252830811920246317)
    ·
      refine ⟨46729820719811554470092369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124612855252830811920246317 46729820719811554470092369)
      ·
        refine ⟨35047365539858665852569277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46729820719811554470092369 35047365539858665852569277)
        ·
          refine ⟨13142762077446999694713479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35047365539858665852569277 13142762077446999694713479)
          ·
            refine ⟨19714143116170499542070219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13142762077446999694713479 19714143116170499542070219)
            ·
              refine ⟨29571214674255749313105329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19714143116170499542070219 29571214674255749313105329)
              ·
                refine ⟨22178411005691811984828997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29571214674255749313105329 22178411005691811984828997)
                ·
                  refine ⟨4158452063567214747155437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22178411005691811984828997 4158452063567214747155437)
                  ·
                    refine ⟨1559419523837705530183289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4158452063567214747155437 1559419523837705530183289)
                    ·
                      refine ⟨1169564642878279147637467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559419523837705530183289 1169564642878279147637467)
                      ·
                        rfl

theorem cell23_2277719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_2277719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277719 prefixEnd_2277719 := by exact prefixLift 2277719
  have htrace : WordTrace (prefixWord ++ tailWord_2277719) baseStart_2277719 baseEnd_2277719 := by
    simpa [prefixWord, tailWord_2277719, baseEnd_2277719] using wordTrace_append hprefix tailTrace_2277719
  have hstable : (prefixWord ++ tailWord_2277719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277719).length < 2 ^ (prefixWord ++ tailWord_2277719).sum := by decide
  have hdescent : baseEnd_2277719 < baseStart_2277719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277736 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2277736 : Nat := 118140960795 + 2277736 * 2 ^ 59
def prefixEnd_2277736 : Nat := 4983230072969 + 3 ^ 40 * 2277736 * 2
def baseEnd_2277736 : Nat := 1169573372049405581124889

theorem tailTrace_2277736 : CollatzResearch.WordTrace tailWord_2277736 prefixEnd_2277736 1169573372049405581124889 := by
  unfold tailWord_2277736
  simp only [CollatzResearch.WordTrace]
  refine ⟨41537928438079476591766531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55383904584105968789022041 41537928438079476591766531)
  ·
    refine ⟨62306892657119214887649797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41537928438079476591766531 62306892657119214887649797)
    ·
      refine ⟨11682542373209852791434337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62306892657119214887649797 11682542373209852791434337)
      ·
        refine ⟨8761906779907389593575753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11682542373209852791434337 8761906779907389593575753)
        ·
          refine ⟨6571430084930542195181815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8761906779907389593575753 6571430084930542195181815)
          ·
            refine ⟨9857145127395813292772723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6571430084930542195181815 9857145127395813292772723)
            ·
              refine ⟨14785717691093719939159085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857145127395813292772723 14785717691093719939159085)
              ·
                refine ⟨5544644134160144977184657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14785717691093719939159085 5544644134160144977184657)
                ·
                  refine ⟨4158483100620108732888493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5544644134160144977184657 4158483100620108732888493)
                  ·
                    refine ⟨1559431162732540774833185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4158483100620108732888493 1559431162732540774833185)
                    ·
                      refine ⟨1169573372049405581124889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559431162732540774833185 1169573372049405581124889)
                      ·
                        rfl

theorem cell23_2277736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2277736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277736 prefixEnd_2277736 := by exact prefixLift 2277736
  have htrace : WordTrace (prefixWord ++ tailWord_2277736) baseStart_2277736 baseEnd_2277736 := by
    simpa [prefixWord, tailWord_2277736, baseEnd_2277736] using wordTrace_append hprefix tailTrace_2277736
  have hstable : (prefixWord ++ tailWord_2277736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277736).length < 2 ^ (prefixWord ++ tailWord_2277736).sum := by decide
  have hdescent : baseEnd_2277736 < baseStart_2277736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277746 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_2277746 : Nat := 118140960795 + 2277746 * 2 ^ 59
def prefixEnd_2277746 : Nat := 4983230072969 + 3 ^ 40 * 2277746 * 2
def baseEnd_2277746 : Nat := 389859502285316847333281

theorem tailTrace_2277746 : CollatzResearch.WordTrace tailWord_2277746 prefixEnd_2277746 389859502285316847333281 := by
  unfold tailWord_2277746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20769055401530681222849273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55384147737415149927598061 20769055401530681222849273)
  ·
    refine ⟨15576791551148010917136955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20769055401530681222849273 15576791551148010917136955)
    ·
      refine ⟨23365187326722016375705433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15576791551148010917136955 23365187326722016375705433)
      ·
        refine ⟨17523890495041512281779075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23365187326722016375705433 17523890495041512281779075)
        ·
          refine ⟨26285835742562268422668613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17523890495041512281779075 26285835742562268422668613)
          ·
            refine ⟨4928594201730425329250365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26285835742562268422668613 4928594201730425329250365)
            ·
              refine ⟨1848222825648909498468887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4928594201730425329250365 1848222825648909498468887)
              ·
                refine ⟨2772334238473364247703331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848222825648909498468887 2772334238473364247703331)
                ·
                  refine ⟨4158501357710046371554997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772334238473364247703331 4158501357710046371554997)
                  ·
                    refine ⟨389859502285316847333281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4158501357710046371554997 389859502285316847333281)
                    ·
                      rfl

theorem cell23_2277746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_2277746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277746 prefixEnd_2277746 := by exact prefixLift 2277746
  have htrace : WordTrace (prefixWord ++ tailWord_2277746) baseStart_2277746 baseEnd_2277746 := by
    simpa [prefixWord, tailWord_2277746, baseEnd_2277746] using wordTrace_append hprefix tailTrace_2277746
  have hstable : (prefixWord ++ tailWord_2277746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277746).length < 2 ^ (prefixWord ++ tailWord_2277746).sum := by decide
  have hdescent : baseEnd_2277746 < baseStart_2277746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277755 : List Nat := [1, 1, 1, 1, 1, 18]
def baseStart_2277755 : Nat := 118140960795 + 2277755 * 2 ^ 59
def prefixEnd_2277755 : Nat := 4983230072969 + 3 ^ 40 * 2277755 * 2
def baseEnd_2277755 : Nat := 4813099292929386859207

theorem tailTrace_2277755 : CollatzResearch.WordTrace tailWord_2277755 prefixEnd_2277755 4813099292929386859207 := by
  unfold tailWord_2277755
  simp only [CollatzResearch.WordTrace]
  refine ⟨83076549863090119428474719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55384366575393412952316479 83076549863090119428474719)
  ·
    refine ⟨124614824794635179142712079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83076549863090119428474719 124614824794635179142712079)
    ·
      refine ⟨186922237191952768714068119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124614824794635179142712079 186922237191952768714068119)
      ·
        refine ⟨280383355787929153071102179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186922237191952768714068119 280383355787929153071102179)
        ·
          refine ⟨420575033681893729606653269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280383355787929153071102179 420575033681893729606653269)
          ·
            refine ⟨4813099292929386859207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 18 420575033681893729606653269 4813099292929386859207)
            ·
              rfl

theorem cell23_2277755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 18].length) (baseStart_2277755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277755 prefixEnd_2277755 := by exact prefixLift 2277755
  have htrace : WordTrace (prefixWord ++ tailWord_2277755) baseStart_2277755 baseEnd_2277755 := by
    simpa [prefixWord, tailWord_2277755, baseEnd_2277755] using wordTrace_append hprefix tailTrace_2277755
  have hstable : (prefixWord ++ tailWord_2277755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277755).length < 2 ^ (prefixWord ++ tailWord_2277755).sum := by decide
  have hdescent : baseEnd_2277755 < baseStart_2277755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277769 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_2277769 : Nat := 118140960795 + 2277769 * 2 ^ 59
def prefixEnd_2277769 : Nat := 4983230072969 + 3 ^ 40 * 2277769 * 2
def baseEnd_2277769 : Nat := 1169590316911003952012237

theorem tailTrace_2277769 : CollatzResearch.WordTrace tailWord_2277769 prefixEnd_2277769 1169590316911003952012237 := by
  unfold tailWord_2277769
  simp only [CollatzResearch.WordTrace]
  refine ⟨83077060485039399819484361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55384706990026266546322907 83077060485039399819484361)
  ·
    refine ⟨62307795363779549864613271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83077060485039399819484361 62307795363779549864613271)
    ·
      refine ⟨93461693045669324796919907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62307795363779549864613271 93461693045669324796919907)
      ·
        refine ⟨140192539568503987195379861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93461693045669324796919907 140192539568503987195379861)
        ·
          refine ⟨6571525292273624399783431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140192539568503987195379861 6571525292273624399783431)
          ·
            refine ⟨9857287938410436599675147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6571525292273624399783431 9857287938410436599675147)
            ·
              refine ⟨14785931907615654899512721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857287938410436599675147 14785931907615654899512721)
              ·
                refine ⟨11089448930711741174634541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14785931907615654899512721 11089448930711741174634541)
                ·
                  refine ⟨4158543349016902940487953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11089448930711741174634541 4158543349016902940487953)
                  ·
                    refine ⟨3118907511762677205365965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158543349016902940487953 3118907511762677205365965)
                    ·
                      refine ⟨1169590316911003952012237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3118907511762677205365965 1169590316911003952012237)
                      ·
                        rfl

theorem cell23_2277769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_2277769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277769 prefixEnd_2277769 := by exact prefixLift 2277769
  have htrace : WordTrace (prefixWord ++ tailWord_2277769) baseStart_2277769 baseEnd_2277769 := by
    simpa [prefixWord, tailWord_2277769, baseEnd_2277769] using wordTrace_append hprefix tailTrace_2277769
  have hstable : (prefixWord ++ tailWord_2277769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277769).length < 2 ^ (prefixWord ++ tailWord_2277769).sum := by decide
  have hdescent : baseEnd_2277769 < baseStart_2277769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277772 : List Nat := [2, 2, 1, 2, 1, 4, 3, 8]
def baseStart_2277772 : Nat := 118140960795 + 2277772 * 2 ^ 59
def prefixEnd_2277772 : Nat := 4983230072969 + 3 ^ 40 * 2277772 * 2
def baseEnd_2277772 : Nat := 43318216938998794084249

theorem tailTrace_2277772 : CollatzResearch.WordTrace tailWord_2277772 prefixEnd_2277772 43318216938998794084249 := by
  unfold tailWord_2277772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41538584952014265665921785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55384779936019020887895713 41538584952014265665921785)
  ·
    refine ⟨31153938714010699249441339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41538584952014265665921785 31153938714010699249441339)
    ·
      refine ⟨46730908071016048874162009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31153938714010699249441339 46730908071016048874162009)
      ·
        refine ⟨35048181053262036655621507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46730908071016048874162009 35048181053262036655621507)
        ·
          refine ⟨52572271579893054983432261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35048181053262036655621507 52572271579893054983432261)
          ·
            refine ⟨9857300921229947809393549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52572271579893054983432261 9857300921229947809393549)
            ·
              refine ⟨3696487845461230428522581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9857300921229947809393549 3696487845461230428522581)
              ·
                refine ⟨43318216938998794084249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3696487845461230428522581 43318216938998794084249)
                ·
                  rfl

theorem cell23_2277772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 8].length) (baseStart_2277772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277772 prefixEnd_2277772 := by exact prefixLift 2277772
  have htrace : WordTrace (prefixWord ++ tailWord_2277772) baseStart_2277772 baseEnd_2277772 := by
    simpa [prefixWord, tailWord_2277772, baseEnd_2277772] using wordTrace_append hprefix tailTrace_2277772
  have hstable : (prefixWord ++ tailWord_2277772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277772).length < 2 ^ (prefixWord ++ tailWord_2277772).sum := by decide
  have hdescent : baseEnd_2277772 < baseStart_2277772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277800 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2277800 : Nat := 118140960795 + 2277800 * 2 ^ 59
def prefixEnd_2277800 : Nat := 4983230072969 + 3 ^ 40 * 2277800 * 2
def baseEnd_2277800 : Nat := 1169606234811293330724595

theorem tailTrace_2277800 : CollatzResearch.WordTrace tailWord_2277800 prefixEnd_2277800 1169606234811293330724595 := by
  unfold tailWord_2277800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41539095573963546056931427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55385460765284728075908569 41539095573963546056931427)
  ·
    refine ⟨62308643360945319085397141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41539095573963546056931427 62308643360945319085397141)
    ·
      refine ⟨2920717657544311832127991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62308643360945319085397141 2920717657544311832127991)
      ·
        refine ⟨4381076486316467748191987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920717657544311832127991 4381076486316467748191987)
        ·
          refine ⟨6571614729474701622287981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381076486316467748191987 6571614729474701622287981)
          ·
            refine ⟨2464355523553013108357993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6571614729474701622287981 2464355523553013108357993)
            ·
              refine ⟨1848266642664759831268495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464355523553013108357993 1848266642664759831268495)
              ·
                refine ⟨2772399963997139746902743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848266642664759831268495 2772399963997139746902743)
                ·
                  refine ⟨4158599945995709620354115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772399963997139746902743 4158599945995709620354115)
                  ·
                    refine ⟨6237899918993564430531173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158599945995709620354115 6237899918993564430531173)
                    ·
                      refine ⟨1169606234811293330724595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6237899918993564430531173 1169606234811293330724595)
                      ·
                        rfl

theorem cell23_2277800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2277800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277800 prefixEnd_2277800 := by exact prefixLift 2277800
  have htrace : WordTrace (prefixWord ++ tailWord_2277800) baseStart_2277800 baseEnd_2277800 := by
    simpa [prefixWord, tailWord_2277800, baseEnd_2277800] using wordTrace_append hprefix tailTrace_2277800
  have hstable : (prefixWord ++ tailWord_2277800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277800).length < 2 ^ (prefixWord ++ tailWord_2277800).sum := by decide
  have hdescent : baseEnd_2277800 < baseStart_2277800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277856 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2]
def baseStart_2277856 : Nat := 118140960795 + 2277856 * 2 ^ 59
def prefixEnd_2277856 : Nat := 4983230072969 + 3 ^ 40 * 2277856 * 2
def baseEnd_2277856 : Nat := 1169634989727945111624337

theorem tailTrace_2277856 : CollatzResearch.WordTrace tailWord_2277856 prefixEnd_2277856 1169634989727945111624337 := by
  unfold tailWord_2277856
  simp only [CollatzResearch.WordTrace]
  refine ⟨41540116817862106838950711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55386822423816142451934281 41540116817862106838950711)
  ·
    refine ⟨62310175226793160258426067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41540116817862106838950711 62310175226793160258426067)
    ·
      refine ⟨93465262840189740387639101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62310175226793160258426067 93465262840189740387639101)
      ·
        refine ⟨35049473565071152645364663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93465262840189740387639101 35049473565071152645364663)
        ·
          refine ⟨52574210347606728968046995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35049473565071152645364663 52574210347606728968046995)
          ·
            refine ⟨78861315521410093452070493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52574210347606728968046995 78861315521410093452070493)
            ·
              refine ⟨29572993320528785044526435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78861315521410093452070493 29572993320528785044526435)
              ·
                refine ⟨44359489980793177566789653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29572993320528785044526435 44359489980793177566789653)
                ·
                  refine ⟨2079351092849680198443265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44359489980793177566789653 2079351092849680198443265)
                  ·
                    refine ⟨1559513319637260148832449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079351092849680198443265 1559513319637260148832449)
                    ·
                      refine ⟨1169634989727945111624337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559513319637260148832449 1169634989727945111624337)
                      ·
                        rfl

theorem cell23_2277856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_2277856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277856 prefixEnd_2277856 := by exact prefixLift 2277856
  have htrace : WordTrace (prefixWord ++ tailWord_2277856) baseStart_2277856 baseEnd_2277856 := by
    simpa [prefixWord, tailWord_2277856, baseEnd_2277856] using wordTrace_append hprefix tailTrace_2277856
  have hstable : (prefixWord ++ tailWord_2277856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277856).length < 2 ^ (prefixWord ++ tailWord_2277856).sum := by decide
  have hdescent : baseEnd_2277856 < baseStart_2277856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277872 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2277872 : Nat := 118140960795 + 2277872 * 2 ^ 59
def prefixEnd_2277872 : Nat := 4983230072969 + 3 ^ 40 * 2277872 * 2
def baseEnd_2277872 : Nat := 1169643205418417049024263

theorem tailTrace_2277872 : CollatzResearch.WordTrace tailWord_2277872 prefixEnd_2277872 1169643205418417049024263 := by
  unfold tailWord_2277872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41540408601833124205241935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55387211469110832273655913 41540408601833124205241935)
  ·
    refine ⟨62310612902749686307862903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41540408601833124205241935 62310612902749686307862903)
    ·
      refine ⟨93465919354124529461794355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62310612902749686307862903 93465919354124529461794355)
      ·
        refine ⟨140198879031186794192691533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93465919354124529461794355 140198879031186794192691533)
        ·
          refine ⟨52574579636695047822259325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140198879031186794192691533 52574579636695047822259325)
          ·
            refine ⟨19715467363760642933347247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52574579636695047822259325 19715467363760642933347247)
            ·
              refine ⟨29573201045640964400020871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19715467363760642933347247 29573201045640964400020871)
              ·
                refine ⟨44359801568461446600031307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29573201045640964400020871 44359801568461446600031307)
                ·
                  refine ⟨66539702352692169900046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44359801568461446600031307 66539702352692169900046961)
                  ·
                    refine ⟨49904776764519127425035221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66539702352692169900046961 49904776764519127425035221)
                    ·
                      refine ⟨1169643205418417049024263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49904776764519127425035221 1169643205418417049024263)
                      ·
                        rfl

theorem cell23_2277872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2277872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277872 prefixEnd_2277872 := by exact prefixLift 2277872
  have htrace : WordTrace (prefixWord ++ tailWord_2277872) baseStart_2277872 baseEnd_2277872 := by
    simpa [prefixWord, tailWord_2277872, baseEnd_2277872] using wordTrace_append hprefix tailTrace_2277872
  have hstable : (prefixWord ++ tailWord_2277872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277872).length < 2 ^ (prefixWord ++ tailWord_2277872).sum := by decide
  have hdescent : baseEnd_2277872 < baseStart_2277872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277873 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_2277873 : Nat := 118140960795 + 2277873 * 2 ^ 59
def prefixEnd_2277873 : Nat := 4983230072969 + 3 ^ 40 * 2277873 * 2
def baseEnd_2277873 : Nat := 1169643718899071545111759

theorem tailTrace_2277873 : CollatzResearch.WordTrace tailWord_2277873 prefixEnd_2277873 1169643718899071545111759 := by
  unfold tailWord_2277873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83080853676662625581270273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55387235784441750387513515 83080853676662625581270273)
  ·
    refine ⟨62310640257496969185952705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83080853676662625581270273 62310640257496969185952705)
    ·
      refine ⟨46732980193122726889464529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62310640257496969185952705 46732980193122726889464529)
      ·
        refine ⟨35049735144842045167098397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46732980193122726889464529 35049735144842045167098397)
        ·
          refine ⟨13143650679315766937661899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35049735144842045167098397 13143650679315766937661899)
          ·
            refine ⟨19715476018973650406492849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143650679315766937661899 19715476018973650406492849)
            ·
              refine ⟨14786607014230237804869637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19715476018973650406492849 14786607014230237804869637)
              ·
                refine ⟨2772488815168169588413057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14786607014230237804869637 2772488815168169588413057)
                ·
                  refine ⟨2079366611376127191309793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772488815168169588413057 2079366611376127191309793)
                  ·
                    refine ⟨1559524958532095393482345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079366611376127191309793 1559524958532095393482345)
                    ·
                      refine ⟨1169643718899071545111759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559524958532095393482345 1169643718899071545111759)
                      ·
                        rfl

theorem cell23_2277873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_2277873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277873 prefixEnd_2277873 := by exact prefixLift 2277873
  have htrace : WordTrace (prefixWord ++ tailWord_2277873) baseStart_2277873 baseEnd_2277873 := by
    simpa [prefixWord, tailWord_2277873, baseEnd_2277873] using wordTrace_append hprefix tailTrace_2277873
  have hstable : (prefixWord ++ tailWord_2277873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277873).length < 2 ^ (prefixWord ++ tailWord_2277873).sum := by decide
  have hdescent : baseEnd_2277873 < baseStart_2277873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277882 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_2277882 : Nat := 118140960795 + 2277882 * 2 ^ 59
def prefixEnd_2277882 : Nat := 4983230072969 + 3 ^ 40 * 2277882 * 2
def baseEnd_2277882 : Nat := 1169648340224962009899217

theorem tailTrace_2277882 : CollatzResearch.WordTrace tailWord_2277882 prefixEnd_2277882 1169648340224962009899217 := by
  unfold tailWord_2277882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770295483407505029586975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55387454622420013412231933 20770295483407505029586975)
  ·
    refine ⟨31155443225111257544380463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20770295483407505029586975 31155443225111257544380463)
    ·
      refine ⟨46733164837666886316570695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31155443225111257544380463 46733164837666886316570695)
      ·
        refine ⟨70099747256500329474856043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46733164837666886316570695 70099747256500329474856043)
        ·
          refine ⟨105149620884750494212284065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70099747256500329474856043 105149620884750494212284065)
          ·
            refine ⟨78862215663562870659213049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105149620884750494212284065 78862215663562870659213049)
            ·
              refine ⟨59146661747672152994409787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78862215663562870659213049 59146661747672152994409787)
              ·
                refine ⟨88719992621508229491614681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59146661747672152994409787 88719992621508229491614681)
                ·
                  refine ⟨66539994466131172118711011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88719992621508229491614681 66539994466131172118711011)
                  ·
                    refine ⟨99809991699196758178066517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66539994466131172118711011 99809991699196758178066517)
                    ·
                      refine ⟨1169648340224962009899217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 99809991699196758178066517 1169648340224962009899217)
                      ·
                        rfl

theorem cell23_2277882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_2277882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277882 prefixEnd_2277882 := by exact prefixLift 2277882
  have htrace : WordTrace (prefixWord ++ tailWord_2277882) baseStart_2277882 baseEnd_2277882 := by
    simpa [prefixWord, tailWord_2277882, baseEnd_2277882] using wordTrace_append hprefix tailTrace_2277882
  have hstable : (prefixWord ++ tailWord_2277882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277882).length < 2 ^ (prefixWord ++ tailWord_2277882).sum := by decide
  have hdescent : baseEnd_2277882 < baseStart_2277882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277894 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2277894 : Nat := 118140960795 + 2277894 * 2 ^ 59
def prefixEnd_2277894 : Nat := 4983230072969 + 3 ^ 40 * 2277894 * 2
def baseEnd_2277894 : Nat := 1169654501992815962949163

theorem tailTrace_2277894 : CollatzResearch.WordTrace tailWord_2277894 prefixEnd_2277894 1169654501992815962949163 := by
  unfold tailWord_2277894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596300612799579567743273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55387746406391030778523157 2596300612799579567743273)
  ·
    refine ⟨1947225459599684675807455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2596300612799579567743273 1947225459599684675807455)
    ·
      refine ⟨2920838189399527013711183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947225459599684675807455 2920838189399527013711183)
      ·
        refine ⟨4381257284099290520566775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920838189399527013711183 4381257284099290520566775)
        ·
          refine ⟨6571885926148935780850163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381257284099290520566775 6571885926148935780850163)
          ·
            refine ⟨9857828889223403671275245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6571885926148935780850163 9857828889223403671275245)
            ·
              refine ⟨3696685833458776376728217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9857828889223403671275245 3696685833458776376728217)
              ·
                refine ⟨2772514375094082282546163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696685833458776376728217 2772514375094082282546163)
                ·
                  refine ⟨4158771562641123423819245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772514375094082282546163 4158771562641123423819245)
                  ·
                    refine ⟨1559539335990421283932217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4158771562641123423819245 1559539335990421283932217)
                    ·
                      refine ⟨1169654501992815962949163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559539335990421283932217 1169654501992815962949163)
                      ·
                        rfl

theorem cell23_2277894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2277894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277894 prefixEnd_2277894 := by exact prefixLift 2277894
  have htrace : WordTrace (prefixWord ++ tailWord_2277894) baseStart_2277894 baseEnd_2277894 := by
    simpa [prefixWord, tailWord_2277894, baseEnd_2277894] using wordTrace_append hprefix tailTrace_2277894
  have hstable : (prefixWord ++ tailWord_2277894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277894).length < 2 ^ (prefixWord ++ tailWord_2277894).sum := by decide
  have hdescent : baseEnd_2277894 < baseStart_2277894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277930 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_2277930 : Nat := 118140960795 + 2277930 * 2 ^ 59
def prefixEnd_2277930 : Nat := 4983230072969 + 3 ^ 40 * 2277930 * 2
def baseEnd_2277930 : Nat := 129963665255153091344333

theorem tailTrace_2277930 : CollatzResearch.WordTrace tailWord_2277930 prefixEnd_2277930 129963665255153091344333 := by
  unfold tailWord_2277930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770733159364031079023811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55388621758304082877396829 20770733159364031079023811)
  ·
    refine ⟨31156099739046046618535717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20770733159364031079023811 31156099739046046618535717)
    ·
      refine ⟨5841768701071133740975447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31156099739046046618535717 5841768701071133740975447)
      ·
        refine ⟨8762653051606700611463171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841768701071133740975447 8762653051606700611463171)
        ·
          refine ⟨13143979577410050917194757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762653051606700611463171 13143979577410050917194757)
          ·
            refine ⟨2464496170764384546974017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13143979577410050917194757 2464496170764384546974017)
            ·
              refine ⟨1848372128073288410230513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464496170764384546974017 1848372128073288410230513)
              ·
                refine ⟨1386279096054966307672885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848372128073288410230513 1386279096054966307672885)
                ·
                  refine ⟨129963665255153091344333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386279096054966307672885 129963665255153091344333)
                  ·
                    rfl

theorem cell23_2277930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_2277930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277930 prefixEnd_2277930 := by exact prefixLift 2277930
  have htrace : WordTrace (prefixWord ++ tailWord_2277930) baseStart_2277930 baseEnd_2277930 := by
    simpa [prefixWord, tailWord_2277930, baseEnd_2277930] using wordTrace_append hprefix tailTrace_2277930
  have hstable : (prefixWord ++ tailWord_2277930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277930).length < 2 ^ (prefixWord ++ tailWord_2277930).sum := by decide
  have hdescent : baseEnd_2277930 < baseStart_2277930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277940 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2277940 : Nat := 118140960795 + 2277940 * 2 ^ 59
def prefixEnd_2277940 : Nat := 4983230072969 + 3 ^ 40 * 2277940 * 2
def baseEnd_2277940 : Nat := 1169678122102922782973951

theorem tailTrace_2277940 : CollatzResearch.WordTrace tailWord_2277940 prefixEnd_2277940 1169678122102922782973951 := by
  unfold tailWord_2277940
  simp only [CollatzResearch.WordTrace]
  refine ⟨41541648683709948011979637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55388864911613264015972849 41541648683709948011979637)
  ·
    refine ⟨3894529564097807626123091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41541648683709948011979637 3894529564097807626123091)
    ·
      refine ⟨5841794346146711439184637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3894529564097807626123091 5841794346146711439184637)
      ·
        refine ⟨2190672879805016789694239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5841794346146711439184637 2190672879805016789694239)
        ·
          refine ⟨3286009319707525184541359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190672879805016789694239 3286009319707525184541359)
          ·
            refine ⟨4929013979561287776812039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286009319707525184541359 4929013979561287776812039)
            ·
              refine ⟨7393520969341931665218059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929013979561287776812039 7393520969341931665218059)
              ·
                refine ⟨11090281454012897497827089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7393520969341931665218059 11090281454012897497827089)
                ·
                  refine ⟨8317711090509673123370317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11090281454012897497827089 8317711090509673123370317)
                  ·
                    refine ⟨3119141658941127421263869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8317711090509673123370317 3119141658941127421263869)
                    ·
                      refine ⟨1169678122102922782973951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3119141658941127421263869 1169678122102922782973951)
                      ·
                        rfl

theorem cell23_2277940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2277940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277940 prefixEnd_2277940 := by exact prefixLift 2277940
  have htrace : WordTrace (prefixWord ++ tailWord_2277940) baseStart_2277940 baseEnd_2277940 := by
    simpa [prefixWord, tailWord_2277940, baseEnd_2277940] using wordTrace_append hprefix tailTrace_2277940
  have hstable : (prefixWord ++ tailWord_2277940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277940).length < 2 ^ (prefixWord ++ tailWord_2277940).sum := by decide
  have hdescent : baseEnd_2277940 < baseStart_2277940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277946 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_2277946 : Nat := 118140960795 + 2277946 * 2 ^ 59
def prefixEnd_2277946 : Nat := 4983230072969 + 3 ^ 40 * 2277946 * 2
def baseEnd_2277946 : Nat := 1169681202986849759498923

theorem tailTrace_2277946 : CollatzResearch.WordTrace tailWord_2277946 prefixEnd_2277946 1169681202986849759498923 := by
  unfold tailWord_2277946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770879051349539762169423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55389010803598772699118461 20770879051349539762169423)
  ·
    refine ⟨31156318577024309643254135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20770879051349539762169423 31156318577024309643254135)
    ·
      refine ⟨46734477865536464464881203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31156318577024309643254135 46734477865536464464881203)
      ·
        refine ⟨70101716798304696697321805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46734477865536464464881203 70101716798304696697321805)
        ·
          refine ⟨26288143799364261261495677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70101716798304696697321805 26288143799364261261495677)
          ·
            refine ⟨9858053924761597973060879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26288143799364261261495677 9858053924761597973060879)
            ·
              refine ⟨14787080887142396959591319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9858053924761597973060879 14787080887142396959591319)
              ·
                refine ⟨22180621330713595439386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14787080887142396959591319 22180621330713595439386979)
                ·
                  refine ⟨33270931996070393159080469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22180621330713595439386979 33270931996070393159080469)
                  ·
                    refine ⟨1559574937315799679331897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33270931996070393159080469 1559574937315799679331897)
                    ·
                      refine ⟨1169681202986849759498923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559574937315799679331897 1169681202986849759498923)
                      ·
                        rfl

theorem cell23_2277946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_2277946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277946 prefixEnd_2277946 := by exact prefixLift 2277946
  have htrace : WordTrace (prefixWord ++ tailWord_2277946) baseStart_2277946 baseEnd_2277946 := by
    simpa [prefixWord, tailWord_2277946, baseEnd_2277946] using wordTrace_append hprefix tailTrace_2277946
  have hstable : (prefixWord ++ tailWord_2277946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277946).length < 2 ^ (prefixWord ++ tailWord_2277946).sum := by decide
  have hdescent : baseEnd_2277946 < baseStart_2277946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277973 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2277973 : Nat := 118140960795 + 2277973 * 2 ^ 59
def prefixEnd_2277973 : Nat := 4983230072969 + 3 ^ 40 * 2277973 * 2
def baseEnd_2277973 : Nat := 389898355654840384620433

theorem tailTrace_2277973 : CollatzResearch.WordTrace tailWord_2277973 prefixEnd_2277973 389898355654840384620433 := by
  unfold tailWord_2277973
  simp only [CollatzResearch.WordTrace]
  refine ⟨83084500976300342659910573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55389667317533561773273715 83084500976300342659910573)
  ·
    refine ⟨31156687866112628497466465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83084500976300342659910573 31156687866112628497466465)
    ·
      refine ⟨23367515899584471373099849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31156687866112628497466465 23367515899584471373099849)
      ·
        refine ⟨17525636924688353529824887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23367515899584471373099849 17525636924688353529824887)
        ·
          refine ⟨26288455387032530294737331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17525636924688353529824887 26288455387032530294737331)
          ·
            refine ⟨39432683080548795442105997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26288455387032530294737331 39432683080548795442105997)
            ·
              refine ⟨14787256155205798290789749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39432683080548795442105997 14787256155205798290789749)
              ·
                refine ⟨1386305264550543589761539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14787256155205798290789749 1386305264550543589761539)
                ·
                  refine ⟨2079457896825815384642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386305264550543589761539 2079457896825815384642309)
                  ·
                    refine ⟨389898355654840384620433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079457896825815384642309 389898355654840384620433)
                    ·
                      rfl

theorem cell23_2277973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2277973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277973 prefixEnd_2277973 := by exact prefixLift 2277973
  have htrace : WordTrace (prefixWord ++ tailWord_2277973) baseStart_2277973 baseEnd_2277973 := by
    simpa [prefixWord, tailWord_2277973, baseEnd_2277973] using wordTrace_append hprefix tailTrace_2277973
  have hstable : (prefixWord ++ tailWord_2277973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277973).length < 2 ^ (prefixWord ++ tailWord_2277973).sum := by decide
  have hdescent : baseEnd_2277973 < baseStart_2277973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2277999 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 5, 5]
def baseStart_2277999 : Nat := 118140960795 + 2277999 * 2 ^ 59
def prefixEnd_2277999 : Nat := 4983230072969 + 3 ^ 40 * 2277999 * 2
def baseEnd_2277999 : Nat := 389902805820512684045393

theorem tailTrace_2277999 : CollatzResearch.WordTrace tailWord_2277999 prefixEnd_2277999 389902805820512684045393 := by
  unfold tailWord_2277999
  simp only [CollatzResearch.WordTrace]
  refine ⟨83085449274206149100357051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55390299516137432733571367 83085449274206149100357051)
  ·
    refine ⟨124628173911309223650535577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83085449274206149100357051 124628173911309223650535577)
    ·
      refine ⟨93471130433481917737901683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124628173911309223650535577 93471130433481917737901683)
      ·
        refine ⟨140206695650222876606852525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93471130433481917737901683 140206695650222876606852525)
        ·
          refine ⟨52577510868833578727569697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140206695650222876606852525 52577510868833578727569697)
          ·
            refine ⟨39433133151625184045677273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52577510868833578727569697 39433133151625184045677273)
            ·
              refine ⟨29574849863718888034257955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39433133151625184045677273 29574849863718888034257955)
              ·
                refine ⟨44362274795578332051386933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29574849863718888034257955 44362274795578332051386933)
                ·
                  refine ⟨4158963262085468629817525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44362274795578332051386933 4158963262085468629817525)
                  ·
                    refine ⟨389902805820512684045393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4158963262085468629817525 389902805820512684045393)
                    ·
                      rfl

theorem cell23_2277999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_2277999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2277999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2277999 prefixEnd_2277999 := by exact prefixLift 2277999
  have htrace : WordTrace (prefixWord ++ tailWord_2277999) baseStart_2277999 baseEnd_2277999 := by
    simpa [prefixWord, tailWord_2277999, baseEnd_2277999] using wordTrace_append hprefix tailTrace_2277999
  have hstable : (prefixWord ++ tailWord_2277999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2277999).length < 2 ^ (prefixWord ++ tailWord_2277999).sum := by decide
  have hdescent : baseEnd_2277999 < baseStart_2277999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2277999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278016 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_2278016 : Nat := 118140960795 + 2278016 * 2 ^ 59
def prefixEnd_2278016 : Nat := 4983230072969 + 3 ^ 40 * 2278016 * 2
def baseEnd_2278016 : Nat := 389905715544221495207867

theorem tailTrace_2278016 : CollatzResearch.WordTrace tailWord_2278016 prefixEnd_2278016 389905715544221495207867 := by
  unfold tailWord_2278016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41543034657572280501862951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55390712876763040669150601 41543034657572280501862951)
  ·
    refine ⟨62314551986358420752794427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41543034657572280501862951 62314551986358420752794427)
    ·
      refine ⟨93471827979537631129191641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62314551986358420752794427 93471827979537631129191641)
      ·
        refine ⟨70103870984653223346893731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93471827979537631129191641 70103870984653223346893731)
        ·
          refine ⟨105155806476979835020340597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70103870984653223346893731 105155806476979835020340597)
          ·
            refine ⟨9858356857216859533156931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105155806476979835020340597 9858356857216859533156931)
            ·
              refine ⟨14787535285825289299735397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9858356857216859533156931 14787535285825289299735397)
              ·
                refine ⟨2772662866092241743700387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14787535285825289299735397 2772662866092241743700387)
                ·
                  refine ⟨4158994299138362615550581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772662866092241743700387 4158994299138362615550581)
                  ·
                    refine ⟨389905715544221495207867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4158994299138362615550581 389905715544221495207867)
                    ·
                      rfl

theorem cell23_2278016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_2278016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278016 prefixEnd_2278016 := by exact prefixLift 2278016
  have htrace : WordTrace (prefixWord ++ tailWord_2278016) baseStart_2278016 baseEnd_2278016 := by
    simpa [prefixWord, tailWord_2278016, baseEnd_2278016] using wordTrace_append hprefix tailTrace_2278016
  have hstable : (prefixWord ++ tailWord_2278016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278016).length < 2 ^ (prefixWord ++ tailWord_2278016).sum := by decide
  have hdescent : baseEnd_2278016 < baseStart_2278016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278023 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_2278023 : Nat := 118140960795 + 2278023 * 2 ^ 59
def prefixEnd_2278023 : Nat := 4983230072969 + 3 ^ 40 * 2278023 * 2
def baseEnd_2278023 : Nat := 1169720740997245958236069

theorem tailTrace_2278023 : CollatzResearch.WordTrace tailWord_2278023 prefixEnd_2278023 1169720740997245958236069 := by
  unfold tailWord_2278023
  simp only [CollatzResearch.WordTrace]
  refine ⟨83086324626119201199230723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55390883084079467466153815 83086324626119201199230723)
  ·
    refine ⟨124629486939178801798846085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83086324626119201199230723 124629486939178801798846085)
    ·
      refine ⟨23368028801096025337283641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124629486939178801798846085 23368028801096025337283641)
      ·
        refine ⟨17526021600822019002962731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23368028801096025337283641 17526021600822019002962731)
        ·
          refine ⟨26289032401233028504444097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17526021600822019002962731 26289032401233028504444097)
          ·
            refine ⟨19716774300924771378333073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26289032401233028504444097 19716774300924771378333073)
            ·
              refine ⟨14787580725693578533749805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19716774300924771378333073 14787580725693578533749805)
              ·
                refine ⟨5545342772135091950156177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14787580725693578533749805 5545342772135091950156177)
                ·
                  refine ⟨4159007079101318962617133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545342772135091950156177 4159007079101318962617133)
                  ·
                    refine ⟨1559627654662994610981425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4159007079101318962617133 1559627654662994610981425)
                    ·
                      refine ⟨1169720740997245958236069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559627654662994610981425 1169720740997245958236069)
                      ·
                        rfl

theorem cell23_2278023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_2278023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278023 prefixEnd_2278023 := by exact prefixLift 2278023
  have htrace : WordTrace (prefixWord ++ tailWord_2278023) baseStart_2278023 baseEnd_2278023 := by
    simpa [prefixWord, tailWord_2278023, baseEnd_2278023] using wordTrace_append hprefix tailTrace_2278023
  have hstable : (prefixWord ++ tailWord_2278023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278023).length < 2 ^ (prefixWord ++ tailWord_2278023).sum := by decide
  have hdescent : baseEnd_2278023 < baseStart_2278023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278063 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 2, 4]
def baseStart_2278063 : Nat := 118140960795 + 2278063 * 2 ^ 59
def prefixEnd_2278063 : Nat := 4983230072969 + 3 ^ 40 * 2278063 * 2
def baseEnd_2278063 : Nat := 389913760074475267245295

theorem tailTrace_2278063 : CollatzResearch.WordTrace tailWord_2278063 prefixEnd_2278063 389913760074475267245295 := by
  unfold tailWord_2278063
  simp only [CollatzResearch.WordTrace]
  refine ⟨83087783545974288030686843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55391855697316192020457895 83087783545974288030686843)
  ·
    refine ⟨124631675318961432046030265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83087783545974288030686843 124631675318961432046030265)
    ·
      refine ⟨93473756489221074034522699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124631675318961432046030265 93473756489221074034522699)
      ·
        refine ⟨140210634733831611051784049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93473756489221074034522699 140210634733831611051784049)
        ·
          refine ⟨105157976050373708288838037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140210634733831611051784049 105157976050373708288838037)
          ·
            refine ⟨4929280127361267576039283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105157976050373708288838037 4929280127361267576039283)
            ·
              refine ⟨7393920191041901364058925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929280127361267576039283 7393920191041901364058925)
              ·
                refine ⟨2772720071640713011522097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7393920191041901364058925 2772720071640713011522097)
                ·
                  refine ⟨2079540053730534758641573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772720071640713011522097 2079540053730534758641573)
                  ·
                    refine ⟨389913760074475267245295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079540053730534758641573 389913760074475267245295)
                    ·
                      rfl

theorem cell23_2278063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_2278063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278063 prefixEnd_2278063 := by exact prefixLift 2278063
  have htrace : WordTrace (prefixWord ++ tailWord_2278063) baseStart_2278063 baseEnd_2278063 := by
    simpa [prefixWord, tailWord_2278063, baseEnd_2278063] using wordTrace_append hprefix tailTrace_2278063
  have hstable : (prefixWord ++ tailWord_2278063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278063).length < 2 ^ (prefixWord ++ tailWord_2278063).sum := by decide
  have hdescent : baseEnd_2278063 < baseStart_2278063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278066 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2278066 : Nat := 118140960795 + 2278066 * 2 ^ 59
def prefixEnd_2278066 : Nat := 4983230072969 + 3 ^ 40 * 2278066 * 2
def baseEnd_2278066 : Nat := 1169742820665389289998371

theorem tailTrace_2278066 : CollatzResearch.WordTrace tailWord_2278066 prefixEnd_2278066 1169742820665389289998371 := by
  unfold tailWord_2278066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771973241240854885761513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55391928643308946362030701 20771973241240854885761513)
  ·
    refine ⟨15578979930930641164321135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20771973241240854885761513 15578979930930641164321135)
    ·
      refine ⟨23368469896395961746481703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15578979930930641164321135 23368469896395961746481703)
      ·
        refine ⟨35052704844593942619722555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23368469896395961746481703 35052704844593942619722555)
        ·
          refine ⟨52579057266890913929583833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35052704844593942619722555 52579057266890913929583833)
          ·
            refine ⟨39434292950168185447187875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52579057266890913929583833 39434292950168185447187875)
            ·
              refine ⟨59151439425252278170781813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39434292950168185447187875 59151439425252278170781813)
              ·
                refine ⟨5545447446117401078510795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59151439425252278170781813 5545447446117401078510795)
                ·
                  refine ⟨8318171169176101617766193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545447446117401078510795 8318171169176101617766193)
                  ·
                    refine ⟨6238628376882076213324645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8318171169176101617766193 6238628376882076213324645)
                    ·
                      refine ⟨1169742820665389289998371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6238628376882076213324645 1169742820665389289998371)
                      ·
                        rfl

theorem cell23_2278066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2278066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278066 prefixEnd_2278066 := by exact prefixLift 2278066
  have htrace : WordTrace (prefixWord ++ tailWord_2278066) baseStart_2278066 baseEnd_2278066 := by
    simpa [prefixWord, tailWord_2278066, baseEnd_2278066] using wordTrace_append hprefix tailTrace_2278066
  have hstable : (prefixWord ++ tailWord_2278066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278066).length < 2 ^ (prefixWord ++ tailWord_2278066).sum := by decide
  have hdescent : baseEnd_2278066 < baseStart_2278066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278089 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_2278089 : Nat := 118140960795 + 2278089 * 2 ^ 59
def prefixEnd_2278089 : Nat := 4983230072969 + 3 ^ 40 * 2278089 * 2
def baseEnd_2278089 : Nat := 389918210240147566670255

theorem tailTrace_2278089 : CollatzResearch.WordTrace tailWord_2278089 prefixEnd_2278089 389918210240147566670255 := by
  unfold tailWord_2278089
  simp only [CollatzResearch.WordTrace]
  refine ⟨83088731843880094471133321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55392487895920062980755547 83088731843880094471133321)
  ·
    refine ⟨62316548882910070853349991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83088731843880094471133321 62316548882910070853349991)
    ·
      refine ⟨93474823324365106280024987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62316548882910070853349991 93474823324365106280024987)
      ·
        refine ⟨140212234986547659420037481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93474823324365106280024987 140212234986547659420037481)
        ·
          refine ⟨105159176239910744565028111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140212234986547659420037481 105159176239910744565028111)
          ·
            refine ⟨157738764359866116847542167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105159176239910744565028111 157738764359866116847542167)
            ·
              refine ⟨236608146539799175271313251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157738764359866116847542167 236608146539799175271313251)
              ·
                refine ⟨354912219809698762906969877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236608146539799175271313251 354912219809698762906969877)
                ·
                  refine ⟨16636510303579629511264213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 354912219809698762906969877 16636510303579629511264213)
                  ·
                    refine ⟨389918210240147566670255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16636510303579629511264213 389918210240147566670255)
                    ·
                      rfl

theorem cell23_2278089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_2278089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278089 prefixEnd_2278089 := by exact prefixLift 2278089
  have htrace : WordTrace (prefixWord ++ tailWord_2278089) baseStart_2278089 baseEnd_2278089 := by
    simpa [prefixWord, tailWord_2278089, baseEnd_2278089] using wordTrace_append hprefix tailTrace_2278089
  have hstable : (prefixWord ++ tailWord_2278089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278089).length < 2 ^ (prefixWord ++ tailWord_2278089).sum := by decide
  have hdescent : baseEnd_2278089 < baseStart_2278089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278093 : List Nat := [1, 6, 2, 1, 2, 11]
def baseStart_2278093 : Nat := 118140960795 + 2278093 * 2 ^ 59
def prefixEnd_2278093 : Nat := 4983230072969 + 3 ^ 40 * 2278093 * 2
def baseEnd_2278093 : Nat := 4813813517049632445929

theorem tailTrace_2278093 : CollatzResearch.WordTrace tailWord_2278093 prefixEnd_2278093 4813813517049632445929 := by
  unfold tailWord_2278093
  simp only [CollatzResearch.WordTrace]
  refine ⟨83088877735865603154278933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55392585157243735436185955 83088877735865603154278933)
  ·
    refine ⟨3894791143868700147856825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83088877735865603154278933 3894791143868700147856825)
    ·
      refine ⟨2921093357901525110892619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3894791143868700147856825 2921093357901525110892619)
      ·
        refine ⟨4381640036852287666338929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921093357901525110892619 4381640036852287666338929)
        ·
          refine ⟨3286230027639215749754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4381640036852287666338929 3286230027639215749754197)
          ·
            refine ⟨4813813517049632445929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3286230027639215749754197 4813813517049632445929)
            ·
              rfl

theorem cell23_2278093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 11].length) (baseStart_2278093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278093 prefixEnd_2278093 := by exact prefixLift 2278093
  have htrace : WordTrace (prefixWord ++ tailWord_2278093) baseStart_2278093 baseEnd_2278093 := by
    simpa [prefixWord, tailWord_2278093, baseEnd_2278093] using wordTrace_append hprefix tailTrace_2278093
  have hstable : (prefixWord ++ tailWord_2278093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278093).length < 2 ^ (prefixWord ++ tailWord_2278093).sum := by decide
  have hdescent : baseEnd_2278093 < baseStart_2278093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278104 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_2278104 : Nat := 118140960795 + 2278104 * 2 ^ 59
def prefixEnd_2278104 : Nat := 4983230072969 + 3 ^ 40 * 2278104 * 2
def baseEnd_2278104 : Nat := 1169762332930260141323197

theorem tailTrace_2278104 : CollatzResearch.WordTrace tailWord_2278104 prefixEnd_2278104 1169762332930260141323197 := by
  unfold tailWord_2278104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41544639469412876016464683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55392852625883834688619577 41544639469412876016464683)
  ·
    refine ⟨62316959204119314024697025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41544639469412876016464683 62316959204119314024697025)
    ·
      refine ⟨46737719403089485518522769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62316959204119314024697025 46737719403089485518522769)
      ·
        refine ⟨35053289552317114138892077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46737719403089485518522769 35053289552317114138892077)
        ·
          refine ⟨13144983582118917802084529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35053289552317114138892077 13144983582118917802084529)
          ·
            refine ⟨9858737686589188351563397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13144983582118917802084529 9858737686589188351563397)
            ·
              refine ⟨1848513316235472815918137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9858737686589188351563397 1848513316235472815918137)
              ·
                refine ⟨1386384987176604611938603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848513316235472815918137 1386384987176604611938603)
                ·
                  refine ⟨2079577480764906917907905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386384987176604611938603 2079577480764906917907905)
                  ·
                    refine ⟨1559683110573680188430929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079577480764906917907905 1559683110573680188430929)
                    ·
                      refine ⟨1169762332930260141323197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559683110573680188430929 1169762332930260141323197)
                      ·
                        rfl

theorem cell23_2278104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_2278104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278104 prefixEnd_2278104 := by exact prefixLift 2278104
  have htrace : WordTrace (prefixWord ++ tailWord_2278104) baseStart_2278104 baseEnd_2278104 := by
    simpa [prefixWord, tailWord_2278104, baseEnd_2278104] using wordTrace_append hprefix tailTrace_2278104
  have hstable : (prefixWord ++ tailWord_2278104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278104).length < 2 ^ (prefixWord ++ tailWord_2278104).sum := by decide
  have hdescent : baseEnd_2278104 < baseStart_2278104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278120 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2278120 : Nat := 118140960795 + 2278120 * 2 ^ 59
def prefixEnd_2278120 : Nat := 4983230072969 + 3 ^ 40 * 2278120 * 2
def baseEnd_2278120 : Nat := 1169770548620732078723123

theorem tailTrace_2278120 : CollatzResearch.WordTrace tailWord_2278120 prefixEnd_2278120 1169770548620732078723123 := by
  unfold tailWord_2278120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41544931253383893382755907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55393241671178524510341209 41544931253383893382755907)
  ·
    refine ⟨62317396880075840074133861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41544931253383893382755907 62317396880075840074133861)
    ·
      refine ⟨11684511915014220013900099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62317396880075840074133861 11684511915014220013900099)
      ·
        refine ⟨17526767872521330020850149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684511915014220013900099 17526767872521330020850149)
        ·
          refine ⟨3286268976097749378909403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17526767872521330020850149 3286268976097749378909403)
          ·
            refine ⟨4929403464146624068364105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286268976097749378909403 4929403464146624068364105)
            ·
              refine ⟨3697052598109968051273079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929403464146624068364105 3697052598109968051273079)
              ·
                refine ⟨5545578897164952076909619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697052598109968051273079 5545578897164952076909619)
                ·
                  refine ⟨8318368345747428115364429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545578897164952076909619 8318368345747428115364429)
                  ·
                    refine ⟨3119388129655285543261661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8318368345747428115364429 3119388129655285543261661)
                    ·
                      refine ⟨1169770548620732078723123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3119388129655285543261661 1169770548620732078723123)
                      ·
                        rfl

theorem cell23_2278120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2278120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278120 prefixEnd_2278120 := by exact prefixLift 2278120
  have htrace : WordTrace (prefixWord ++ tailWord_2278120) baseStart_2278120 baseEnd_2278120 := by
    simpa [prefixWord, tailWord_2278120, baseEnd_2278120] using wordTrace_append hprefix tailTrace_2278120
  have hstable : (prefixWord ++ tailWord_2278120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278120).length < 2 ^ (prefixWord ++ tailWord_2278120).sum := by decide
  have hdescent : baseEnd_2278120 < baseStart_2278120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278130 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2278130 : Nat := 118140960795 + 2278130 * 2 ^ 59
def prefixEnd_2278130 : Nat := 4983230072969 + 3 ^ 40 * 2278130 * 2
def baseEnd_2278130 : Nat := 1169775683427277039598077

theorem tailTrace_2278130 : CollatzResearch.WordTrace tailWord_2278130 prefixEnd_2278130 1169775683427277039598077 := by
  unfold tailWord_2278130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772556809182889618343961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55393484824487705648917229 20772556809182889618343961)
  ·
    refine ⟨15579417606887167213757971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20772556809182889618343961 15579417606887167213757971)
    ·
      refine ⟨23369126410330750820636957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15579417606887167213757971 23369126410330750820636957)
      ·
        refine ⟨8763422403874031557738859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23369126410330750820636957 8763422403874031557738859)
        ·
          refine ⟨13145133605811047336608289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8763422403874031557738859 13145133605811047336608289)
          ·
            refine ⟨9858850204358285502456217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13145133605811047336608289 9858850204358285502456217)
            ·
              refine ⟨7394137653268714126842163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9858850204358285502456217 7394137653268714126842163)
              ·
                refine ⟨11091206479903071190263245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7394137653268714126842163 11091206479903071190263245)
                ·
                  refine ⟨4159202429963651696348717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11091206479903071190263245 4159202429963651696348717)
                  ·
                    refine ⟨1559700911236369386130769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4159202429963651696348717 1559700911236369386130769)
                    ·
                      refine ⟨1169775683427277039598077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559700911236369386130769 1169775683427277039598077)
                      ·
                        rfl

theorem cell23_2278130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2278130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278130 prefixEnd_2278130 := by exact prefixLift 2278130
  have htrace : WordTrace (prefixWord ++ tailWord_2278130) baseStart_2278130 baseEnd_2278130 := by
    simpa [prefixWord, tailWord_2278130, baseEnd_2278130] using wordTrace_append hprefix tailTrace_2278130
  have hstable : (prefixWord ++ tailWord_2278130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278130).length < 2 ^ (prefixWord ++ tailWord_2278130).sum := by decide
  have hdescent : baseEnd_2278130 < baseStart_2278130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278228 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_2278228 : Nat := 118140960795 + 2278228 * 2 ^ 59
def prefixEnd_2278228 : Nat := 4983230072969 + 3 ^ 40 * 2278228 * 2
def baseEnd_2278228 : Nat := 1169826004531417656172627

theorem tailTrace_2278228 : CollatzResearch.WordTrace tailWord_2278228 prefixEnd_2278228 1169826004531417656172627 := by
  unfold tailWord_2278228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41546900795188260605221669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55395867726917680806962225 41546900795188260605221669)
  ·
    refine ⟨7790043899097798863479063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41546900795188260605221669 7790043899097798863479063)
    ·
      refine ⟨11685065848646698295218595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790043899097798863479063 11685065848646698295218595)
      ·
        refine ⟨17527598772970047442827893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685065848646698295218595 17527598772970047442827893)
        ·
          refine ⟨1643212384965941947765115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17527598772970047442827893 1643212384965941947765115)
          ·
            refine ⟨2464818577448912921647673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643212384965941947765115 2464818577448912921647673)
            ·
              refine ⟨1848613933086684691235755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464818577448912921647673 1848613933086684691235755)
              ·
                refine ⟨2772920899630027036853633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848613933086684691235755 2772920899630027036853633)
                ·
                  refine ⟨2079690674722520277640225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772920899630027036853633 2079690674722520277640225)
                  ·
                    refine ⟨1559768006041890208230169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079690674722520277640225 1559768006041890208230169)
                    ·
                      refine ⟨1169826004531417656172627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559768006041890208230169 1169826004531417656172627)
                      ·
                        rfl

theorem cell23_2278228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_2278228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278228 prefixEnd_2278228 := by exact prefixLift 2278228
  have htrace : WordTrace (prefixWord ++ tailWord_2278228) baseStart_2278228 baseEnd_2278228 := by
    simpa [prefixWord, tailWord_2278228, baseEnd_2278228] using wordTrace_append hprefix tailTrace_2278228
  have hstable : (prefixWord ++ tailWord_2278228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278228).length < 2 ^ (prefixWord ++ tailWord_2278228).sum := by decide
  have hdescent : baseEnd_2278228 < baseStart_2278228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278256 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 10]
def baseStart_2278256 : Nat := 118140960795 + 2278256 * 2 ^ 59
def prefixEnd_2278256 : Nat := 4983230072969 + 3 ^ 40 * 2278256 * 2
def baseEnd_2278256 : Nat := 129982264665527060735833

theorem tailTrace_2278256 : CollatzResearch.WordTrace tailWord_2278256 prefixEnd_2278256 129982264665527060735833 := by
  unfold tailWord_2278256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547411417137540996231311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55396548556183387994975081 41547411417137540996231311)
  ·
    refine ⟨62321117125706311494346967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41547411417137540996231311 62321117125706311494346967)
    ·
      refine ⟨93481675688559467241520451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62321117125706311494346967 93481675688559467241520451)
      ·
        refine ⟨140222513532839200862280677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93481675688559467241520451 140222513532839200862280677)
        ·
          refine ⟨26291721287407350161677627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140222513532839200862280677 26291721287407350161677627)
          ·
            refine ⟨39437581931111025242516441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26291721287407350161677627 39437581931111025242516441)
            ·
              refine ⟨29578186448333268931887331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39437581931111025242516441 29578186448333268931887331)
              ·
                refine ⟨44367279672499903397830997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29578186448333268931887331 44367279672499903397830997)
                ·
                  refine ⟨129982264665527060735833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44367279672499903397830997 129982264665527060735833)
                  ·
                    rfl

theorem cell23_2278256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_2278256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278256 prefixEnd_2278256 := by exact prefixLift 2278256
  have htrace : WordTrace (prefixWord ++ tailWord_2278256) baseStart_2278256 baseEnd_2278256 := by
    simpa [prefixWord, tailWord_2278256, baseEnd_2278256] using wordTrace_append hprefix tailTrace_2278256
  have hstable : (prefixWord ++ tailWord_2278256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278256).length < 2 ^ (prefixWord ++ tailWord_2278256).sum := by decide
  have hdescent : baseEnd_2278256 < baseStart_2278256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278277 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2278277 : Nat := 118140960795 + 2278277 * 2 ^ 59
def prefixEnd_2278277 : Nat := 4983230072969 + 3 ^ 40 * 2278277 * 2
def baseEnd_2278277 : Nat := 389950388361162654819967

theorem tailTrace_2278277 : CollatzResearch.WordTrace tailWord_2278277 prefixEnd_2278277 389950388361162654819967 := by
  unfold tailWord_2278277
  simp only [CollatzResearch.WordTrace]
  refine ⟨83095588767199002578977085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55397059178132668385984723 83095588767199002578977085)
  ·
    refine ⟨31160845787699625967116407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83095588767199002578977085 31160845787699625967116407)
    ·
      refine ⟨46741268681549438950674611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31160845787699625967116407 46741268681549438950674611)
      ·
        refine ⟨70111903022324158426011917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46741268681549438950674611 70111903022324158426011917)
        ·
          refine ⟨26291963633371559409754469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70111903022324158426011917 26291963633371559409754469)
          ·
            refine ⟨4929743181257167389328963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26291963633371559409754469 4929743181257167389328963)
            ·
              refine ⟨7394614771885751083993445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929743181257167389328963 7394614771885751083993445)
              ·
                refine ⟨1386490269728578328248771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7394614771885751083993445 1386490269728578328248771)
                ·
                  refine ⟨2079735404592867492373157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386490269728578328248771 2079735404592867492373157)
                  ·
                    refine ⟨389950388361162654819967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079735404592867492373157 389950388361162654819967)
                    ·
                      rfl

theorem cell23_2278277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2278277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278277 prefixEnd_2278277 := by exact prefixLift 2278277
  have htrace : WordTrace (prefixWord ++ tailWord_2278277) baseStart_2278277 baseEnd_2278277 := by
    simpa [prefixWord, tailWord_2278277, baseEnd_2278277] using wordTrace_append hprefix tailTrace_2278277
  have hstable : (prefixWord ++ tailWord_2278277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278277).length < 2 ^ (prefixWord ++ tailWord_2278277).sum := by decide
  have hdescent : baseEnd_2278277 < baseStart_2278277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278294 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2278294 : Nat := 118140960795 + 2278294 * 2 ^ 59
def prefixEnd_2278294 : Nat := 4983230072969 + 3 ^ 40 * 2278294 * 2
def baseEnd_2278294 : Nat := 389953298084871465982441

theorem tailTrace_2278294 : CollatzResearch.WordTrace tailWord_2278294 prefixEnd_2278294 389953298084871465982441 := by
  unfold tailWord_2278294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193513050508588405146621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55397472538758276321563957 5193513050508588405146621)
  ·
    refine ⟨1947567393940720651929983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5193513050508588405146621 1947567393940720651929983)
    ·
      refine ⟨2921351090911080977894975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947567393940720651929983 2921351090911080977894975)
      ·
        refine ⟨4382026636366621466842463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921351090911080977894975 4382026636366621466842463)
        ·
          refine ⟨6573039954549932200263695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382026636366621466842463 6573039954549932200263695)
          ·
            refine ⟨9859559931824898300395543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573039954549932200263695 9859559931824898300395543)
            ·
              refine ⟨14789339897737347450593315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9859559931824898300395543 14789339897737347450593315)
              ·
                refine ⟨22184009846606021175889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789339897737347450593315 22184009846606021175889973)
                ·
                  refine ⟨2079750923119314485239685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22184009846606021175889973 2079750923119314485239685)
                  ·
                    refine ⟨389953298084871465982441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079750923119314485239685 389953298084871465982441)
                    ·
                      rfl

theorem cell23_2278294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2278294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278294 prefixEnd_2278294 := by exact prefixLift 2278294
  have htrace : WordTrace (prefixWord ++ tailWord_2278294) baseStart_2278294 baseEnd_2278294 := by
    simpa [prefixWord, tailWord_2278294, baseEnd_2278294] using wordTrace_append hprefix tailTrace_2278294
  have hstable : (prefixWord ++ tailWord_2278294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278294).length < 2 ^ (prefixWord ++ tailWord_2278294).sum := by decide
  have hdescent : baseEnd_2278294 < baseStart_2278294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278323 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4]
def baseStart_2278323 : Nat := 118140960795 + 2278323 * 2 ^ 59
def prefixEnd_2278323 : Nat := 4983230072969 + 3 ^ 40 * 2278323 * 2
def baseEnd_2278323 : Nat := 1169874785193594784484689

theorem tailTrace_2278323 : CollatzResearch.WordTrace tailWord_2278323 prefixEnd_2278323 1169874785193594784484689 := by
  unfold tailWord_2278323
  simp only [CollatzResearch.WordTrace]
  refine ⟨83097266525032352435151623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55398177683354901623434415 83097266525032352435151623)
  ·
    refine ⟨124645899787548528652727435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83097266525032352435151623 124645899787548528652727435)
    ·
      refine ⟨186968849681322792979091153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124645899787548528652727435 186968849681322792979091153)
      ·
        refine ⟨140226637260992094734318365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186968849681322792979091153 140226637260992094734318365)
        ·
          refine ⟨52584988972872035525369387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140226637260992094734318365 52584988972872035525369387)
          ·
            refine ⟨78877483459308053288054081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52584988972872035525369387 78877483459308053288054081)
            ·
              refine ⟨59158112594481039966040561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78877483459308053288054081 59158112594481039966040561)
              ·
                refine ⟨44368584445860779974530421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59158112594481039966040561 44368584445860779974530421)
                ·
                  refine ⟨4159554791799448122612227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44368584445860779974530421 4159554791799448122612227)
                  ·
                    refine ⟨6239332187699172183918341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4159554791799448122612227 6239332187699172183918341)
                    ·
                      refine ⟨1169874785193594784484689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6239332187699172183918341 1169874785193594784484689)
                      ·
                        rfl

theorem cell23_2278323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_2278323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278323 prefixEnd_2278323 := by exact prefixLift 2278323
  have htrace : WordTrace (prefixWord ++ tailWord_2278323) baseStart_2278323 baseEnd_2278323 := by
    simpa [prefixWord, tailWord_2278323, baseEnd_2278323] using wordTrace_append hprefix tailTrace_2278323
  have hstable : (prefixWord ++ tailWord_2278323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278323).length < 2 ^ (prefixWord ++ tailWord_2278323).sum := by decide
  have hdescent : baseEnd_2278323 < baseStart_2278323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278324 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 6]
def baseStart_2278324 : Nat := 118140960795 + 2278324 * 2 ^ 59
def prefixEnd_2278324 : Nat := 4983230072969 + 3 ^ 40 * 2278324 * 2
def baseEnd_2278324 : Nat := 129986144297138808952465

theorem tailTrace_2278324 : CollatzResearch.WordTrace tailWord_2278324 prefixEnd_2278324 129986144297138808952465 := by
  unfold tailWord_2278324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41548651499014364802969013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55398201998685819737292017 41548651499014364802969013)
  ·
    refine ⟨3895186078032596700278345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41548651499014364802969013 3895186078032596700278345)
    ·
      refine ⟨2921389558524447525208759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895186078032596700278345 2921389558524447525208759)
      ·
        refine ⟨4382084337786671287813139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921389558524447525208759 4382084337786671287813139)
        ·
          refine ⟨6573126506680006931719709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382084337786671287813139 6573126506680006931719709)
          ·
            refine ⟨2464922440005002599394891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6573126506680006931719709 2464922440005002599394891)
            ·
              refine ⟨3697383660007503899092337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464922440005002599394891 3697383660007503899092337)
              ·
                refine ⟨2773037745005627924319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697383660007503899092337 2773037745005627924319253)
                ·
                  refine ⟨129986144297138808952465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2773037745005627924319253 129986144297138808952465)
                  ·
                    rfl

theorem cell23_2278324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_2278324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278324 prefixEnd_2278324 := by exact prefixLift 2278324
  have htrace : WordTrace (prefixWord ++ tailWord_2278324) baseStart_2278324 baseEnd_2278324 := by
    simpa [prefixWord, tailWord_2278324, baseEnd_2278324] using wordTrace_append hprefix tailTrace_2278324
  have hstable : (prefixWord ++ tailWord_2278324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278324).length < 2 ^ (prefixWord ++ tailWord_2278324).sum := by decide
  have hdescent : baseEnd_2278324 < baseStart_2278324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278334 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_2278334 : Nat := 118140960795 + 2278334 * 2 ^ 59
def prefixEnd_2278334 : Nat := 4983230072969 + 3 ^ 40 * 2278334 * 2
def baseEnd_2278334 : Nat := 1169880433480794241447139

theorem tailTrace_2278334 : CollatzResearch.WordTrace tailWord_2278334 prefixEnd_2278334 1169880433480794241447139 := by
  unfold tailWord_2278334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387208465999062664225257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55398445151995000875868037 10387208465999062664225257)
  ·
    refine ⟨7790406349499296998168943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10387208465999062664225257 7790406349499296998168943)
    ·
      refine ⟨11685609524248945497253415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790406349499296998168943 11685609524248945497253415)
      ·
        refine ⟨17528414286373418245880123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685609524248945497253415 17528414286373418245880123)
        ·
          refine ⟨26292621429560127368820185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17528414286373418245880123 26292621429560127368820185)
          ·
            refine ⟨19719466072170095526615139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26292621429560127368820185 19719466072170095526615139)
            ·
              refine ⟨29579199108255143289922709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19719466072170095526615139 29579199108255143289922709)
              ·
                refine ⟨1386524958199459841715127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29579199108255143289922709 1386524958199459841715127)
                ·
                  refine ⟨2079787437299189762572691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386524958199459841715127 2079787437299189762572691)
                  ·
                    refine ⟨3119681155948784643859037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2079787437299189762572691 3119681155948784643859037)
                    ·
                      refine ⟨1169880433480794241447139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3119681155948784643859037 1169880433480794241447139)
                      ·
                        rfl

theorem cell23_2278334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_2278334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278334 prefixEnd_2278334 := by exact prefixLift 2278334
  have htrace : WordTrace (prefixWord ++ tailWord_2278334) baseStart_2278334 baseEnd_2278334 := by
    simpa [prefixWord, tailWord_2278334, baseEnd_2278334] using wordTrace_append hprefix tailTrace_2278334
  have hstable : (prefixWord ++ tailWord_2278334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278334).length < 2 ^ (prefixWord ++ tailWord_2278334).sum := by decide
  have hdescent : baseEnd_2278334 < baseStart_2278334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278343 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2278343 : Nat := 118140960795 + 2278343 * 2 ^ 59
def prefixEnd_2278343 : Nat := 4983230072969 + 3 ^ 40 * 2278343 * 2
def baseEnd_2278343 : Nat := 1169885054806684706234597

theorem tailTrace_2278343 : CollatzResearch.WordTrace tailWord_2278343 prefixEnd_2278343 1169885054806684706234597 := by
  unfold tailWord_2278343
  simp only [CollatzResearch.WordTrace]
  refine ⟨83097995984959895850879683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55398663989973263900586455 83097995984959895850879683)
  ·
    refine ⟨124646993977439843776319525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83097995984959895850879683 124646993977439843776319525)
    ·
      refine ⟨23371311370769970708059911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124646993977439843776319525 23371311370769970708059911)
      ·
        refine ⟨35056967056154956062089867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23371311370769970708059911 35056967056154956062089867)
        ·
          refine ⟨52585450584232434093134801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35056967056154956062089867 52585450584232434093134801)
          ·
            refine ⟨39439087938174325569851101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52585450584232434093134801 39439087938174325569851101)
            ·
              refine ⟨14789657976815372088694163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39439087938174325569851101 14789657976815372088694163)
              ·
                refine ⟨22184486965223058133041245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789657976815372088694163 22184486965223058133041245)
                ·
                  refine ⟨8319182611958646799890467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22184486965223058133041245 8319182611958646799890467)
                  ·
                    refine ⟨12478773917937970199835701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8319182611958646799890467 12478773917937970199835701)
                    ·
                      refine ⟨1169885054806684706234597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12478773917937970199835701 1169885054806684706234597)
                      ·
                        rfl

theorem cell23_2278343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2278343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278343 prefixEnd_2278343 := by exact prefixLift 2278343
  have htrace : WordTrace (prefixWord ++ tailWord_2278343) baseStart_2278343 baseEnd_2278343 := by
    simpa [prefixWord, tailWord_2278343, baseEnd_2278343] using wordTrace_append hprefix tailTrace_2278343
  have hstable : (prefixWord ++ tailWord_2278343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278343).length < 2 ^ (prefixWord ++ tailWord_2278343).sum := by decide
  have hdescent : baseEnd_2278343 < baseStart_2278343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278350 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2278350 : Nat := 118140960795 + 2278350 * 2 ^ 59
def prefixEnd_2278350 : Nat := 4983230072969 + 3 ^ 40 * 2278350 * 2
def baseEnd_2278350 : Nat := 389962883057088726282355

theorem tailTrace_2278350 : CollatzResearch.WordTrace tailWord_2278350 prefixEnd_2278350 389962883057088726282355 := by
  unfold tailWord_2278350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387281411991817005798063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55398834197289690697589669 10387281411991817005798063)
  ·
    refine ⟨15580922117987725508697095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387281411991817005798063 15580922117987725508697095)
    ·
      refine ⟨23371383176981588263045643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580922117987725508697095 23371383176981588263045643)
      ·
        refine ⟨35057074765472382394568465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23371383176981588263045643 35057074765472382394568465)
        ·
          refine ⟨26292806074104286795926349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35057074765472382394568465 26292806074104286795926349)
          ·
            refine ⟨9859802277789107548472381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26292806074104286795926349 9859802277789107548472381)
            ·
              refine ⟨3697425854170915330677143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9859802277789107548472381 3697425854170915330677143)
              ·
                refine ⟨5546138781256372996015715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697425854170915330677143 5546138781256372996015715)
                ·
                  refine ⟨8319208171884559494023573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546138781256372996015715 8319208171884559494023573)
                  ·
                    refine ⟨389962883057088726282355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8319208171884559494023573 389962883057088726282355)
                    ·
                      rfl

theorem cell23_2278350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2278350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278350 prefixEnd_2278350 := by exact prefixLift 2278350
  have htrace : WordTrace (prefixWord ++ tailWord_2278350) baseStart_2278350 baseEnd_2278350 := by
    simpa [prefixWord, tailWord_2278350, baseEnd_2278350] using wordTrace_append hprefix tailTrace_2278350
  have hstable : (prefixWord ++ tailWord_2278350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278350).length < 2 ^ (prefixWord ++ tailWord_2278350).sum := by decide
  have hdescent : baseEnd_2278350 < baseStart_2278350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278353 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_2278353 : Nat := 118140960795 + 2278353 * 2 ^ 59
def prefixEnd_2278353 : Nat := 4983230072969 + 3 ^ 40 * 2278353 * 2
def baseEnd_2278353 : Nat := 1169890189613229667109551

theorem tailTrace_2278353 : CollatzResearch.WordTrace tailWord_2278353 prefixEnd_2278353 1169890189613229667109551 := by
  unfold tailWord_2278353
  simp only [CollatzResearch.WordTrace]
  refine ⟨83098360714923667558743713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55398907143282445039162475 83098360714923667558743713)
  ·
    refine ⟨62323770536192750669057785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83098360714923667558743713 62323770536192750669057785)
    ·
      refine ⟨46742827902144563001793339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62323770536192750669057785 46742827902144563001793339)
      ·
        refine ⟨70114241853216844502690009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46742827902144563001793339 70114241853216844502690009)
        ·
          refine ⟨52585681389912633377017507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70114241853216844502690009 52585681389912633377017507)
          ·
            refine ⟨78878522084868950065526261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52585681389912633377017507 78878522084868950065526261)
            ·
              refine ⟨7394861445456464068643087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78878522084868950065526261 7394861445456464068643087)
              ·
                refine ⟨11092292168184696102964631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7394861445456464068643087 11092292168184696102964631)
                ·
                  refine ⟨16638438252277044154446947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11092292168184696102964631 16638438252277044154446947)
                  ·
                    refine ⟨24957657378415566231670421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16638438252277044154446947 24957657378415566231670421)
                    ·
                      refine ⟨1169890189613229667109551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24957657378415566231670421 1169890189613229667109551)
                      ·
                        rfl

theorem cell23_2278353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_2278353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278353 prefixEnd_2278353 := by exact prefixLift 2278353
  have htrace : WordTrace (prefixWord ++ tailWord_2278353) baseStart_2278353 baseEnd_2278353 := by
    simpa [prefixWord, tailWord_2278353, baseEnd_2278353] using wordTrace_append hprefix tailTrace_2278353
  have hstable : (prefixWord ++ tailWord_2278353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278353).length < 2 ^ (prefixWord ++ tailWord_2278353).sum := by decide
  have hdescent : baseEnd_2278353 < baseStart_2278353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278393 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_2278393 : Nat := 118140960795 + 2278393 * 2 ^ 59
def prefixEnd_2278393 : Nat := 4983230072969 + 3 ^ 40 * 2278393 * 2
def baseEnd_2278393 : Nat := 389970242946469836869789

theorem tailTrace_2278393 : CollatzResearch.WordTrace tailWord_2278393 prefixEnd_2278393 389970242946469836869789 := by
  unfold tailWord_2278393
  simp only [CollatzResearch.WordTrace]
  refine ⟨83099819634778754390199833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55399879756519169593466555 83099819634778754390199833)
  ·
    refine ⟨62324864726084065792649875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83099819634778754390199833 62324864726084065792649875)
    ·
      refine ⟨93487297089126098688974813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62324864726084065792649875 93487297089126098688974813)
      ·
        refine ⟨35057736408422287008365555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93487297089126098688974813 35057736408422287008365555)
        ·
          refine ⟨52586604612633430512548333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35057736408422287008365555 52586604612633430512548333)
          ·
            refine ⟨19719976729737536442205625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52586604612633430512548333 19719976729737536442205625)
            ·
              refine ⟨14789982547303152331654219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19719976729737536442205625 14789982547303152331654219)
              ·
                refine ⟨22184973820954728497481329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789982547303152331654219 22184973820954728497481329)
                ·
                  refine ⟨16638730365716046373110997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22184973820954728497481329 16638730365716046373110997)
                  ·
                    refine ⟨389970242946469836869789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16638730365716046373110997 389970242946469836869789)
                    ·
                      rfl

theorem cell23_2278393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_2278393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278393 prefixEnd_2278393 := by exact prefixLift 2278393
  have htrace : WordTrace (prefixWord ++ tailWord_2278393) baseStart_2278393 baseEnd_2278393 := by
    simpa [prefixWord, tailWord_2278393, baseEnd_2278393] using wordTrace_append hprefix tailTrace_2278393
  have hstable : (prefixWord ++ tailWord_2278393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278393).length < 2 ^ (prefixWord ++ tailWord_2278393).sum := by decide
  have hdescent : baseEnd_2278393 < baseStart_2278393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278442 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2278442 : Nat := 118140960795 + 2278442 * 2 ^ 59
def prefixEnd_2278442 : Nat := 4983230072969 + 3 ^ 40 * 2278442 * 2
def baseEnd_2278442 : Nat := 1169935889391479818896643

theorem tailTrace_2278442 : CollatzResearch.WordTrace tailWord_2278442 prefixEnd_2278442 1169935889391479818896643 := by
  unfold tailWord_2278442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775401702900308939683395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55401071207734157172489053 20775401702900308939683395)
  ·
    refine ⟨31163102554350463409525093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20775401702900308939683395 31163102554350463409525093)
    ·
      refine ⟨5843081728940711889285955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31163102554350463409525093 5843081728940711889285955)
      ·
        refine ⟨8764622593411067833928933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843081728940711889285955 8764622593411067833928933)
        ·
          refine ⟨1643366736264575218861675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8764622593411067833928933 1643366736264575218861675)
          ·
            refine ⟨2465050104396862828292513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643366736264575218861675 2465050104396862828292513)
            ·
              refine ⟨1848787578297647121219385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465050104396862828292513 1848787578297647121219385)
              ·
                refine ⟨1386590683723235340914539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848787578297647121219385 1386590683723235340914539)
                ·
                  refine ⟨2079886025584853011371809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386590683723235340914539 2079886025584853011371809)
                  ·
                    refine ⟨1559914519188639758528857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079886025584853011371809 1559914519188639758528857)
                    ·
                      refine ⟨1169935889391479818896643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559914519188639758528857 1169935889391479818896643)
                      ·
                        rfl

theorem cell23_2278442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2278442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278442 prefixEnd_2278442 := by exact prefixLift 2278442
  have htrace : WordTrace (prefixWord ++ tailWord_2278442) baseStart_2278442 baseEnd_2278442 := by
    simpa [prefixWord, tailWord_2278442, baseEnd_2278442] using wordTrace_append hprefix tailTrace_2278442
  have hstable : (prefixWord ++ tailWord_2278442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278442).length < 2 ^ (prefixWord ++ tailWord_2278442).sum := by decide
  have hdescent : baseEnd_2278442 < baseStart_2278442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278447 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 8, 2, 2]
def baseStart_2278447 : Nat := 118140960795 + 2278447 * 2 ^ 59
def prefixEnd_2278447 : Nat := 4983230072969 + 3 ^ 40 * 2278447 * 2
def baseEnd_2278447 : Nat := 1169938456794752299334119

theorem tailTrace_2278447 : CollatzResearch.WordTrace tailWord_2278447 prefixEnd_2278447 1169938456794752299334119 := by
  unfold tailWord_2278447
  simp only [CollatzResearch.WordTrace]
  refine ⟨83101789176583121612665595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55401192784388747741777063 83101789176583121612665595)
  ·
    refine ⟨124652683764874682418998393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83101789176583121612665595 124652683764874682418998393)
    ·
      refine ⟨93489512823656011814248795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124652683764874682418998393 93489512823656011814248795)
      ·
        refine ⟨140234269235484017721373193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93489512823656011814248795 140234269235484017721373193)
        ·
          refine ⟨105175701926613013291029895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140234269235484017721373193 105175701926613013291029895)
          ·
            refine ⟨157763552889919519936544843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105175701926613013291029895 157763552889919519936544843)
            ·
              refine ⟨236645329334879279904817265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157763552889919519936544843 236645329334879279904817265)
              ·
                refine ⟨177483997001159459928612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236645329334879279904817265 177483997001159459928612949)
                ·
                  refine ⟨2079890589857337421038433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 177483997001159459928612949 2079890589857337421038433)
                  ·
                    refine ⟨1559917942393003065778825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079890589857337421038433 1559917942393003065778825)
                    ·
                      refine ⟨1169938456794752299334119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559917942393003065778825 1169938456794752299334119)
                      ·
                        rfl

theorem cell23_2278447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2, 2].length) (baseStart_2278447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278447 prefixEnd_2278447 := by exact prefixLift 2278447
  have htrace : WordTrace (prefixWord ++ tailWord_2278447) baseStart_2278447 baseEnd_2278447 := by
    simpa [prefixWord, tailWord_2278447, baseEnd_2278447] using wordTrace_append hprefix tailTrace_2278447
  have hstable : (prefixWord ++ tailWord_2278447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278447).length < 2 ^ (prefixWord ++ tailWord_2278447).sum := by decide
  have hdescent : baseEnd_2278447 < baseStart_2278447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278450 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2278450 : Nat := 118140960795 + 2278450 * 2 ^ 59
def prefixEnd_2278450 : Nat := 4983230072969 + 3 ^ 40 * 2278450 * 2
def baseEnd_2278450 : Nat := 1169939997236715787596605

theorem tailTrace_2278450 : CollatzResearch.WordTrace tailWord_2278450 prefixEnd_2278450 1169939997236715787596605 := by
  unfold tailWord_2278450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775474648893063281256201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55401265730381502083349869 20775474648893063281256201)
  ·
    refine ⟨15581605986669797460942151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20775474648893063281256201 15581605986669797460942151)
    ·
      refine ⟨23372408980004696191413227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581605986669797460942151 23372408980004696191413227)
      ·
        refine ⟨35058613470007044287119841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23372408980004696191413227 35058613470007044287119841)
        ·
          refine ⟨26293960102505283215339881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35058613470007044287119841 26293960102505283215339881)
          ·
            refine ⟨19720470076878962411504911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26293960102505283215339881 19720470076878962411504911)
            ·
              refine ⟨29580705115318443617257367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19720470076878962411504911 29580705115318443617257367)
              ·
                refine ⟨44371057672977665425886051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29580705115318443617257367 44371057672977665425886051)
                ·
                  refine ⟨66556586509466498138829077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44371057672977665425886051 66556586509466498138829077)
                  ·
                    refine ⟨3119839992631242100257613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66556586509466498138829077 3119839992631242100257613)
                    ·
                      refine ⟨1169939997236715787596605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3119839992631242100257613 1169939997236715787596605)
                      ·
                        rfl

theorem cell23_2278450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2278450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278450 prefixEnd_2278450 := by exact prefixLift 2278450
  have htrace : WordTrace (prefixWord ++ tailWord_2278450) baseStart_2278450 baseEnd_2278450 := by
    simpa [prefixWord, tailWord_2278450, baseEnd_2278450] using wordTrace_append hprefix tailTrace_2278450
  have hstable : (prefixWord ++ tailWord_2278450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278450).length < 2 ^ (prefixWord ++ tailWord_2278450).sum := by decide
  have hdescent : baseEnd_2278450 < baseStart_2278450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278460 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2278460 : Nat := 118140960795 + 2278460 * 2 ^ 59
def prefixEnd_2278460 : Nat := 4983230072969 + 3 ^ 40 * 2278460 * 2
def baseEnd_2278460 : Nat := 1169945132043260748471559

theorem tailTrace_2278460 : CollatzResearch.WordTrace tailWord_2278460 prefixEnd_2278460 1169945132043260748471559 := by
  unfold tailWord_2278460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551131662768012416444417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55401508883690683221925889 41551131662768012416444417)
  ·
    refine ⟨31163348747076009312333313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41551131662768012416444417 31163348747076009312333313)
    ·
      refine ⟨23372511560307006984249985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31163348747076009312333313 23372511560307006984249985)
      ·
        refine ⟨17529383670230255238187489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23372511560307006984249985 17529383670230255238187489)
        ·
          refine ⟨13147037752672691428640617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17529383670230255238187489 13147037752672691428640617)
          ·
            refine ⟨9860278314504518571480463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147037752672691428640617 9860278314504518571480463)
            ·
              refine ⟨14790417471756777857220695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860278314504518571480463 14790417471756777857220695)
              ·
                refine ⟨22185626207635166785831043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14790417471756777857220695 22185626207635166785831043)
                ·
                  refine ⟨33278439311452750178746565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22185626207635166785831043 33278439311452750178746565)
                  ·
                    refine ⟨6239707370897390658514981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33278439311452750178746565 6239707370897390658514981)
                    ·
                      refine ⟨1169945132043260748471559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6239707370897390658514981 1169945132043260748471559)
                      ·
                        rfl

theorem cell23_2278460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2278460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278460 prefixEnd_2278460 := by exact prefixLift 2278460
  have htrace : WordTrace (prefixWord ++ tailWord_2278460) baseStart_2278460 baseEnd_2278460 := by
    simpa [prefixWord, tailWord_2278460, baseEnd_2278460] using wordTrace_append hprefix tailTrace_2278460
  have hstable : (prefixWord ++ tailWord_2278460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278460).length < 2 ^ (prefixWord ++ tailWord_2278460).sum := by decide
  have hdescent : baseEnd_2278460 < baseStart_2278460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278464 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2]
def baseStart_2278464 : Nat := 118140960795 + 2278464 * 2 ^ 59
def prefixEnd_2278464 : Nat := 4983230072969 + 3 ^ 40 * 2278464 * 2
def baseEnd_2278464 : Nat := 1169947185965878732821541

theorem tailTrace_2278464 : CollatzResearch.WordTrace tailWord_2278464 prefixEnd_2278464 1169947185965878732821541 := by
  unfold tailWord_2278464
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551204608760766758017223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55401606145014355677356297 41551204608760766758017223)
  ·
    refine ⟨62326806913141150137025835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41551204608760766758017223 62326806913141150137025835)
    ·
      refine ⟨93490210369711725205538753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62326806913141150137025835 93490210369711725205538753)
      ·
        refine ⟨70117657777283793904154065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93490210369711725205538753 70117657777283793904154065)
        ·
          refine ⟨52588243332962845428115549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70117657777283793904154065 52588243332962845428115549)
          ·
            refine ⟨19720591249861067035543331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52588243332962845428115549 19720591249861067035543331)
            ·
              refine ⟨29580886874791600553314997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19720591249861067035543331 29580886874791600553314997)
              ·
                refine ⟨2773208144511712551873281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29580886874791600553314997 2773208144511712551873281)
                ·
                  refine ⟨2079906108383784413904961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773208144511712551873281 2079906108383784413904961)
                  ·
                    refine ⟨1559929581287838310428721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079906108383784413904961 1559929581287838310428721)
                    ·
                      refine ⟨1169947185965878732821541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559929581287838310428721 1169947185965878732821541)
                      ·
                        rfl

theorem cell23_2278464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_2278464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278464 prefixEnd_2278464 := by exact prefixLift 2278464
  have htrace : WordTrace (prefixWord ++ tailWord_2278464) baseStart_2278464 baseEnd_2278464 := by
    simpa [prefixWord, tailWord_2278464, baseEnd_2278464] using wordTrace_append hprefix tailTrace_2278464
  have hstable : (prefixWord ++ tailWord_2278464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278464).length < 2 ^ (prefixWord ++ tailWord_2278464).sum := by decide
  have hdescent : baseEnd_2278464 < baseStart_2278464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278498 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2278498 : Nat := 118140960795 + 2278498 * 2 ^ 59
def prefixEnd_2278498 : Nat := 4983230072969 + 3 ^ 40 * 2278498 * 2
def baseEnd_2278498 : Nat := 1169964644308131599796385

theorem tailTrace_2278498 : CollatzResearch.WordTrace tailWord_2278498 prefixEnd_2278498 1169964644308131599796385 := by
  unfold tailWord_2278498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775912324849589330693037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55402432866265571548514765 20775912324849589330693037)
  ·
    refine ⟨7790967121818595999009889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20775912324849589330693037 7790967121818595999009889)
    ·
      refine ⟨5843225341363946999257417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7790967121818595999009889 5843225341363946999257417)
      ·
        refine ⟨4382419006022960249443063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5843225341363946999257417 4382419006022960249443063)
        ·
          refine ⟨6573628509034440374164595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382419006022960249443063 6573628509034440374164595)
          ·
            refine ⟨9860442763551660561246893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573628509034440374164595 9860442763551660561246893)
            ·
              refine ⟨3697666036331872710467585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9860442763551660561246893 3697666036331872710467585)
              ·
                refine ⟨2773249527248904532850689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697666036331872710467585 2773249527248904532850689)
                ·
                  refine ⟨2079937145436678399638017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773249527248904532850689 2079937145436678399638017)
                  ·
                    refine ⟨1559952859077508799728513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079937145436678399638017 1559952859077508799728513)
                    ·
                      refine ⟨1169964644308131599796385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1559952859077508799728513 1169964644308131599796385)
                      ·
                        rfl

theorem cell23_2278498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2278498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278498 prefixEnd_2278498 := by exact prefixLift 2278498
  have htrace : WordTrace (prefixWord ++ tailWord_2278498) baseStart_2278498 baseEnd_2278498 := by
    simpa [prefixWord, tailWord_2278498, baseEnd_2278498] using wordTrace_append hprefix tailTrace_2278498
  have hstable : (prefixWord ++ tailWord_2278498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278498).length < 2 ^ (prefixWord ++ tailWord_2278498).sum := by decide
  have hdescent : baseEnd_2278498 < baseStart_2278498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278500 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_2278500 : Nat := 118140960795 + 2278500 * 2 ^ 59
def prefixEnd_2278500 : Nat := 4983230072969 + 3 ^ 40 * 2278500 * 2
def baseEnd_2278500 : Nat := 389988557089813530657125

theorem tailTrace_2278500 : CollatzResearch.WordTrace tailWord_2278500 prefixEnd_2278500 389988557089813530657125 := by
  unfold tailWord_2278500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551861122695555832172477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55402481496927407776229969 41551861122695555832172477)
  ·
    refine ⟨15581947921010833437064679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41551861122695555832172477 15581947921010833437064679)
    ·
      refine ⟨23372921881516250155597019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581947921010833437064679 23372921881516250155597019)
      ·
        refine ⟨35059382822274375233395529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23372921881516250155597019 35059382822274375233395529)
        ·
          refine ⟨26294537116705781425046647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35059382822274375233395529 26294537116705781425046647)
          ·
            refine ⟨39441805675058672137569971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26294537116705781425046647 39441805675058672137569971)
            ·
              refine ⟨59162708512588008206354957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39441805675058672137569971 59162708512588008206354957)
              ·
                refine ⟨22186015692220503077383109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59162708512588008206354957 22186015692220503077383109)
                ·
                  refine ⟨4159877942291344327009333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22186015692220503077383109 4159877942291344327009333)
                  ·
                    refine ⟨389988557089813530657125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4159877942291344327009333 389988557089813530657125)
                    ·
                      rfl

theorem cell23_2278500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_2278500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278500 prefixEnd_2278500 := by exact prefixLift 2278500
  have htrace : WordTrace (prefixWord ++ tailWord_2278500) baseStart_2278500 baseEnd_2278500 := by
    simpa [prefixWord, tailWord_2278500, baseEnd_2278500] using wordTrace_append hprefix tailTrace_2278500
  have hstable : (prefixWord ++ tailWord_2278500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278500).length < 2 ^ (prefixWord ++ tailWord_2278500).sum := by decide
  have hdescent : baseEnd_2278500 < baseStart_2278500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278504 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 7]
def baseStart_2278504 : Nat := 118140960795 + 2278504 * 2 ^ 59
def prefixEnd_2278504 : Nat := 4983230072969 + 3 ^ 40 * 2278504 * 2
def baseEnd_2278504 : Nat := 129996413910228730702373

theorem tailTrace_2278504 : CollatzResearch.WordTrace tailWord_2278504 prefixEnd_2278504 129996413910228730702373 := by
  unfold tailWord_2278504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551934068688310173745283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55402578758251080231660377 41551934068688310173745283)
  ·
    refine ⟨62327901103032465260617925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41551934068688310173745283 62327901103032465260617925)
    ·
      refine ⟨11686481456818587236365861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62327901103032465260617925 11686481456818587236365861)
      ·
        refine ⟨2191215273153485106818599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11686481456818587236365861 2191215273153485106818599)
        ·
          refine ⟨3286822909730227660227899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191215273153485106818599 3286822909730227660227899)
          ·
            refine ⟨4930234364595341490341849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286822909730227660227899 4930234364595341490341849)
            ·
              refine ⟨3697675773446506117756387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930234364595341490341849 3697675773446506117756387)
              ·
                refine ⟨5546513660169759176634581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697675773446506117756387 5546513660169759176634581)
                ·
                  refine ⟨129996413910228730702373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5546513660169759176634581 129996413910228730702373)
                  ·
                    rfl

theorem cell23_2278504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_2278504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278504 prefixEnd_2278504 := by exact prefixLift 2278504
  have htrace : WordTrace (prefixWord ++ tailWord_2278504) baseStart_2278504 baseEnd_2278504 := by
    simpa [prefixWord, tailWord_2278504, baseEnd_2278504] using wordTrace_append hprefix tailTrace_2278504
  have hstable : (prefixWord ++ tailWord_2278504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278504).length < 2 ^ (prefixWord ++ tailWord_2278504).sum := by decide
  have hdescent : baseEnd_2278504 < baseStart_2278504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278520 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2278520 : Nat := 118140960795 + 2278520 * 2 ^ 59
def prefixEnd_2278520 : Nat := 4983230072969 + 3 ^ 40 * 2278520 * 2
def baseEnd_2278520 : Nat := 1169975940882530513721283

theorem tailTrace_2278520 : CollatzResearch.WordTrace tailWord_2278520 prefixEnd_2278520 1169975940882530513721283 := by
  unfold tailWord_2278520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41552225852659327540036507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55402967803545770053382009 41552225852659327540036507)
  ·
    refine ⟨62328338778988991310054761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41552225852659327540036507 62328338778988991310054761)
    ·
      refine ⟨46746254084241743482541071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62328338778988991310054761 46746254084241743482541071)
      ·
        refine ⟨70119381126362615223811607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46746254084241743482541071 70119381126362615223811607)
        ·
          refine ⟨105179071689543922835717411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70119381126362615223811607 105179071689543922835717411)
          ·
            refine ⟨157768607534315884253576117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105179071689543922835717411 157768607534315884253576117)
            ·
              refine ⟨14790806956342114148772761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157768607534315884253576117 14790806956342114148772761)
              ·
                refine ⟨11093105217256585611579571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14790806956342114148772761 11093105217256585611579571)
                ·
                  refine ⟨16639657825884878417369357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11093105217256585611579571 16639657825884878417369357)
                  ·
                    refine ⟨6239871684706829406513509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16639657825884878417369357 6239871684706829406513509)
                    ·
                      refine ⟨1169975940882530513721283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6239871684706829406513509 1169975940882530513721283)
                      ·
                        rfl

theorem cell23_2278520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2278520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278520 prefixEnd_2278520 := by exact prefixLift 2278520
  have htrace : WordTrace (prefixWord ++ tailWord_2278520) baseStart_2278520 baseEnd_2278520 := by
    simpa [prefixWord, tailWord_2278520, baseEnd_2278520] using wordTrace_append hprefix tailTrace_2278520
  have hstable : (prefixWord ++ tailWord_2278520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278520).length < 2 ^ (prefixWord ++ tailWord_2278520).sum := by decide
  have hdescent : baseEnd_2278520 < baseStart_2278520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278554 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2278554 : Nat := 118140960795 + 2278554 * 2 ^ 59
def prefixEnd_2278554 : Nat := 4983230072969 + 3 ^ 40 * 2278554 * 2
def baseEnd_2278554 : Nat := 1169993399224783380696127

theorem tailTrace_2278554 : CollatzResearch.WordTrace tailWord_2278554 prefixEnd_2278554 1169993399224783380696127 := by
  unfold tailWord_2278554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20776422946798869721702679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55403794524796985924540477 20776422946798869721702679)
  ·
    refine ⟨31164634420198304582554019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20776422946798869721702679 31164634420198304582554019)
    ·
      refine ⟨46746951630297456873831029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31164634420198304582554019 46746951630297456873831029)
      ·
        refine ⟨4382526715340386581921659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46746951630297456873831029 4382526715340386581921659)
        ·
          refine ⟨6573790073010579872882489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382526715340386581921659 6573790073010579872882489)
          ·
            refine ⟨4930342554757934904661867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6573790073010579872882489 4930342554757934904661867)
            ·
              refine ⟨7395513832136902356992801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930342554757934904661867 7395513832136902356992801)
              ·
                refine ⟨5546635374102676767744601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395513832136902356992801 5546635374102676767744601)
                ·
                  refine ⟨4159976530577007575808451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546635374102676767744601 4159976530577007575808451)
                  ·
                    refine ⟨6239964795865511363712677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4159976530577007575808451 6239964795865511363712677)
                    ·
                      refine ⟨1169993399224783380696127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6239964795865511363712677 1169993399224783380696127)
                      ·
                        rfl

theorem cell23_2278554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2278554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278554 prefixEnd_2278554 := by exact prefixLift 2278554
  have htrace : WordTrace (prefixWord ++ tailWord_2278554) baseStart_2278554 baseEnd_2278554 := by
    simpa [prefixWord, tailWord_2278554, baseEnd_2278554] using wordTrace_append hprefix tailTrace_2278554
  have hstable : (prefixWord ++ tailWord_2278554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278554).length < 2 ^ (prefixWord ++ tailWord_2278554).sum := by decide
  have hdescent : baseEnd_2278554 < baseStart_2278554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278560 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 8]
def baseStart_2278560 : Nat := 118140960795 + 2278560 * 2 ^ 59
def prefixEnd_2278560 : Nat := 4983230072969 + 3 ^ 40 * 2278560 * 2
def baseEnd_2278560 : Nat := 129999608900967817469011

theorem tailTrace_2278560 : CollatzResearch.WordTrace tailWord_2278560 prefixEnd_2278560 129999608900967817469011 := by
  unfold tailWord_2278560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41552955312586870955764567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55403940416782494607686089 41552955312586870955764567)
  ·
    refine ⟨62329432968880306433646851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41552955312586870955764567 62329432968880306433646851)
    ·
      refine ⟨93494149453320459650470277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62329432968880306433646851 93494149453320459650470277)
      ·
        refine ⟨17530153022497586184463177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93494149453320459650470277 17530153022497586184463177)
        ·
          refine ⟨13147614766873189638347383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17530153022497586184463177 13147614766873189638347383)
          ·
            refine ⟨19721422150309784457521075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13147614766873189638347383 19721422150309784457521075)
            ·
              refine ⟨29582133225464676686281613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19721422150309784457521075 29582133225464676686281613)
              ·
                refine ⟨11093299959549253757355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29582133225464676686281613 11093299959549253757355605)
                ·
                  refine ⟨129999608900967817469011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11093299959549253757355605 129999608900967817469011)
                  ·
                    rfl

theorem cell23_2278560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_2278560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278560 prefixEnd_2278560 := by exact prefixLift 2278560
  have htrace : WordTrace (prefixWord ++ tailWord_2278560) baseStart_2278560 baseEnd_2278560 := by
    simpa [prefixWord, tailWord_2278560, baseEnd_2278560] using wordTrace_append hprefix tailTrace_2278560
  have hstable : (prefixWord ++ tailWord_2278560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278560).length < 2 ^ (prefixWord ++ tailWord_2278560).sum := by decide
  have hdescent : baseEnd_2278560 < baseStart_2278560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278564 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_2278564 : Nat := 118140960795 + 2278564 * 2 ^ 59
def prefixEnd_2278564 : Nat := 4983230072969 + 3 ^ 40 * 2278564 * 2
def baseEnd_2278564 : Nat := 389999511343776113857027

theorem tailTrace_2278564 : CollatzResearch.WordTrace tailWord_2278564 prefixEnd_2278564 389999511343776113857027 := by
  unfold tailWord_2278564
  simp only [CollatzResearch.WordTrace]
  refine ⟨41553028258579625297337373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55404037678106167063116497 41553028258579625297337373)
  ·
    refine ⟨15582385596967359486501515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41553028258579625297337373 15582385596967359486501515)
    ·
      refine ⟨23373578395451039229752273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15582385596967359486501515 23373578395451039229752273)
      ·
        refine ⟨17530183796588279422314205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23373578395451039229752273 17530183796588279422314205)
        ·
          refine ⟨6573818923720604783367827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17530183796588279422314205 6573818923720604783367827)
          ·
            refine ⟨9860728385580907175051741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573818923720604783367827 9860728385580907175051741)
            ·
              refine ⟨3697773144592840190644403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9860728385580907175051741 3697773144592840190644403)
              ·
                refine ⟨5546659716889260285966605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697773144592840190644403 5546659716889260285966605)
                ·
                  refine ⟨2079997393833472607237477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5546659716889260285966605 2079997393833472607237477)
                  ·
                    refine ⟨389999511343776113857027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079997393833472607237477 389999511343776113857027)
                    ·
                      rfl

theorem cell23_2278564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_2278564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278564 prefixEnd_2278564 := by exact prefixLift 2278564
  have htrace : WordTrace (prefixWord ++ tailWord_2278564) baseStart_2278564 baseEnd_2278564 := by
    simpa [prefixWord, tailWord_2278564, baseEnd_2278564] using wordTrace_append hprefix tailTrace_2278564
  have hstable : (prefixWord ++ tailWord_2278564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278564).length < 2 ^ (prefixWord ++ tailWord_2278564).sum := by decide
  have hdescent : baseEnd_2278564 < baseStart_2278564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278654 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2278654 : Nat := 118140960795 + 2278654 * 2 ^ 59
def prefixEnd_2278654 : Nat := 4983230072969 + 3 ^ 40 * 2278654 * 2
def baseEnd_2278654 : Nat := 390014915763410996481889

theorem tailTrace_2278654 : CollatzResearch.WordTrace tailWord_2278654 prefixEnd_2278654 390014915763410996481889 := by
  unfold tailWord_2278654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388667385854149495681377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55406226057888797310300677 10388667385854149495681377)
  ·
    refine ⟨7791500539390612121761033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10388667385854149495681377 7791500539390612121761033)
    ·
      refine ⟨5843625404542959091320775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7791500539390612121761033 5843625404542959091320775)
      ·
        refine ⟨8765438106814438636981163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843625404542959091320775 8765438106814438636981163)
        ·
          refine ⟨13148157160221657955471745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8765438106814438636981163 13148157160221657955471745)
          ·
            refine ⟨9861117870166243466603809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13148157160221657955471745 9861117870166243466603809)
            ·
              refine ⟨7395838402624682599952857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9861117870166243466603809 7395838402624682599952857)
              ·
                refine ⟨5546878801968511949964643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395838402624682599952857 5546878801968511949964643)
                ·
                  refine ⟨8320318202952767924946965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546878801968511949964643 8320318202952767924946965)
                  ·
                    refine ⟨390014915763410996481889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8320318202952767924946965 390014915763410996481889)
                    ·
                      rfl

theorem cell23_2278654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2278654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278654 prefixEnd_2278654 := by exact prefixLift 2278654
  have htrace : WordTrace (prefixWord ++ tailWord_2278654) baseStart_2278654 baseEnd_2278654 := by
    simpa [prefixWord, tailWord_2278654, baseEnd_2278654] using wordTrace_append hprefix tailTrace_2278654
  have hstable : (prefixWord ++ tailWord_2278654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278654).length < 2 ^ (prefixWord ++ tailWord_2278654).sum := by decide
  have hdescent : baseEnd_2278654 < baseStart_2278654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278688 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_2278688 : Nat := 118140960795 + 2278688 * 2 ^ 59
def prefixEnd_2278688 : Nat := 4983230072969 + 3 ^ 40 * 2278688 * 2
def baseEnd_2278688 : Nat := 390020735210828618806837

theorem tailTrace_2278688 : CollatzResearch.WordTrace tailWord_2278688 prefixEnd_2278688 390020735210828618806837 := by
  unfold tailWord_2278688
  simp only [CollatzResearch.WordTrace]
  refine ⟨41555289584355009886094359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55407052779140013181459145 41555289584355009886094359)
  ·
    refine ⟨62332934376532514829141539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41555289584355009886094359 62332934376532514829141539)
    ·
      refine ⟨93499401564798772243712309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62332934376532514829141539 93499401564798772243712309)
      ·
        refine ⟨8765568896699884897848029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93499401564798772243712309 8765568896699884897848029)
        ·
          refine ⟨3287088336262456836693011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8765568896699884897848029 3287088336262456836693011)
          ·
            refine ⟨4930632504393685255039517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287088336262456836693011 4930632504393685255039517)
            ·
              refine ⟨1848987189147631970639819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4930632504393685255039517 1848987189147631970639819)
              ·
                refine ⟨2773480783721447955959729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848987189147631970639819 2773480783721447955959729)
                ·
                  refine ⟨2080110587791085966969797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773480783721447955959729 2080110587791085966969797)
                  ·
                    refine ⟨390020735210828618806837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080110587791085966969797 390020735210828618806837)
                    ·
                      rfl

theorem cell23_2278688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_2278688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278688 prefixEnd_2278688 := by exact prefixLift 2278688
  have htrace : WordTrace (prefixWord ++ tailWord_2278688) baseStart_2278688 baseEnd_2278688 := by
    simpa [prefixWord, tailWord_2278688, baseEnd_2278688] using wordTrace_append hprefix tailTrace_2278688
  have hstable : (prefixWord ++ tailWord_2278688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278688).length < 2 ^ (prefixWord ++ tailWord_2278688).sum := by decide
  have hdescent : baseEnd_2278688 < baseStart_2278688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278698 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2278698 : Nat := 118140960795 + 2278698 * 2 ^ 59
def prefixEnd_2278698 : Nat := 4983230072969 + 3 ^ 40 * 2278698 * 2
def baseEnd_2278698 : Nat := 1170067340439030817295465

theorem tailTrace_2278698 : CollatzResearch.WordTrace tailWord_2278698 prefixEnd_2278698 1170067340439030817295465 := by
  unfold tailWord_2278698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20777735974668447870013187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55407295932449194320035165 20777735974668447870013187)
  ·
    refine ⟨31166603962002671805019781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20777735974668447870013187 31166603962002671805019781)
    ·
      refine ⟨5843738242875500963441209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31166603962002671805019781 5843738242875500963441209)
      ·
        refine ⟨4382803682156625722580907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5843738242875500963441209 4382803682156625722580907)
        ·
          refine ⟨6574205523234938583871361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382803682156625722580907 6574205523234938583871361)
          ·
            refine ⟨4930654142426203937903521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574205523234938583871361 4930654142426203937903521)
            ·
              refine ⟨3697990606819652953427641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930654142426203937903521 3697990606819652953427641)
              ·
                refine ⟨2773492955114739715070731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697990606819652953427641 2773492955114739715070731)
                ·
                  refine ⟨4160239432672109572606097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773492955114739715070731 4160239432672109572606097)
                  ·
                    refine ⟨3120179574504082179454573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4160239432672109572606097 3120179574504082179454573)
                    ·
                      refine ⟨1170067340439030817295465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3120179574504082179454573 1170067340439030817295465)
                      ·
                        rfl

theorem cell23_2278698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2278698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278698 prefixEnd_2278698 := by exact prefixLift 2278698
  have htrace : WordTrace (prefixWord ++ tailWord_2278698) baseStart_2278698 baseEnd_2278698 := by
    simpa [prefixWord, tailWord_2278698, baseEnd_2278698] using wordTrace_append hprefix tailTrace_2278698
  have hstable : (prefixWord ++ tailWord_2278698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278698).length < 2 ^ (prefixWord ++ tailWord_2278698).sum := by decide
  have hdescent : baseEnd_2278698 < baseStart_2278698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278701 : List Nat := [1, 5, 3, 1, 1, 1, 4, 7]
def baseStart_2278701 : Nat := 118140960795 + 2278701 * 2 ^ 59
def prefixEnd_2278701 : Nat := 4983230072969 + 3 ^ 40 * 2278701 * 2
def baseEnd_2278701 : Nat := 43335884477073863168813

theorem tailTrace_2278701 : CollatzResearch.WordTrace tailWord_2278701 prefixEnd_2278701 43335884477073863168813 := by
  unfold tailWord_2278701
  simp only [CollatzResearch.WordTrace]
  refine ⟨83111053317662922992411957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55407368878441948661607971 83111053317662922992411957)
  ·
    refine ⟨7791661248530899030538621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83111053317662922992411957 7791661248530899030538621)
    ·
      refine ⟨2921872968199087136451983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7791661248530899030538621 2921872968199087136451983)
      ·
        refine ⟨4382809452298630704677975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921872968199087136451983 4382809452298630704677975)
        ·
          refine ⟨6574214178447946057016963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382809452298630704677975 6574214178447946057016963)
          ·
            refine ⟨9861321267671919085525445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6574214178447946057016963 9861321267671919085525445)
            ·
              refine ⟨1848997737688484828536021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9861321267671919085525445 1848997737688484828536021)
              ·
                refine ⟨43335884477073863168813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1848997737688484828536021 43335884477073863168813)
                ·
                  rfl

theorem cell23_2278701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 7].length) (baseStart_2278701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278701 prefixEnd_2278701 := by exact prefixLift 2278701
  have htrace : WordTrace (prefixWord ++ tailWord_2278701) baseStart_2278701 baseEnd_2278701 := by
    simpa [prefixWord, tailWord_2278701, baseEnd_2278701] using wordTrace_append hprefix tailTrace_2278701
  have hstable : (prefixWord ++ tailWord_2278701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278701).length < 2 ^ (prefixWord ++ tailWord_2278701).sum := by decide
  have hdescent : baseEnd_2278701 < baseStart_2278701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278707 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_2278707 : Nat := 118140960795 + 2278707 * 2 ^ 59
def prefixEnd_2278707 : Nat := 4983230072969 + 3 ^ 40 * 2278707 * 2
def baseEnd_2278707 : Nat := 1170071961764921282082923

theorem tailTrace_2278707 : CollatzResearch.WordTrace tailWord_2278707 prefixEnd_2278707 1170071961764921282082923 := by
  unfold tailWord_2278707
  simp only [CollatzResearch.WordTrace]
  refine ⟨83111272155641186017130375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55407514770427457344753583 83111272155641186017130375)
  ·
    refine ⟨124666908233461779025695563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83111272155641186017130375 124666908233461779025695563)
    ·
      refine ⟨187000362350192668538543345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124666908233461779025695563 187000362350192668538543345)
      ·
        refine ⟨140250271762644501403907509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187000362350192668538543345 140250271762644501403907509)
        ·
          refine ⟨13148462977747922006616329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140250271762644501403907509 13148462977747922006616329)
          ·
            refine ⟨9861347233310941504962247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13148462977747922006616329 9861347233310941504962247)
            ·
              refine ⟨14792020849966412257443371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9861347233310941504962247 14792020849966412257443371)
              ·
                refine ⟨22188031274949618386165057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14792020849966412257443371 22188031274949618386165057)
                ·
                  refine ⟨16641023456212213789623793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22188031274949618386165057 16641023456212213789623793)
                  ·
                    refine ⟨12480767592159160342217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16641023456212213789623793 12480767592159160342217845)
                    ·
                      refine ⟨1170071961764921282082923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12480767592159160342217845 1170071961764921282082923)
                      ·
                        rfl

theorem cell23_2278707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_2278707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278707 prefixEnd_2278707 := by exact prefixLift 2278707
  have htrace : WordTrace (prefixWord ++ tailWord_2278707) baseStart_2278707 baseEnd_2278707 := by
    simpa [prefixWord, tailWord_2278707, baseEnd_2278707] using wordTrace_append hprefix tailTrace_2278707
  have hstable : (prefixWord ++ tailWord_2278707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278707).length < 2 ^ (prefixWord ++ tailWord_2278707).sum := by decide
  have hdescent : baseEnd_2278707 < baseStart_2278707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278737 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2278737 : Nat := 118140960795 + 2278737 * 2 ^ 59
def prefixEnd_2278737 : Nat := 4983230072969 + 3 ^ 40 * 2278737 * 2
def baseEnd_2278737 : Nat := 1170087366184556164707785

theorem tailTrace_2278737 : CollatzResearch.WordTrace tailWord_2278737 prefixEnd_2278737 1170087366184556164707785 := by
  unfold tailWord_2278737
  simp only [CollatzResearch.WordTrace]
  refine ⟨83112366345532501140722465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55408244230355000760481643 83112366345532501140722465)
  ·
    refine ⟨62334274759149375855541849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83112366345532501140722465 62334274759149375855541849)
    ·
      refine ⟨46750706069362031891656387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62334274759149375855541849 46750706069362031891656387)
      ·
        refine ⟨70126059104043047837484581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46750706069362031891656387 70126059104043047837484581)
        ·
          refine ⟨13148636082008071469528359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70126059104043047837484581 13148636082008071469528359)
          ·
            refine ⟨19722954123012107204292539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13148636082008071469528359 19722954123012107204292539)
            ·
              refine ⟨29584431184518160806438809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19722954123012107204292539 29584431184518160806438809)
              ·
                refine ⟨22188323388388620604829107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29584431184518160806438809 22188323388388620604829107)
                ·
                  refine ⟨33282485082582930907243661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22188323388388620604829107 33282485082582930907243661)
                  ·
                    refine ⟨12480931905968599090216373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33282485082582930907243661 12480931905968599090216373)
                    ·
                      refine ⟨1170087366184556164707785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12480931905968599090216373 1170087366184556164707785)
                      ·
                        rfl

theorem cell23_2278737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2278737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278737 prefixEnd_2278737 := by exact prefixLift 2278737
  have htrace : WordTrace (prefixWord ++ tailWord_2278737) baseStart_2278737 baseEnd_2278737 := by
    simpa [prefixWord, tailWord_2278737, baseEnd_2278737] using wordTrace_append hprefix tailTrace_2278737
  have hstable : (prefixWord ++ tailWord_2278737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278737).length < 2 ^ (prefixWord ++ tailWord_2278737).sum := by decide
  have hdescent : baseEnd_2278737 < baseStart_2278737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278749 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2278749 : Nat := 118140960795 + 2278749 * 2 ^ 59
def prefixEnd_2278749 : Nat := 4983230072969 + 3 ^ 40 * 2278749 * 2
def baseEnd_2278749 : Nat := 1170093527952410117757731

theorem tailTrace_2278749 : CollatzResearch.WordTrace tailWord_2278749 prefixEnd_2278749 1170093527952410117757731 := by
  unfold tailWord_2278749
  simp only [CollatzResearch.WordTrace]
  refine ⟨83112804021489027190159301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55408536014326018126772867 83112804021489027190159301)
  ·
    refine ⟨15583650754029192598154869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83112804021489027190159301 15583650754029192598154869)
    ·
      refine ⟨1460967258190236806077019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15583650754029192598154869 1460967258190236806077019)
      ·
        refine ⟨2191450887285355209115529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460967258190236806077019 2191450887285355209115529)
        ·
          refine ⟨1643588165464016406836647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2191450887285355209115529 1643588165464016406836647)
          ·
            refine ⟨2465382248196024610254971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643588165464016406836647 2465382248196024610254971)
            ·
              refine ⟨3698073372294036915382457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465382248196024610254971 3698073372294036915382457)
              ·
                refine ⟨2773555029220527686536843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3698073372294036915382457 2773555029220527686536843)
                ·
                  refine ⟨4160332543830791529805265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773555029220527686536843 4160332543830791529805265)
                  ·
                    refine ⟨3120249407873093647353949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4160332543830791529805265 3120249407873093647353949)
                    ·
                      refine ⟨1170093527952410117757731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3120249407873093647353949 1170093527952410117757731)
                      ·
                        rfl

theorem cell23_2278749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2278749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278749 prefixEnd_2278749 := by exact prefixLift 2278749
  have htrace : WordTrace (prefixWord ++ tailWord_2278749) baseStart_2278749 baseEnd_2278749 := by
    simpa [prefixWord, tailWord_2278749, baseEnd_2278749] using wordTrace_append hprefix tailTrace_2278749
  have hstable : (prefixWord ++ tailWord_2278749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278749).length < 2 ^ (prefixWord ++ tailWord_2278749).sum := by decide
  have hdescent : baseEnd_2278749 < baseStart_2278749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278754 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2278754 : Nat := 118140960795 + 2278754 * 2 ^ 59
def prefixEnd_2278754 : Nat := 4983230072969 + 3 ^ 40 * 2278754 * 2
def baseEnd_2278754 : Nat := 1170096095355682598195207

theorem tailTrace_2278754 : CollatzResearch.WordTrace tailWord_2278754 prefixEnd_2278754 1170096095355682598195207 := by
  unfold tailWord_2278754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20778246596617728261022829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55408657590980608696060877 20778246596617728261022829)
  ·
    refine ⟨7791842473731648097883561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20778246596617728261022829 7791842473731648097883561)
    ·
      refine ⟨5843881855298736073412671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7791842473731648097883561 5843881855298736073412671)
      ·
        refine ⟨8765822782948104110119007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843881855298736073412671 8765822782948104110119007)
        ·
          refine ⟨13148734174422156165178511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8765822782948104110119007 13148734174422156165178511)
          ·
            refine ⟨19723101261633234247767767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13148734174422156165178511 19723101261633234247767767)
            ·
              refine ⟨29584651892449851371651651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19723101261633234247767767 29584651892449851371651651)
              ·
                refine ⟨44376977838674777057477477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29584651892449851371651651 44376977838674777057477477)
                ·
                  refine ⟨8320683344751520698277027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44376977838674777057477477 8320683344751520698277027)
                  ·
                    refine ⟨12481025017127281047415541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8320683344751520698277027 12481025017127281047415541)
                    ·
                      refine ⟨1170096095355682598195207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12481025017127281047415541 1170096095355682598195207)
                      ·
                        rfl

theorem cell23_2278754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2278754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278754 prefixEnd_2278754 := by exact prefixLift 2278754
  have htrace : WordTrace (prefixWord ++ tailWord_2278754) baseStart_2278754 baseEnd_2278754 := by
    simpa [prefixWord, tailWord_2278754, baseEnd_2278754] using wordTrace_append hprefix tailTrace_2278754
  have hstable : (prefixWord ++ tailWord_2278754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278754).length < 2 ^ (prefixWord ++ tailWord_2278754).sum := by decide
  have hdescent : baseEnd_2278754 < baseStart_2278754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278757 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 9]
def baseStart_2278757 : Nat := 118140960795 + 2278757 * 2 ^ 59
def prefixEnd_2278757 : Nat := 4983230072969 + 3 ^ 40 * 2278757 * 2
def baseEnd_2278757 : Nat := 130010848421960676273077

theorem tailTrace_2278757 : CollatzResearch.WordTrace tailWord_2278757 prefixEnd_2278757 130010848421960676273077 := by
  unfold tailWord_2278757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83113095805460044556450525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55408730536973363037633683 83113095805460044556450525)
  ·
    refine ⟨31167410927047516708668947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83113095805460044556450525 31167410927047516708668947)
    ·
      refine ⟨46751116390571275063003421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31167410927047516708668947 46751116390571275063003421)
      ·
        refine ⟨17531668646464228148626283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46751116390571275063003421 17531668646464228148626283)
        ·
          refine ⟨26297502969696342222939425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17531668646464228148626283 26297502969696342222939425)
          ·
            refine ⟨19723127227272256667204569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26297502969696342222939425 19723127227272256667204569)
            ·
              refine ⟨14792345420454192500403427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19723127227272256667204569 14792345420454192500403427)
              ·
                refine ⟨22188518130681288750605141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14792345420454192500403427 22188518130681288750605141)
                ·
                  refine ⟨130010848421960676273077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22188518130681288750605141 130010848421960676273077)
                  ·
                    rfl

theorem cell23_2278757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_2278757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278757 prefixEnd_2278757 := by exact prefixLift 2278757
  have htrace : WordTrace (prefixWord ++ tailWord_2278757) baseStart_2278757 baseEnd_2278757 := by
    simpa [prefixWord, tailWord_2278757, baseEnd_2278757] using wordTrace_append hprefix tailTrace_2278757
  have hstable : (prefixWord ++ tailWord_2278757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278757).length < 2 ^ (prefixWord ++ tailWord_2278757).sum := by decide
  have hdescent : baseEnd_2278757 < baseStart_2278757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278791 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 5]
def baseStart_2278791 : Nat := 118140960795 + 2278791 * 2 ^ 59
def prefixEnd_2278791 : Nat := 4983230072969 + 3 ^ 40 * 2278791 * 2
def baseEnd_2278791 : Nat := 130012788237766550381393

theorem tailTrace_2278791 : CollatzResearch.WordTrace tailWord_2278791 prefixEnd_2278791 130012788237766550381393 := by
  unfold tailWord_2278791
  simp only [CollatzResearch.WordTrace]
  refine ⟨83114335887336868363188227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55409557258224578908792151 83114335887336868363188227)
  ·
    refine ⟨124671503831005302544782341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83114335887336868363188227 124671503831005302544782341)
    ·
      refine ⟨23375906968313494227146689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124671503831005302544782341 23375906968313494227146689)
      ·
        refine ⟨17531930226235120670360017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23375906968313494227146689 17531930226235120670360017)
        ·
          refine ⟨13148947669676340502770013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17531930226235120670360017 13148947669676340502770013)
          ·
            refine ⟨4930855376128627688538755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13148947669676340502770013 4930855376128627688538755)
            ·
              refine ⟨7396283064192941532808133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930855376128627688538755 7396283064192941532808133)
              ·
                refine ⟨1386803074536176537401525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7396283064192941532808133 1386803074536176537401525)
                ·
                  refine ⟨130012788237766550381393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386803074536176537401525 130012788237766550381393)
                  ·
                    rfl

theorem cell23_2278791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 5].length) (baseStart_2278791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278791 prefixEnd_2278791 := by exact prefixLift 2278791
  have htrace : WordTrace (prefixWord ++ tailWord_2278791) baseStart_2278791 baseEnd_2278791 := by
    simpa [prefixWord, tailWord_2278791, baseEnd_2278791] using wordTrace_append hprefix tailTrace_2278791
  have hstable : (prefixWord ++ tailWord_2278791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278791).length < 2 ^ (prefixWord ++ tailWord_2278791).sum := by decide
  have hdescent : baseEnd_2278791 < baseStart_2278791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278827 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_2278827 : Nat := 118140960795 + 2278827 * 2 ^ 59
def prefixEnd_2278827 : Nat := 4983230072969 + 3 ^ 40 * 2278827 * 2
def baseEnd_2278827 : Nat := 1170133579443460812582371

theorem tailTrace_2278827 : CollatzResearch.WordTrace tailWord_2278827 prefixEnd_2278827 1170133579443460812582371 := by
  unfold tailWord_2278827
  simp only [CollatzResearch.WordTrace]
  refine ⟨83115648915206446511498735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55410432610137631007665823 83115648915206446511498735)
  ·
    refine ⟨124673473372809669767248103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83115648915206446511498735 124673473372809669767248103)
    ·
      refine ⟨187010210059214504650872155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124673473372809669767248103 187010210059214504650872155)
      ·
        refine ⟨280515315088821756976308233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187010210059214504650872155 280515315088821756976308233)
        ·
          refine ⟨210386486316616317732231175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280515315088821756976308233 210386486316616317732231175)
          ·
            refine ⟨315579729474924476598346763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210386486316616317732231175 315579729474924476598346763)
            ·
              refine ⟨473369594212386714897520145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315579729474924476598346763 473369594212386714897520145)
              ·
                refine ⟨355027195659290036173140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473369594212386714897520145 355027195659290036173140109)
                ·
                  refine ⟨133135198372233763564927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355027195659290036173140109 133135198372233763564927541)
                  ·
                    refine ⟨12481424847396915334211957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133135198372233763564927541 12481424847396915334211957)
                    ·
                      refine ⟨1170133579443460812582371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12481424847396915334211957 1170133579443460812582371)
                      ·
                        rfl

theorem cell23_2278827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_2278827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278827 prefixEnd_2278827 := by exact prefixLift 2278827
  have htrace : WordTrace (prefixWord ++ tailWord_2278827) baseStart_2278827 baseEnd_2278827 := by
    simpa [prefixWord, tailWord_2278827, baseEnd_2278827] using wordTrace_append hprefix tailTrace_2278827
  have hstable : (prefixWord ++ tailWord_2278827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278827).length < 2 ^ (prefixWord ++ tailWord_2278827).sum := by decide
  have hdescent : baseEnd_2278827 < baseStart_2278827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278885 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_2278885 : Nat := 118140960795 + 2278885 * 2 ^ 59
def prefixEnd_2278885 : Nat := 4983230072969 + 3 ^ 40 * 2278885 * 2
def baseEnd_2278885 : Nat := 390054453773807195219035

theorem tailTrace_2278885 : CollatzResearch.WordTrace tailWord_2278885 prefixEnd_2278885 390054453773807195219035 := by
  unfold tailWord_2278885
  simp only [CollatzResearch.WordTrace]
  refine ⟨83117764348996322417110109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55411842899330881611406739 83117764348996322417110109)
  ·
    refine ⟨31169161630873620906416291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83117764348996322417110109 31169161630873620906416291)
    ·
      refine ⟨46753742446310431359624437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31169161630873620906416291 46753742446310431359624437)
      ·
        refine ⟨4383163354341602939964791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46753742446310431359624437 4383163354341602939964791)
        ·
          refine ⟨6574745031512404409947187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4383163354341602939964791 6574745031512404409947187)
          ·
            refine ⟨9862117547268606614920781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6574745031512404409947187 9862117547268606614920781)
            ·
              refine ⟨3698294080225727480595293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9862117547268606614920781 3698294080225727480595293)
              ·
                refine ⟨1386860280084647805223235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3698294080225727480595293 1386860280084647805223235)
                ·
                  refine ⟨2080290420126971707834853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386860280084647805223235 2080290420126971707834853)
                  ·
                    refine ⟨390054453773807195219035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080290420126971707834853 390054453773807195219035)
                    ·
                      rfl

theorem cell23_2278885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_2278885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278885 prefixEnd_2278885 := by exact prefixLift 2278885
  have htrace : WordTrace (prefixWord ++ tailWord_2278885) baseStart_2278885 baseEnd_2278885 := by
    simpa [prefixWord, tailWord_2278885, baseEnd_2278885] using wordTrace_append hprefix tailTrace_2278885
  have hstable : (prefixWord ++ tailWord_2278885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278885).length < 2 ^ (prefixWord ++ tailWord_2278885).sum := by decide
  have hdescent : baseEnd_2278885 < baseStart_2278885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278902 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2278902 : Nat := 118140960795 + 2278902 * 2 ^ 59
def prefixEnd_2278902 : Nat := 4983230072969 + 3 ^ 40 * 2278902 * 2
def baseEnd_2278902 : Nat := 390057363497516006381509

theorem tailTrace_2278902 : CollatzResearch.WordTrace tailWord_2278902 prefixEnd_2278902 390057363497516006381509 := by
  unfold tailWord_2278902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194899024370920895029935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55412256259956489546985973 5194899024370920895029935)
  ·
    refine ⟨7792348536556381342544903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5194899024370920895029935 7792348536556381342544903)
    ·
      refine ⟨11688522804834572013817355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792348536556381342544903 11688522804834572013817355)
      ·
        refine ⟨17532784207251858020726033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11688522804834572013817355 17532784207251858020726033)
        ·
          refine ⟨13149588155438893515544525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17532784207251858020726033 13149588155438893515544525)
          ·
            refine ⟨4931095558289585068329197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13149588155438893515544525 4931095558289585068329197)
            ·
              refine ⟨1849160834358594400623449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931095558289585068329197 1849160834358594400623449)
              ·
                refine ⟨1386870625768945800467587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849160834358594400623449 1386870625768945800467587)
                ·
                  refine ⟨2080305938653418700701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386870625768945800467587 2080305938653418700701381)
                  ·
                    refine ⟨390057363497516006381509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080305938653418700701381 390057363497516006381509)
                    ·
                      rfl

theorem cell23_2278902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2278902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278902 prefixEnd_2278902 := by exact prefixLift 2278902
  have htrace : WordTrace (prefixWord ++ tailWord_2278902) baseStart_2278902 baseEnd_2278902 := by
    simpa [prefixWord, tailWord_2278902, baseEnd_2278902] using wordTrace_append hprefix tailTrace_2278902
  have hstable : (prefixWord ++ tailWord_2278902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278902).length < 2 ^ (prefixWord ++ tailWord_2278902).sum := by decide
  have hdescent : baseEnd_2278902 < baseStart_2278902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278908 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_2278908 : Nat := 118140960795 + 2278908 * 2 ^ 59
def prefixEnd_2278908 : Nat := 4983230072969 + 3 ^ 40 * 2278908 * 2
def baseEnd_2278908 : Nat := 1170175171376474995669499

theorem tailTrace_2278908 : CollatzResearch.WordTrace tailWord_2278908 prefixEnd_2278908 1170175171376474995669499 := by
  unfold tailWord_2278908
  simp only [CollatzResearch.WordTrace]
  refine ⟨41559301613956498672598689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55412402151941998230131585 41559301613956498672598689)
  ·
    refine ⟨31169476210467374004449017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41559301613956498672598689 31169476210467374004449017)
    ·
      refine ⟨23377107157850530503336763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31169476210467374004449017 23377107157850530503336763)
      ·
        refine ⟨35065660736775795755005145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23377107157850530503336763 35065660736775795755005145)
        ·
          refine ⟨26299245552581846816253859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35065660736775795755005145 26299245552581846816253859)
          ·
            refine ⟨39448868328872770224380789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26299245552581846816253859 39448868328872770224380789)
            ·
              refine ⟨3698331405831822208535699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39448868328872770224380789 3698331405831822208535699)
              ·
                refine ⟨5547497108747733312803549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698331405831822208535699 5547497108747733312803549)
                ·
                  refine ⟨2080311415780399992301331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5547497108747733312803549 2080311415780399992301331)
                  ·
                    refine ⟨3120467123670599988451997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080311415780399992301331 3120467123670599988451997)
                    ·
                      refine ⟨1170175171376474995669499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3120467123670599988451997 1170175171376474995669499)
                      ·
                        rfl

theorem cell23_2278908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_2278908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278908 prefixEnd_2278908 := by exact prefixLift 2278908
  have htrace : WordTrace (prefixWord ++ tailWord_2278908) baseStart_2278908 baseEnd_2278908 := by
    simpa [prefixWord, tailWord_2278908, baseEnd_2278908] using wordTrace_append hprefix tailTrace_2278908
  have hstable : (prefixWord ++ tailWord_2278908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278908).length < 2 ^ (prefixWord ++ tailWord_2278908).sum := by decide
  have hdescent : baseEnd_2278908 < baseStart_2278908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278931 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4]
def baseStart_2278931 : Nat := 118140960795 + 2278931 * 2 ^ 59
def prefixEnd_2278931 : Nat := 4983230072969 + 3 ^ 40 * 2278931 * 2
def baseEnd_2278931 : Nat := 1170186981431528405681893

theorem tailTrace_2278931 : CollatzResearch.WordTrace tailWord_2278931 prefixEnd_2278931 1170186981431528405681893 := by
  unfold tailWord_2278931
  simp only [CollatzResearch.WordTrace]
  refine ⟨83119442106829672273284647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55412961404553114848856431 83119442106829672273284647)
  ·
    refine ⟨124679163160244508409926971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83119442106829672273284647 124679163160244508409926971)
    ·
      refine ⟨187018744740366762614890457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124679163160244508409926971 187018744740366762614890457)
      ·
        refine ⟨140264058555275071961167843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187018744740366762614890457 140264058555275071961167843)
        ·
          refine ⟨210396087832912607941751765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140264058555275071961167843 210396087832912607941751765)
          ·
            refine ⟨4931158308583889248634807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 210396087832912607941751765 4931158308583889248634807)
            ·
              refine ⟨7396737462875833872952211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931158308583889248634807 7396737462875833872952211)
              ·
                refine ⟨11095106194313750809428317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396737462875833872952211 11095106194313750809428317)
                ·
                  refine ⟨4160664822867656553535619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11095106194313750809428317 4160664822867656553535619)
                  ·
                    refine ⟨6240997234301484830303429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4160664822867656553535619 6240997234301484830303429)
                    ·
                      refine ⟨1170186981431528405681893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6240997234301484830303429 1170186981431528405681893)
                      ·
                        rfl

theorem cell23_2278931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_2278931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278931 prefixEnd_2278931 := by exact prefixLift 2278931
  have htrace : WordTrace (prefixWord ++ tailWord_2278931) baseStart_2278931 baseEnd_2278931 := by
    simpa [prefixWord, tailWord_2278931, baseEnd_2278931] using wordTrace_append hprefix tailTrace_2278931
  have hstable : (prefixWord ++ tailWord_2278931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278931).length < 2 ^ (prefixWord ++ tailWord_2278931).sum := by decide
  have hdescent : baseEnd_2278931 < baseStart_2278931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278941 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2278941 : Nat := 118140960795 + 2278941 * 2 ^ 59
def prefixEnd_2278941 : Nat := 4983230072969 + 3 ^ 40 * 2278941 * 2
def baseEnd_2278941 : Nat := 390064038746024455518949

theorem tailTrace_2278941 : CollatzResearch.WordTrace tailWord_2278941 prefixEnd_2278941 390064038746024455518949 := by
  unfold tailWord_2278941
  simp only [CollatzResearch.WordTrace]
  refine ⟨83119806836793443981148677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55413204557862295987432451 83119806836793443981148677)
  ·
    refine ⟨15584963781898770746465377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83119806836793443981148677 15584963781898770746465377)
    ·
      refine ⟨11688722836424078059849033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15584963781898770746465377 11688722836424078059849033)
      ·
        refine ⟨8766542127318058544886775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11688722836424078059849033 8766542127318058544886775)
        ·
          refine ⟨13149813190977087817330163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8766542127318058544886775 13149813190977087817330163)
          ·
            refine ⟨19724719786465631725995245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13149813190977087817330163 19724719786465631725995245)
            ·
              refine ⟨7396769919924611897248217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19724719786465631725995245 7396769919924611897248217)
              ·
                refine ⟨5547577439943458922936163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7396769919924611897248217 5547577439943458922936163)
                ·
                  refine ⟨8321366159915188384404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5547577439943458922936163 8321366159915188384404245)
                  ·
                    refine ⟨390064038746024455518949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8321366159915188384404245 390064038746024455518949)
                    ·
                      rfl

theorem cell23_2278941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2278941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2278941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2278941 prefixEnd_2278941 := by exact prefixLift 2278941
  have htrace : WordTrace (prefixWord ++ tailWord_2278941) baseStart_2278941 baseEnd_2278941 := by
    simpa [prefixWord, tailWord_2278941, baseEnd_2278941] using wordTrace_append hprefix tailTrace_2278941
  have hstable : (prefixWord ++ tailWord_2278941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278941).length < 2 ^ (prefixWord ++ tailWord_2278941).sum := by decide
  have hdescent : baseEnd_2278941 < baseStart_2278941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279015 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2279015 : Nat := 118140960795 + 2279015 * 2 ^ 59
def prefixEnd_2279015 : Nat := 4983230072969 + 3 ^ 40 * 2279015 * 2
def baseEnd_2279015 : Nat := 1170230113806506077031507

theorem tailTrace_2279015 : CollatzResearch.WordTrace tailWord_2279015 prefixEnd_2279015 1170230113806506077031507 := by
  unfold tailWord_2279015
  simp only [CollatzResearch.WordTrace]
  refine ⟨83122505838525354619342499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55415003892350236412894999 83122505838525354619342499)
  ·
    refine ⟨124683758757788031929013749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83122505838525354619342499 124683758757788031929013749)
    ·
      refine ⟨11689102383542627993345039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124683758757788031929013749 11689102383542627993345039)
      ·
        refine ⟨17533653575313941990017559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11689102383542627993345039 17533653575313941990017559)
        ·
          refine ⟨26300480362970912985026339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533653575313941990017559 26300480362970912985026339)
          ·
            refine ⟨39450720544456369477539509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26300480362970912985026339 39450720544456369477539509)
            ·
              refine ⟨3698505051042784638519329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39450720544456369477539509 3698505051042784638519329)
              ·
                refine ⟨2773878788282088478889497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3698505051042784638519329 2773878788282088478889497)
                ·
                  refine ⟨2080409091211566359167123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773878788282088478889497 2080409091211566359167123)
                  ·
                    refine ⟨3120613636817349538750685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080409091211566359167123 3120613636817349538750685)
                    ·
                      refine ⟨1170230113806506077031507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3120613636817349538750685 1170230113806506077031507)
                      ·
                        rfl

theorem cell23_2279015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2279015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279015 prefixEnd_2279015 := by exact prefixLift 2279015
  have htrace : WordTrace (prefixWord ++ tailWord_2279015) baseStart_2279015 baseEnd_2279015 := by
    simpa [prefixWord, tailWord_2279015, baseEnd_2279015] using wordTrace_append hprefix tailTrace_2279015
  have hstable : (prefixWord ++ tailWord_2279015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279015).length < 2 ^ (prefixWord ++ tailWord_2279015).sum := by decide
  have hdescent : baseEnd_2279015 < baseStart_2279015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279091 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 4, 5]
def baseStart_2279091 : Nat := 118140960795 + 2279091 * 2 ^ 59
def prefixEnd_2279091 : Nat := 4983230072969 + 3 ^ 40 * 2279091 * 2
def baseEnd_2279091 : Nat := 390089712778749259893719

theorem tailTrace_2279091 : CollatzResearch.WordTrace tailWord_2279091 prefixEnd_2279091 390089712778749259893719 := by
  unfold tailWord_2279091
  simp only [CollatzResearch.WordTrace]
  refine ⟨83125277786250019599109127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55416851857500013066072751 83125277786250019599109127)
  ·
    refine ⟨124687916679375029398663691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83125277786250019599109127 124687916679375029398663691)
    ·
      refine ⟨187031875019062544097995537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124687916679375029398663691 187031875019062544097995537)
      ·
        refine ⟨140273906264296908073496653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187031875019062544097995537 140273906264296908073496653)
        ·
          refine ⟨52602714849111340527561245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140273906264296908073496653 52602714849111340527561245)
          ·
            refine ⟨19726018068416752697835467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52602714849111340527561245 19726018068416752697835467)
            ·
              refine ⟨29589027102625129046753201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19726018068416752697835467 29589027102625129046753201)
              ·
                refine ⟨22191770326968846785064901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29589027102625129046753201 22191770326968846785064901)
                ·
                  refine ⟨4160956936306658772199669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22191770326968846785064901 4160956936306658772199669)
                  ·
                    refine ⟨390089712778749259893719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4160956936306658772199669 390089712778749259893719)
                    ·
                      rfl

theorem cell23_2279091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].length) (baseStart_2279091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279091 prefixEnd_2279091 := by exact prefixLift 2279091
  have htrace : WordTrace (prefixWord ++ tailWord_2279091) baseStart_2279091 baseEnd_2279091 := by
    simpa [prefixWord, tailWord_2279091, baseEnd_2279091] using wordTrace_append hprefix tailTrace_2279091
  have hstable : (prefixWord ++ tailWord_2279091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279091).length < 2 ^ (prefixWord ++ tailWord_2279091).sum := by decide
  have hdescent : baseEnd_2279091 < baseStart_2279091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279101 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2279101 : Nat := 118140960795 + 2279101 * 2 ^ 59
def prefixEnd_2279101 : Nat := 4983230072969 + 3 ^ 40 * 2279101 * 2
def baseEnd_2279101 : Nat := 1170274273142792740556111

theorem tailTrace_2279101 : CollatzResearch.WordTrace tailWord_2279101 prefixEnd_2279101 1170274273142792740556111 := by
  unfold tailWord_2279101
  simp only [CollatzResearch.WordTrace]
  refine ⟨83125642516213791306973157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55417095010809194204648771 83125642516213791306973157)
  ·
    refine ⟨15586057971790085870057467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83125642516213791306973157 15586057971790085870057467)
    ·
      refine ⟨23379086957685128805086201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15586057971790085870057467 23379086957685128805086201)
      ·
        refine ⟨17534315218263846603814651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23379086957685128805086201 17534315218263846603814651)
        ·
          refine ⟨26301472827395769905721977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17534315218263846603814651 26301472827395769905721977)
          ·
            refine ⟨19726104620546827429291483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26301472827395769905721977 19726104620546827429291483)
            ·
              refine ⟨29589156930820241143937225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19726104620546827429291483 29589156930820241143937225)
              ·
                refine ⟨22191867698115180857952919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29589156930820241143937225 22191867698115180857952919)
                ·
                  refine ⟨33287801547172771286929379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22191867698115180857952919 33287801547172771286929379)
                  ·
                    refine ⟨49931702320759156930394069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33287801547172771286929379 49931702320759156930394069)
                    ·
                      refine ⟨1170274273142792740556111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49931702320759156930394069 1170274273142792740556111)
                      ·
                        rfl

theorem cell23_2279101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2279101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279101 prefixEnd_2279101 := by exact prefixLift 2279101
  have htrace : WordTrace (prefixWord ++ tailWord_2279101) baseStart_2279101 baseEnd_2279101 := by
    simpa [prefixWord, tailWord_2279101, baseEnd_2279101] using wordTrace_append hprefix tailTrace_2279101
  have hstable : (prefixWord ++ tailWord_2279101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279101).length < 2 ^ (prefixWord ++ tailWord_2279101).sum := by decide
  have hdescent : baseEnd_2279101 < baseStart_2279101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279106 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2279106 : Nat := 118140960795 + 2279106 * 2 ^ 59
def prefixEnd_2279106 : Nat := 4983230072969 + 3 ^ 40 * 2279106 * 2
def baseEnd_2279106 : Nat := 1170276840546065220993589

theorem tailTrace_2279106 : CollatzResearch.WordTrace tailWord_2279106 prefixEnd_2279106 1170276840546065220993589 := by
  unfold tailWord_2279106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781456220298919290226293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55417216587463784773936781 20781456220298919290226293)
  ·
    refine ⟨1948261520653023683458715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20781456220298919290226293 1948261520653023683458715)
    ·
      refine ⟨2922392280979535525188073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1948261520653023683458715 2922392280979535525188073)
      ·
        refine ⟨2191794210734651643891055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2922392280979535525188073 2191794210734651643891055)
        ·
          refine ⟨3287691316101977465836583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191794210734651643891055 3287691316101977465836583)
          ·
            refine ⟨4931536974152966198754875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287691316101977465836583 4931536974152966198754875)
            ·
              refine ⟨7397305461229449298132313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931536974152966198754875 7397305461229449298132313)
              ·
                refine ⟨5547979095922086973599235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7397305461229449298132313 5547979095922086973599235)
                ·
                  refine ⟨8321968643883130460398853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5547979095922086973599235 8321968643883130460398853)
                  ·
                    refine ⟨1560369120728086961324785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8321968643883130460398853 1560369120728086961324785)
                    ·
                      refine ⟨1170276840546065220993589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560369120728086961324785 1170276840546065220993589)
                      ·
                        rfl

theorem cell23_2279106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2279106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279106 prefixEnd_2279106 := by exact prefixLift 2279106
  have htrace : WordTrace (prefixWord ++ tailWord_2279106) baseStart_2279106 baseEnd_2279106 := by
    simpa [prefixWord, tailWord_2279106, baseEnd_2279106] using wordTrace_append hprefix tailTrace_2279106
  have hstable : (prefixWord ++ tailWord_2279106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279106).length < 2 ^ (prefixWord ++ tailWord_2279106).sum := by decide
  have hdescent : baseEnd_2279106 < baseStart_2279106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279128 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2279128 : Nat := 118140960795 + 2279128 * 2 ^ 59
def prefixEnd_2279128 : Nat := 4983230072969 + 3 ^ 40 * 2279128 * 2
def baseEnd_2279128 : Nat := 1170288137120464134918487

theorem tailTrace_2279128 : CollatzResearch.WordTrace tailWord_2279128 prefixEnd_2279128 1170288137120464134918487 := by
  unfold tailWord_2279128
  simp only [CollatzResearch.WordTrace]
  refine ⟨41563313643557987459103019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55417751524743983278804025 41563313643557987459103019)
  ·
    refine ⟨62344970465336981188654529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41563313643557987459103019 62344970465336981188654529)
    ·
      refine ⟨46758727849002735891490897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62344970465336981188654529 46758727849002735891490897)
      ·
        refine ⟨35069045886752051918618173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46758727849002735891490897 35069045886752051918618173)
        ·
          refine ⟨13150892207532019469481815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35069045886752051918618173 13150892207532019469481815)
          ·
            refine ⟨19726338311298029204222723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13150892207532019469481815 19726338311298029204222723)
            ·
              refine ⟨29589507466947043806334085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19726338311298029204222723 29589507466947043806334085)
              ·
                refine ⟨5548032650052570713687641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29589507466947043806334085 5548032650052570713687641)
                ·
                  refine ⟨4161024487539428035265731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5548032650052570713687641 4161024487539428035265731)
                  ·
                    refine ⟨6241536731309142052898597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161024487539428035265731 6241536731309142052898597)
                    ·
                      refine ⟨1170288137120464134918487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6241536731309142052898597 1170288137120464134918487)
                      ·
                        rfl

theorem cell23_2279128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2279128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279128 prefixEnd_2279128 := by exact prefixLift 2279128
  have htrace : WordTrace (prefixWord ++ tailWord_2279128) baseStart_2279128 baseEnd_2279128 := by
    simpa [prefixWord, tailWord_2279128, baseEnd_2279128] using wordTrace_append hprefix tailTrace_2279128
  have hstable : (prefixWord ++ tailWord_2279128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279128).length < 2 ^ (prefixWord ++ tailWord_2279128).sum := by decide
  have hdescent : baseEnd_2279128 < baseStart_2279128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279148 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_2279148 : Nat := 118140960795 + 2279148 * 2 ^ 59
def prefixEnd_2279148 : Nat := 4983230072969 + 3 ^ 40 * 2279148 * 2
def baseEnd_2279148 : Nat := 1170298406733554056668395

theorem tailTrace_2279148 : CollatzResearch.WordTrace tailWord_2279148 prefixEnd_2279148 1170298406733554056668395 := by
  unfold tailWord_2279148
  simp only [CollatzResearch.WordTrace]
  refine ⟨41563678373521759166967049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55418237831362345555956065 41563678373521759166967049)
  ·
    refine ⟨31172758780141319375225287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41563678373521759166967049 31172758780141319375225287)
    ·
      refine ⟨46759138170211979062837931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31172758780141319375225287 46759138170211979062837931)
      ·
        refine ⟨70138707255317968594256897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46759138170211979062837931 70138707255317968594256897)
        ·
          refine ⟨52604030441488476445692673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70138707255317968594256897 52604030441488476445692673)
          ·
            refine ⟨39453022831116357334269505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52604030441488476445692673 39453022831116357334269505)
            ·
              refine ⟨29589767123337268000702129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39453022831116357334269505 29589767123337268000702129)
              ·
                refine ⟨22192325342502951000526597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29589767123337268000702129 22192325342502951000526597)
                ·
                  refine ⟨4161061001719303312598737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22192325342502951000526597 4161061001719303312598737)
                  ·
                    refine ⟨3120795751289477484449053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161061001719303312598737 3120795751289477484449053)
                    ·
                      refine ⟨1170298406733554056668395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3120795751289477484449053 1170298406733554056668395)
                      ·
                        rfl

theorem cell23_2279148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_2279148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279148 prefixEnd_2279148 := by exact prefixLift 2279148
  have htrace : WordTrace (prefixWord ++ tailWord_2279148) baseStart_2279148 baseEnd_2279148 := by
    simpa [prefixWord, tailWord_2279148, baseEnd_2279148] using wordTrace_append hprefix tailTrace_2279148
  have hstable : (prefixWord ++ tailWord_2279148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279148).length < 2 ^ (prefixWord ++ tailWord_2279148).sum := by decide
  have hdescent : baseEnd_2279148 < baseStart_2279148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279172 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_2279172 : Nat := 118140960795 + 2279172 * 2 ^ 59
def prefixEnd_2279172 : Nat := 4983230072969 + 3 ^ 40 * 2279172 * 2
def baseEnd_2279172 : Nat := 390103576756420654256095

theorem tailTrace_2279172 : CollatzResearch.WordTrace tailWord_2279172 prefixEnd_2279172 390103576756420654256095 := by
  unfold tailWord_2279172
  simp only [CollatzResearch.WordTrace]
  refine ⟨41564116049478285216403885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55418821399304380288538513 41564116049478285216403885)
  ·
    refine ⟨15586543518554356956151457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41564116049478285216403885 15586543518554356956151457)
    ·
      refine ⟨11689907638915767717113593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15586543518554356956151457 11689907638915767717113593)
      ·
        refine ⟨8767430729186825787835195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11689907638915767717113593 8767430729186825787835195)
        ·
          refine ⟨13151146093780238681752793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767430729186825787835195 13151146093780238681752793)
          ·
            refine ⟨9863359570335179011314595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13151146093780238681752793 9863359570335179011314595)
            ·
              refine ⟨14795039355502768516971893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9863359570335179011314595 14795039355502768516971893)
              ·
                refine ⟨1387034939578384548466115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14795039355502768516971893 1387034939578384548466115)
                ·
                  refine ⟨2080552409367576822699173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387034939578384548466115 2080552409367576822699173)
                  ·
                    refine ⟨390103576756420654256095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080552409367576822699173 390103576756420654256095)
                    ·
                      rfl

theorem cell23_2279172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_2279172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279172 prefixEnd_2279172 := by exact prefixLift 2279172
  have htrace : WordTrace (prefixWord ++ tailWord_2279172) baseStart_2279172 baseEnd_2279172 := by
    simpa [prefixWord, tailWord_2279172, baseEnd_2279172] using wordTrace_append hprefix tailTrace_2279172
  have hstable : (prefixWord ++ tailWord_2279172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279172).length < 2 ^ (prefixWord ++ tailWord_2279172).sum := by decide
  have hdescent : baseEnd_2279172 < baseStart_2279172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279174 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2279174 : Nat := 118140960795 + 2279174 * 2 ^ 59
def prefixEnd_2279174 : Nat := 4983230072969 + 3 ^ 40 * 2279174 * 2
def baseEnd_2279174 : Nat := 1170311757230570954943277

theorem tailTrace_2279174 : CollatzResearch.WordTrace tailWord_2279174 prefixEnd_2279174 1170311757230570954943277 := by
  unfold tailWord_2279174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597759532654666399199393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55418870029966216516253717 2597759532654666399199393)
  ·
    refine ⟨1948319649490999799399545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2597759532654666399199393 1948319649490999799399545)
    ·
      refine ⟨1461239737118249849549659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1948319649490999799399545 1461239737118249849549659)
      ·
        refine ⟨2191859605677374774324489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461239737118249849549659 2191859605677374774324489)
        ·
          refine ⟨1643894704258031080743367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2191859605677374774324489 1643894704258031080743367)
          ·
            refine ⟨2465842056387046621115051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643894704258031080743367 2465842056387046621115051)
            ·
              refine ⟨3698763084580569931672577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465842056387046621115051 3698763084580569931672577)
              ·
                refine ⟨2774072313435427448754433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3698763084580569931672577 2774072313435427448754433)
                ·
                  refine ⟨2080554235076570586565825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2774072313435427448754433 2080554235076570586565825)
                  ·
                    refine ⟨1560415676307427939924369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2080554235076570586565825 1560415676307427939924369)
                    ·
                      refine ⟨1170311757230570954943277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560415676307427939924369 1170311757230570954943277)
                      ·
                        rfl

theorem cell23_2279174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2279174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279174 prefixEnd_2279174 := by exact prefixLift 2279174
  have htrace : WordTrace (prefixWord ++ tailWord_2279174) baseStart_2279174 baseEnd_2279174 := by
    simpa [prefixWord, tailWord_2279174, baseEnd_2279174] using wordTrace_append hprefix tailTrace_2279174
  have hstable : (prefixWord ++ tailWord_2279174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279174).length < 2 ^ (prefixWord ++ tailWord_2279174).sum := by decide
  have hdescent : baseEnd_2279174 < baseStart_2279174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279205 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_2279205 : Nat := 118140960795 + 2279205 * 2 ^ 59
def prefixEnd_2279205 : Nat := 4983230072969 + 3 ^ 40 * 2279205 * 2
def baseEnd_2279205 : Nat := 1170327675130860333655633

theorem tailTrace_2279205 : CollatzResearch.WordTrace tailWord_2279205 prefixEnd_2279205 1170327675130860333655633 := by
  unfold tailWord_2279205
  simp only [CollatzResearch.WordTrace]
  refine ⟨83129435707837017068759069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55419623805224678045839379 83129435707837017068759069)
  ·
    refine ⟨31173538390438881400784651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83129435707837017068759069 31173538390438881400784651)
    ·
      refine ⟨46760307585658322101176977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31173538390438881400784651 46760307585658322101176977)
      ·
        refine ⟨35070230689243741575882733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46760307585658322101176977 35070230689243741575882733)
        ·
          refine ⟨13151336508466403090956025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35070230689243741575882733 13151336508466403090956025)
          ·
            refine ⟨9863502381349802318217019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13151336508466403090956025 9863502381349802318217019)
            ·
              refine ⟨14795253572024703477325529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9863502381349802318217019 14795253572024703477325529)
              ·
                refine ⟨11096440179018527607994147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14795253572024703477325529 11096440179018527607994147)
                ·
                  refine ⟨16644660268527791411991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11096440179018527607994147 16644660268527791411991221)
                  ·
                    refine ⟨1560436900174480444874177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16644660268527791411991221 1560436900174480444874177)
                    ·
                      refine ⟨1170327675130860333655633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560436900174480444874177 1170327675130860333655633)
                      ·
                        rfl

theorem cell23_2279205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_2279205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279205 prefixEnd_2279205 := by exact prefixLift 2279205
  have htrace : WordTrace (prefixWord ++ tailWord_2279205) baseStart_2279205 baseEnd_2279205 := by
    simpa [prefixWord, tailWord_2279205, baseEnd_2279205] using wordTrace_append hprefix tailTrace_2279205
  have hstable : (prefixWord ++ tailWord_2279205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279205).length < 2 ^ (prefixWord ++ tailWord_2279205).sum := by decide
  have hdescent : baseEnd_2279205 < baseStart_2279205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279228 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_2279228 : Nat := 118140960795 + 2279228 * 2 ^ 59
def prefixEnd_2279228 : Nat := 4983230072969 + 3 ^ 40 * 2279228 * 2
def baseEnd_2279228 : Nat := 390113161728637914556009

theorem tailTrace_2279228 : CollatzResearch.WordTrace tailWord_2279228 prefixEnd_2279228 390113161728637914556009 := by
  unfold tailWord_2279228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41565137293376845998423169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55420183057835794664564225 41565137293376845998423169)
  ·
    refine ⟨31173852970032634498817377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41565137293376845998423169 31173852970032634498817377)
    ·
      refine ⟨23380389727524475874113033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31173852970032634498817377 23380389727524475874113033)
      ·
        refine ⟨17535292295643356905584775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23380389727524475874113033 17535292295643356905584775)
        ·
          refine ⟨26302938443465035358377163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17535292295643356905584775 26302938443465035358377163)
          ·
            refine ⟨39454407665197553037565745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26302938443465035358377163 39454407665197553037565745)
            ·
              refine ⟨29590805748898164778174309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39454407665197553037565745 29590805748898164778174309)
              ·
                refine ⟨5548276077918405895907683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29590805748898164778174309 5548276077918405895907683)
                ·
                  refine ⟨8322414116877608843861525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5548276077918405895907683 8322414116877608843861525)
                  ·
                    refine ⟨390113161728637914556009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8322414116877608843861525 390113161728637914556009)
                    ·
                      rfl

theorem cell23_2279228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_2279228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279228 prefixEnd_2279228 := by exact prefixLift 2279228
  have htrace : WordTrace (prefixWord ++ tailWord_2279228) baseStart_2279228 baseEnd_2279228 := by
    simpa [prefixWord, tailWord_2279228, baseEnd_2279228] using wordTrace_append hprefix tailTrace_2279228
  have hstable : (prefixWord ++ tailWord_2279228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279228).length < 2 ^ (prefixWord ++ tailWord_2279228).sum := by decide
  have hdescent : baseEnd_2279228 < baseStart_2279228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279235 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 4]
def baseStart_2279235 : Nat := 118140960795 + 2279235 * 2 ^ 59
def prefixEnd_2279235 : Nat := 4983230072969 + 3 ^ 40 * 2279235 * 2
def baseEnd_2279235 : Nat := 1170343079550495216280495

theorem tailTrace_2279235 : CollatzResearch.WordTrace tailWord_2279235 prefixEnd_2279235 1170343079550495216280495 := by
  unfold tailWord_2279235
  simp only [CollatzResearch.WordTrace]
  refine ⟨83130529897728332192351159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55420353265152221461567439 83130529897728332192351159)
  ·
    refine ⟨124695794846592498288526739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83130529897728332192351159 124695794846592498288526739)
    ·
      refine ⟨187043692269888747432790109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124695794846592498288526739 187043692269888747432790109)
      ·
        refine ⟨70141384601208280287296291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187043692269888747432790109 70141384601208280287296291)
        ·
          refine ⟨105212076901812420430944437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70141384601208280287296291 105212076901812420430944437)
          ·
            refine ⟨9863632209544914415401041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105212076901812420430944437 9863632209544914415401041)
            ·
              refine ⟨7397724157158685811550781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9863632209544914415401041 7397724157158685811550781)
              ·
                refine ⟨2774146558934507179331543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7397724157158685811550781 2774146558934507179331543)
                ·
                  refine ⟨4161219838401760768997315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774146558934507179331543 4161219838401760768997315)
                  ·
                    refine ⟨6241829757602641153495973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161219838401760768997315 6241829757602641153495973)
                    ·
                      refine ⟨1170343079550495216280495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6241829757602641153495973 1170343079550495216280495)
                      ·
                        rfl

theorem cell23_2279235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_2279235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279235 prefixEnd_2279235 := by exact prefixLift 2279235
  have htrace : WordTrace (prefixWord ++ tailWord_2279235) baseStart_2279235 baseEnd_2279235 := by
    simpa [prefixWord, tailWord_2279235, baseEnd_2279235] using wordTrace_append hprefix tailTrace_2279235
  have hstable : (prefixWord ++ tailWord_2279235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279235).length < 2 ^ (prefixWord ++ tailWord_2279235).sum := by decide
  have hdescent : baseEnd_2279235 < baseStart_2279235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279258 : List Nat := [3, 1, 1, 2, 1, 3, 4, 8]
def baseStart_2279258 : Nat := 118140960795 + 2279258 * 2 ^ 59
def prefixEnd_2279258 : Nat := 4983230072969 + 3 ^ 40 * 2279258 * 2
def baseEnd_2279258 : Nat := 43346477392798097270107

theorem tailTrace_2279258 : CollatzResearch.WordTrace tailWord_2279258 prefixEnd_2279258 43346477392798097270107 := by
  unfold tailWord_2279258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20782842194161251780109607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55420912517763338080292285 20782842194161251780109607)
  ·
    refine ⟨31174263291241877670164411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20782842194161251780109607 31174263291241877670164411)
    ·
      refine ⟨46761394936862816505246617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31174263291241877670164411 46761394936862816505246617)
      ·
        refine ⟨35071046202647112378934963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46761394936862816505246617 35071046202647112378934963)
        ·
          refine ⟨52606569303970668568402445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35071046202647112378934963 52606569303970668568402445)
          ·
            refine ⟨19727463488989000713150917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52606569303970668568402445 19727463488989000713150917)
            ·
              refine ⟨3698899404185437633715797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19727463488989000713150917 3698899404185437633715797)
              ·
                refine ⟨43346477392798097270107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3698899404185437633715797 43346477392798097270107)
                ·
                  rfl

theorem cell23_2279258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_2279258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279258 prefixEnd_2279258 := by exact prefixLift 2279258
  have htrace : WordTrace (prefixWord ++ tailWord_2279258) baseStart_2279258 baseEnd_2279258 := by
    simpa [prefixWord, tailWord_2279258, baseEnd_2279258] using wordTrace_append hprefix tailTrace_2279258
  have hstable : (prefixWord ++ tailWord_2279258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279258).length < 2 ^ (prefixWord ++ tailWord_2279258).sum := by decide
  have hdescent : baseEnd_2279258 < baseStart_2279258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279286 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2279286 : Nat := 118140960795 + 2279286 * 2 ^ 59
def prefixEnd_2279286 : Nat := 4983230072969 + 3 ^ 40 * 2279286 * 2
def baseEnd_2279286 : Nat := 1170369267063874516742761

theorem tailTrace_2279286 : CollatzResearch.WordTrace tailWord_2279286 prefixEnd_2279286 1170369267063874516742761 := by
  unfold tailWord_2279286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5195774376283972993903607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55421593347029045268305141 5195774376283972993903607)
  ·
    refine ⟨7793661564425959490855411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5195774376283972993903607 7793661564425959490855411)
    ·
      refine ⟨11690492346638939236283117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7793661564425959490855411 11690492346638939236283117)
      ·
        refine ⟨4383934629989602213606169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11690492346638939236283117 4383934629989602213606169)
        ·
          refine ⟨3287950972492201660204627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4383934629989602213606169 3287950972492201660204627)
          ·
            refine ⟨4931926458738302490306941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287950972492201660204627 4931926458738302490306941)
            ·
              refine ⟨1849472422026863433865103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931926458738302490306941 1849472422026863433865103)
              ·
                refine ⟨2774208633040295150797655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849472422026863433865103 2774208633040295150797655)
                ·
                  refine ⟨4161312949560442726196483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774208633040295150797655 4161312949560442726196483)
                  ·
                    refine ⟨6241969424340664089294725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161312949560442726196483 6241969424340664089294725)
                    ·
                      refine ⟨1170369267063874516742761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6241969424340664089294725 1170369267063874516742761)
                      ·
                        rfl

theorem cell23_2279286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2279286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279286 prefixEnd_2279286 := by exact prefixLift 2279286
  have htrace : WordTrace (prefixWord ++ tailWord_2279286) baseStart_2279286 baseEnd_2279286 := by
    simpa [prefixWord, tailWord_2279286, baseEnd_2279286] using wordTrace_append hprefix tailTrace_2279286
  have hstable : (prefixWord ++ tailWord_2279286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279286).length < 2 ^ (prefixWord ++ tailWord_2279286).sum := by decide
  have hdescent : baseEnd_2279286 < baseStart_2279286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279375 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_2279375 : Nat := 118140960795 + 2279375 * 2 ^ 59
def prefixEnd_2279375 : Nat := 4983230072969 + 3 ^ 40 * 2279375 * 2
def baseEnd_2279375 : Nat := 1170414966842124668529851

theorem tailTrace_2279375 : CollatzResearch.WordTrace tailWord_2279375 prefixEnd_2279375 1170414966842124668529851 := by
  unfold tailWord_2279375
  simp only [CollatzResearch.WordTrace]
  refine ⟨83135636117221136102447579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55423757411480757401631719 83135636117221136102447579)
  ·
    refine ⟨124703454175831704153671369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83135636117221136102447579 124703454175831704153671369)
    ·
      refine ⟨93527590631873778115253527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124703454175831704153671369 93527590631873778115253527)
      ·
        refine ⟨140291385947810667172880291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93527590631873778115253527 140291385947810667172880291)
        ·
          refine ⟨210437078921716000759320437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140291385947810667172880291 210437078921716000759320437)
          ·
            refine ⟨19728476148910875071186291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210437078921716000759320437 19728476148910875071186291)
            ·
              refine ⟨29592714223366312606779437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19728476148910875071186291 29592714223366312606779437)
              ·
                refine ⟨11097267833762367227542289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29592714223366312606779437 11097267833762367227542289)
                ·
                  refine ⟨8322950875321775420656717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11097267833762367227542289 8322950875321775420656717)
                  ·
                    refine ⟨3121106578245665782746269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8322950875321775420656717 3121106578245665782746269)
                    ·
                      refine ⟨1170414966842124668529851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121106578245665782746269 1170414966842124668529851)
                      ·
                        rfl

theorem cell23_2279375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_2279375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279375 prefixEnd_2279375 := by exact prefixLift 2279375
  have htrace : WordTrace (prefixWord ++ tailWord_2279375) baseStart_2279375 baseEnd_2279375 := by
    simpa [prefixWord, tailWord_2279375, baseEnd_2279375] using wordTrace_append hprefix tailTrace_2279375
  have hstable : (prefixWord ++ tailWord_2279375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279375).length < 2 ^ (prefixWord ++ tailWord_2279375).sum := by decide
  have hdescent : baseEnd_2279375 < baseStart_2279375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279395 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 7]
def baseStart_2279395 : Nat := 118140960795 + 2279395 * 2 ^ 59
def prefixEnd_2279395 : Nat := 4983230072969 + 3 ^ 40 * 2279395 * 2
def baseEnd_2279395 : Nat := 390141745485071530093253

theorem tailTrace_2279395 : CollatzResearch.WordTrace tailWord_2279395 prefixEnd_2279395 390141745485071530093253 := by
  unfold tailWord_2279395
  simp only [CollatzResearch.WordTrace]
  refine ⟨83136365577148679518175639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55424243718099119678783759 83136365577148679518175639)
  ·
    refine ⟨124704548365723019277263459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83136365577148679518175639 124704548365723019277263459)
    ·
      refine ⟨187056822548584528915895189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124704548365723019277263459 187056822548584528915895189)
      ·
        refine ⟨8768288556964899792932587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187056822548584528915895189 8768288556964899792932587)
        ·
          refine ⟨13152432835447349689398881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8768288556964899792932587 13152432835447349689398881)
          ·
            refine ⟨9864324626585512267049161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13152432835447349689398881 9864324626585512267049161)
            ·
              refine ⟨7398243469939134200286871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9864324626585512267049161 7398243469939134200286871)
              ·
                refine ⟨11097365204908701300430307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7398243469939134200286871 11097365204908701300430307)
                ·
                  refine ⟨16646047807363051950645461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11097365204908701300430307 16646047807363051950645461)
                  ·
                    refine ⟨390141745485071530093253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16646047807363051950645461 390141745485071530093253)
                    ·
                      rfl

theorem cell23_2279395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_2279395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279395 prefixEnd_2279395 := by exact prefixLift 2279395
  have htrace : WordTrace (prefixWord ++ tailWord_2279395) baseStart_2279395 baseEnd_2279395 := by
    simpa [prefixWord, tailWord_2279395, baseEnd_2279395] using wordTrace_append hprefix tailTrace_2279395
  have hstable : (prefixWord ++ tailWord_2279395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279395).length < 2 ^ (prefixWord ++ tailWord_2279395).sum := by decide
  have hdescent : baseEnd_2279395 < baseStart_2279395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279422 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2279422 : Nat := 118140960795 + 2279422 * 2 ^ 59
def prefixEnd_2279422 : Nat := 4983230072969 + 3 ^ 40 * 2279422 * 2
def baseEnd_2279422 : Nat := 1170439100432885984642135

theorem tailTrace_2279422 : CollatzResearch.WordTrace tailWord_2279422 prefixEnd_2279422 1170439100432885984642135 := by
  unfold tailWord_2279422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392168793506357891176065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55424900232033908752939013 10392168793506357891176065)
  ·
    refine ⟨7794126595129768418382049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10392168793506357891176065 7794126595129768418382049)
    ·
      refine ⟨5845594946347326313786537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7794126595129768418382049 5845594946347326313786537)
      ·
        refine ⟨4384196209760494735339903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5845594946347326313786537 4384196209760494735339903)
        ·
          refine ⟨6576294314640742103009855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384196209760494735339903 6576294314640742103009855)
          ·
            refine ⟨9864441471961113154514783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6576294314640742103009855 9864441471961113154514783)
            ·
              refine ⟨14796662207941669731772175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864441471961113154514783 14796662207941669731772175)
              ·
                refine ⟨22194993311912504597658263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14796662207941669731772175 22194993311912504597658263)
                ·
                  refine ⟨33292489967868756896487395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22194993311912504597658263 33292489967868756896487395)
                  ·
                    refine ⟨49938734951803135344731093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33292489967868756896487395 49938734951803135344731093)
                    ·
                      refine ⟨1170439100432885984642135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49938734951803135344731093 1170439100432885984642135)
                      ·
                        rfl

theorem cell23_2279422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2279422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279422 prefixEnd_2279422 := by exact prefixLift 2279422
  have htrace : WordTrace (prefixWord ++ tailWord_2279422) baseStart_2279422 baseEnd_2279422 := by
    simpa [prefixWord, tailWord_2279422, baseEnd_2279422] using wordTrace_append hprefix tailTrace_2279422
  have hstable : (prefixWord ++ tailWord_2279422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279422).length < 2 ^ (prefixWord ++ tailWord_2279422).sum := by decide
  have hdescent : baseEnd_2279422 < baseStart_2279422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279432 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_2279432 : Nat := 118140960795 + 2279432 * 2 ^ 59
def prefixEnd_2279432 : Nat := 4983230072969 + 3 ^ 40 * 2279432 * 2
def baseEnd_2279432 : Nat := 1170444235239430945517089

theorem tailTrace_2279432 : CollatzResearch.WordTrace tailWord_2279432 prefixEnd_2279432 1170444235239430945517089 := by
  unfold tailWord_2279432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41568857539007317418636275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55425143385343089891515033 41568857539007317418636275)
  ·
    refine ⟨62353286308510976127954413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41568857539007317418636275 62353286308510976127954413)
    ·
      refine ⟨23382482365691616047982905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62353286308510976127954413 23382482365691616047982905)
      ·
        refine ⟨17536861774268712035987179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23382482365691616047982905 17536861774268712035987179)
        ·
          refine ⟨26305292661403068053980769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17536861774268712035987179 26305292661403068053980769)
          ·
            refine ⟨19728969496052301040485577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305292661403068053980769 19728969496052301040485577)
            ·
              refine ⟨14796727122039225780364183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19728969496052301040485577 14796727122039225780364183)
              ·
                refine ⟨22195090683058838670546275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14796727122039225780364183 22195090683058838670546275)
                ·
                  refine ⟨33292636024588258005819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22195090683058838670546275 33292636024588258005819413)
                  ·
                    refine ⟨1560592313652574594022785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33292636024588258005819413 1560592313652574594022785)
                    ·
                      refine ⟨1170444235239430945517089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560592313652574594022785 1170444235239430945517089)
                      ·
                        rfl

theorem cell23_2279432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_2279432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279432 prefixEnd_2279432 := by exact prefixLift 2279432
  have htrace : WordTrace (prefixWord ++ tailWord_2279432) baseStart_2279432 baseEnd_2279432 := by
    simpa [prefixWord, tailWord_2279432, baseEnd_2279432] using wordTrace_append hprefix tailTrace_2279432
  have hstable : (prefixWord ++ tailWord_2279432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279432).length < 2 ^ (prefixWord ++ tailWord_2279432).sum := by decide
  have hdescent : baseEnd_2279432 < baseStart_2279432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279459 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 1, 4]
def baseStart_2279459 : Nat := 118140960795 + 2279459 * 2 ^ 59
def prefixEnd_2279459 : Nat := 4983230072969 + 3 ^ 40 * 2279459 * 2
def baseEnd_2279459 : Nat := 390152699739034113293155

theorem tailTrace_2279459 : CollatzResearch.WordTrace tailWord_2279459 prefixEnd_2279459 390152699739034113293155 := by
  unfold tailWord_2279459
  simp only [CollatzResearch.WordTrace]
  refine ⟨83138699848916818448505431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55425799899277878965670287 83138699848916818448505431)
  ·
    refine ⟨124708049773375227672758147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83138699848916818448505431 124708049773375227672758147)
    ·
      refine ⟨187062074660062841509137221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124708049773375227672758147 187062074660062841509137221)
      ·
        refine ⟨35074138998761782782963229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187062074660062841509137221 35074138998761782782963229)
        ·
          refine ⟨13152802124535668543611211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35074138998761782782963229 13152802124535668543611211)
          ·
            refine ⟨19729203186803502815416817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13152802124535668543611211 19729203186803502815416817)
            ·
              refine ⟨14796902390102627111562613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19729203186803502815416817 14796902390102627111562613)
              ·
                refine ⟨1387209599072121291708995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14796902390102627111562613 1387209599072121291708995)
                ·
                  refine ⟨2080814398608181937563493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387209599072121291708995 2080814398608181937563493)
                  ·
                    refine ⟨390152699739034113293155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080814398608181937563493 390152699739034113293155)
                    ·
                      rfl

theorem cell23_2279459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 4].length) (baseStart_2279459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279459 prefixEnd_2279459 := by exact prefixLift 2279459
  have htrace : WordTrace (prefixWord ++ tailWord_2279459) baseStart_2279459 baseEnd_2279459 := by
    simpa [prefixWord, tailWord_2279459, baseEnd_2279459] using wordTrace_append hprefix tailTrace_2279459
  have hstable : (prefixWord ++ tailWord_2279459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279459).length < 2 ^ (prefixWord ++ tailWord_2279459).sum := by decide
  have hdescent : baseEnd_2279459 < baseStart_2279459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_2279465 : Nat := 118140960795 + 2279465 * 2 ^ 59
def prefixEnd_2279465 : Nat := 4983230072969 + 3 ^ 40 * 2279465 * 2
def baseEnd_2279465 : Nat := 1170461180101029316404437

theorem tailTrace_2279465 : CollatzResearch.WordTrace tailWord_2279465 prefixEnd_2279465 1170461180101029316404437 := by
  unfold tailWord_2279465
  simp only [CollatzResearch.WordTrace]
  refine ⟨83138918686895081473223849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55425945791263387648815899 83138918686895081473223849)
  ·
    refine ⟨62354189015171311104917887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83138918686895081473223849 62354189015171311104917887)
    ·
      refine ⟨93531283522756966657376831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62354189015171311104917887 93531283522756966657376831)
      ·
        refine ⟨140296925284135449986065247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93531283522756966657376831 140296925284135449986065247)
        ·
          refine ⟨210445387926203174979097871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140296925284135449986065247 210445387926203174979097871)
          ·
            refine ⟨315668081889304762468646807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210445387926203174979097871 315668081889304762468646807)
            ·
              refine ⟨473502122833957143702970211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315668081889304762468646807 473502122833957143702970211)
              ·
                refine ⟨710253184250935715554455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473502122833957143702970211 710253184250935715554455317)
                ·
                  refine ⟨33293118011762611666615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 710253184250935715554455317 33293118011762611666615093)
                  ·
                    refine ⟨3121229813602744843745165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33293118011762611666615093 3121229813602744843745165)
                    ·
                      refine ⟨1170461180101029316404437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121229813602744843745165 1170461180101029316404437)
                      ·
                        rfl

theorem cell23_2279465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_2279465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279465 prefixEnd_2279465 := by exact prefixLift 2279465
  have htrace : WordTrace (prefixWord ++ tailWord_2279465) baseStart_2279465 baseEnd_2279465 := by
    simpa [prefixWord, tailWord_2279465, baseEnd_2279465] using wordTrace_append hprefix tailTrace_2279465
  have hstable : (prefixWord ++ tailWord_2279465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279465).length < 2 ^ (prefixWord ++ tailWord_2279465).sum := by decide
  have hdescent : baseEnd_2279465 < baseStart_2279465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279472 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 6]
def baseStart_2279472 : Nat := 118140960795 + 2279472 * 2 ^ 59
def prefixEnd_2279472 : Nat := 4983230072969 + 3 ^ 40 * 2279472 * 2
def baseEnd_2279472 : Nat := 130051641607290087668545

theorem tailTrace_2279472 : CollatzResearch.WordTrace tailWord_2279472 prefixEnd_2279472 130051641607290087668545 := by
  unfold tailWord_2279472
  simp only [CollatzResearch.WordTrace]
  refine ⟨41569586998934860834364335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55426115998579814445819113 41569586998934860834364335)
  ·
    refine ⟨62354380498402291251546503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41569586998934860834364335 62354380498402291251546503)
    ·
      refine ⟨93531570747603436877319755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62354380498402291251546503 93531570747603436877319755)
      ·
        refine ⟨140297356121405155315979633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93531570747603436877319755 140297356121405155315979633)
        ·
          refine ⟨105223017091053866486984725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140297356121405155315979633 105223017091053866486984725)
          ·
            refine ⟨4932328926143149991577409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105223017091053866486984725 4932328926143149991577409)
            ·
              refine ⟨3699246694607362493683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4932328926143149991577409 3699246694607362493683057)
              ·
                refine ⟨2774435020955521870262293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699246694607362493683057 2774435020955521870262293)
                ·
                  refine ⟨130051641607290087668545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2774435020955521870262293 130051641607290087668545)
                  ·
                    rfl

theorem cell23_2279472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_2279472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279472 prefixEnd_2279472 := by exact prefixLift 2279472
  have htrace : WordTrace (prefixWord ++ tailWord_2279472) baseStart_2279472 baseEnd_2279472 := by
    simpa [prefixWord, tailWord_2279472, baseEnd_2279472] using wordTrace_append hprefix tailTrace_2279472
  have hstable : (prefixWord ++ tailWord_2279472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279472).length < 2 ^ (prefixWord ++ tailWord_2279472).sum := by decide
  have hdescent : baseEnd_2279472 < baseStart_2279472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279495 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2279495 : Nat := 118140960795 + 2279495 * 2 ^ 59
def prefixEnd_2279495 : Nat := 4983230072969 + 3 ^ 40 * 2279495 * 2
def baseEnd_2279495 : Nat := 1170476584520664199029299

theorem tailTrace_2279495 : CollatzResearch.WordTrace tailWord_2279495 prefixEnd_2279495 1170476584520664199029299 := by
  unfold tailWord_2279495
  simp only [CollatzResearch.WordTrace]
  refine ⟨83140012876786396596815939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55426675251190931064543959 83140012876786396596815939)
  ·
    refine ⟨124710019315179594895223909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83140012876786396596815939 124710019315179594895223909)
    ·
      refine ⟨23383128621596174042854483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124710019315179594895223909 23383128621596174042854483)
      ·
        refine ⟨35074692932394261064281725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23383128621596174042854483 35074692932394261064281725)
        ·
          refine ⟨13153009849647847899105647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35074692932394261064281725 13153009849647847899105647)
          ·
            refine ⟨19729514774471771848658471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13153009849647847899105647 19729514774471771848658471)
            ·
              refine ⟨29594272161707657772987707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19729514774471771848658471 29594272161707657772987707)
              ·
                refine ⟨44391408242561486659481561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29594272161707657772987707 44391408242561486659481561)
                ·
                  refine ⟨33293556181921114994611171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44391408242561486659481561 33293556181921114994611171)
                  ·
                    refine ⟨49940334272881672491916757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33293556181921114994611171 49940334272881672491916757)
                    ·
                      refine ⟨1170476584520664199029299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49940334272881672491916757 1170476584520664199029299)
                      ·
                        rfl

theorem cell23_2279495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2279495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279495 prefixEnd_2279495 := by exact prefixLift 2279495
  have htrace : WordTrace (prefixWord ++ tailWord_2279495) baseStart_2279495 baseEnd_2279495 := by
    simpa [prefixWord, tailWord_2279495, baseEnd_2279495] using wordTrace_append hprefix tailTrace_2279495
  have hstable : (prefixWord ++ tailWord_2279495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279495).length < 2 ^ (prefixWord ++ tailWord_2279495).sum := by decide
  have hdescent : baseEnd_2279495 < baseStart_2279495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279502 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2279502 : Nat := 118140960795 + 2279502 * 2 ^ 59
def prefixEnd_2279502 : Nat := 4983230072969 + 3 ^ 40 * 2279502 * 2
def baseEnd_2279502 : Nat := 390160059628415223880589

theorem tailTrace_2279502 : CollatzResearch.WordTrace tailWord_2279502 prefixEnd_2279502 390160059628415223880589 := by
  unfold tailWord_2279502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392533523470129599040095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55426845458507357861547173 10392533523470129599040095)
  ·
    refine ⟨15588800285205194398560143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10392533523470129599040095 15588800285205194398560143)
    ·
      refine ⟨23383200427807791597840215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15588800285205194398560143 23383200427807791597840215)
      ·
        refine ⟨35074800641711687396760323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23383200427807791597840215 35074800641711687396760323)
        ·
          refine ⟨52612200962567531095140485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35074800641711687396760323 52612200962567531095140485)
          ·
            refine ⟨9864787680481412080338841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52612200962567531095140485 9864787680481412080338841)
            ·
              refine ⟨7398590760361059060254131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9864787680481412080338841 7398590760361059060254131)
              ·
                refine ⟨11097886140541588590381197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7398590760361059060254131 11097886140541588590381197)
                ·
                  refine ⟨4161707302703095721392949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11097886140541588590381197 4161707302703095721392949)
                  ·
                    refine ⟨390160059628415223880589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4161707302703095721392949 390160059628415223880589)
                    ·
                      rfl

theorem cell23_2279502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2279502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279502 prefixEnd_2279502 := by exact prefixLift 2279502
  have htrace : WordTrace (prefixWord ++ tailWord_2279502) baseStart_2279502 baseEnd_2279502 := by
    simpa [prefixWord, tailWord_2279502, baseEnd_2279502] using wordTrace_append hprefix tailTrace_2279502
  have hstable : (prefixWord ++ tailWord_2279502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279502).length < 2 ^ (prefixWord ++ tailWord_2279502).sum := by decide
  have hdescent : baseEnd_2279502 < baseStart_2279502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279509 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2279509 : Nat := 118140960795 + 2279509 * 2 ^ 59
def prefixEnd_2279509 : Nat := 4983230072969 + 3 ^ 40 * 2279509 * 2
def baseEnd_2279509 : Nat := 1170483773249827144254235

theorem tailTrace_2279509 : CollatzResearch.WordTrace tailWord_2279509 prefixEnd_2279509 1170483773249827144254235 := by
  unfold tailWord_2279509
  simp only [CollatzResearch.WordTrace]
  refine ⟨83140523498735676987825581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55427015665823784658550387 83140523498735676987825581)
  ·
    refine ⟨31177696312025878870434593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83140523498735676987825581 31177696312025878870434593)
    ·
      refine ⟨23383272234019409152825945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31177696312025878870434593 23383272234019409152825945)
      ·
        refine ⟨17537454175514556864619459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23383272234019409152825945 17537454175514556864619459)
        ·
          refine ⟨26306181263271835296929189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537454175514556864619459 26306181263271835296929189)
          ·
            refine ⟨4932408986863469118174223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26306181263271835296929189 4932408986863469118174223)
            ·
              refine ⟨7398613480295203677261335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932408986863469118174223 7398613480295203677261335)
              ·
                refine ⟨11097920220442805515892003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7398613480295203677261335 11097920220442805515892003)
                ·
                  refine ⟨16646880330664208273838005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11097920220442805515892003 16646880330664208273838005)
                  ·
                    refine ⟨1560645030999769525672313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16646880330664208273838005 1560645030999769525672313)
                    ·
                      refine ⟨1170483773249827144254235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560645030999769525672313 1170483773249827144254235)
                      ·
                        rfl

theorem cell23_2279509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2279509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279509 prefixEnd_2279509 := by exact prefixLift 2279509
  have htrace : WordTrace (prefixWord ++ tailWord_2279509) baseStart_2279509 baseEnd_2279509 := by
    simpa [prefixWord, tailWord_2279509, baseEnd_2279509] using wordTrace_append hprefix tailTrace_2279509
  have hstable : (prefixWord ++ tailWord_2279509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279509).length < 2 ^ (prefixWord ++ tailWord_2279509).sum := by decide
  have hdescent : baseEnd_2279509 < baseStart_2279509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279510 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2279510 : Nat := 118140960795 + 2279510 * 2 ^ 59
def prefixEnd_2279510 : Nat := 4983230072969 + 3 ^ 40 * 2279510 * 2
def baseEnd_2279510 : Nat := 390161428910160546780577

theorem tailTrace_2279510 : CollatzResearch.WordTrace tailWord_2279510 prefixEnd_2279510 390161428910160546780577 := by
  unfold tailWord_2279510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196284998233253384913249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55427039981154702772407989 5196284998233253384913249)
  ·
    refine ⟨3897213748674940038684937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5196284998233253384913249 3897213748674940038684937)
    ·
      refine ⟨2922910311506205029013703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3897213748674940038684937 2922910311506205029013703)
      ·
        refine ⟨4384365467259307543520555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922910311506205029013703 4384365467259307543520555)
        ·
          refine ⟨6576548200888961315280833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384365467259307543520555 6576548200888961315280833)
          ·
            refine ⟨4932411150666720986460625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6576548200888961315280833 4932411150666720986460625)
            ·
              refine ⟨3699308363000040739845469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4932411150666720986460625 3699308363000040739845469)
              ·
                refine ⟨1387240636125015277442051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3699308363000040739845469 1387240636125015277442051)
                ·
                  refine ⟨2080860954187522916163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387240636125015277442051 2080860954187522916163077)
                  ·
                    refine ⟨390161428910160546780577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080860954187522916163077 390161428910160546780577)
                    ·
                      rfl

theorem cell23_2279510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2279510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279510 prefixEnd_2279510 := by exact prefixLift 2279510
  have htrace : WordTrace (prefixWord ++ tailWord_2279510) baseStart_2279510 baseEnd_2279510 := by
    simpa [prefixWord, tailWord_2279510, baseEnd_2279510] using wordTrace_append hprefix tailTrace_2279510
  have hstable : (prefixWord ++ tailWord_2279510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279510).length < 2 ^ (prefixWord ++ tailWord_2279510).sum := by decide
  have hdescent : baseEnd_2279510 < baseStart_2279510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279549 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2279549 : Nat := 118140960795 + 2279549 * 2 ^ 59
def prefixEnd_2279549 : Nat := 4983230072969 + 3 ^ 40 * 2279549 * 2
def baseEnd_2279549 : Nat := 390168104158668995918017

theorem tailTrace_2279549 : CollatzResearch.WordTrace tailWord_2279549 prefixEnd_2279549 390168104158668995918017 := by
  unfold tailWord_2279549
  simp only [CollatzResearch.WordTrace]
  refine ⟨83141982418590763819281701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55427988279060509212854467 83141982418590763819281701)
  ·
    refine ⟨15589121703485768216115319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83141982418590763819281701 15589121703485768216115319)
    ·
      refine ⟨23383682555228652324172979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15589121703485768216115319 23383682555228652324172979)
      ·
        refine ⟨35075523832842978486259469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23383682555228652324172979 35075523832842978486259469)
        ·
          refine ⟨13153321437316116932347301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35075523832842978486259469 13153321437316116932347301)
          ·
            refine ⟨2466247769496771924815119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13153321437316116932347301 2466247769496771924815119)
            ·
              refine ⟨3699371654245157887222679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466247769496771924815119 3699371654245157887222679)
              ·
                refine ⟨5549057481367736830834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699371654245157887222679 5549057481367736830834019)
                ·
                  refine ⟨8323586222051605246251029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549057481367736830834019 8323586222051605246251029)
                  ·
                    refine ⟨390168104158668995918017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8323586222051605246251029 390168104158668995918017)
                    ·
                      rfl

theorem cell23_2279549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2279549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279549 prefixEnd_2279549 := by exact prefixLift 2279549
  have htrace : WordTrace (prefixWord ++ tailWord_2279549) baseStart_2279549 baseEnd_2279549 := by
    simpa [prefixWord, tailWord_2279549, baseEnd_2279549] using wordTrace_append hprefix tailTrace_2279549
  have hstable : (prefixWord ++ tailWord_2279549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279549).length < 2 ^ (prefixWord ++ tailWord_2279549).sum := by decide
  have hdescent : baseEnd_2279549 < baseStart_2279549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279556 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_2279556 : Nat := 118140960795 + 2279556 * 2 ^ 59
def prefixEnd_2279556 : Nat := 4983230072969 + 3 ^ 40 * 2279556 * 2
def baseEnd_2279556 : Nat := 1170507906840588460366519

theorem tailTrace_2279556 : CollatzResearch.WordTrace tailWord_2279556 prefixEnd_2279556 1170507906840588460366519 := by
  unfold tailWord_2279556
  simp only [CollatzResearch.WordTrace]
  refine ⟨41571118864782702007393261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55428158486376936009857681 41571118864782702007393261)
  ·
    refine ⟨15589169574293513252772473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41571118864782702007393261 15589169574293513252772473)
    ·
      refine ⟨11691877180720134939579355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15589169574293513252772473 11691877180720134939579355)
      ·
        refine ⟨17537815771080202409369033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11691877180720134939579355 17537815771080202409369033)
        ·
          refine ⟨13153361828310151807026775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17537815771080202409369033 13153361828310151807026775)
          ·
            refine ⟨19730042742465227710540163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13153361828310151807026775 19730042742465227710540163)
            ·
              refine ⟨29595064113697841565810245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19730042742465227710540163 29595064113697841565810245)
              ·
                refine ⟨5549074521318345293589421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29595064113697841565810245 5549074521318345293589421)
                ·
                  refine ⟨2080902945494379485096033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5549074521318345293589421 2080902945494379485096033)
                  ·
                    refine ⟨1560677209120784613822025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2080902945494379485096033 1560677209120784613822025)
                    ·
                      refine ⟨1170507906840588460366519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560677209120784613822025 1170507906840588460366519)
                      ·
                        rfl

theorem cell23_2279556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_2279556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279556 prefixEnd_2279556 := by exact prefixLift 2279556
  have htrace : WordTrace (prefixWord ++ tailWord_2279556) baseStart_2279556 baseEnd_2279556 := by
    simpa [prefixWord, tailWord_2279556, baseEnd_2279556] using wordTrace_append hprefix tailTrace_2279556
  have hstable : (prefixWord ++ tailWord_2279556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279556).length < 2 ^ (prefixWord ++ tailWord_2279556).sum := by decide
  have hdescent : baseEnd_2279556 < baseStart_2279556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279559 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2279559 : Nat := 118140960795 + 2279559 * 2 ^ 59
def prefixEnd_2279559 : Nat := 4983230072969 + 3 ^ 40 * 2279559 * 2
def baseEnd_2279559 : Nat := 1170509447282551948629005

theorem tailTrace_2279559 : CollatzResearch.WordTrace tailWord_2279559 prefixEnd_2279559 1170509447282551948629005 := by
  unfold tailWord_2279559
  simp only [CollatzResearch.WordTrace]
  refine ⟨83142347148554535527145731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55428231432369690351430487 83142347148554535527145731)
  ·
    refine ⟨124713520722831803290718597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83142347148554535527145731 124713520722831803290718597)
    ·
      refine ⟨23383785135530963117009737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124713520722831803290718597 23383785135530963117009737)
      ·
        refine ⟨17537838851648222337757303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23383785135530963117009737 17537838851648222337757303)
        ·
          refine ⟨26306758277472333506635955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537838851648222337757303 26306758277472333506635955)
          ·
            refine ⟨39460137416208500259953933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26306758277472333506635955 39460137416208500259953933)
            ·
              refine ⟨14797551531078187597482725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39460137416208500259953933 14797551531078187597482725)
              ·
                refine ⟨2774540912077160174528011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14797551531078187597482725 2774540912077160174528011)
                ·
                  refine ⟨4161811368115740261792017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774540912077160174528011 4161811368115740261792017)
                  ·
                    refine ⟨3121358526086805196344013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161811368115740261792017 3121358526086805196344013)
                    ·
                      refine ⟨1170509447282551948629005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121358526086805196344013 1170509447282551948629005)
                      ·
                        rfl

theorem cell23_2279559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2279559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279559 prefixEnd_2279559 := by exact prefixLift 2279559
  have htrace : WordTrace (prefixWord ++ tailWord_2279559) baseStart_2279559 baseEnd_2279559 := by
    simpa [prefixWord, tailWord_2279559, baseEnd_2279559] using wordTrace_append hprefix tailTrace_2279559
  have hstable : (prefixWord ++ tailWord_2279559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279559).length < 2 ^ (prefixWord ++ tailWord_2279559).sum := by decide
  have hdescent : baseEnd_2279559 < baseStart_2279559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279562 : List Nat := [3, 1, 2, 3, 1, 3, 1, 9]
def baseStart_2279562 : Nat := 118140960795 + 2279562 * 2 ^ 59
def prefixEnd_2279562 : Nat := 4983230072969 + 3 ^ 40 * 2279562 * 2
def baseEnd_2279562 : Nat := 43352258804611682847833

theorem tailTrace_2279562 : CollatzResearch.WordTrace tailWord_2279562 prefixEnd_2279562 43352258804611682847833 := by
  unfold tailWord_2279562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20785614141885916759876235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55428304378362444693003293 20785614141885916759876235)
  ·
    refine ⟨31178421212828875139814353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20785614141885916759876235 31178421212828875139814353)
    ·
      refine ⟨23383815909621656354860765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31178421212828875139814353 23383815909621656354860765)
      ·
        refine ⟨8768930966108121133072787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23383815909621656354860765 8768930966108121133072787)
        ·
          refine ⟨13153396449162181699609181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8768930966108121133072787 13153396449162181699609181)
          ·
            refine ⟨4932523668435818137353443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13153396449162181699609181 4932523668435818137353443)
            ·
              refine ⟨7398785502653727206030165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932523668435818137353443 7398785502653727206030165)
              ·
                refine ⟨43352258804611682847833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7398785502653727206030165 43352258804611682847833)
                ·
                  rfl

theorem cell23_2279562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_2279562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279562 prefixEnd_2279562 := by exact prefixLift 2279562
  have htrace : WordTrace (prefixWord ++ tailWord_2279562) baseStart_2279562 baseEnd_2279562 := by
    simpa [prefixWord, tailWord_2279562, baseEnd_2279562] using wordTrace_append hprefix tailTrace_2279562
  have hstable : (prefixWord ++ tailWord_2279562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279562).length < 2 ^ (prefixWord ++ tailWord_2279562).sum := by decide
  have hdescent : baseEnd_2279562 < baseStart_2279562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279589 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_2279589 : Nat := 118140960795 + 2279589 * 2 ^ 59
def prefixEnd_2279589 : Nat := 4983230072969 + 3 ^ 40 * 2279589 * 2
def baseEnd_2279589 : Nat := 1170524851702186831253867

theorem tailTrace_2279589 : CollatzResearch.WordTrace tailWord_2279589 prefixEnd_2279589 1170524851702186831253867 := by
  unfold tailWord_2279589
  simp only [CollatzResearch.WordTrace]
  refine ⟨83143441338445850650737821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55428960892297233767158547 83143441338445850650737821)
  ·
    refine ⟨31178790501917193994026683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83143441338445850650737821 31178790501917193994026683)
    ·
      refine ⟨46768185752875790991040025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31178790501917193994026683 46768185752875790991040025)
      ·
        refine ⟨35076139314656843243280019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46768185752875790991040025 35076139314656843243280019)
        ·
          refine ⟨52614208971985264864920029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35076139314656843243280019 52614208971985264864920029)
          ·
            refine ⟨19730328364494474324345011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52614208971985264864920029 19730328364494474324345011)
            ·
              refine ⟨29595492546741711486517517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19730328364494474324345011 29595492546741711486517517)
              ·
                refine ⟨11098309705028141807444069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29595492546741711486517517 11098309705028141807444069)
                ·
                  refine ⟨2080933069692776588895763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11098309705028141807444069 2080933069692776588895763)
                  ·
                    refine ⟨3121399604539164883343645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080933069692776588895763 3121399604539164883343645)
                    ·
                      refine ⟨1170524851702186831253867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121399604539164883343645 1170524851702186831253867)
                      ·
                        rfl

theorem cell23_2279589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_2279589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279589 prefixEnd_2279589 := by exact prefixLift 2279589
  have htrace : WordTrace (prefixWord ++ tailWord_2279589) baseStart_2279589 baseEnd_2279589 := by
    simpa [prefixWord, tailWord_2279589, baseEnd_2279589] using wordTrace_append hprefix tailTrace_2279589
  have hstable : (prefixWord ++ tailWord_2279589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279589).length < 2 ^ (prefixWord ++ tailWord_2279589).sum := by decide
  have hdescent : baseEnd_2279589 < baseStart_2279589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279595 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_2279595 : Nat := 118140960795 + 2279595 * 2 ^ 59
def prefixEnd_2279595 : Nat := 4983230072969 + 3 ^ 40 * 2279595 * 2
def baseEnd_2279595 : Nat := 1170527932586113807778839

theorem tailTrace_2279595 : CollatzResearch.WordTrace tailWord_2279595 prefixEnd_2279595 1170527932586113807778839 := by
  unfold tailWord_2279595
  simp only [CollatzResearch.WordTrace]
  refine ⟨83143660176424113675456239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55429106784282742450304159 83143660176424113675456239)
  ·
    refine ⟨124715490264636170513184359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83143660176424113675456239 124715490264636170513184359)
    ·
      refine ⟨187073235396954255769776539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124715490264636170513184359 187073235396954255769776539)
      ·
        refine ⟨280609853095431383654664809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187073235396954255769776539 280609853095431383654664809)
        ·
          refine ⟨210457389821573537740998607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280609853095431383654664809 210457389821573537740998607)
          ·
            refine ⟨315686084732360306611497911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210457389821573537740998607 315686084732360306611497911)
            ·
              refine ⟨473529127098540459917246867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315686084732360306611497911 473529127098540459917246867)
              ·
                refine ⟨710293690647810689875870301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473529127098540459917246867 710293690647810689875870301)
                ·
                  refine ⟨266360133992929008703451363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710293690647810689875870301 266360133992929008703451363)
                  ·
                    refine ⟨399540200989393513055177045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266360133992929008703451363 399540200989393513055177045)
                    ·
                      refine ⟨1170527932586113807778839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 399540200989393513055177045 1170527932586113807778839)
                      ·
                        rfl

theorem cell23_2279595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_2279595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279595 prefixEnd_2279595 := by exact prefixLift 2279595
  have htrace : WordTrace (prefixWord ++ tailWord_2279595) baseStart_2279595 baseEnd_2279595 := by
    simpa [prefixWord, tailWord_2279595, baseEnd_2279595] using wordTrace_append hprefix tailTrace_2279595
  have hstable : (prefixWord ++ tailWord_2279595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279595).length < 2 ^ (prefixWord ++ tailWord_2279595).sum := by decide
  have hdescent : baseEnd_2279595 < baseStart_2279595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 3, 3, 2]
def baseStart_2279599 : Nat := 118140960795 + 2279599 * 2 ^ 59
def prefixEnd_2279599 : Nat := 4983230072969 + 3 ^ 40 * 2279599 * 2
def baseEnd_2279599 : Nat := 1170529986508731792128821

theorem tailTrace_2279599 : CollatzResearch.WordTrace tailWord_2279599 prefixEnd_2279599 1170529986508731792128821 := by
  unfold tailWord_2279599
  simp only [CollatzResearch.WordTrace]
  refine ⟨83143806068409622358601851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55429204045606414905734567 83143806068409622358601851)
  ·
    refine ⟨124715709102614433537902777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83143806068409622358601851 124715709102614433537902777)
    ·
      refine ⟨93536781826960825153427083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124715709102614433537902777 93536781826960825153427083)
      ·
        refine ⟨140305172740441237730140625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93536781826960825153427083 140305172740441237730140625)
        ·
          refine ⟨105228879555330928297605469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140305172740441237730140625 105228879555330928297605469)
          ·
            refine ⟨39460829833249098111602051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105228879555330928297605469 39460829833249098111602051)
            ·
              refine ⟨59191244749873647167403077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39460829833249098111602051 59191244749873647167403077)
              ·
                refine ⟨11098358390601308843888077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59191244749873647167403077 11098358390601308843888077)
                ·
                  refine ⟨4161884396475490816458029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11098358390601308843888077 4161884396475490816458029)
                  ·
                    refine ⟨1560706648678309056171761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4161884396475490816458029 1560706648678309056171761)
                    ·
                      refine ⟨1170529986508731792128821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560706648678309056171761 1170529986508731792128821)
                      ·
                        rfl

theorem cell23_2279599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3, 2].length) (baseStart_2279599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279599 prefixEnd_2279599 := by exact prefixLift 2279599
  have htrace : WordTrace (prefixWord ++ tailWord_2279599) baseStart_2279599 baseEnd_2279599 := by
    simpa [prefixWord, tailWord_2279599, baseEnd_2279599] using wordTrace_append hprefix tailTrace_2279599
  have hstable : (prefixWord ++ tailWord_2279599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279599).length < 2 ^ (prefixWord ++ tailWord_2279599).sum := by decide
  have hdescent : baseEnd_2279599 < baseStart_2279599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279616 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2]
def baseStart_2279616 : Nat := 118140960795 + 2279616 * 2 ^ 59
def prefixEnd_2279616 : Nat := 4983230072969 + 3 ^ 40 * 2279616 * 2
def baseEnd_2279616 : Nat := 1170538715679858225616243

theorem tailTrace_2279616 : CollatzResearch.WordTrace tailWord_2279616 prefixEnd_2279616 1170538715679858225616243 := by
  unfold tailWord_2279616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41572213054674017130985351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55429617406232022841313801 41572213054674017130985351)
  ·
    refine ⟨62358319582011025696478027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41572213054674017130985351 62358319582011025696478027)
    ·
      refine ⟨93537479373016538544717041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62358319582011025696478027 93537479373016538544717041)
      ·
        refine ⟨70153109529762403908537781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93537479373016538544717041 70153109529762403908537781)
        ·
          refine ⟨6576854018415225366425417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70153109529762403908537781 6576854018415225366425417)
          ·
            refine ⟨4932640513811419024819063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6576854018415225366425417 4932640513811419024819063)
            ·
              refine ⟨7398960770717128537228595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932640513811419024819063 7398960770717128537228595)
              ·
                refine ⟨11098441156075692805842893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7398960770717128537228595 11098441156075692805842893)
                ·
                  refine ⟨4161915433528384802191085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11098441156075692805842893 4161915433528384802191085)
                  ·
                    refine ⟨1560718287573144300821657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4161915433528384802191085 1560718287573144300821657)
                    ·
                      refine ⟨1170538715679858225616243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560718287573144300821657 1170538715679858225616243)
                      ·
                        rfl

theorem cell23_2279616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_2279616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279616 prefixEnd_2279616 := by exact prefixLift 2279616
  have htrace : WordTrace (prefixWord ++ tailWord_2279616) baseStart_2279616 baseEnd_2279616 := by
    simpa [prefixWord, tailWord_2279616, baseEnd_2279616] using wordTrace_append hprefix tailTrace_2279616
  have hstable : (prefixWord ++ tailWord_2279616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279616).length < 2 ^ (prefixWord ++ tailWord_2279616).sum := by decide
  have hdescent : baseEnd_2279616 < baseStart_2279616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279632 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_2279632 : Nat := 118140960795 + 2279632 * 2 ^ 59
def prefixEnd_2279632 : Nat := 4983230072969 + 3 ^ 40 * 2279632 * 2
def baseEnd_2279632 : Nat := 1170546931370330163016169

theorem tailTrace_2279632 : CollatzResearch.WordTrace tailWord_2279632 prefixEnd_2279632 1170546931370330163016169 := by
  unfold tailWord_2279632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41572504838645034497276575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55430006451526712663035433 41572504838645034497276575)
  ·
    refine ⟨62358757257967551745914863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41572504838645034497276575 62358757257967551745914863)
    ·
      refine ⟨93538135886951327618872295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62358757257967551745914863 93538135886951327618872295)
      ·
        refine ⟨140307203830426991428308443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93538135886951327618872295 140307203830426991428308443)
        ·
          refine ⟨210460805745640487142462665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140307203830426991428308443 210460805745640487142462665)
          ·
            refine ⟨157845604309230365356846999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210460805745640487142462665 157845604309230365356846999)
            ·
              refine ⟨236768406463845548035270499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157845604309230365356846999 236768406463845548035270499)
              ·
                refine ⟨355152609695768322052905749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236768406463845548035270499 355152609695768322052905749)
                ·
                  refine ⟨16647778579489140096229957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 355152609695768322052905749 16647778579489140096229957)
                  ·
                    refine ⟨3121458483654213768043117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16647778579489140096229957 3121458483654213768043117)
                    ·
                      refine ⟨1170546931370330163016169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121458483654213768043117 1170546931370330163016169)
                      ·
                        rfl

theorem cell23_2279632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_2279632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279632 prefixEnd_2279632 := by exact prefixLift 2279632
  have htrace : WordTrace (prefixWord ++ tailWord_2279632) baseStart_2279632 baseEnd_2279632 := by
    simpa [prefixWord, tailWord_2279632, baseEnd_2279632] using wordTrace_append hprefix tailTrace_2279632
  have hstable : (prefixWord ++ tailWord_2279632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279632).length < 2 ^ (prefixWord ++ tailWord_2279632).sum := by decide
  have hdescent : baseEnd_2279632 < baseStart_2279632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279652 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 7]
def baseStart_2279652 : Nat := 118140960795 + 2279652 * 2 ^ 59
def prefixEnd_2279652 : Nat := 4983230072969 + 3 ^ 40 * 2279652 * 2
def baseEnd_2279652 : Nat := 130061911220380009418453

theorem tailTrace_2279652 : CollatzResearch.WordTrace tailWord_2279652 prefixEnd_2279652 130061911220380009418453 := by
  unfold tailWord_2279652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41572869568608806205140605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55430492758145074940187473 41572869568608806205140605)
  ·
    refine ⟨15589826088228302326927727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41572869568608806205140605 15589826088228302326927727)
    ·
      refine ⟨23384739132342453490391591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15589826088228302326927727 23384739132342453490391591)
      ·
        refine ⟨35077108698513680235587387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23384739132342453490391591 35077108698513680235587387)
        ·
          refine ⟨52615663047770520353381081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35077108698513680235587387 52615663047770520353381081)
          ·
            refine ⟨39461747285827890265035811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52615663047770520353381081 39461747285827890265035811)
            ·
              refine ⟨59192620928741835397553717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39461747285827890265035811 59192620928741835397553717)
              ·
                refine ⟨5549308212069547068520661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59192620928741835397553717 5549308212069547068520661)
                ·
                  refine ⟨130061911220380009418453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5549308212069547068520661 130061911220380009418453)
                  ·
                    rfl

theorem cell23_2279652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_2279652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279652 prefixEnd_2279652 := by exact prefixLift 2279652
  have htrace : WordTrace (prefixWord ++ tailWord_2279652) baseStart_2279652 baseEnd_2279652 := by
    simpa [prefixWord, tailWord_2279652, baseEnd_2279652] using wordTrace_append hprefix tailTrace_2279652
  have hstable : (prefixWord ++ tailWord_2279652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279652).length < 2 ^ (prefixWord ++ tailWord_2279652).sum := by decide
  have hdescent : baseEnd_2279652 < baseStart_2279652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279663 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 2, 2, 2]
def baseStart_2279663 : Nat := 118140960795 + 2279663 * 2 ^ 59
def prefixEnd_2279663 : Nat := 4983230072969 + 3 ^ 40 * 2279663 * 2
def baseEnd_2279663 : Nat := 1170562849270619541728527

theorem tailTrace_2279663 : CollatzResearch.WordTrace tailWord_2279663 prefixEnd_2279663 1170562849270619541728527 := by
  unfold tailWord_2279663
  simp only [CollatzResearch.WordTrace]
  refine ⟨83146140340177761288931643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55430760226785174192621095 83146140340177761288931643)
  ·
    refine ⟨124719210510266641933397465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83146140340177761288931643 124719210510266641933397465)
    ·
      refine ⟨93539407882699981450048099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124719210510266641933397465 93539407882699981450048099)
      ·
        refine ⟨140309111824049972175072149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93539407882699981450048099 140309111824049972175072149)
        ·
          refine ⟨6576989616752342445706507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140309111824049972175072149 6576989616752342445706507)
          ·
            refine ⟨9865484425128513668559761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6576989616752342445706507 9865484425128513668559761)
            ·
              refine ⟨7399113318846385251419821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9865484425128513668559761 7399113318846385251419821)
              ·
                refine ⟨2774667494567394469282433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7399113318846385251419821 2774667494567394469282433)
                ·
                  refine ⟨2081000620925545851961825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2774667494567394469282433 2081000620925545851961825)
                  ·
                    refine ⟨1560750465694159388971369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081000620925545851961825 1560750465694159388971369)
                    ·
                      refine ⟨1170562849270619541728527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560750465694159388971369 1170562849270619541728527)
                      ·
                        rfl

theorem cell23_2279663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2, 2].length) (baseStart_2279663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279663 prefixEnd_2279663 := by exact prefixLift 2279663
  have htrace : WordTrace (prefixWord ++ tailWord_2279663) baseStart_2279663 baseEnd_2279663 := by
    simpa [prefixWord, tailWord_2279663, baseEnd_2279663] using wordTrace_append hprefix tailTrace_2279663
  have hstable : (prefixWord ++ tailWord_2279663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279663).length < 2 ^ (prefixWord ++ tailWord_2279663).sum := by decide
  have hdescent : baseEnd_2279663 < baseStart_2279663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279756 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2279756 : Nat := 118140960795 + 2279756 * 2 ^ 59
def prefixEnd_2279756 : Nat := 4983230072969 + 3 ^ 40 * 2279756 * 2
def baseEnd_2279756 : Nat := 1170610602971487677865599

theorem tailTrace_2279756 : CollatzResearch.WordTrace tailWord_2279756 prefixEnd_2279756 1170610602971487677865599 := by
  unfold tailWord_2279756
  simp only [CollatzResearch.WordTrace]
  refine ⟨41574766164420419086033561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55433021552560558781378081 41574766164420419086033561)
  ·
    refine ⟨31181074623315314314525171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41574766164420419086033561 31181074623315314314525171)
    ·
      refine ⟨46771611934972971471787757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31181074623315314314525171 46771611934972971471787757)
      ·
        refine ⟨17539354475614864301920409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46771611934972971471787757 17539354475614864301920409)
        ·
          refine ⟨13154515856711148226440307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17539354475614864301920409 13154515856711148226440307)
          ·
            refine ⟨19731773785066722339660461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154515856711148226440307 19731773785066722339660461)
            ·
              refine ⟨7399415169400020877372673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19731773785066722339660461 7399415169400020877372673)
              ·
                refine ⟨5549561377050015658029505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7399415169400020877372673 5549561377050015658029505)
                ·
                  refine ⟨4162171032787511743522129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549561377050015658029505 4162171032787511743522129)
                  ·
                    refine ⟨3121628274590633807641597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4162171032787511743522129 3121628274590633807641597)
                    ·
                      refine ⟨1170610602971487677865599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121628274590633807641597 1170610602971487677865599)
                      ·
                        rfl

theorem cell23_2279756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2279756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279756 prefixEnd_2279756 := by exact prefixLift 2279756
  have htrace : WordTrace (prefixWord ++ tailWord_2279756) baseStart_2279756 baseEnd_2279756 := by
    simpa [prefixWord, tailWord_2279756, baseEnd_2279756] using wordTrace_append hprefix tailTrace_2279756
  have hstable : (prefixWord ++ tailWord_2279756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279756).length < 2 ^ (prefixWord ++ tailWord_2279756).sum := by decide
  have hdescent : baseEnd_2279756 < baseStart_2279756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279776 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 6]
def baseStart_2279776 : Nat := 118140960795 + 2279776 * 2 ^ 59
def prefixEnd_2279776 : Nat := 4983230072969 + 3 ^ 40 * 2279776 * 2
def baseEnd_2279776 : Nat := 130068985842730844401723

theorem tailTrace_2279776 : CollatzResearch.WordTrace tailWord_2279776 prefixEnd_2279776 130068985842730844401723 := by
  unfold tailWord_2279776
  simp only [CollatzResearch.WordTrace]
  refine ⟨41575130894384190793897591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55433507859178921058530121 41575130894384190793897591)
  ·
    refine ⟨62362696341576286190846387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41575130894384190793897591 62362696341576286190846387)
    ·
      refine ⟨93544044512364429286269581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62362696341576286190846387 93544044512364429286269581)
      ·
        refine ⟨35079016692136660982351093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93544044512364429286269581 35079016692136660982351093)
        ·
          refine ⟨3288657814887811967095415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35079016692136660982351093 3288657814887811967095415)
          ·
            refine ⟨4932986722331717950643123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288657814887811967095415 4932986722331717950643123)
            ·
              refine ⟨7399480083497576925964685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932986722331717950643123 7399480083497576925964685)
              ·
                refine ⟨2774805031311591347236757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7399480083497576925964685 2774805031311591347236757)
                ·
                  refine ⟨130068985842730844401723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2774805031311591347236757 130068985842730844401723)
                  ·
                    rfl

theorem cell23_2279776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_2279776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279776 prefixEnd_2279776 := by exact prefixLift 2279776
  have htrace : WordTrace (prefixWord ++ tailWord_2279776) baseStart_2279776 baseEnd_2279776 := by
    simpa [prefixWord, tailWord_2279776, baseEnd_2279776] using wordTrace_append hprefix tailTrace_2279776
  have hstable : (prefixWord ++ tailWord_2279776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279776).length < 2 ^ (prefixWord ++ tailWord_2279776).sum := by decide
  have hdescent : baseEnd_2279776 < baseStart_2279776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279810 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2279810 : Nat := 118140960795 + 2279810 * 2 ^ 59
def prefixEnd_2279810 : Nat := 4983230072969 + 3 ^ 40 * 2279810 * 2
def baseEnd_2279810 : Nat := 130070925658536718510039

theorem tailTrace_2279810 : CollatzResearch.WordTrace tailWord_2279810 prefixEnd_2279810 130070925658536718510039 := by
  unfold tailWord_2279810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20787875467661301348633221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55434334580430136929688589 20787875467661301348633221)
  ·
    refine ⟨3897726650186494002868729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20787875467661301348633221 3897726650186494002868729)
    ·
      refine ⟨2923294987639870502151547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3897726650186494002868729 2923294987639870502151547)
      ·
        refine ⟨4384942481459805753227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2923294987639870502151547 4384942481459805753227321)
        ·
          refine ⟨3288706861094854314920491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384942481459805753227321 3288706861094854314920491)
          ·
            refine ⟨4933060291642281472380737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288706861094854314920491 4933060291642281472380737)
            ·
              refine ⟨3699795218731711104285553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933060291642281472380737 3699795218731711104285553)
              ·
                refine ⟨2774846414048783328214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699795218731711104285553 2774846414048783328214165)
                ·
                  refine ⟨130070925658536718510039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2774846414048783328214165 130070925658536718510039)
                  ·
                    rfl

theorem cell23_2279810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2279810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279810 prefixEnd_2279810 := by exact prefixLift 2279810
  have htrace : WordTrace (prefixWord ++ tailWord_2279810) baseStart_2279810 baseEnd_2279810 := by
    simpa [prefixWord, tailWord_2279810, baseEnd_2279810] using wordTrace_append hprefix tailTrace_2279810
  have hstable : (prefixWord ++ tailWord_2279810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279810).length < 2 ^ (prefixWord ++ tailWord_2279810).sum := by decide
  have hdescent : baseEnd_2279810 < baseStart_2279810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279820 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_2279820 : Nat := 118140960795 + 2279820 * 2 ^ 59
def prefixEnd_2279820 : Nat := 4983230072969 + 3 ^ 40 * 2279820 * 2
def baseEnd_2279820 : Nat := 1170643465733375427465305

theorem tailTrace_2279820 : CollatzResearch.WordTrace tailWord_2279820 prefixEnd_2279820 1170643465733375427465305 := by
  unfold tailWord_2279820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41575933300304488551198457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55434577733739318068264609 41575933300304488551198457)
  ·
    refine ⟨31181949975228366413398843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41575933300304488551198457 31181949975228366413398843)
    ·
      refine ⟨46772924962842549620098265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31181949975228366413398843 46772924962842549620098265)
      ·
        refine ⟨35079693722131912215073699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46772924962842549620098265 35079693722131912215073699)
        ·
          refine ⟨52619540583197868322610549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35079693722131912215073699 52619540583197868322610549)
          ·
            refine ⟨4933081929674800155244739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52619540583197868322610549 4933081929674800155244739)
            ·
              refine ⟨7399622894512200232867109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933081929674800155244739 7399622894512200232867109)
              ·
                refine ⟨1387429292721037543662583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7399622894512200232867109 1387429292721037543662583)
                ·
                  refine ⟨2081143939081556315493875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387429292721037543662583 2081143939081556315493875)
                  ·
                    refine ⟨3121715908622334473240813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2081143939081556315493875 3121715908622334473240813)
                    ·
                      refine ⟨1170643465733375427465305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121715908622334473240813 1170643465733375427465305)
                      ·
                        rfl

theorem cell23_2279820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_2279820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279820 prefixEnd_2279820 := by exact prefixLift 2279820
  have htrace : WordTrace (prefixWord ++ tailWord_2279820) baseStart_2279820 baseEnd_2279820 := by
    simpa [prefixWord, tailWord_2279820, baseEnd_2279820] using wordTrace_append hprefix tailTrace_2279820
  have hstable : (prefixWord ++ tailWord_2279820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279820).length < 2 ^ (prefixWord ++ tailWord_2279820).sum := by decide
  have hdescent : baseEnd_2279820 < baseStart_2279820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2279829 : Nat := 118140960795 + 2279829 * 2 ^ 59
def prefixEnd_2279829 : Nat := 4983230072969 + 3 ^ 40 * 2279829 * 2
def baseEnd_2279829 : Nat := 1170648087059265892252763

theorem tailTrace_2279829 : CollatzResearch.WordTrace tailWord_2279829 prefixEnd_2279829 1170648087059265892252763 := by
  unfold tailWord_2279829
  simp only [CollatzResearch.WordTrace]
  refine ⟨83152194857576371639474541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55434796571717581092983027 83152194857576371639474541)
  ·
    refine ⟨31182073071591139364802953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83152194857576371639474541 31182073071591139364802953)
    ·
      refine ⟨23386554803693354523602215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31182073071591139364802953 23386554803693354523602215)
      ·
        refine ⟨35079832205540031785403323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23386554803693354523602215 35079832205540031785403323)
        ·
          refine ⟨52619748308310047678104985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35079832205540031785403323 52619748308310047678104985)
          ·
            refine ⟨39464811231232535758578739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52619748308310047678104985 39464811231232535758578739)
            ·
              refine ⟨59197216846848803637868109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39464811231232535758578739 59197216846848803637868109)
              ·
                refine ⟨22198956317568301364200541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59197216846848803637868109 22198956317568301364200541)
                ·
                  refine ⟨8324608619088113011575203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22198956317568301364200541 8324608619088113011575203)
                  ·
                    refine ⟨12486912928632169517362805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8324608619088113011575203 12486912928632169517362805)
                    ·
                      refine ⟨1170648087059265892252763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12486912928632169517362805 1170648087059265892252763)
                      ·
                        rfl

theorem cell23_2279829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2279829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279829 prefixEnd_2279829 := by exact prefixLift 2279829
  have htrace : WordTrace (prefixWord ++ tailWord_2279829) baseStart_2279829 baseEnd_2279829 := by
    simpa [prefixWord, tailWord_2279829, baseEnd_2279829] using wordTrace_append hprefix tailTrace_2279829
  have hstable : (prefixWord ++ tailWord_2279829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279829).length < 2 ^ (prefixWord ++ tailWord_2279829).sum := by decide
  have hdescent : baseEnd_2279829 < baseStart_2279829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279843 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 5, 2, 2]
def baseStart_2279843 : Nat := 118140960795 + 2279843 * 2 ^ 59
def prefixEnd_2279843 : Nat := 4983230072969 + 3 ^ 40 * 2279843 * 2
def baseEnd_2279843 : Nat := 1170655275788428837477699

theorem tailTrace_2279843 : CollatzResearch.WordTrace tailWord_2279843 prefixEnd_2279843 1170655275788428837477699 := by
  unfold tailWord_2279843
  simp only [CollatzResearch.WordTrace]
  refine ⟨83152705479525652030484183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55435136986350434686989455 83152705479525652030484183)
  ·
    refine ⟨124729058219288478045726275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83152705479525652030484183 124729058219288478045726275)
    ·
      refine ⟨187093587328932717068589413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124729058219288478045726275 187093587328932717068589413)
      ·
        refine ⟨35080047624174884450360515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187093587328932717068589413 35080047624174884450360515)
        ·
          refine ⟨52620071436262326675540773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35080047624174884450360515 52620071436262326675540773)
          ·
            refine ⟨9866263394299186251663895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52620071436262326675540773 9866263394299186251663895)
            ·
              refine ⟨14799395091448779377495843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866263394299186251663895 14799395091448779377495843)
              ·
                refine ⟨22199092637173169066243765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14799395091448779377495843 22199092637173169066243765)
                ·
                  refine ⟨2081164934734984599960353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22199092637173169066243765 2081164934734984599960353)
                  ·
                    refine ⟨1560873701051238449970265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081164934734984599960353 1560873701051238449970265)
                    ·
                      refine ⟨1170655275788428837477699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560873701051238449970265 1170655275788428837477699)
                      ·
                        rfl

theorem cell23_2279843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_2279843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279843 prefixEnd_2279843 := by exact prefixLift 2279843
  have htrace : WordTrace (prefixWord ++ tailWord_2279843) baseStart_2279843 baseEnd_2279843 := by
    simpa [prefixWord, tailWord_2279843, baseEnd_2279843] using wordTrace_append hprefix tailTrace_2279843
  have hstable : (prefixWord ++ tailWord_2279843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279843).length < 2 ^ (prefixWord ++ tailWord_2279843).sum := by decide
  have hdescent : baseEnd_2279843 < baseStart_2279843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279863 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_2279863 : Nat := 118140960795 + 2279863 * 2 ^ 59
def prefixEnd_2279863 : Nat := 4983230072969 + 3 ^ 40 * 2279863 * 2
def baseEnd_2279863 : Nat := 1170665545401518759227607

theorem tailTrace_2279863 : CollatzResearch.WordTrace tailWord_2279863 prefixEnd_2279863 1170665545401518759227607 := by
  unfold tailWord_2279863
  simp only [CollatzResearch.WordTrace]
  refine ⟨83153434939453195446212243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55435623292968796964141495 83153434939453195446212243)
  ·
    refine ⟨124730152409179793169318365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83153434939453195446212243 124730152409179793169318365)
    ·
      refine ⟨46773807153442422438494387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124730152409179793169318365 46773807153442422438494387)
      ·
        refine ⟨70160710730163633657741581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46773807153442422438494387 70160710730163633657741581)
        ·
          refine ⟨26310266523811362621653093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70160710730163633657741581 26310266523811362621653093)
          ·
            refine ⟨4933174973214630491559955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26310266523811362621653093 4933174973214630491559955)
            ·
              refine ⟨7399762459821945737339933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933174973214630491559955 7399762459821945737339933)
              ·
                refine ⟨2774910922433229651502475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7399762459821945737339933 2774910922433229651502475)
                ·
                  refine ⟨4162366383649844477253713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774910922433229651502475 4162366383649844477253713)
                  ·
                    refine ⟨3121774787737383357940285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4162366383649844477253713 3121774787737383357940285)
                    ·
                      refine ⟨1170665545401518759227607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121774787737383357940285 1170665545401518759227607)
                      ·
                        rfl

theorem cell23_2279863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_2279863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279863 prefixEnd_2279863 := by exact prefixLift 2279863
  have htrace : WordTrace (prefixWord ++ tailWord_2279863) baseStart_2279863 baseEnd_2279863 := by
    simpa [prefixWord, tailWord_2279863, baseEnd_2279863] using wordTrace_append hprefix tailTrace_2279863
  have hstable : (prefixWord ++ tailWord_2279863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279863).length < 2 ^ (prefixWord ++ tailWord_2279863).sum := by decide
  have hdescent : baseEnd_2279863 < baseStart_2279863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279889 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2279889 : Nat := 118140960795 + 2279889 * 2 ^ 59
def prefixEnd_2279889 : Nat := 4983230072969 + 3 ^ 40 * 2279889 * 2
def baseEnd_2279889 : Nat := 1170678895898535657502487

theorem tailTrace_2279889 : CollatzResearch.WordTrace tailWord_2279889 prefixEnd_2279889 1170678895898535657502487 := by
  unfold tailWord_2279889
  simp only [CollatzResearch.WordTrace]
  refine ⟨83154383237359001886658721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55436255491572667924439147 83154383237359001886658721)
  ·
    refine ⟨62365787428019251414994041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83154383237359001886658721 62365787428019251414994041)
    ·
      refine ⟨46774340571014438561245531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62365787428019251414994041 46774340571014438561245531)
      ·
        refine ⟨70161510856521657841868297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46774340571014438561245531 70161510856521657841868297)
        ·
          refine ⟨52621133142391243381401223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70161510856521657841868297 52621133142391243381401223)
          ·
            refine ⟨78931699713586865072101835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52621133142391243381401223 78931699713586865072101835)
            ·
              refine ⟨118397549570380297608152753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78931699713586865072101835 118397549570380297608152753)
              ·
                refine ⟨88798162177785223206114565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118397549570380297608152753 88798162177785223206114565)
                ·
                  refine ⟨16649655408334729351146481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88798162177785223206114565 16649655408334729351146481)
                  ·
                    refine ⟨12487241556251047013359861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16649655408334729351146481 12487241556251047013359861)
                    ·
                      refine ⟨1170678895898535657502487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12487241556251047013359861 1170678895898535657502487)
                      ·
                        rfl

theorem cell23_2279889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2279889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279889 prefixEnd_2279889 := by exact prefixLift 2279889
  have htrace : WordTrace (prefixWord ++ tailWord_2279889) baseStart_2279889 baseEnd_2279889 := by
    simpa [prefixWord, tailWord_2279889, baseEnd_2279889] using wordTrace_append hprefix tailTrace_2279889
  have hstable : (prefixWord ++ tailWord_2279889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279889).length < 2 ^ (prefixWord ++ tailWord_2279889).sum := by decide
  have hdescent : baseEnd_2279889 < baseStart_2279889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279893 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2279893 : Nat := 118140960795 + 2279893 * 2 ^ 59
def prefixEnd_2279893 : Nat := 4983230072969 + 3 ^ 40 * 2279893 * 2
def baseEnd_2279893 : Nat := 1170680949821153641852469

theorem tailTrace_2279893 : CollatzResearch.WordTrace tailWord_2279893 prefixEnd_2279893 1170680949821153641852469 := by
  unfold tailWord_2279893
  simp only [CollatzResearch.WordTrace]
  refine ⟨83154529129344510569804333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55436352752896340379869555 83154529129344510569804333)
  ·
    refine ⟨31182948423504191463676625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83154529129344510569804333 31182948423504191463676625)
    ·
      refine ⟨23387211317628143597757469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31182948423504191463676625 23387211317628143597757469)
      ·
        refine ⟨8770204244110553849159051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23387211317628143597757469 8770204244110553849159051)
        ·
          refine ⟨13155306366165830773738577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8770204244110553849159051 13155306366165830773738577)
          ·
            refine ⟨9866479774624373080303933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13155306366165830773738577 9866479774624373080303933)
            ·
              refine ⟨3699929915484139905113975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9866479774624373080303933 3699929915484139905113975)
              ·
                refine ⟨5549894873226209857670963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699929915484139905113975 5549894873226209857670963)
                ·
                  refine ⟨8324842309839314786506445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549894873226209857670963 8324842309839314786506445)
                  ·
                    refine ⟨3121815866189743044939917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8324842309839314786506445 3121815866189743044939917)
                    ·
                      refine ⟨1170680949821153641852469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3121815866189743044939917 1170680949821153641852469)
                      ·
                        rfl

theorem cell23_2279893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2279893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279893 prefixEnd_2279893 := by exact prefixLift 2279893
  have htrace : WordTrace (prefixWord ++ tailWord_2279893) baseStart_2279893 baseEnd_2279893 := by
    simpa [prefixWord, tailWord_2279893, baseEnd_2279893] using wordTrace_append hprefix tailTrace_2279893
  have hstable : (prefixWord ++ tailWord_2279893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279893).length < 2 ^ (prefixWord ++ tailWord_2279893).sum := by decide
  have hdescent : baseEnd_2279893 < baseStart_2279893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279946 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2279946 : Nat := 118140960795 + 2279946 * 2 ^ 59
def prefixEnd_2279946 : Nat := 4983230072969 + 3 ^ 40 * 2279946 * 2
def baseEnd_2279946 : Nat := 1170708164295841934489725

theorem tailTrace_2279946 : CollatzResearch.WordTrace tailWord_2279946 prefixEnd_2279946 1170708164295841934489725 := by
  unfold tailWord_2279946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20789115549538125155370923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55437641465435000414322461 20789115549538125155370923)
  ·
    refine ⟨31183673324307187733056385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20789115549538125155370923 31183673324307187733056385)
    ·
      refine ⟨23387754993230390799792289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31183673324307187733056385 23387754993230390799792289)
      ·
        refine ⟨17540816244922793099844217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23387754993230390799792289 17540816244922793099844217)
        ·
          refine ⟨13155612183692094824883163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17540816244922793099844217 13155612183692094824883163)
          ·
            refine ⟨19733418275538142237324745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155612183692094824883163 19733418275538142237324745)
            ·
              refine ⟨14800063706653606677993559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19733418275538142237324745 14800063706653606677993559)
              ·
                refine ⟨22200095559980410016990339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800063706653606677993559 22200095559980410016990339)
                ·
                  refine ⟨33300143339970615025485509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22200095559980410016990339 33300143339970615025485509)
                  ·
                    refine ⟨6243776876244490317278533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33300143339970615025485509 6243776876244490317278533)
                    ·
                      refine ⟨1170708164295841934489725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6243776876244490317278533 1170708164295841934489725)
                      ·
                        rfl

theorem cell23_2279946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2279946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279946 prefixEnd_2279946 := by exact prefixLift 2279946
  have htrace : WordTrace (prefixWord ++ tailWord_2279946) baseStart_2279946 baseEnd_2279946 := by
    simpa [prefixWord, tailWord_2279946, baseEnd_2279946] using wordTrace_append hprefix tailTrace_2279946
  have hstable : (prefixWord ++ tailWord_2279946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279946).length < 2 ^ (prefixWord ++ tailWord_2279946).sum := by decide
  have hdescent : baseEnd_2279946 < baseStart_2279946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2279993 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2279993 : Nat := 118140960795 + 2279993 * 2 ^ 59
def prefixEnd_2279993 : Nat := 4983230072969 + 3 ^ 40 * 2279993 * 2
def baseEnd_2279993 : Nat := 1170732297886603250602009

theorem tailTrace_2279993 : CollatzResearch.WordTrace tailWord_2279993 prefixEnd_2279993 1170732297886603250602009 := by
  unfold tailWord_2279993
  simp only [CollatzResearch.WordTrace]
  refine ⟨83158176428982227648444633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55438784285988151765629755 83158176428982227648444633)
  ·
    refine ⟨62368632321736670736333475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83158176428982227648444633 62368632321736670736333475)
    ·
      refine ⟨93552948482605006104500213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62368632321736670736333475 93552948482605006104500213)
      ·
        refine ⟨8770588920244219322296895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93552948482605006104500213 8770588920244219322296895)
        ·
          refine ⟨13155883380366328983445343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8770588920244219322296895 13155883380366328983445343)
          ·
            refine ⟨19733825070549493475168015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155883380366328983445343 19733825070549493475168015)
            ·
              refine ⟨29600737605824240212752023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19733825070549493475168015 29600737605824240212752023)
              ·
                refine ⟨44401106408736360319128035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29600737605824240212752023 44401106408736360319128035)
                ·
                  refine ⟨66601659613104540478692053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44401106408736360319128035 66601659613104540478692053)
                  ·
                    refine ⟨1560976397182137667469345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66601659613104540478692053 1560976397182137667469345)
                    ·
                      refine ⟨1170732297886603250602009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560976397182137667469345 1170732297886603250602009)
                      ·
                        rfl

theorem cell23_2279993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2279993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2279993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2279993 prefixEnd_2279993 := by exact prefixLift 2279993
  have htrace : WordTrace (prefixWord ++ tailWord_2279993) baseStart_2279993 baseEnd_2279993 := by
    simpa [prefixWord, tailWord_2279993, baseEnd_2279993] using wordTrace_append hprefix tailTrace_2279993
  have hstable : (prefixWord ++ tailWord_2279993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2279993).length < 2 ^ (prefixWord ++ tailWord_2279993).sum := by decide
  have hdescent : baseEnd_2279993 < baseStart_2279993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2279993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280020 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2280020 : Nat := 118140960795 + 2280020 * 2 ^ 59
def prefixEnd_2280020 : Nat := 4983230072969 + 3 ^ 40 * 2280020 * 2
def baseEnd_2280020 : Nat := 390248720621424881654795

theorem tailTrace_2280020 : CollatzResearch.WordTrace tailWord_2280020 prefixEnd_2280020 390248720621424881654795 := by
  unfold tailWord_2280020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41579580599942205629838757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55439440799922940839785009 41579580599942205629838757)
  ·
    refine ⟨7796171362489163555594767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41579580599942205629838757 7796171362489163555594767)
    ·
      refine ⟨11694257043733745333392151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7796171362489163555594767 11694257043733745333392151)
      ·
        refine ⟨17541385565600618000088227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11694257043733745333392151 17541385565600618000088227)
        ·
          refine ⟨26312078348400927000132341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17541385565600618000088227 26312078348400927000132341)
          ·
            refine ⟨2466757345162586906262407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26312078348400927000132341 2466757345162586906262407)
            ·
              refine ⟨3700136017743880359393611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466757345162586906262407 3700136017743880359393611)
              ·
                refine ⟨5550204026615820539090417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700136017743880359393611 5550204026615820539090417)
                ·
                  refine ⟨4162653019961865404317813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550204026615820539090417 4162653019961865404317813)
                  ·
                    refine ⟨390248720621424881654795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4162653019961865404317813 390248720621424881654795)
                    ·
                      rfl

theorem cell23_2280020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2280020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280020 prefixEnd_2280020 := by exact prefixLift 2280020
  have htrace : WordTrace (prefixWord ++ tailWord_2280020) baseStart_2280020 baseEnd_2280020 := by
    simpa [prefixWord, tailWord_2280020, baseEnd_2280020] using wordTrace_append hprefix tailTrace_2280020
  have hstable : (prefixWord ++ tailWord_2280020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280020).length < 2 ^ (prefixWord ++ tailWord_2280020).sum := by decide
  have hdescent : baseEnd_2280020 < baseStart_2280020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280023 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_2280023 : Nat := 118140960795 + 2280023 * 2 ^ 59
def prefixEnd_2280023 : Nat := 4983230072969 + 3 ^ 40 * 2280023 * 2
def baseEnd_2280023 : Nat := 1170747702306238133226871

theorem tailTrace_2280023 : CollatzResearch.WordTrace tailWord_2280023 prefixEnd_2280023 1170747702306238133226871 := by
  unfold tailWord_2280023
  simp only [CollatzResearch.WordTrace]
  refine ⟨83159270618873542772036723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55439513745915695181357815 83159270618873542772036723)
  ·
    refine ⟨124738905928310314158055085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83159270618873542772036723 124738905928310314158055085)
    ·
      refine ⟨46777089723116367809270657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124738905928310314158055085 46777089723116367809270657)
      ·
        refine ⟨35082817292337275856952993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46777089723116367809270657 35082817292337275856952993)
        ·
          refine ⟨26312112969252956892714745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35082817292337275856952993 26312112969252956892714745)
          ·
            refine ⟨19734084726939717669536059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26312112969252956892714745 19734084726939717669536059)
            ·
              refine ⟨29601127090409576504304089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19734084726939717669536059 29601127090409576504304089)
              ·
                refine ⟨22200845317807182378228067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29601127090409576504304089 22200845317807182378228067)
                ·
                  refine ⟨33301267976710773567342101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22200845317807182378228067 33301267976710773567342101)
                  ·
                    refine ⟨1560996936408317510969161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33301267976710773567342101 1560996936408317510969161)
                    ·
                      refine ⟨1170747702306238133226871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1560996936408317510969161 1170747702306238133226871)
                      ·
                        rfl

theorem cell23_2280023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_2280023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280023 prefixEnd_2280023 := by exact prefixLift 2280023
  have htrace : WordTrace (prefixWord ++ tailWord_2280023) baseStart_2280023 baseEnd_2280023 := by
    simpa [prefixWord, tailWord_2280023, baseEnd_2280023] using wordTrace_append hprefix tailTrace_2280023
  have hstable : (prefixWord ++ tailWord_2280023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280023).length < 2 ^ (prefixWord ++ tailWord_2280023).sum := by decide
  have hdescent : baseEnd_2280023 < baseStart_2280023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280036 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_2280036 : Nat := 118140960795 + 2280036 * 2 ^ 59
def prefixEnd_2280036 : Nat := 4983230072969 + 3 ^ 40 * 2280036 * 2
def baseEnd_2280036 : Nat := 1170754377554746582364311

theorem tailTrace_2280036 : CollatzResearch.WordTrace tailWord_2280036 prefixEnd_2280036 1170754377554746582364311 := by
  unfold tailWord_2280036
  simp only [CollatzResearch.WordTrace]
  refine ⟨41579872383913222996129981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55439829845217630661506641 41579872383913222996129981)
  ·
    refine ⟨15592452143967458623548743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41579872383913222996129981 15592452143967458623548743)
    ·
      refine ⟨23388678215951187935323115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15592452143967458623548743 23388678215951187935323115)
      ·
        refine ⟨35083017323926781902984673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23388678215951187935323115 35083017323926781902984673)
        ·
          refine ⟨26312262992945086427238505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35083017323926781902984673 26312262992945086427238505)
          ·
            refine ⟨19734197244708814820428879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26312262992945086427238505 19734197244708814820428879)
            ·
              refine ⟨29601295867063222230643319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19734197244708814820428879 29601295867063222230643319)
              ·
                refine ⟨44401943800594833345964979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29601295867063222230643319 44401943800594833345964979)
                ·
                  refine ⟨66602915700892250018947469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44401943800594833345964979 66602915700892250018947469)
                  ·
                    refine ⟨24976093387834593757105301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66602915700892250018947469 24976093387834593757105301)
                    ·
                      refine ⟨1170754377554746582364311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24976093387834593757105301 1170754377554746582364311)
                      ·
                        rfl

theorem cell23_2280036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_2280036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280036 prefixEnd_2280036 := by exact prefixLift 2280036
  have htrace : WordTrace (prefixWord ++ tailWord_2280036) baseStart_2280036 baseEnd_2280036 := by
    simpa [prefixWord, tailWord_2280036, baseEnd_2280036] using wordTrace_append hprefix tailTrace_2280036
  have hstable : (prefixWord ++ tailWord_2280036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280036).length < 2 ^ (prefixWord ++ tailWord_2280036).sum := by decide
  have hdescent : baseEnd_2280036 < baseStart_2280036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280084 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2280084 : Nat := 118140960795 + 2280084 * 2 ^ 59
def prefixEnd_2280084 : Nat := 4983230072969 + 3 ^ 40 * 2280084 * 2
def baseEnd_2280084 : Nat := 390259674875387464854697

theorem tailTrace_2280084 : CollatzResearch.WordTrace tailWord_2280084 prefixEnd_2280084 390259674875387464854697 := by
  unfold tailWord_2280084
  simp only [CollatzResearch.WordTrace]
  refine ⟨41580747735826275095003653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55440996981101700126671537 41580747735826275095003653)
  ·
    refine ⟨7796390200467426580313185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41580747735826275095003653 7796390200467426580313185)
    ·
      refine ⟨5847292650350569935234889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7796390200467426580313185 5847292650350569935234889)
      ·
        refine ⟨4385469487762927451426167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5847292650350569935234889 4385469487762927451426167)
        ·
          refine ⟨6578204231644391177139251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385469487762927451426167 6578204231644391177139251)
          ·
            refine ⟨9867306347466586765708877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578204231644391177139251 9867306347466586765708877)
            ·
              refine ⟨3700239880299970037140829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9867306347466586765708877 3700239880299970037140829)
              ·
                refine ⟨1387589955112488763927811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3700239880299970037140829 1387589955112488763927811)
                ·
                  refine ⟨2081384932668733145891717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387589955112488763927811 2081384932668733145891717)
                  ·
                    refine ⟨390259674875387464854697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081384932668733145891717 390259674875387464854697)
                    ·
                      rfl

theorem cell23_2280084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2280084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280084 prefixEnd_2280084 := by exact prefixLift 2280084
  have htrace : WordTrace (prefixWord ++ tailWord_2280084) baseStart_2280084 baseEnd_2280084 := by
    simpa [prefixWord, tailWord_2280084, baseEnd_2280084] using wordTrace_append hprefix tailTrace_2280084
  have hstable : (prefixWord ++ tailWord_2280084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280084).length < 2 ^ (prefixWord ++ tailWord_2280084).sum := by decide
  have hdescent : baseEnd_2280084 < baseStart_2280084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280140 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_2280140 : Nat := 118140960795 + 2280140 * 2 ^ 59
def prefixEnd_2280140 : Nat := 4983230072969 + 3 ^ 40 * 2280140 * 2
def baseEnd_2280140 : Nat := 390269259847604725154611

theorem tailTrace_2280140 : CollatzResearch.WordTrace tailWord_2280140 prefixEnd_2280140 390269259847604725154611 := by
  unfold tailWord_2280140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41581768979724835877022937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55442358639633114502697249 41581768979724835877022937)
  ·
    refine ⟨31186326734793626907767203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41581768979724835877022937 31186326734793626907767203)
    ·
      refine ⟨46779490102190440361650805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31186326734793626907767203 46779490102190440361650805)
      ·
        refine ⟨4385577197080353783904763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46779490102190440361650805 4385577197080353783904763)
        ·
          refine ⟨6578365795620530675857145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385577197080353783904763 6578365795620530675857145)
          ·
            refine ⟨4933774346715398006892859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6578365795620530675857145 4933774346715398006892859)
            ·
              refine ⟨7400661520073097010339289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933774346715398006892859 7400661520073097010339289)
              ·
                refine ⟨5550496140054822757754467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7400661520073097010339289 5550496140054822757754467)
                ·
                  refine ⟨8325744210082234136631701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550496140054822757754467 8325744210082234136631701)
                  ·
                    refine ⟨390269259847604725154611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8325744210082234136631701 390269259847604725154611)
                    ·
                      rfl

theorem cell23_2280140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_2280140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280140 prefixEnd_2280140 := by exact prefixLift 2280140
  have htrace : WordTrace (prefixWord ++ tailWord_2280140) baseStart_2280140 baseEnd_2280140 := by
    simpa [prefixWord, tailWord_2280140, baseEnd_2280140] using wordTrace_append hprefix tailTrace_2280140
  have hstable : (prefixWord ++ tailWord_2280140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280140).length < 2 ^ (prefixWord ++ tailWord_2280140).sum := by decide
  have hdescent : baseEnd_2280140 < baseStart_2280140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280193 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2280193 : Nat := 118140960795 + 2280193 * 2 ^ 59
def prefixEnd_2280193 : Nat := 4983230072969 + 3 ^ 40 * 2280193 * 2
def baseEnd_2280193 : Nat := 1170834994017502468101089

theorem tailTrace_2280193 : CollatzResearch.WordTrace tailWord_2280193 prefixEnd_2280193 1170834994017502468101089 := by
  unfold tailWord_2280193
  simp only [CollatzResearch.WordTrace]
  refine ⟨83165471028257661805725233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55443647352171774537150155 83165471028257661805725233)
  ·
    refine ⟨62374103271193246354293925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83165471028257661805725233 62374103271193246354293925)
    ·
      refine ⟨11695144363348733691430111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62374103271193246354293925 11695144363348733691430111)
      ·
        refine ⟨17542716545023100537145167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11695144363348733691430111 17542716545023100537145167)
        ·
          refine ⟨26314074817534650805717751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17542716545023100537145167 26314074817534650805717751)
          ·
            refine ⟨39471112226301976208576627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26314074817534650805717751 39471112226301976208576627)
            ·
              refine ⟨59206668339452964312864941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39471112226301976208576627 59206668339452964312864941)
              ·
                refine ⟨22202500627294861617324353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59206668339452964312864941 22202500627294861617324353)
                ·
                  refine ⟨16651875470471146212993265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22202500627294861617324353 16651875470471146212993265)
                  ·
                    refine ⟨12488906602853359659744949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16651875470471146212993265 12488906602853359659744949)
                    ·
                      refine ⟨1170834994017502468101089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12488906602853359659744949 1170834994017502468101089)
                      ·
                        rfl

theorem cell23_2280193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2280193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280193 prefixEnd_2280193 := by exact prefixLift 2280193
  have htrace : WordTrace (prefixWord ++ tailWord_2280193) baseStart_2280193 baseEnd_2280193 := by
    simpa [prefixWord, tailWord_2280193, baseEnd_2280193] using wordTrace_append hprefix tailTrace_2280193
  have hstable : (prefixWord ++ tailWord_2280193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280193).length < 2 ^ (prefixWord ++ tailWord_2280193).sum := by decide
  have hdescent : baseEnd_2280193 < baseStart_2280193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280207 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 1, 3, 2]
def baseStart_2280207 : Nat := 118140960795 + 2280207 * 2 ^ 59
def prefixEnd_2280207 : Nat := 4983230072969 + 3 ^ 40 * 2280207 * 2
def baseEnd_2280207 : Nat := 1170842182746665413326025

theorem tailTrace_2280207 : CollatzResearch.WordTrace tailWord_2280207 prefixEnd_2280207 1170842182746665413326025 := by
  unfold tailWord_2280207
  simp only [CollatzResearch.WordTrace]
  refine ⟨83165981650206942196734875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55443987766804628131156583 83165981650206942196734875)
  ·
    refine ⟨124748972475310413295102313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83165981650206942196734875 124748972475310413295102313)
    ·
      refine ⟨93561729356482809971326735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124748972475310413295102313 93561729356482809971326735)
      ·
        refine ⟨140342594034724214956990103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93561729356482809971326735 140342594034724214956990103)
        ·
          refine ⟨210513891052086322435485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140342594034724214956990103 210513891052086322435485155)
          ·
            refine ⟨315770836578129483653227733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210513891052086322435485155 315770836578129483653227733)
            ·
              refine ⟨7400878982299909773122525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 315770836578129483653227733 7400878982299909773122525)
              ·
                refine ⟨2775329618362466164920947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7400878982299909773122525 2775329618362466164920947)
                ·
                  refine ⟨4162994427543699247381421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775329618362466164920947 4162994427543699247381421)
                  ·
                    refine ⟨1561122910328887217768033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4162994427543699247381421 1561122910328887217768033)
                    ·
                      refine ⟨1170842182746665413326025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561122910328887217768033 1170842182746665413326025)
                      ·
                        rfl

theorem cell23_2280207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 3, 2].length) (baseStart_2280207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280207 prefixEnd_2280207 := by exact prefixLift 2280207
  have htrace : WordTrace (prefixWord ++ tailWord_2280207) baseStart_2280207 baseEnd_2280207 := by
    simpa [prefixWord, tailWord_2280207, baseEnd_2280207] using wordTrace_append hprefix tailTrace_2280207
  have hstable : (prefixWord ++ tailWord_2280207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280207).length < 2 ^ (prefixWord ++ tailWord_2280207).sum := by decide
  have hdescent : baseEnd_2280207 < baseStart_2280207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280213 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2280213 : Nat := 118140960795 + 2280213 * 2 ^ 59
def prefixEnd_2280213 : Nat := 4983230072969 + 3 ^ 40 * 2280213 * 2
def baseEnd_2280213 : Nat := 390281754543530796616999

theorem tailTrace_2280213 : CollatzResearch.WordTrace tailWord_2280213 prefixEnd_2280213 390281754543530796616999 := by
  unfold tailWord_2280213
  simp only [CollatzResearch.WordTrace]
  refine ⟨83166200488185205221453293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55444133658790136814302195 83166200488185205221453293)
  ·
    refine ⟨31187325183069451958044985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83166200488185205221453293 31187325183069451958044985)
    ·
      refine ⟨23390493887302088968533739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31187325183069451958044985 23390493887302088968533739)
      ·
        refine ⟨35085740830953133452800609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23390493887302088968533739 35085740830953133452800609)
        ·
          refine ⟨26314305623214850089600457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35085740830953133452800609 26314305623214850089600457)
          ·
            refine ⟨19735729217411137567200343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26314305623214850089600457 19735729217411137567200343)
            ·
              refine ⟨29603593826116706350800515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19735729217411137567200343 29603593826116706350800515)
              ·
                refine ⟨44405390739175059526200773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29603593826116706350800515 44405390739175059526200773)
                ·
                  refine ⟨8326010763595323661162645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44405390739175059526200773 8326010763595323661162645)
                  ·
                    refine ⟨390281754543530796616999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8326010763595323661162645 390281754543530796616999)
                    ·
                      rfl

theorem cell23_2280213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2280213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280213 prefixEnd_2280213 := by exact prefixLift 2280213
  have htrace : WordTrace (prefixWord ++ tailWord_2280213) baseStart_2280213 baseEnd_2280213 := by
    simpa [prefixWord, tailWord_2280213, baseEnd_2280213] using wordTrace_append hprefix tailTrace_2280213
  have hstable : (prefixWord ++ tailWord_2280213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280213).length < 2 ^ (prefixWord ++ tailWord_2280213).sum := by decide
  have hdescent : baseEnd_2280213 < baseStart_2280213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280270 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_2280270 : Nat := 118140960795 + 2280270 * 2 ^ 59
def prefixEnd_2280270 : Nat := 4983230072969 + 3 ^ 40 * 2280270 * 2
def baseEnd_2280270 : Nat := 1170874532027898666838235

theorem tailTrace_2280270 : CollatzResearch.WordTrace tailWord_2280270 prefixEnd_2280270 1170874532027898666838235 := by
  unfold tailWord_2280270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10396034931122337994534783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55445519632652469304185509 10396034931122337994534783)
  ·
    refine ⟨15594052396683506991802175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10396034931122337994534783 15594052396683506991802175)
    ·
      refine ⟨23391078595025260487703263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15594052396683506991802175 23391078595025260487703263)
      ·
        refine ⟨35086617892537890731554895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23391078595025260487703263 35086617892537890731554895)
        ·
          refine ⟨52629926838806836097332343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35086617892537890731554895 52629926838806836097332343)
          ·
            refine ⟨78944890258210254145998515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52629926838806836097332343 78944890258210254145998515)
            ·
              refine ⟨118417335387315381218997773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78944890258210254145998515 118417335387315381218997773)
              ·
                refine ⟨44406500770243267957124165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118417335387315381218997773 44406500770243267957124165)
                ·
                  refine ⟨8326218894420612741960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44406500770243267957124165 8326218894420612741960781)
                  ·
                    refine ⟨3122332085407729778235293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8326218894420612741960781 3122332085407729778235293)
                    ·
                      refine ⟨1170874532027898666838235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122332085407729778235293 1170874532027898666838235)
                      ·
                        rfl

theorem cell23_2280270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_2280270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280270 prefixEnd_2280270 := by exact prefixLift 2280270
  have htrace : WordTrace (prefixWord ++ tailWord_2280270) baseStart_2280270 baseEnd_2280270 := by
    simpa [prefixWord, tailWord_2280270, baseEnd_2280270] using wordTrace_append hprefix tailTrace_2280270
  have hstable : (prefixWord ++ tailWord_2280270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280270).length < 2 ^ (prefixWord ++ tailWord_2280270).sum := by decide
  have hdescent : baseEnd_2280270 < baseStart_2280270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280303 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 8]
def baseStart_2280303 : Nat := 118140960795 + 2280303 * 2 ^ 59
def prefixEnd_2280303 : Nat := 4983230072969 + 3 ^ 40 * 2280303 * 2
def baseEnd_2280303 : Nat := 390297158963165679241861

theorem tailTrace_2280303 : CollatzResearch.WordTrace tailWord_2280303 prefixEnd_2280303 390297158963165679241861 := by
  unfold tailWord_2280303
  simp only [CollatzResearch.WordTrace]
  refine ⟨83169483057859150592229563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55446322038572767061486375 83169483057859150592229563)
  ·
    refine ⟨124754224586788725888344345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83169483057859150592229563 124754224586788725888344345)
    ·
      refine ⟨93565668440091544416258259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124754224586788725888344345 93565668440091544416258259)
      ·
        refine ⟨140348502660137316624387389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93565668440091544416258259 140348502660137316624387389)
        ·
          refine ⟨52630688497551493734145271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140348502660137316624387389 52630688497551493734145271)
          ·
            refine ⟨78946032746327240601217907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52630688497551493734145271 78946032746327240601217907)
            ·
              refine ⟨118419049119490860901826861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78946032746327240601217907 118419049119490860901826861)
              ·
                refine ⟨44407143419809072838185073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118419049119490860901826861 44407143419809072838185073)
                ·
                  refine ⟨33305357564856804628638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44407143419809072838185073 33305357564856804628638805)
                  ·
                    refine ⟨390297158963165679241861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33305357564856804628638805 390297158963165679241861)
                    ·
                      rfl

theorem cell23_2280303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_2280303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280303 prefixEnd_2280303 := by exact prefixLift 2280303
  have htrace : WordTrace (prefixWord ++ tailWord_2280303) baseStart_2280303 baseEnd_2280303 := by
    simpa [prefixWord, tailWord_2280303, baseEnd_2280303] using wordTrace_append hprefix tailTrace_2280303
  have hstable : (prefixWord ++ tailWord_2280303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280303).length < 2 ^ (prefixWord ++ tailWord_2280303).sum := by decide
  have hdescent : baseEnd_2280303 < baseStart_2280303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280320 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_2280320 : Nat := 118140960795 + 2280320 * 2 ^ 59
def prefixEnd_2280320 : Nat := 4983230072969 + 3 ^ 40 * 2280320 * 2
def baseEnd_2280320 : Nat := 390300068686874490404335

theorem tailTrace_2280320 : CollatzResearch.WordTrace tailWord_2280320 prefixEnd_2280320 390300068686874490404335 := by
  unfold tailWord_2280320
  simp only [CollatzResearch.WordTrace]
  refine ⟨41585051549398781247799207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55446735399198374997065609 41585051549398781247799207)
  ·
    refine ⟨62377577324098171871698811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41585051549398781247799207 62377577324098171871698811)
    ·
      refine ⟨93566365986147257807548217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62377577324098171871698811 93566365986147257807548217)
      ·
        refine ⟨70174774489610443355661163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93566365986147257807548217 70174774489610443355661163)
        ·
          refine ⟨105262161734415665033491745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70174774489610443355661163 105262161734415665033491745)
          ·
            refine ⟨78946621300811748775118809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105262161734415665033491745 78946621300811748775118809)
            ·
              refine ⟨59209965975608811581339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78946621300811748775118809 59209965975608811581339107)
              ·
                refine ⟨88814948963413217372008661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59209965975608811581339107 88814948963413217372008661)
                ·
                  refine ⟨2081600366329997282156453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88814948963413217372008661 2081600366329997282156453)
                  ·
                    refine ⟨390300068686874490404335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081600366329997282156453 390300068686874490404335)
                    ·
                      rfl

theorem cell23_2280320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_2280320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280320 prefixEnd_2280320 := by exact prefixLift 2280320
  have htrace : WordTrace (prefixWord ++ tailWord_2280320) baseStart_2280320 baseEnd_2280320 := by
    simpa [prefixWord, tailWord_2280320, baseEnd_2280320] using wordTrace_append hprefix tailTrace_2280320
  have hstable : (prefixWord ++ tailWord_2280320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280320).length < 2 ^ (prefixWord ++ tailWord_2280320).sum := by decide
  have hdescent : baseEnd_2280320 < baseStart_2280320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280327 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2280327 : Nat := 118140960795 + 2280327 * 2 ^ 59
def prefixEnd_2280327 : Nat := 4983230072969 + 3 ^ 40 * 2280327 * 2
def baseEnd_2280327 : Nat := 1170903800425204943825473

theorem tailTrace_2280327 : CollatzResearch.WordTrace tailWord_2280327 prefixEnd_2280327 1170903800425204943825473 := by
  unfold tailWord_2280327
  simp only [CollatzResearch.WordTrace]
  refine ⟨83170358409772202691103235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55446905606514801794068823 83170358409772202691103235)
  ·
    refine ⟨124755537614658304036654853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83170358409772202691103235 124755537614658304036654853)
    ·
      refine ⟨23391663302748432006872785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124755537614658304036654853 23391663302748432006872785)
      ·
        refine ⟨17543747477061324005154589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23391663302748432006872785 17543747477061324005154589)
        ·
          refine ⟨6578905303897996501932971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17543747477061324005154589 6578905303897996501932971)
          ·
            refine ⟨9868357955846994752899457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578905303897996501932971 9868357955846994752899457)
            ·
              refine ⟨7401268466885246064674593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9868357955846994752899457 7401268466885246064674593)
              ·
                refine ⟨5550951350163934548505945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7401268466885246064674593 5550951350163934548505945)
                ·
                  refine ⟨4163213512622950911379459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550951350163934548505945 4163213512622950911379459)
                  ·
                    refine ⟨6244820268934426367069189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163213512622950911379459 6244820268934426367069189)
                    ·
                      refine ⟨1170903800425204943825473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6244820268934426367069189 1170903800425204943825473)
                      ·
                        rfl

theorem cell23_2280327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2280327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280327 prefixEnd_2280327 := by exact prefixLift 2280327
  have htrace : WordTrace (prefixWord ++ tailWord_2280327) baseStart_2280327 baseEnd_2280327 := by
    simpa [prefixWord, tailWord_2280327, baseEnd_2280327] using wordTrace_append hprefix tailTrace_2280327
  have hstable : (prefixWord ++ tailWord_2280327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280327).length < 2 ^ (prefixWord ++ tailWord_2280327).sum := by decide
  have hdescent : baseEnd_2280327 < baseStart_2280327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280354 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2280354 : Nat := 118140960795 + 2280354 * 2 ^ 59
def prefixEnd_2280354 : Nat := 4983230072969 + 3 ^ 40 * 2280354 * 2
def baseEnd_2280354 : Nat := 390305888134292112729283

theorem tailTrace_2280354 : CollatzResearch.WordTrace tailWord_2280354 prefixEnd_2280354 390305888134292112729283 := by
  unfold tailWord_2280354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792835795168596575584029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55447562120449590868224077 20792835795168596575584029)
  ·
    refine ⟨7797313423188223715844011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20792835795168596575584029 7797313423188223715844011)
    ·
      refine ⟨11695970134782335573766017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7797313423188223715844011 11695970134782335573766017)
      ·
        refine ⟨8771977601086751680324513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11695970134782335573766017 8771977601086751680324513)
        ·
          refine ⟨6578983200815063760243385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8771977601086751680324513 6578983200815063760243385)
          ·
            refine ⟨4934237400611297820182539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6578983200815063760243385 4934237400611297820182539)
            ·
              refine ⟨7401356100916946730273809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934237400611297820182539 7401356100916946730273809)
              ·
                refine ⟨5551017075687710047705357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7401356100916946730273809 5551017075687710047705357)
                ·
                  refine ⟨2081631403382891267889509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5551017075687710047705357 2081631403382891267889509)
                  ·
                    refine ⟨390305888134292112729283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081631403382891267889509 390305888134292112729283)
                    ·
                      rfl

theorem cell23_2280354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2280354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280354 prefixEnd_2280354 := by exact prefixLift 2280354
  have htrace : WordTrace (prefixWord ++ tailWord_2280354) baseStart_2280354 baseEnd_2280354 := by
    simpa [prefixWord, tailWord_2280354, baseEnd_2280354] using wordTrace_append hprefix tailTrace_2280354
  have hstable : (prefixWord ++ tailWord_2280354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280354).length < 2 ^ (prefixWord ++ tailWord_2280354).sum := by decide
  have hdescent : baseEnd_2280354 < baseStart_2280354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280404 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2280404 : Nat := 118140960795 + 2280404 * 2 ^ 59
def prefixEnd_2280404 : Nat := 4983230072969 + 3 ^ 40 * 2280404 * 2
def baseEnd_2280404 : Nat := 1170943338435601142562619

theorem tailTrace_2280404 : CollatzResearch.WordTrace tailWord_2280404 prefixEnd_2280404 1170943338435601142562619 := by
  unfold tailWord_2280404
  simp only [CollatzResearch.WordTrace]
  refine ⟨41586583415246622420828133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55448777886995496561104177 41586583415246622420828133)
  ·
    refine ⟨7797484390358741703905275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41586583415246622420828133 7797484390358741703905275)
    ·
      refine ⟨11696226585538112555857913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7797484390358741703905275 11696226585538112555857913)
      ·
        refine ⟨8772169939153584416893435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11696226585538112555857913 8772169939153584416893435)
        ·
          refine ⟨13158254908730376625340153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772169939153584416893435 13158254908730376625340153)
          ·
            refine ⟨9868691181547782469005115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13158254908730376625340153 9868691181547782469005115)
            ·
              refine ⟨14803036772321673703507673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868691181547782469005115 14803036772321673703507673)
              ·
                refine ⟨11102277579241255277630755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14803036772321673703507673 11102277579241255277630755)
                ·
                  refine ⟨16653416368861882916446133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11102277579241255277630755 16653416368861882916446133)
                  ·
                    refine ⟨1561257784580801523416825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16653416368861882916446133 1561257784580801523416825)
                    ·
                      refine ⟨1170943338435601142562619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561257784580801523416825 1170943338435601142562619)
                      ·
                        rfl

theorem cell23_2280404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2280404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280404 prefixEnd_2280404 := by exact prefixLift 2280404
  have htrace : WordTrace (prefixWord ++ tailWord_2280404) baseStart_2280404 baseEnd_2280404 := by
    simpa [prefixWord, tailWord_2280404, baseEnd_2280404] using wordTrace_append hprefix tailTrace_2280404
  have hstable : (prefixWord ++ tailWord_2280404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280404).length < 2 ^ (prefixWord ++ tailWord_2280404).sum := by decide
  have hdescent : baseEnd_2280404 < baseStart_2280404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280417 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_2280417 : Nat := 118140960795 + 2280417 * 2 ^ 59
def prefixEnd_2280417 : Nat := 4983230072969 + 3 ^ 40 * 2280417 * 2
def baseEnd_2280417 : Nat := 1170950013684109591700059

theorem tailTrace_2280417 : CollatzResearch.WordTrace tailWord_2280417 prefixEnd_2280417 1170950013684109591700059 := by
  unfold tailWord_2280417
  simp only [CollatzResearch.WordTrace]
  refine ⟨83173640979446148061879505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55449093986297432041253003 83173640979446148061879505)
  ·
    refine ⟨62380230734584611046409629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83173640979446148061879505 62380230734584611046409629)
    ·
      refine ⟨23392586525469229142403611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62380230734584611046409629 23392586525469229142403611)
      ·
        refine ⟨35088879788203843713605417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23392586525469229142403611 35088879788203843713605417)
        ·
          refine ⟨26316659841152882785204063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35088879788203843713605417 26316659841152882785204063)
          ·
            refine ⟨39474989761729324177806095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26316659841152882785204063 39474989761729324177806095)
            ·
              refine ⟨59212484642593986266709143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39474989761729324177806095 59212484642593986266709143)
              ·
                refine ⟨88818726963890979400063715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59212484642593986266709143 88818726963890979400063715)
                ·
                  refine ⟨133228090445836469100095573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88818726963890979400063715 133228090445836469100095573)
                  ·
                    refine ⟨1561266684912146122266745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 133228090445836469100095573 1561266684912146122266745)
                    ·
                      refine ⟨1170950013684109591700059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561266684912146122266745 1170950013684109591700059)
                      ·
                        rfl

theorem cell23_2280417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_2280417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280417 prefixEnd_2280417 := by exact prefixLift 2280417
  have htrace : WordTrace (prefixWord ++ tailWord_2280417) baseStart_2280417 baseEnd_2280417 := by
    simpa [prefixWord, tailWord_2280417, baseEnd_2280417] using wordTrace_append hprefix tailTrace_2280417
  have hstable : (prefixWord ++ tailWord_2280417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280417).length < 2 ^ (prefixWord ++ tailWord_2280417).sum := by decide
  have hdescent : baseEnd_2280417 < baseStart_2280417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280467 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3]
def baseStart_2280467 : Nat := 118140960795 + 2280467 * 2 ^ 59
def prefixEnd_2280467 : Nat := 4983230072969 + 3 ^ 40 * 2280467 * 2
def baseEnd_2280467 : Nat := 1170975687716834396074829

theorem tailTrace_2280467 : CollatzResearch.WordTrace tailWord_2280467 prefixEnd_2280467 1170975687716834396074829 := by
  unfold tailWord_2280467
  simp only [CollatzResearch.WordTrace]
  refine ⟨83175464629265006601199655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55450309752843337734133103 83175464629265006601199655)
  ·
    refine ⟨124763196943897509901799483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83175464629265006601199655 124763196943897509901799483)
    ·
      refine ⟨187144795415846264852699225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124763196943897509901799483 187144795415846264852699225)
      ·
        refine ⟨140358596561884698639524419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187144795415846264852699225 140358596561884698639524419)
        ·
          refine ⟨210537894842827047959286629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140358596561884698639524419 210537894842827047959286629)
          ·
            refine ⟨39475855283030071492366243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210537894842827047959286629 39475855283030071492366243)
            ·
              refine ⟨59213782924545107238549365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39475855283030071492366243 59213782924545107238549365)
              ·
                refine ⟨5551292149176103803614003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59213782924545107238549365 5551292149176103803614003)
                ·
                  refine ⟨8326938223764155705421005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5551292149176103803614003 8326938223764155705421005)
                  ·
                    refine ⟨3122601833911558389532877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8326938223764155705421005 3122601833911558389532877)
                    ·
                      refine ⟨1170975687716834396074829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122601833911558389532877 1170975687716834396074829)
                      ·
                        rfl

theorem cell23_2280467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_2280467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280467 prefixEnd_2280467 := by exact prefixLift 2280467
  have htrace : WordTrace (prefixWord ++ tailWord_2280467) baseStart_2280467 baseEnd_2280467 := by
    simpa [prefixWord, tailWord_2280467, baseEnd_2280467] using wordTrace_append hprefix tailTrace_2280467
  have hstable : (prefixWord ++ tailWord_2280467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280467).length < 2 ^ (prefixWord ++ tailWord_2280467).sum := by decide
  have hdescent : baseEnd_2280467 < baseStart_2280467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280471 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2280471 : Nat := 118140960795 + 2280471 * 2 ^ 59
def prefixEnd_2280471 : Nat := 4983230072969 + 3 ^ 40 * 2280471 * 2
def baseEnd_2280471 : Nat := 1170977741639452380424811

theorem tailTrace_2280471 : CollatzResearch.WordTrace tailWord_2280471 prefixEnd_2280471 1170977741639452380424811 := by
  unfold tailWord_2280471
  simp only [CollatzResearch.WordTrace]
  refine ⟨83175610521250515284345267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55450407014167010189563511 83175610521250515284345267)
  ·
    refine ⟨124763415781875772926517901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83175610521250515284345267 124763415781875772926517901)
    ·
      refine ⟨46786280918203414847444213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124763415781875772926517901 46786280918203414847444213)
      ·
        refine ⟨4386213836081570141947895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46786280918203414847444213 4386213836081570141947895)
        ·
          refine ⟨6579320754122355212921843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386213836081570141947895 6579320754122355212921843)
          ·
            refine ⟨9868981131183532819382765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579320754122355212921843 9868981131183532819382765)
            ·
              refine ⟨3700867924193824807268537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9868981131183532819382765 3700867924193824807268537)
              ·
                refine ⟨2775650943145368605451403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700867924193824807268537 2775650943145368605451403)
                ·
                  refine ⟨4163476414718052908177105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775650943145368605451403 4163476414718052908177105)
                  ·
                    refine ⟨3122607311038539681132829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163476414718052908177105 3122607311038539681132829)
                    ·
                      refine ⟨1170977741639452380424811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122607311038539681132829 1170977741639452380424811)
                      ·
                        rfl

theorem cell23_2280471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2280471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280471 prefixEnd_2280471 := by exact prefixLift 2280471
  have htrace : WordTrace (prefixWord ++ tailWord_2280471) baseStart_2280471 baseEnd_2280471 := by
    simpa [prefixWord, tailWord_2280471, baseEnd_2280471] using wordTrace_append hprefix tailTrace_2280471
  have hstable : (prefixWord ++ tailWord_2280471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280471).length < 2 ^ (prefixWord ++ tailWord_2280471).sum := by decide
  have hdescent : baseEnd_2280471 < baseStart_2280471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280484 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2280484 : Nat := 118140960795 + 2280484 * 2 ^ 59
def prefixEnd_2280484 : Nat := 4983230072969 + 3 ^ 40 * 2280484 * 2
def baseEnd_2280484 : Nat := 1170984416887960829562251

theorem tailTrace_2280484 : CollatzResearch.WordTrace tailWord_2280484 prefixEnd_2280484 1170984416887960829562251 := by
  unfold tailWord_2280484
  simp only [CollatzResearch.WordTrace]
  refine ⟨41588042335101709252284253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55450723113468945669712337 41588042335101709252284253)
  ·
    refine ⟨15595515875663140969606595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41588042335101709252284253 15595515875663140969606595)
    ·
      refine ⟨23393273813494711454409893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15595515875663140969606595 23393273813494711454409893)
      ·
        refine ⟨4386238840030258397701855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23393273813494711454409893 4386238840030258397701855)
        ·
          refine ⟨6579358260045387596552783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386238840030258397701855 6579358260045387596552783)
          ·
            refine ⟨9869037390068081394829175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579358260045387596552783 9869037390068081394829175)
            ·
              refine ⟨14803556085102122092243763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9869037390068081394829175 14803556085102122092243763)
              ·
                refine ⟨22205334127653183138365645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14803556085102122092243763 22205334127653183138365645)
                ·
                  refine ⟨8327000297869943676887117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22205334127653183138365645 8327000297869943676887117)
                  ·
                    refine ⟨3122625111701228878832669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8327000297869943676887117 3122625111701228878832669)
                    ·
                      refine ⟨1170984416887960829562251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122625111701228878832669 1170984416887960829562251)
                      ·
                        rfl

theorem cell23_2280484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2280484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280484 prefixEnd_2280484 := by exact prefixLift 2280484
  have htrace : WordTrace (prefixWord ++ tailWord_2280484) baseStart_2280484 baseEnd_2280484 := by
    simpa [prefixWord, tailWord_2280484, baseEnd_2280484] using wordTrace_append hprefix tailTrace_2280484
  have hstable : (prefixWord ++ tailWord_2280484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280484).length < 2 ^ (prefixWord ++ tailWord_2280484).sum := by decide
  have hdescent : baseEnd_2280484 < baseStart_2280484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280502 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2280502 : Nat := 118140960795 + 2280502 * 2 ^ 59
def prefixEnd_2280502 : Nat := 4983230072969 + 3 ^ 40 * 2280502 * 2
def baseEnd_2280502 : Nat := 1170993659539741759137169

theorem tailTrace_2280502 : CollatzResearch.WordTrace tailWord_2280502 prefixEnd_2280502 1170993659539741759137169 := by
  unfold tailWord_2280502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198546324008637973670235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55451160789425471719149173 5198546324008637973670235)
  ·
    refine ⟨7797819486012956960505353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5198546324008637973670235 7797819486012956960505353)
    ·
      refine ⟨5848364614509717720379015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7797819486012956960505353 5848364614509717720379015)
      ·
        refine ⟨8772546921764576580568523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848364614509717720379015 8772546921764576580568523)
        ·
          refine ⟨13158820382646864870852785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772546921764576580568523 13158820382646864870852785)
          ·
            refine ⟨9869115286985148653139589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13158820382646864870852785 9869115286985148653139589)
            ·
              refine ⟨1850459116309715372463673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9869115286985148653139589 1850459116309715372463673)
              ·
                refine ⟨1387844337232286529347755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850459116309715372463673 1387844337232286529347755)
                ·
                  refine ⟨2081766505848429794021633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387844337232286529347755 2081766505848429794021633)
                  ·
                    refine ⟨1561324879386322345516225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081766505848429794021633 1561324879386322345516225)
                    ·
                      refine ⟨1170993659539741759137169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561324879386322345516225 1170993659539741759137169)
                      ·
                        rfl

theorem cell23_2280502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2280502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280502 prefixEnd_2280502 := by exact prefixLift 2280502
  have htrace : WordTrace (prefixWord ++ tailWord_2280502) baseStart_2280502 baseEnd_2280502 := by
    simpa [prefixWord, tailWord_2280502, baseEnd_2280502] using wordTrace_append hprefix tailTrace_2280502
  have hstable : (prefixWord ++ tailWord_2280502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280502).length < 2 ^ (prefixWord ++ tailWord_2280502).sum := by decide
  have hdescent : baseEnd_2280502 < baseStart_2280502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280518 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2280518 : Nat := 118140960795 + 2280518 * 2 ^ 59
def prefixEnd_2280518 : Nat := 4983230072969 + 3 ^ 40 * 2280518 * 2
def baseEnd_2280518 : Nat := 1171001875230213696537095

theorem tailTrace_2280518 : CollatzResearch.WordTrace tailWord_2280518 prefixEnd_2280518 1171001875230213696537095 := by
  unfold tailWord_2280518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599291398502507572228319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55451549834720161540870805 2599291398502507572228319)
  ·
    refine ⟨3898937097753761358342479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2599291398502507572228319 3898937097753761358342479)
    ·
      refine ⟨5848405646630642037513719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3898937097753761358342479 5848405646630642037513719)
      ·
        refine ⟨8772608469945963056270579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848405646630642037513719 8772608469945963056270579)
        ·
          refine ⟨13158912704918944584405869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772608469945963056270579 13158912704918944584405869)
          ·
            refine ⟨4934592264344604219152201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13158912704918944584405869 4934592264344604219152201)
            ·
              refine ⟨3700944198258453164364151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4934592264344604219152201 3700944198258453164364151)
              ·
                refine ⟨5551416297387679746546227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700944198258453164364151 5551416297387679746546227)
                ·
                  refine ⟨8327124446081519619819341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5551416297387679746546227 8327124446081519619819341)
                  ·
                    refine ⟨3122671667280569857432253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8327124446081519619819341 3122671667280569857432253)
                    ·
                      refine ⟨1171001875230213696537095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122671667280569857432253 1171001875230213696537095)
                      ·
                        rfl

theorem cell23_2280518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2280518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280518 prefixEnd_2280518 := by exact prefixLift 2280518
  have htrace : WordTrace (prefixWord ++ tailWord_2280518) baseStart_2280518 baseEnd_2280518 := by
    simpa [prefixWord, tailWord_2280518, baseEnd_2280518] using wordTrace_append hprefix tailTrace_2280518
  have hstable : (prefixWord ++ tailWord_2280518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280518).length < 2 ^ (prefixWord ++ tailWord_2280518).sum := by decide
  have hdescent : baseEnd_2280518 < baseStart_2280518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280552 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2280552 : Nat := 118140960795 + 2280552 * 2 ^ 59
def prefixEnd_2280552 : Nat := 4983230072969 + 3 ^ 40 * 2280552 * 2
def baseEnd_2280552 : Nat := 1171019333572466563511939

theorem tailTrace_2280552 : CollatzResearch.WordTrace tailWord_2280552 prefixEnd_2280552 1171019333572466563511939 := by
  unfold tailWord_2280552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41589282416978533059021955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55452376555971377412029273 41589282416978533059021955)
  ·
    refine ⟨62383923625467799588532933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41589282416978533059021955 62383923625467799588532933)
    ·
      refine ⟨11696985679775212422849925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62383923625467799588532933 11696985679775212422849925)
      ·
        refine ⟨2193184814957852329284361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11696985679775212422849925 2193184814957852329284361)
        ·
          refine ⟨1644888611218389246963271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193184814957852329284361 1644888611218389246963271)
          ·
            refine ⟨2467332916827583870444907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644888611218389246963271 2467332916827583870444907)
            ·
              refine ⟨3700999375241375805667361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467332916827583870444907 3700999375241375805667361)
              ·
                refine ⟨2775749531431031854250521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700999375241375805667361 2775749531431031854250521)
                ·
                  refine ⟨2081812148573273890687891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2775749531431031854250521 2081812148573273890687891)
                  ·
                    refine ⟨3122718222859910836031837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2081812148573273890687891 3122718222859910836031837)
                    ·
                      refine ⟨1171019333572466563511939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122718222859910836031837 1171019333572466563511939)
                      ·
                        rfl

theorem cell23_2280552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2280552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280552 prefixEnd_2280552 := by exact prefixLift 2280552
  have htrace : WordTrace (prefixWord ++ tailWord_2280552) baseStart_2280552 baseEnd_2280552 := by
    simpa [prefixWord, tailWord_2280552, baseEnd_2280552] using wordTrace_append hprefix tailTrace_2280552
  have hstable : (prefixWord ++ tailWord_2280552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280552).length < 2 ^ (prefixWord ++ tailWord_2280552).sum := by decide
  have hdescent : baseEnd_2280552 < baseStart_2280552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280554 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2280554 : Nat := 118140960795 + 2280554 * 2 ^ 59
def prefixEnd_2280554 : Nat := 4983230072969 + 3 ^ 40 * 2280554 * 2
def baseEnd_2280554 : Nat := 1171020360533775555686929

theorem tailTrace_2280554 : CollatzResearch.WordTrace tailWord_2280554 prefixEnd_2280554 1171020360533775555686929 := by
  unfold tailWord_2280554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20794659444987455114904179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55452425186633213639744477 20794659444987455114904179)
  ·
    refine ⟨31191989167481182672356269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20794659444987455114904179 31191989167481182672356269)
    ·
      refine ⟨11696995937805443502133601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31191989167481182672356269 11696995937805443502133601)
      ·
        refine ⟨8772746953354082626600201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11696995937805443502133601 8772746953354082626600201)
        ·
          refine ⟨6579560215015561969950151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8772746953354082626600201 6579560215015561969950151)
          ·
            refine ⟨9869340322523342954925227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579560215015561969950151 9869340322523342954925227)
            ·
              refine ⟨14804010483785014432387841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9869340322523342954925227 14804010483785014432387841)
              ·
                refine ⟨11103007862838760824290881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14804010483785014432387841 11103007862838760824290881)
                ·
                  refine ⟨8327255897129070618218161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11103007862838760824290881 8327255897129070618218161)
                  ·
                    refine ⟨6245441922846802963663621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8327255897129070618218161 6245441922846802963663621)
                    ·
                      refine ⟨1171020360533775555686929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6245441922846802963663621 1171020360533775555686929)
                      ·
                        rfl

theorem cell23_2280554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2280554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280554 prefixEnd_2280554 := by exact prefixLift 2280554
  have htrace : WordTrace (prefixWord ++ tailWord_2280554) baseStart_2280554 baseEnd_2280554 := by
    simpa [prefixWord, tailWord_2280554, baseEnd_2280554] using wordTrace_append hprefix tailTrace_2280554
  have hstable : (prefixWord ++ tailWord_2280554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280554).length < 2 ^ (prefixWord ++ tailWord_2280554).sum := by decide
  have hdescent : baseEnd_2280554 < baseStart_2280554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280558 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_2280558 : Nat := 118140960795 + 2280558 * 2 ^ 59
def prefixEnd_2280558 : Nat := 4983230072969 + 3 ^ 40 * 2280558 * 2
def baseEnd_2280558 : Nat := 1171022414456393540036911

theorem tailTrace_2280558 : CollatzResearch.WordTrace tailWord_2280558 prefixEnd_2280558 1171022414456393540036911 := by
  unfold tailWord_2280558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10397347958991916142845291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55452522447956886095174885 10397347958991916142845291)
  ·
    refine ⟨15596021938487874214267937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10397347958991916142845291 15596021938487874214267937)
    ·
      refine ⟨11697016453865905660700953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15596021938487874214267937 11697016453865905660700953)
      ·
        refine ⟨8772762340399429245525715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697016453865905660700953 8772762340399429245525715)
        ·
          refine ⟨13159143510599143868288573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772762340399429245525715 13159143510599143868288573)
          ·
            refine ⟨4934678816474678950608215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13159143510599143868288573 4934678816474678950608215)
            ·
              refine ⟨7402018224712018425912323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934678816474678950608215 7402018224712018425912323)
              ·
                refine ⟨11103027337068027638868485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402018224712018425912323 11103027337068027638868485)
                ·
                  refine ⟨2081817625700255182287841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11103027337068027638868485 2081817625700255182287841)
                  ·
                    refine ⟨1561363219275191386715881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081817625700255182287841 1561363219275191386715881)
                    ·
                      refine ⟨1171022414456393540036911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561363219275191386715881 1171022414456393540036911)
                      ·
                        rfl

theorem cell23_2280558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_2280558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280558 prefixEnd_2280558 := by exact prefixLift 2280558
  have htrace : WordTrace (prefixWord ++ tailWord_2280558) baseStart_2280558 baseEnd_2280558 := by
    simpa [prefixWord, tailWord_2280558, baseEnd_2280558] using wordTrace_append hprefix tailTrace_2280558
  have hstable : (prefixWord ++ tailWord_2280558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280558).length < 2 ^ (prefixWord ++ tailWord_2280558).sum := by decide
  have hdescent : baseEnd_2280558 < baseStart_2280558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280594 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2280594 : Nat := 118140960795 + 2280594 * 2 ^ 59
def prefixEnd_2280594 : Nat := 4983230072969 + 3 ^ 40 * 2280594 * 2
def baseEnd_2280594 : Nat := 390346966586651799728915

theorem tailTrace_2280594 : CollatzResearch.WordTrace tailWord_2280594 prefixEnd_2280594 390346966586651799728915 := by
  unfold tailWord_2280594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795024174951226822768209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55453397799869938194048557 20795024174951226822768209)
  ·
    refine ⟨15596268131213420117076157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20795024174951226822768209 15596268131213420117076157)
    ·
      refine ⟨5848600549205032543903559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15596268131213420117076157 5848600549205032543903559)
      ·
        refine ⟨8772900823807548815855339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848600549205032543903559 8772900823807548815855339)
        ·
          refine ⟨13159351235711323223783009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772900823807548815855339 13159351235711323223783009)
          ·
            refine ⟨9869513426783492417837257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13159351235711323223783009 9869513426783492417837257)
            ·
              refine ⟨7402135070087619313377943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9869513426783492417837257 7402135070087619313377943)
              ·
                refine ⟨11103202605131428970066915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402135070087619313377943 11103202605131428970066915)
                ·
                  refine ⟨16654803907697143455100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103202605131428970066915 16654803907697143455100373)
                  ·
                    refine ⟨390346966586651799728915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16654803907697143455100373 390346966586651799728915)
                    ·
                      rfl

theorem cell23_2280594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2280594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280594 prefixEnd_2280594 := by exact prefixLift 2280594
  have htrace : WordTrace (prefixWord ++ tailWord_2280594) baseStart_2280594 baseEnd_2280594 := by
    simpa [prefixWord, tailWord_2280594, baseEnd_2280594] using wordTrace_append hprefix tailTrace_2280594
  have hstable : (prefixWord ++ tailWord_2280594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280594).length < 2 ^ (prefixWord ++ tailWord_2280594).sum := by decide
  have hdescent : baseEnd_2280594 < baseStart_2280594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280621 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2280621 : Nat := 118140960795 + 2280621 * 2 ^ 59
def prefixEnd_2280621 : Nat := 4983230072969 + 3 ^ 40 * 2280621 * 2
def baseEnd_2280621 : Nat := 1171054763737626793549121

theorem tailTrace_2280621 : CollatzResearch.WordTrace tailWord_2280621 prefixEnd_2280621 1171054763737626793549121 := by
  unfold tailWord_2280621
  simp only [CollatzResearch.WordTrace]
  refine ⟨83181081470707090902305717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55454054313804727268203811 83181081470707090902305717)
  ·
    refine ⟨7798226387878789772091161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83181081470707090902305717 7798226387878789772091161)
    ·
      refine ⟨5848669790909092329068371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7798226387878789772091161 5848669790909092329068371)
      ·
        refine ⟨8773004686363638493602557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848669790909092329068371 8773004686363638493602557)
        ·
          refine ⟨3289876757386364435100959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8773004686363638493602557 3289876757386364435100959)
          ·
            refine ⟨4934815136079546652651439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289876757386364435100959 4934815136079546652651439)
            ·
              refine ⟨7402222704119319978977159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934815136079546652651439 7402222704119319978977159)
              ·
                refine ⟨11103334056178979968465739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402222704119319978977159 11103334056178979968465739)
                ·
                  refine ⟨16655001084268469952698609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103334056178979968465739 16655001084268469952698609)
                  ·
                    refine ⟨12491250813201352464523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16655001084268469952698609 12491250813201352464523957)
                    ·
                      refine ⟨1171054763737626793549121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12491250813201352464523957 1171054763737626793549121)
                      ·
                        rfl

theorem cell23_2280621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2280621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280621 prefixEnd_2280621 := by exact prefixLift 2280621
  have htrace : WordTrace (prefixWord ++ tailWord_2280621) baseStart_2280621 baseEnd_2280621 := by
    simpa [prefixWord, tailWord_2280621, baseEnd_2280621] using wordTrace_append hprefix tailTrace_2280621
  have hstable : (prefixWord ++ tailWord_2280621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280621).length < 2 ^ (prefixWord ++ tailWord_2280621).sum := by decide
  have hdescent : baseEnd_2280621 < baseStart_2280621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280627 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_2280627 : Nat := 118140960795 + 2280627 * 2 ^ 59
def prefixEnd_2280627 : Nat := 4983230072969 + 3 ^ 40 * 2280627 * 2
def baseEnd_2280627 : Nat := 1171057844621553770074093

theorem tailTrace_2280627 : CollatzResearch.WordTrace tailWord_2280627 prefixEnd_2280627 1171057844621553770074093 := by
  unfold tailWord_2280627
  simp only [CollatzResearch.WordTrace]
  refine ⟨83181300308685353927024135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55454200205790235951349423 83181300308685353927024135)
  ·
    refine ⟨124771950463028030890536203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83181300308685353927024135 124771950463028030890536203)
    ·
      refine ⟨187157925694542046335804305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124771950463028030890536203 187157925694542046335804305)
      ·
        refine ⟨140368444270906534751853229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187157925694542046335804305 140368444270906534751853229)
        ·
          refine ⟨52638166601589950531944961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140368444270906534751853229 52638166601589950531944961)
          ·
            refine ⟨39478624951192462898958721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52638166601589950531944961 39478624951192462898958721)
            ·
              refine ⟨29608968713394347174219041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39478624951192462898958721 29608968713394347174219041)
              ·
                refine ⟨22206726535045760380664281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29608968713394347174219041 22206726535045760380664281)
                ·
                  refine ⟨16655044901284320285498211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22206726535045760380664281 16655044901284320285498211)
                  ·
                    refine ⟨24982567351926480428247317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16655044901284320285498211 24982567351926480428247317)
                    ·
                      refine ⟨1171057844621553770074093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24982567351926480428247317 1171057844621553770074093)
                      ·
                        rfl

theorem cell23_2280627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_2280627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280627 prefixEnd_2280627 := by exact prefixLift 2280627
  have htrace : WordTrace (prefixWord ++ tailWord_2280627) baseStart_2280627 baseEnd_2280627 := by
    simpa [prefixWord, tailWord_2280627, baseEnd_2280627] using wordTrace_append hprefix tailTrace_2280627
  have hstable : (prefixWord ++ tailWord_2280627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280627).length < 2 ^ (prefixWord ++ tailWord_2280627).sum := by decide
  have hdescent : baseEnd_2280627 < baseStart_2280627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280634 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_2280634 : Nat := 118140960795 + 2280634 * 2 ^ 59
def prefixEnd_2280634 : Nat := 4983230072969 + 3 ^ 40 * 2280634 * 2
def baseEnd_2280634 : Nat := 1171061438986135242686561

theorem tailTrace_2280634 : CollatzResearch.WordTrace tailWord_2280634 prefixEnd_2280634 1171061438986135242686561 := by
  unfold tailWord_2280634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795388904914998530632239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55454370413106662748352637 20795388904914998530632239)
  ·
    refine ⟨31193083357372497795948359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20795388904914998530632239 31193083357372497795948359)
    ·
      refine ⟨46789625036058746693922539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31193083357372497795948359 46789625036058746693922539)
      ·
        refine ⟨70184437554088120040883809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46789625036058746693922539 70184437554088120040883809)
        ·
          refine ⟨52638328165566090030662857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70184437554088120040883809 52638328165566090030662857)
          ·
            refine ⟨39478746124174567522997143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52638328165566090030662857 39478746124174567522997143)
            ·
              refine ⟨59218119186261851284495715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39478746124174567522997143 59218119186261851284495715)
              ·
                refine ⟨88827178779392776926743573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59218119186261851284495715 88827178779392776926743573)
                ·
                  refine ⟨4163774005284036418441105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88827178779392776926743573 4163774005284036418441105)
                  ·
                    refine ⟨3122830503963027313830829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163774005284036418441105 3122830503963027313830829)
                    ·
                      refine ⟨1171061438986135242686561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122830503963027313830829 1171061438986135242686561)
                      ·
                        rfl

theorem cell23_2280634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_2280634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280634 prefixEnd_2280634 := by exact prefixLift 2280634
  have htrace : WordTrace (prefixWord ++ tailWord_2280634) baseStart_2280634 baseEnd_2280634 := by
    simpa [prefixWord, tailWord_2280634, baseEnd_2280634] using wordTrace_append hprefix tailTrace_2280634
  have hstable : (prefixWord ++ tailWord_2280634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280634).length < 2 ^ (prefixWord ++ tailWord_2280634).sum := by decide
  have hdescent : baseEnd_2280634 < baseStart_2280634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280657 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2280657 : Nat := 118140960795 + 2280657 * 2 ^ 59
def prefixEnd_2280657 : Nat := 4983230072969 + 3 ^ 40 * 2280657 * 2
def baseEnd_2280657 : Nat := 1171073249041188652698955

theorem tailTrace_2280657 : CollatzResearch.WordTrace tailWord_2280657 prefixEnd_2280657 1171073249041188652698955 := by
  unfold tailWord_2280657
  simp only [CollatzResearch.WordTrace]
  refine ⟨83182394498576669050616225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55454929665717779367077483 83182394498576669050616225)
  ·
    refine ⟨62386795873932501787962169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83182394498576669050616225 62386795873932501787962169)
    ·
      refine ⟨46790096905449376340971627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62386795873932501787962169 46790096905449376340971627)
      ·
        refine ⟨70185145358174064511457441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46790096905449376340971627 70185145358174064511457441)
        ·
          refine ⟨52638859018630548383593081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70185145358174064511457441 52638859018630548383593081)
          ·
            refine ⟨39479144263972911287694811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52638859018630548383593081 39479144263972911287694811)
            ·
              refine ⟨59218716395959366931542217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39479144263972911287694811 59218716395959366931542217)
              ·
                refine ⟨44414037296969525198656663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59218716395959366931542217 44414037296969525198656663)
                ·
                  refine ⟨66621055945454287797984995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44414037296969525198656663 66621055945454287797984995)
                  ·
                    refine ⟨99931583918181431696977493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66621055945454287797984995 99931583918181431696977493)
                    ·
                      refine ⟨1171073249041188652698955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 99931583918181431696977493 1171073249041188652698955)
                      ·
                        rfl

theorem cell23_2280657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2280657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280657 prefixEnd_2280657 := by exact prefixLift 2280657
  have htrace : WordTrace (prefixWord ++ tailWord_2280657) baseStart_2280657 baseEnd_2280657 := by
    simpa [prefixWord, tailWord_2280657, baseEnd_2280657] using wordTrace_append hprefix tailTrace_2280657
  have hstable : (prefixWord ++ tailWord_2280657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280657).length < 2 ^ (prefixWord ++ tailWord_2280657).sum := by decide
  have hdescent : baseEnd_2280657 < baseStart_2280657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280658 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2280658 : Nat := 118140960795 + 2280658 * 2 ^ 59
def prefixEnd_2280658 : Nat := 4983230072969 + 3 ^ 40 * 2280658 * 2
def baseEnd_2280658 : Nat := 390357920840614382928817

theorem tailTrace_2280658 : CollatzResearch.WordTrace tailWord_2280658 prefixEnd_2280658 390357920840614382928817 := by
  unfold tailWord_2280658
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795607742893261555350657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55454953981048697480935085 20795607742893261555350657)
  ·
    refine ⟨15596705807169946166512993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20795607742893261555350657 15596705807169946166512993)
    ·
      refine ⟨11697529355377459624884745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15596705807169946166512993 11697529355377459624884745)
      ·
        refine ⟨8773147016533094718663559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697529355377459624884745 8773147016533094718663559)
        ·
          refine ⟨13159720524799642077995339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8773147016533094718663559 13159720524799642077995339)
          ·
            refine ⟨19739580787199463116993009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13159720524799642077995339 19739580787199463116993009)
            ·
              refine ⟨14804685590399597337744757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19739580787199463116993009 14804685590399597337744757)
              ·
                refine ⟨1387939274099962250413571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14804685590399597337744757 1387939274099962250413571)
                ·
                  refine ⟨2081908911149943375620357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387939274099962250413571 2081908911149943375620357)
                  ·
                    refine ⟨390357920840614382928817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081908911149943375620357 390357920840614382928817)
                    ·
                      rfl

theorem cell23_2280658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2280658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280658 prefixEnd_2280658 := by exact prefixLift 2280658
  have htrace : WordTrace (prefixWord ++ tailWord_2280658) baseStart_2280658 baseEnd_2280658 := by
    simpa [prefixWord, tailWord_2280658, baseEnd_2280658] using wordTrace_append hprefix tailTrace_2280658
  have hstable : (prefixWord ++ tailWord_2280658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280658).length < 2 ^ (prefixWord ++ tailWord_2280658).sum := by decide
  have hdescent : baseEnd_2280658 < baseStart_2280658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280684 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_2280684 : Nat := 118140960795 + 2280684 * 2 ^ 59
def prefixEnd_2280684 : Nat := 4983230072969 + 3 ^ 40 * 2280684 * 2
def baseEnd_2280684 : Nat := 390362371006286682353777

theorem tailTrace_2280684 : CollatzResearch.WordTrace tailWord_2280684 prefixEnd_2280684 390362371006286682353777 := by
  unfold tailWord_2280684
  simp only [CollatzResearch.WordTrace]
  refine ⟨41591689634739426330924553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55455586179652568441232737 41591689634739426330924553)
  ·
    refine ⟨31193767226054569748193415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41591689634739426330924553 31193767226054569748193415)
    ·
      refine ⟨46790650839081854622290123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31193767226054569748193415 46790650839081854622290123)
      ·
        refine ⟨70185976258622781933435185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46790650839081854622290123 70185976258622781933435185)
        ·
          refine ⟨52639482193967086450076389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70185976258622781933435185 52639482193967086450076389)
          ·
            refine ⟨9869902911368828709389323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52639482193967086450076389 9869902911368828709389323)
            ·
              refine ⟨14804854367053243064083985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9869902911368828709389323 14804854367053243064083985)
              ·
                refine ⟨11103640775289932298062989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14804854367053243064083985 11103640775289932298062989)
                ·
                  refine ⟨4163865290733724611773621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11103640775289932298062989 4163865290733724611773621)
                  ·
                    refine ⟨390362371006286682353777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4163865290733724611773621 390362371006286682353777)
                    ·
                      rfl

theorem cell23_2280684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_2280684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280684 prefixEnd_2280684 := by exact prefixLift 2280684
  have htrace : WordTrace (prefixWord ++ tailWord_2280684) baseStart_2280684 baseEnd_2280684 := by
    simpa [prefixWord, tailWord_2280684, baseEnd_2280684] using wordTrace_append hprefix tailTrace_2280684
  have hstable : (prefixWord ++ tailWord_2280684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280684).length < 2 ^ (prefixWord ++ tailWord_2280684).sum := by decide
  have hdescent : baseEnd_2280684 < baseStart_2280684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280692 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2280692 : Nat := 118140960795 + 2280692 * 2 ^ 59
def prefixEnd_2280692 : Nat := 4983230072969 + 3 ^ 40 * 2280692 * 2
def baseEnd_2280692 : Nat := 390363740288032005253765

theorem tailTrace_2280692 : CollatzResearch.WordTrace tailWord_2280692 prefixEnd_2280692 390363740288032005253765 := by
  unfold tailWord_2280692
  simp only [CollatzResearch.WordTrace]
  refine ⟨41591835526724935014070165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55455780702299913352093553 41591835526724935014070165)
  ·
    refine ⟨1949617290315231328784539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41591835526724935014070165 1949617290315231328784539)
    ·
      refine ⟨2924425935472846993176809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949617290315231328784539 2924425935472846993176809)
      ·
        refine ⟨2193319451604635244882607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2924425935472846993176809 2193319451604635244882607)
        ·
          refine ⟨3289979177406952867323911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193319451604635244882607 3289979177406952867323911)
          ·
            refine ⟨4934968766110429300985867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289979177406952867323911 4934968766110429300985867)
            ·
              refine ⟨7402453149165643951478801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934968766110429300985867 7402453149165643951478801)
              ·
                refine ⟨5551839861874232963609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7402453149165643951478801 5551839861874232963609101)
                ·
                  refine ⟨2081939948202837361353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5551839861874232963609101 2081939948202837361353413)
                  ·
                    refine ⟨390363740288032005253765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081939948202837361353413 390363740288032005253765)
                    ·
                      rfl

theorem cell23_2280692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2280692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280692 prefixEnd_2280692 := by exact prefixLift 2280692
  have htrace : WordTrace (prefixWord ++ tailWord_2280692) baseStart_2280692 baseEnd_2280692 := by
    simpa [prefixWord, tailWord_2280692, baseEnd_2280692] using wordTrace_append hprefix tailTrace_2280692
  have hstable : (prefixWord ++ tailWord_2280692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280692).length < 2 ^ (prefixWord ++ tailWord_2280692).sum := by decide
  have hdescent : baseEnd_2280692 < baseStart_2280692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280694 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2280694 : Nat := 118140960795 + 2280694 * 2 ^ 59
def prefixEnd_2280694 : Nat := 4983230072969 + 3 ^ 40 * 2280694 * 2
def baseEnd_2280694 : Nat := 1171092247825405007936285

theorem tailTrace_2280694 : CollatzResearch.WordTrace tailWord_2280694 prefixEnd_2280694 1171092247825405007936285 := by
  unfold tailWord_2280694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198983999965164023107071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55455829332961749579808757 5198983999965164023107071)
  ·
    refine ⟨7798475999947746034660607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5198983999965164023107071 7798475999947746034660607)
    ·
      refine ⟨11697713999921619051990911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798475999947746034660607 11697713999921619051990911)
      ·
        refine ⟨17546570999882428577986367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11697713999921619051990911 17546570999882428577986367)
        ·
          refine ⟨26319856499823642866979551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17546570999882428577986367 26319856499823642866979551)
          ·
            refine ⟨39479784749735464300469327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26319856499823642866979551 39479784749735464300469327)
            ·
              refine ⟨59219677124603196450703991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39479784749735464300469327 59219677124603196450703991)
              ·
                refine ⟨88829515686904794676055987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59219677124603196450703991 88829515686904794676055987)
                ·
                  refine ⟨133244273530357192014083981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88829515686904794676055987 133244273530357192014083981)
                  ·
                    refine ⟨49966602573883947005281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133244273530357192014083981 49966602573883947005281493)
                    ·
                      refine ⟨1171092247825405007936285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49966602573883947005281493 1171092247825405007936285)
                      ·
                        rfl

theorem cell23_2280694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2280694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280694 prefixEnd_2280694 := by exact prefixLift 2280694
  have htrace : WordTrace (prefixWord ++ tailWord_2280694) baseStart_2280694 baseEnd_2280694 := by
    simpa [prefixWord, tailWord_2280694, baseEnd_2280694] using wordTrace_append hprefix tailTrace_2280694
  have hstable : (prefixWord ++ tailWord_2280694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280694).length < 2 ^ (prefixWord ++ tailWord_2280694).sum := by decide
  have hdescent : baseEnd_2280694 < baseStart_2280694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280708 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_2280708 : Nat := 118140960795 + 2280708 * 2 ^ 59
def prefixEnd_2280708 : Nat := 4983230072969 + 3 ^ 40 * 2280708 * 2
def baseEnd_2280708 : Nat := 1171099436554567953161221

theorem tailTrace_2280708 : CollatzResearch.WordTrace tailWord_2280708 prefixEnd_2280708 1171099436554567953161221 := by
  unfold tailWord_2280708
  simp only [CollatzResearch.WordTrace]
  refine ⟨41592127310695952380361389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55456169747594603173815185 41592127310695952380361389)
  ·
    refine ⟨15597047741510982142635521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41592127310695952380361389 15597047741510982142635521)
    ·
      refine ⟨11697785806133236606976641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15597047741510982142635521 11697785806133236606976641)
      ·
        refine ⟨8773339354599927455232481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697785806133236606976641 8773339354599927455232481)
        ·
          refine ⟨6580004515949945591424361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8773339354599927455232481 6580004515949945591424361)
          ·
            refine ⟨4935003386962459193568271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580004515949945591424361 4935003386962459193568271)
            ·
              refine ⟨7402505080443688790352407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935003386962459193568271 7402505080443688790352407)
              ·
                refine ⟨11103757620665533185528611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402505080443688790352407 11103757620665533185528611)
                ·
                  refine ⟨16655636430998299778292917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103757620665533185528611 16655636430998299778292917)
                  ·
                    refine ⟨1561465915406090604214961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16655636430998299778292917 1561465915406090604214961)
                    ·
                      refine ⟨1171099436554567953161221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561465915406090604214961 1171099436554567953161221)
                      ·
                        rfl

theorem cell23_2280708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_2280708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280708 prefixEnd_2280708 := by exact prefixLift 2280708
  have htrace : WordTrace (prefixWord ++ tailWord_2280708) baseStart_2280708 baseEnd_2280708 := by
    simpa [prefixWord, tailWord_2280708, baseEnd_2280708] using wordTrace_append hprefix tailTrace_2280708
  have hstable : (prefixWord ++ tailWord_2280708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280708).length < 2 ^ (prefixWord ++ tailWord_2280708).sum := by decide
  have hdescent : baseEnd_2280708 < baseStart_2280708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280715 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 1, 1, 3]
def baseStart_2280715 : Nat := 118140960795 + 2280715 * 2 ^ 59
def prefixEnd_2280715 : Nat := 4983230072969 + 3 ^ 40 * 2280715 * 2
def baseEnd_2280715 : Nat := 1171103030919149425773689

theorem tailTrace_2280715 : CollatzResearch.WordTrace tailWord_2280715 prefixEnd_2280715 1171103030919149425773689 := by
  unfold tailWord_2280715
  simp only [CollatzResearch.WordTrace]
  refine ⟨83184509932366544956227599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55456339954911029970818399 83184509932366544956227599)
  ·
    refine ⟨124776764898549817434341399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83184509932366544956227599 124776764898549817434341399)
    ·
      refine ⟨187165147347824726151512099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124776764898549817434341399 187165147347824726151512099)
      ·
        refine ⟨280747721021737089227268149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187165147347824726151512099 280747721021737089227268149)
        ·
          refine ⟨26320098845787852115056389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 280747721021737089227268149 26320098845787852115056389)
          ·
            refine ⟨4935018533585222271573073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26320098845787852115056389 4935018533585222271573073)
            ·
              refine ⟨3701263900188916703679805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935018533585222271573073 3701263900188916703679805)
              ·
                refine ⟨1387973962570843763879927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701263900188916703679805 1387973962570843763879927)
                ·
                  refine ⟨2081960943856265645819891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387973962570843763879927 2081960943856265645819891)
                  ·
                    refine ⟨3122941415784398468729837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2081960943856265645819891 3122941415784398468729837)
                    ·
                      refine ⟨1171103030919149425773689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3122941415784398468729837 1171103030919149425773689)
                      ·
                        rfl

theorem cell23_2280715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 1, 3].length) (baseStart_2280715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280715 prefixEnd_2280715 := by exact prefixLift 2280715
  have htrace : WordTrace (prefixWord ++ tailWord_2280715) baseStart_2280715 baseEnd_2280715 := by
    simpa [prefixWord, tailWord_2280715, baseEnd_2280715] using wordTrace_append hprefix tailTrace_2280715
  have hstable : (prefixWord ++ tailWord_2280715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280715).length < 2 ^ (prefixWord ++ tailWord_2280715).sum := by decide
  have hdescent : baseEnd_2280715 < baseStart_2280715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280718 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2280718 : Nat := 118140960795 + 2280718 * 2 ^ 59
def prefixEnd_2280718 : Nat := 4983230072969 + 3 ^ 40 * 2280718 * 2
def baseEnd_2280718 : Nat := 390368190453704304678725

theorem tailTrace_2280718 : CollatzResearch.WordTrace tailWord_2280718 prefixEnd_2280718 390368190453704304678725 := by
  unfold tailWord_2280718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398077418919459558573351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55456412900903784312391205 10398077418919459558573351)
  ·
    refine ⟨15597116128379189337860027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10398077418919459558573351 15597116128379189337860027)
    ·
      refine ⟨23395674192568784006790041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15597116128379189337860027 23395674192568784006790041)
      ·
        refine ⟨17546755644426588005092531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23395674192568784006790041 17546755644426588005092531)
        ·
          refine ⟨26320133466639882007638797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17546755644426588005092531 26320133466639882007638797)
          ·
            refine ⟨9870050049989955752864549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26320133466639882007638797 9870050049989955752864549)
            ·
              refine ⟨1850634384373116703662103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9870050049989955752864549 1850634384373116703662103)
              ·
                refine ⟨2775951576559675055493155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850634384373116703662103 2775951576559675055493155)
                ·
                  refine ⟨4163927364839512583239733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775951576559675055493155 4163927364839512583239733)
                  ·
                    refine ⟨390368190453704304678725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4163927364839512583239733 390368190453704304678725)
                    ·
                      rfl

theorem cell23_2280718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2280718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280718 prefixEnd_2280718 := by exact prefixLift 2280718
  have htrace : WordTrace (prefixWord ++ tailWord_2280718) baseStart_2280718 baseEnd_2280718 := by
    simpa [prefixWord, tailWord_2280718, baseEnd_2280718] using wordTrace_append hprefix tailTrace_2280718
  have hstable : (prefixWord ++ tailWord_2280718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280718).length < 2 ^ (prefixWord ++ tailWord_2280718).sum := by decide
  have hdescent : baseEnd_2280718 < baseStart_2280718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280721 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_2280721 : Nat := 118140960795 + 2280721 * 2 ^ 59
def prefixEnd_2280721 : Nat := 4983230072969 + 3 ^ 40 * 2280721 * 2
def baseEnd_2280721 : Nat := 1171106111803076402298661

theorem tailTrace_2280721 : CollatzResearch.WordTrace tailWord_2280721 prefixEnd_2280721 1171106111803076402298661 := by
  unfold tailWord_2280721
  simp only [CollatzResearch.WordTrace]
  refine ⟨83184728770344807980946017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55456485846896538653964011 83184728770344807980946017)
  ·
    refine ⟨62388546577758605985709513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83184728770344807980946017 62388546577758605985709513)
    ·
      refine ⟨46791409933318954489282135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62388546577758605985709513 46791409933318954489282135)
      ·
        refine ⟨70187114899978431733923203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46791409933318954489282135 70187114899978431733923203)
        ·
          refine ⟨105280672349967647600884805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70187114899978431733923203 105280672349967647600884805)
          ·
            refine ⟨19740126065618933925165901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105280672349967647600884805 19740126065618933925165901)
            ·
              refine ⟨7402547274607100221937213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19740126065618933925165901 7402547274607100221937213)
              ·
                refine ⟨2775955227977662583226455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7402547274607100221937213 2775955227977662583226455)
                ·
                  refine ⟨4163932841966493874839683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775955227977662583226455 4163932841966493874839683)
                  ·
                    refine ⟨6245899262949740812259525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163932841966493874839683 6245899262949740812259525)
                    ·
                      refine ⟨1171106111803076402298661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6245899262949740812259525 1171106111803076402298661)
                      ·
                        rfl

theorem cell23_2280721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_2280721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280721 prefixEnd_2280721 := by exact prefixLift 2280721
  have htrace : WordTrace (prefixWord ++ tailWord_2280721) baseStart_2280721 baseEnd_2280721 := by
    simpa [prefixWord, tailWord_2280721, baseEnd_2280721] using wordTrace_append hprefix tailTrace_2280721
  have hstable : (prefixWord ++ tailWord_2280721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280721).length < 2 ^ (prefixWord ++ tailWord_2280721).sum := by decide
  have hdescent : baseEnd_2280721 < baseStart_2280721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280722 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_2280722 : Nat := 118140960795 + 2280722 * 2 ^ 59
def prefixEnd_2280722 : Nat := 4983230072969 + 3 ^ 40 * 2280722 * 2
def baseEnd_2280722 : Nat := 130122958364858988709573

theorem tailTrace_2280722 : CollatzResearch.WordTrace tailWord_2280722 prefixEnd_2280722 130122958364858988709573 := by
  unfold tailWord_2280722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796191310835296287933105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55456510162227456767821613 20796191310835296287933105)
  ·
    refine ⟨15597143483126472215949829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20796191310835296287933105 15597143483126472215949829)
    ·
      refine ⟨2924464403086213540490593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15597143483126472215949829 2924464403086213540490593)
      ·
        refine ⟨2193348302314660155367945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2924464403086213540490593 2193348302314660155367945)
        ·
          refine ⟨1645011226735995116525959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193348302314660155367945 1645011226735995116525959)
          ·
            refine ⟨2467516840103992674788939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645011226735995116525959 2467516840103992674788939)
            ·
              refine ⟨3701275260155989012183409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467516840103992674788939 3701275260155989012183409)
              ·
                refine ⟨2775956445116991759137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701275260155989012183409 2775956445116991759137557)
                ·
                  refine ⟨130122958364858988709573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2775956445116991759137557 130122958364858988709573)
                  ·
                    rfl

theorem cell23_2280722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_2280722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280722 prefixEnd_2280722 := by exact prefixLift 2280722
  have htrace : WordTrace (prefixWord ++ tailWord_2280722) baseStart_2280722 baseEnd_2280722 := by
    simpa [prefixWord, tailWord_2280722, baseEnd_2280722] using wordTrace_append hprefix tailTrace_2280722
  have hstable : (prefixWord ++ tailWord_2280722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280722).length < 2 ^ (prefixWord ++ tailWord_2280722).sum := by decide
  have hdescent : baseEnd_2280722 < baseStart_2280722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280741 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_2280741 : Nat := 118140960795 + 2280741 * 2 ^ 59
def prefixEnd_2280741 : Nat := 4983230072969 + 3 ^ 40 * 2280741 * 2
def baseEnd_2280741 : Nat := 1171116381416166324048569

theorem tailTrace_2280741 : CollatzResearch.WordTrace tailWord_2280741 prefixEnd_2280741 1171116381416166324048569 := by
  unfold tailWord_2280741
  simp only [CollatzResearch.WordTrace]
  refine ⟨83185458230272351396674077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55456972153514900931116051 83185458230272351396674077)
  ·
    refine ⟨31194546836352131773752779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83185458230272351396674077 31194546836352131773752779)
    ·
      refine ⟨46791820254528197660629169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31194546836352131773752779 46791820254528197660629169)
      ·
        refine ⟨35093865190896148245471877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46791820254528197660629169 35093865190896148245471877)
        ·
          refine ⟨6580099723293027796025977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35093865190896148245471877 6580099723293027796025977)
          ·
            refine ⟨4935074792469770847019483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580099723293027796025977 4935074792469770847019483)
            ·
              refine ⟨7402612188704656270529225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935074792469770847019483 7402612188704656270529225)
              ·
                refine ⟨5551959141528492202896919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7402612188704656270529225 5551959141528492202896919)
                ·
                  refine ⟨8327938712292738304345379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5551959141528492202896919 8327938712292738304345379)
                  ·
                    refine ⟨12491908068439107456518069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8327938712292738304345379 12491908068439107456518069)
                    ·
                      refine ⟨1171116381416166324048569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12491908068439107456518069 1171116381416166324048569)
                      ·
                        rfl

theorem cell23_2280741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_2280741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280741 prefixEnd_2280741 := by exact prefixLift 2280741
  have htrace : WordTrace (prefixWord ++ tailWord_2280741) baseStart_2280741 baseEnd_2280741 := by
    simpa [prefixWord, tailWord_2280741, baseEnd_2280741] using wordTrace_append hprefix tailTrace_2280741
  have hstable : (prefixWord ++ tailWord_2280741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280741).length < 2 ^ (prefixWord ++ tailWord_2280741).sum := by decide
  have hdescent : baseEnd_2280741 < baseStart_2280741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280761 : List Nat := [1, 2, 1, 6, 2, 1, 1, 9]
def baseStart_2280761 : Nat := 118140960795 + 2280761 * 2 ^ 59
def prefixEnd_2280761 : Nat := 4983230072969 + 3 ^ 40 * 2280761 * 2
def baseEnd_2280761 : Nat := 43375061149231712807351

theorem tailTrace_2280761 : CollatzResearch.WordTrace tailWord_2280761 prefixEnd_2280761 43375061149231712807351 := by
  unfold tailWord_2280761
  simp only [CollatzResearch.WordTrace]
  refine ⟨83186187690199894812402137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55457458460133263208268091 83186187690199894812402137)
  ·
    refine ⟨62389640767649921109301603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83186187690199894812402137 62389640767649921109301603)
    ·
      refine ⟨93584461151474881663952405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62389640767649921109301603 93584461151474881663952405)
      ·
        refine ⟨4386771616475385077997769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93584461151474881663952405 4386771616475385077997769)
        ·
          refine ⟨3290078712356538808498327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4386771616475385077997769 3290078712356538808498327)
          ·
            refine ⟨4935118068534808212747491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290078712356538808498327 4935118068534808212747491)
            ·
              refine ⟨7402677102802212319121237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935118068534808212747491 7402677102802212319121237)
              ·
                refine ⟨43375061149231712807351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7402677102802212319121237 43375061149231712807351)
                ·
                  rfl

theorem cell23_2280761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 9].length) (baseStart_2280761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280761 prefixEnd_2280761 := by exact prefixLift 2280761
  have htrace : WordTrace (prefixWord ++ tailWord_2280761) baseStart_2280761 baseEnd_2280761 := by
    simpa [prefixWord, tailWord_2280761, baseEnd_2280761] using wordTrace_append hprefix tailTrace_2280761
  have hstable : (prefixWord ++ tailWord_2280761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280761).length < 2 ^ (prefixWord ++ tailWord_2280761).sum := by decide
  have hdescent : baseEnd_2280761 < baseStart_2280761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280784 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_2280784 : Nat := 118140960795 + 2280784 * 2 ^ 59
def prefixEnd_2280784 : Nat := 4983230072969 + 3 ^ 40 * 2280784 * 2
def baseEnd_2280784 : Nat := 1171138461084309655810871

theorem tailTrace_2280784 : CollatzResearch.WordTrace tailWord_2280784 prefixEnd_2280784 1171138461084309655810871 := by
  unfold tailWord_2280784
  simp only [CollatzResearch.WordTrace]
  refine ⟨41593513284558284870244703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55458017712744379826992937 41593513284558284870244703)
  ·
    refine ⟨62390269926837427305367055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41593513284558284870244703 62390269926837427305367055)
    ·
      refine ⟨93585404890256140958050583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62390269926837427305367055 93585404890256140958050583)
      ·
        refine ⟨140378107335384211437075875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93585404890256140958050583 140378107335384211437075875)
        ·
          refine ⟨210567161003076317155613813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140378107335384211437075875 210567161003076317155613813)
          ·
            refine ⟨19740671344038404733338795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210567161003076317155613813 19740671344038404733338795)
            ·
              refine ⟨29611007016057607100008193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19740671344038404733338795 29611007016057607100008193)
              ·
                refine ⟨22208255262043205325006145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29611007016057607100008193 22208255262043205325006145)
                ·
                  refine ⟨16656191446532403993754609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22208255262043205325006145 16656191446532403993754609)
                  ·
                    refine ⟨12492143584899302995315957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16656191446532403993754609 12492143584899302995315957)
                    ·
                      refine ⟨1171138461084309655810871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12492143584899302995315957 1171138461084309655810871)
                      ·
                        rfl

theorem cell23_2280784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_2280784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280784 prefixEnd_2280784 := by exact prefixLift 2280784
  have htrace : WordTrace (prefixWord ++ tailWord_2280784) baseStart_2280784 baseEnd_2280784 := by
    simpa [prefixWord, tailWord_2280784, baseEnd_2280784] using wordTrace_append hprefix tailTrace_2280784
  have hstable : (prefixWord ++ tailWord_2280784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280784).length < 2 ^ (prefixWord ++ tailWord_2280784).sum := by decide
  have hdescent : baseEnd_2280784 < baseStart_2280784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280788 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2280788 : Nat := 118140960795 + 2280788 * 2 ^ 59
def prefixEnd_2280788 : Nat := 4983230072969 + 3 ^ 40 * 2280788 * 2
def baseEnd_2280788 : Nat := 1171140515006927640160853

theorem tailTrace_2280788 : CollatzResearch.WordTrace tailWord_2280788 prefixEnd_2280788 1171140515006927640160853 := by
  unfold tailWord_2280788
  simp only [CollatzResearch.WordTrace]
  refine ⟨41593586230551039211817509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55458114974068052282423345 41593586230551039211817509)
  ·
    refine ⟨7798797418228319852215783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41593586230551039211817509 7798797418228319852215783)
    ·
      refine ⟨11698196127342479778323675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798797418228319852215783 11698196127342479778323675)
      ·
        refine ⟨17547294191013719667485513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11698196127342479778323675 17547294191013719667485513)
        ·
          refine ⟨13160470643260289750614135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17547294191013719667485513 13160470643260289750614135)
          ·
            refine ⟨19740705964890434625921203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13160470643260289750614135 19740705964890434625921203)
            ·
              refine ⟨29611058947335651938881805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19740705964890434625921203 29611058947335651938881805)
              ·
                refine ⟨11104147105250869477080677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29611058947335651938881805 11104147105250869477080677)
                ·
                  refine ⟨2082027582234538026952627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11104147105250869477080677 2082027582234538026952627)
                  ·
                    refine ⟨3123041373351807040428941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2082027582234538026952627 3123041373351807040428941)
                    ·
                      refine ⟨1171140515006927640160853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3123041373351807040428941 1171140515006927640160853)
                      ·
                        rfl

theorem cell23_2280788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2280788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280788 prefixEnd_2280788 := by exact prefixLift 2280788
  have htrace : WordTrace (prefixWord ++ tailWord_2280788) baseStart_2280788 baseEnd_2280788 := by
    simpa [prefixWord, tailWord_2280788, baseEnd_2280788] using wordTrace_append hprefix tailTrace_2280788
  have hstable : (prefixWord ++ tailWord_2280788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280788).length < 2 ^ (prefixWord ++ tailWord_2280788).sum := by decide
  have hdescent : baseEnd_2280788 < baseStart_2280788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280789 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2280789 : Nat := 118140960795 + 2280789 * 2 ^ 59
def prefixEnd_2280789 : Nat := 4983230072969 + 3 ^ 40 * 2280789 * 2
def baseEnd_2280789 : Nat := 1171141028487582136248349

theorem tailTrace_2280789 : CollatzResearch.WordTrace tailWord_2280789 prefixEnd_2280789 1171141028487582136248349 := by
  unfold tailWord_2280789
  simp only [CollatzResearch.WordTrace]
  refine ⟨83187208934098455594421421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55458139289398970396280947 83187208934098455594421421)
  ·
    refine ⟨31195203350286920847908033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83187208934098455594421421 31195203350286920847908033)
    ·
      refine ⟨23396402512715190635931025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31195203350286920847908033 23396402512715190635931025)
      ·
        refine ⟨17547301884536392976948269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23396402512715190635931025 17547301884536392976948269)
        ·
          refine ⟨6580238206701147366355601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17547301884536392976948269 6580238206701147366355601)
          ·
            refine ⟨4935178655025860524766701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580238206701147366355601 4935178655025860524766701)
            ·
              refine ⟨1850691995634697696787513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4935178655025860524766701 1850691995634697696787513)
              ·
                refine ⟨1388018996726023272590635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850691995634697696787513 1388018996726023272590635)
                ·
                  refine ⟨2082028495089034908885953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388018996726023272590635 2082028495089034908885953)
                  ·
                    refine ⟨1561521371316776181664465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082028495089034908885953 1561521371316776181664465)
                    ·
                      refine ⟨1171141028487582136248349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561521371316776181664465 1171141028487582136248349)
                      ·
                        rfl

theorem cell23_2280789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2280789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280789 prefixEnd_2280789 := by exact prefixLift 2280789
  have htrace : WordTrace (prefixWord ++ tailWord_2280789) baseStart_2280789 baseEnd_2280789 := by
    simpa [prefixWord, tailWord_2280789, baseEnd_2280789] using wordTrace_append hprefix tailTrace_2280789
  have hstable : (prefixWord ++ tailWord_2280789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280789).length < 2 ^ (prefixWord ++ tailWord_2280789).sum := by decide
  have hdescent : baseEnd_2280789 < baseStart_2280789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280828 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_2280828 : Nat := 118140960795 + 2280828 * 2 ^ 59
def prefixEnd_2280828 : Nat := 4983230072969 + 3 ^ 40 * 2280828 * 2
def baseEnd_2280828 : Nat := 1171161054233107483660669

theorem tailTrace_2280828 : CollatzResearch.WordTrace tailWord_2280828 prefixEnd_2280828 1171161054233107483660669 := by
  unfold tailWord_2280828
  simp only [CollatzResearch.WordTrace]
  refine ⟨41594315690478582627545569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55459087587304776836727425 41594315690478582627545569)
  ·
    refine ⟨31195736767858936970659177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41594315690478582627545569 31195736767858936970659177)
    ·
      refine ⟨23396802575894202727994383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31195736767858936970659177 23396802575894202727994383)
      ·
        refine ⟨35095203863841304091991575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23396802575894202727994383 35095203863841304091991575)
        ·
          refine ⟨52642805795761956137987363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35095203863841304091991575 52642805795761956137987363)
          ·
            refine ⟨78964208693642934206981045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52642805795761956137987363 78964208693642934206981045)
            ·
              refine ⟨7402894565029025081904473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78964208693642934206981045 7402894565029025081904473)
              ·
                refine ⟨5552170923771768811428355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7402894565029025081904473 5552170923771768811428355)
                ·
                  refine ⟨8328256385657653217142533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5552170923771768811428355 8328256385657653217142533)
                  ·
                    refine ⟨1561548072310809978214225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8328256385657653217142533 1561548072310809978214225)
                    ·
                      refine ⟨1171161054233107483660669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561548072310809978214225 1171161054233107483660669)
                      ·
                        rfl

theorem cell23_2280828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_2280828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280828 prefixEnd_2280828 := by exact prefixLift 2280828
  have htrace : WordTrace (prefixWord ++ tailWord_2280828) baseStart_2280828 baseEnd_2280828 := by
    simpa [prefixWord, tailWord_2280828, baseEnd_2280828] using wordTrace_append hprefix tailTrace_2280828
  have hstable : (prefixWord ++ tailWord_2280828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280828).length < 2 ^ (prefixWord ++ tailWord_2280828).sum := by decide
  have hdescent : baseEnd_2280828 < baseStart_2280828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280881 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_2280881 : Nat := 118140960795 + 2280881 * 2 ^ 59
def prefixEnd_2280881 : Nat := 4983230072969 + 3 ^ 40 * 2280881 * 2
def baseEnd_2280881 : Nat := 390396089569265258765975

theorem tailTrace_2280881 : CollatzResearch.WordTrace tailWord_2280881 prefixEnd_2280881 390396089569265258765975 := by
  unfold tailWord_2280881
  simp only [CollatzResearch.WordTrace]
  refine ⟨83190564449765155306770497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55460376299843436871180331 83190564449765155306770497)
  ·
    refine ⟨62392923337323866480077873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83190564449765155306770497 62392923337323866480077873)
    ·
      refine ⟨46794692502992899860058405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62392923337323866480077873 46794692502992899860058405)
      ·
        refine ⟨8774004844311168723760951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46794692502992899860058405 8774004844311168723760951)
        ·
          refine ⟨13161007266466753085641427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774004844311168723760951 13161007266466753085641427)
          ·
            refine ⟨19741510899700129628462141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161007266466753085641427 19741510899700129628462141)
            ·
              refine ⟨7403066587387548610673303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19741510899700129628462141 7403066587387548610673303)
              ·
                refine ⟨11104599881081322916009955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403066587387548610673303 11104599881081322916009955)
                ·
                  refine ⟨16656899821621984374014933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11104599881081322916009955 16656899821621984374014933)
                  ·
                    refine ⟨390396089569265258765975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16656899821621984374014933 390396089569265258765975)
                    ·
                      rfl

theorem cell23_2280881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_2280881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280881 prefixEnd_2280881 := by exact prefixLift 2280881
  have htrace : WordTrace (prefixWord ++ tailWord_2280881) baseStart_2280881 baseEnd_2280881 := by
    simpa [prefixWord, tailWord_2280881, baseEnd_2280881] using wordTrace_append hprefix tailTrace_2280881
  have hstable : (prefixWord ++ tailWord_2280881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280881).length < 2 ^ (prefixWord ++ tailWord_2280881).sum := by decide
  have hdescent : baseEnd_2280881 < baseStart_2280881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280885 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 5]
def baseStart_2280885 : Nat := 118140960795 + 2280885 * 2 ^ 59
def prefixEnd_2280885 : Nat := 4983230072969 + 3 ^ 40 * 2280885 * 2
def baseEnd_2280885 : Nat := 130132258070045973405323

theorem tailTrace_2280885 : CollatzResearch.WordTrace tailWord_2280885 prefixEnd_2280885 130132258070045973405323 := by
  unfold tailWord_2280885
  simp only [CollatzResearch.WordTrace]
  refine ⟨83190710341750663989916109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55460473561167109326610739 83190710341750663989916109)
  ·
    refine ⟨31196516378156498996218541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83190710341750663989916109 31196516378156498996218541)
    ·
      refine ⟨11698693641808687123581953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31196516378156498996218541 11698693641808687123581953)
      ·
        refine ⟨8774020231356515342686465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11698693641808687123581953 8774020231356515342686465)
        ·
          refine ⟨6580515173517386507014849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8774020231356515342686465 6580515173517386507014849)
          ·
            refine ⟨4935386380138039880261137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580515173517386507014849 4935386380138039880261137)
            ·
              refine ⟨3701539785103529910195853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935386380138039880261137 3701539785103529910195853)
              ·
                refine ⟨1388077419413823716323445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701539785103529910195853 1388077419413823716323445)
                ·
                  refine ⟨130132258070045973405323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388077419413823716323445 130132258070045973405323)
                  ·
                    rfl

theorem cell23_2280885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_2280885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280885 prefixEnd_2280885 := by exact prefixLift 2280885
  have htrace : WordTrace (prefixWord ++ tailWord_2280885) baseStart_2280885 baseEnd_2280885 := by
    simpa [prefixWord, tailWord_2280885, baseEnd_2280885] using wordTrace_append hprefix tailTrace_2280885
  have hstable : (prefixWord ++ tailWord_2280885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280885).length < 2 ^ (prefixWord ++ tailWord_2280885).sum := by decide
  have hdescent : baseEnd_2280885 < baseStart_2280885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280962 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2280962 : Nat := 118140960795 + 2280962 * 2 ^ 59
def prefixEnd_2280962 : Nat := 4983230072969 + 3 ^ 40 * 2280962 * 2
def baseEnd_2280962 : Nat := 390409953546936653128351

theorem tailTrace_2280962 : CollatzResearch.WordTrace tailWord_2280962 prefixEnd_2280962 390409953546936653128351 := by
  unfold tailWord_2280962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20798379690617926535117285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55462345841647804093646093 20798379690617926535117285)
  ·
    refine ⟨3899696191990861225334491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20798379690617926535117285 3899696191990861225334491)
    ·
      refine ⟨5849544287986291838001737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3899696191990861225334491 5849544287986291838001737)
      ·
        refine ⟨4387158215989718878501303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5849544287986291838001737 4387158215989718878501303)
        ·
          refine ⟨6580737323984578317751955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387158215989718878501303 6580737323984578317751955)
          ·
            refine ⟨9871105985976867476627933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6580737323984578317751955 9871105985976867476627933)
            ·
              refine ⟨3701664744741325303735475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9871105985976867476627933 3701664744741325303735475)
              ·
                refine ⟨5552497117111987955603213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3701664744741325303735475 5552497117111987955603213)
                ·
                  refine ⟨2082186418916995483351205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5552497117111987955603213 2082186418916995483351205)
                  ·
                    refine ⟨390409953546936653128351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082186418916995483351205 390409953546936653128351)
                    ·
                      rfl

theorem cell23_2280962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2280962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280962 prefixEnd_2280962 := by exact prefixLift 2280962
  have htrace : WordTrace (prefixWord ++ tailWord_2280962) baseStart_2280962 baseEnd_2280962 := by
    simpa [prefixWord, tailWord_2280962, baseEnd_2280962] using wordTrace_append hprefix tailTrace_2280962
  have hstable : (prefixWord ++ tailWord_2280962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280962).length < 2 ^ (prefixWord ++ tailWord_2280962).sum := by decide
  have hdescent : baseEnd_2280962 < baseStart_2280962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2280988 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2280988 : Nat := 118140960795 + 2280988 * 2 ^ 59
def prefixEnd_2280988 : Nat := 4983230072969 + 3 ^ 40 * 2280988 * 2
def baseEnd_2280988 : Nat := 390414403712608952553311

theorem tailTrace_2280988 : CollatzResearch.WordTrace tailWord_2280988 prefixEnd_2280988 390414403712608952553311 := by
  unfold tailWord_2280988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597233530188756290457809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55462978040251675053943745 41597233530188756290457809)
  ·
    refine ⟨31197925147641567217843357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41597233530188756290457809 31197925147641567217843357)
    ·
      refine ⟨11699221930365587706691259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31197925147641567217843357 11699221930365587706691259)
      ·
        refine ⟨17548832895548381560036889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699221930365587706691259 17548832895548381560036889)
        ·
          refine ⟨13161624671661286170027667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17548832895548381560036889 13161624671661286170027667)
          ·
            refine ⟨19742437007491929255041501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161624671661286170027667 19742437007491929255041501)
            ·
              refine ⟨7403413877809473470640563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19742437007491929255041501 7403413877809473470640563)
              ·
                refine ⟨11105120816714210205960845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403413877809473470640563 11105120816714210205960845)
                ·
                  refine ⟨4164420306267828827235317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11105120816714210205960845 4164420306267828827235317)
                  ·
                    refine ⟨390414403712608952553311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4164420306267828827235317 390414403712608952553311)
                    ·
                      rfl

theorem cell23_2280988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2280988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2280988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2280988 prefixEnd_2280988 := by exact prefixLift 2280988
  have htrace : WordTrace (prefixWord ++ tailWord_2280988) baseStart_2280988 baseEnd_2280988 := by
    simpa [prefixWord, tailWord_2280988, baseEnd_2280988] using wordTrace_append hprefix tailTrace_2280988
  have hstable : (prefixWord ++ tailWord_2280988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2280988).length < 2 ^ (prefixWord ++ tailWord_2280988).sum := by decide
  have hdescent : baseEnd_2280988 < baseStart_2280988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2280988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281042 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_2281042 : Nat := 118140960795 + 2281042 * 2 ^ 59
def prefixEnd_2281042 : Nat := 4983230072969 + 3 ^ 40 * 2281042 * 2
def baseEnd_2281042 : Nat := 1171270939093169646384685

theorem tailTrace_2281042 : CollatzResearch.WordTrace tailWord_2281042 prefixEnd_2281042 1171270939093169646384685 := by
  unfold tailWord_2281042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20799109150545469950845345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55464291068121253202254253 20799109150545469950845345)
  ·
    refine ⟨15599331862909102463134009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20799109150545469950845345 15599331862909102463134009)
    ·
      refine ⟨11699498897181826847350507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15599331862909102463134009 11699498897181826847350507)
      ·
        refine ⟨17549248345772740271025761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699498897181826847350507 17549248345772740271025761)
        ·
          refine ⟨13161936259329555203269321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17549248345772740271025761 13161936259329555203269321)
          ·
            refine ⟨9871452194497166402451991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161936259329555203269321 9871452194497166402451991)
            ·
              refine ⟨14807178291745749603677987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9871452194497166402451991 14807178291745749603677987)
              ·
                refine ⟨22210767437618624405516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14807178291745749603677987 22210767437618624405516981)
                ·
                  refine ⟨2082259447276746038017217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22210767437618624405516981 2082259447276746038017217)
                  ·
                    refine ⟨1561694585457559528512913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082259447276746038017217 1561694585457559528512913)
                    ·
                      refine ⟨1171270939093169646384685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561694585457559528512913 1171270939093169646384685)
                      ·
                        rfl

theorem cell23_2281042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_2281042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281042 prefixEnd_2281042 := by exact prefixLift 2281042
  have htrace : WordTrace (prefixWord ++ tailWord_2281042) baseStart_2281042 baseEnd_2281042 := by
    simpa [prefixWord, tailWord_2281042, baseEnd_2281042] using wordTrace_append hprefix tailTrace_2281042
  have hstable : (prefixWord ++ tailWord_2281042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281042).length < 2 ^ (prefixWord ++ tailWord_2281042).sum := by decide
  have hdescent : baseEnd_2281042 < baseStart_2281042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281045 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2281045 : Nat := 118140960795 + 2281045 * 2 ^ 59
def prefixEnd_2281045 : Nat := 4983230072969 + 3 ^ 40 * 2281045 * 2
def baseEnd_2281045 : Nat := 1171272479535133134647171

theorem tailTrace_2281045 : CollatzResearch.WordTrace tailWord_2281045 prefixEnd_2281045 1171272479535133134647171 := by
  unfold tailWord_2281045
  simp only [CollatzResearch.WordTrace]
  refine ⟨83196546021171011315740589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55464364014114007543827059 83196546021171011315740589)
  ·
    refine ⟨31198704757939129243402721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83196546021171011315740589 31198704757939129243402721)
    ·
      refine ⟨23399028568454346932552041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31198704757939129243402721 23399028568454346932552041)
      ·
        refine ⟨17549271426340760199414031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23399028568454346932552041 17549271426340760199414031)
        ·
          refine ⟨26323907139511140299121047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17549271426340760199414031 26323907139511140299121047)
          ·
            refine ⟨39485860709266710448681571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26323907139511140299121047 39485860709266710448681571)
            ·
              refine ⟨59228791063900065673022357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39485860709266710448681571 59228791063900065673022357)
              ·
                refine ⟨2776349581120315578422923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59228791063900065673022357 2776349581120315578422923)
                ·
                  refine ⟨4164524371680473367634385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776349581120315578422923 4164524371680473367634385)
                  ·
                    refine ⟨3123393278760355025725789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4164524371680473367634385 3123393278760355025725789)
                    ·
                      refine ⟨1171272479535133134647171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3123393278760355025725789 1171272479535133134647171)
                      ·
                        rfl

theorem cell23_2281045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2281045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281045 prefixEnd_2281045 := by exact prefixLift 2281045
  have htrace : WordTrace (prefixWord ++ tailWord_2281045) baseStart_2281045 baseEnd_2281045 := by
    simpa [prefixWord, tailWord_2281045, baseEnd_2281045] using wordTrace_append hprefix tailTrace_2281045
  have hstable : (prefixWord ++ tailWord_2281045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281045).length < 2 ^ (prefixWord ++ tailWord_2281045).sum := by decide
  have hdescent : baseEnd_2281045 < baseStart_2281045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281046 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2281046 : Nat := 118140960795 + 2281046 * 2 ^ 59
def prefixEnd_2281046 : Nat := 4983230072969 + 3 ^ 40 * 2281046 * 2
def baseEnd_2281046 : Nat := 1171272993015787630734667

theorem tailTrace_2281046 : CollatzResearch.WordTrace tailWord_2281046 prefixEnd_2281046 1171272993015787630734667 := by
  unfold tailWord_2281046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199786405885461780407937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55464388329444925657684661 5199786405885461780407937)
  ·
    refine ⟨3899839804414096335305953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5199786405885461780407937 3899839804414096335305953)
    ·
      refine ⟨2924879853310572251479465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3899839804414096335305953 2924879853310572251479465)
      ·
        refine ⟨2193659889982929188609599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2924879853310572251479465 2193659889982929188609599)
        ·
          refine ⟨3290489834974393782914399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193659889982929188609599 3290489834974393782914399)
          ·
            refine ⟨4935734752461590674371599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290489834974393782914399 4935734752461590674371599)
            ·
              refine ⟨7403602128692386011557399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935734752461590674371599 7403602128692386011557399)
              ·
                refine ⟨11105403193038579017336099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403602128692386011557399 11105403193038579017336099)
                ·
                  refine ⟨16658104789557868526004149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11105403193038579017336099 16658104789557868526004149)
                  ·
                    refine ⟨1561697324021050174312889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16658104789557868526004149 1561697324021050174312889)
                    ·
                      refine ⟨1171272993015787630734667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561697324021050174312889 1171272993015787630734667)
                      ·
                        rfl

theorem cell23_2281046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2281046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281046 prefixEnd_2281046 := by exact prefixLift 2281046
  have htrace : WordTrace (prefixWord ++ tailWord_2281046) baseStart_2281046 baseEnd_2281046 := by
    simpa [prefixWord, tailWord_2281046, baseEnd_2281046] using wordTrace_append hprefix tailTrace_2281046
  have hstable : (prefixWord ++ tailWord_2281046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281046).length < 2 ^ (prefixWord ++ tailWord_2281046).sum := by decide
  have hdescent : baseEnd_2281046 < baseStart_2281046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281053 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2281053 : Nat := 118140960795 + 2281053 * 2 ^ 59
def prefixEnd_2281053 : Nat := 4983230072969 + 3 ^ 40 * 2281053 * 2
def baseEnd_2281053 : Nat := 1171276587380369103347135

theorem tailTrace_2281053 : CollatzResearch.WordTrace tailWord_2281053 prefixEnd_2281053 1171276587380369103347135 := by
  unfold tailWord_2281053
  simp only [CollatzResearch.WordTrace]
  refine ⟨83196837805142028682031813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55464558536761352454687875 83196837805142028682031813)
  ·
    refine ⟨15599407088464130377880965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83196837805142028682031813 15599407088464130377880965)
    ·
      refine ⟨2924888829087024445852681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15599407088464130377880965 2924888829087024445852681)
      ·
        refine ⟨2193666621815268334389511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2924888829087024445852681 2193666621815268334389511)
        ·
          refine ⟨3290499932722902501584267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193666621815268334389511 3290499932722902501584267)
          ·
            refine ⟨4935749899084353752376401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290499932722902501584267 4935749899084353752376401)
            ·
              refine ⟨3701812424313265314282301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935749899084353752376401 3701812424313265314282301)
              ·
                refine ⟨1388179659117474492855863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701812424313265314282301 1388179659117474492855863)
                ·
                  refine ⟨2082269488676211739283795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388179659117474492855863 2082269488676211739283795)
                  ·
                    refine ⟨3123404233014317608925693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2082269488676211739283795 3123404233014317608925693)
                    ·
                      refine ⟨1171276587380369103347135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3123404233014317608925693 1171276587380369103347135)
                      ·
                        rfl

theorem cell23_2281053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2281053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281053 prefixEnd_2281053 := by exact prefixLift 2281053
  have htrace : WordTrace (prefixWord ++ tailWord_2281053) baseStart_2281053 baseEnd_2281053 := by
    simpa [prefixWord, tailWord_2281053, baseEnd_2281053] using wordTrace_append hprefix tailTrace_2281053
  have hstable : (prefixWord ++ tailWord_2281053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281053).length < 2 ^ (prefixWord ++ tailWord_2281053).sum := by decide
  have hdescent : baseEnd_2281053 < baseStart_2281053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281059 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 1, 2, 2]
def baseStart_2281059 : Nat := 118140960795 + 2281059 * 2 ^ 59
def prefixEnd_2281059 : Nat := 4983230072969 + 3 ^ 40 * 2281059 * 2
def baseEnd_2281059 : Nat := 1171279668264296079872107

theorem tailTrace_2281059 : CollatzResearch.WordTrace tailWord_2281059 prefixEnd_2281059 1171279668264296079872107 := by
  unfold tailWord_2281059
  simp only [CollatzResearch.WordTrace]
  refine ⟨83197056643120291706750231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55464704428746861137833487 83197056643120291706750231)
  ·
    refine ⟨124795584964680437560125347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83197056643120291706750231 124795584964680437560125347)
    ·
      refine ⟨187193377447020656340188021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124795584964680437560125347 187193377447020656340188021)
      ·
        refine ⟨17549379135658186531892627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187193377447020656340188021 17549379135658186531892627)
        ·
          refine ⟨26324068703487279797838941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17549379135658186531892627 26324068703487279797838941)
          ·
            refine ⟨9871525763807729924189603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26324068703487279797838941 9871525763807729924189603)
            ·
              refine ⟨14807288645711594886284405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9871525763807729924189603 14807288645711594886284405)
              ·
                refine ⟨1388183310535462020589163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14807288645711594886284405 1388183310535462020589163)
                ·
                  refine ⟨2082274965803193030883745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388183310535462020589163 2082274965803193030883745)
                  ·
                    refine ⟨1561706224352394773162809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082274965803193030883745 1561706224352394773162809)
                    ·
                      refine ⟨1171279668264296079872107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561706224352394773162809 1171279668264296079872107)
                      ·
                        rfl

theorem cell23_2281059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_2281059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281059 prefixEnd_2281059 := by exact prefixLift 2281059
  have htrace : WordTrace (prefixWord ++ tailWord_2281059) baseStart_2281059 baseEnd_2281059 := by
    simpa [prefixWord, tailWord_2281059, baseEnd_2281059] using wordTrace_append hprefix tailTrace_2281059
  have hstable : (prefixWord ++ tailWord_2281059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281059).length < 2 ^ (prefixWord ++ tailWord_2281059).sum := by decide
  have hdescent : baseEnd_2281059 < baseStart_2281059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281069 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2281069 : Nat := 118140960795 + 2281069 * 2 ^ 59
def prefixEnd_2281069 : Nat := 4983230072969 + 3 ^ 40 * 2281069 * 2
def baseEnd_2281069 : Nat := 390428267690280346915687

theorem tailTrace_2281069 : CollatzResearch.WordTrace tailWord_2281069 prefixEnd_2281069 390428267690280346915687 := by
  unfold tailWord_2281069
  simp only [CollatzResearch.WordTrace]
  refine ⟨83197421373084063414614261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55464947582056042276409507 83197421373084063414614261)
  ·
    refine ⟨7799758253726630945120087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83197421373084063414614261 7799758253726630945120087)
    ·
      refine ⟨11699637380589946417680131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799758253726630945120087 11699637380589946417680131)
      ·
        refine ⟨17549456070884919626520197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699637380589946417680131 17549456070884919626520197)
        ·
          refine ⟨3290523013290922429972537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17549456070884919626520197 3290523013290922429972537)
          ·
            refine ⟨2467892259968191822479403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3290523013290922429972537 2467892259968191822479403)
            ·
              refine ⟨3701838389952287733719105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467892259968191822479403 3701838389952287733719105)
              ·
                refine ⟨2776378792464215800289329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701838389952287733719105 2776378792464215800289329)
                ·
                  refine ⟨2082284094348161850216997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2776378792464215800289329 2082284094348161850216997)
                  ·
                    refine ⟨390428267690280346915687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082284094348161850216997 390428267690280346915687)
                    ·
                      rfl

theorem cell23_2281069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2281069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281069 prefixEnd_2281069 := by exact prefixLift 2281069
  have htrace : WordTrace (prefixWord ++ tailWord_2281069) baseStart_2281069 baseEnd_2281069 := by
    simpa [prefixWord, tailWord_2281069, baseEnd_2281069] using wordTrace_append hprefix tailTrace_2281069
  have hstable : (prefixWord ++ tailWord_2281069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281069).length < 2 ^ (prefixWord ++ tailWord_2281069).sum := by decide
  have hdescent : baseEnd_2281069 < baseStart_2281069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281149 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_2281149 : Nat := 118140960795 + 2281149 * 2 ^ 59
def prefixEnd_2281149 : Nat := 4983230072969 + 3 ^ 40 * 2281149 * 2
def baseEnd_2281149 : Nat := 1171325881523200727746693

theorem tailTrace_2281149 : CollatzResearch.WordTrace tailWord_2281149 prefixEnd_2281149 1171325881523200727746693 := by
  unfold tailWord_2281149
  simp only [CollatzResearch.WordTrace]
  refine ⟨83200339212794237077526501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55466892808529491385017667 83200339212794237077526501)
  ·
    refine ⟨15600063602398919452036219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83200339212794237077526501 15600063602398919452036219)
    ·
      refine ⟨23400095403598379178054329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15600063602398919452036219 23400095403598379178054329)
      ·
        refine ⟨17550071552698784383540747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23400095403598379178054329 17550071552698784383540747)
        ·
          refine ⟨26325107329048176575311121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17550071552698784383540747 26325107329048176575311121)
          ·
            refine ⟨19743830496786132431483341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26325107329048176575311121 19743830496786132431483341)
            ·
              refine ⟨7403936436294799661806253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19743830496786132431483341 7403936436294799661806253)
              ·
                refine ⟨2776476163610549873177345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7403936436294799661806253 2776476163610549873177345)
                ·
                  refine ⟨2082357122707912404883009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2776476163610549873177345 2082357122707912404883009)
                  ·
                    refine ⟨1561767842030934303662257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082357122707912404883009 1561767842030934303662257)
                    ·
                      refine ⟨1171325881523200727746693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561767842030934303662257 1171325881523200727746693)
                      ·
                        rfl

theorem cell23_2281149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_2281149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281149 prefixEnd_2281149 := by exact prefixLift 2281149
  have htrace : WordTrace (prefixWord ++ tailWord_2281149) baseStart_2281149 baseEnd_2281149 := by
    simpa [prefixWord, tailWord_2281149, baseEnd_2281149] using wordTrace_append hprefix tailTrace_2281149
  have hstable : (prefixWord ++ tailWord_2281149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281149).length < 2 ^ (prefixWord ++ tailWord_2281149).sum := by decide
  have hdescent : baseEnd_2281149 < baseStart_2281149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281192 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2281192 : Nat := 118140960795 + 2281192 * 2 ^ 59
def prefixEnd_2281192 : Nat := 4983230072969 + 3 ^ 40 * 2281192 * 2
def baseEnd_2281192 : Nat := 1171347961191344059508995

theorem tailTrace_2281192 : CollatzResearch.WordTrace tailWord_2281192 prefixEnd_2281192 1171347961191344059508995 := by
  unfold tailWord_2281192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41600953775819227710670915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55467938367758970280894553 41600953775819227710670915)
  ·
    refine ⟨62401430663728841566006373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41600953775819227710670915 62401430663728841566006373)
    ·
      refine ⟨11700268249449157793626195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62401430663728841566006373 11700268249449157793626195)
      ·
        refine ⟨17550402374173736690439293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11700268249449157793626195 17550402374173736690439293)
        ·
          refine ⟨6581400890315151258914735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17550402374173736690439293 6581400890315151258914735)
          ·
            refine ⟨9872101335472726888372103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581400890315151258914735 9872101335472726888372103)
            ·
              refine ⟨14808152003209090332558155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9872101335472726888372103 14808152003209090332558155)
              ·
                refine ⟨22212228004813635498837233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808152003209090332558155 22212228004813635498837233)
                ·
                  refine ⟨16659171003610226624127925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22212228004813635498837233 16659171003610226624127925)
                  ·
                    refine ⟨1561797281588458746011993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16659171003610226624127925 1561797281588458746011993)
                    ·
                      refine ⟨1171347961191344059508995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561797281588458746011993 1171347961191344059508995)
                      ·
                        rfl

theorem cell23_2281192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2281192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281192 prefixEnd_2281192 := by exact prefixLift 2281192
  have htrace : WordTrace (prefixWord ++ tailWord_2281192) baseStart_2281192 baseEnd_2281192 := by
    simpa [prefixWord, tailWord_2281192, baseEnd_2281192] using wordTrace_append hprefix tailTrace_2281192
  have hstable : (prefixWord ++ tailWord_2281192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281192).length < 2 ^ (prefixWord ++ tailWord_2281192).sum := by decide
  have hdescent : baseEnd_2281192 < baseStart_2281192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281215 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 5, 4]
def baseStart_2281215 : Nat := 118140960795 + 2281215 * 2 ^ 59
def prefixEnd_2281215 : Nat := 4983230072969 + 3 ^ 40 * 2281215 * 2
def baseEnd_2281215 : Nat := 390453257082132489840463

theorem tailTrace_2281215 : CollatzResearch.WordTrace tailWord_2281215 prefixEnd_2281215 390453257082132489840463 := by
  unfold tailWord_2281215
  simp only [CollatzResearch.WordTrace]
  refine ⟨83202746430555130349429099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55468497620370086899619399 83202746430555130349429099)
  ·
    refine ⟨124804119645832695524143649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83202746430555130349429099 124804119645832695524143649)
    ·
      refine ⟨93603089734374521643107737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124804119645832695524143649 93603089734374521643107737)
      ·
        refine ⟨70202317300780891232330803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93603089734374521643107737 70202317300780891232330803)
        ·
          refine ⟨105303475951171336848496205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70202317300780891232330803 105303475951171336848496205)
          ·
            refine ⟨39488803481689251318186077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105303475951171336848496205 39488803481689251318186077)
            ·
              refine ⟨14808301305633469244319779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39488803481689251318186077 14808301305633469244319779)
              ·
                refine ⟨22212451958450203866479669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808301305633469244319779 22212451958450203866479669)
                ·
                  refine ⟨2082417371104706612482469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22212451958450203866479669 2082417371104706612482469)
                  ·
                    refine ⟨390453257082132489840463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082417371104706612482469 390453257082132489840463)
                    ·
                      rfl

theorem cell23_2281215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_2281215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281215 prefixEnd_2281215 := by exact prefixLift 2281215
  have htrace : WordTrace (prefixWord ++ tailWord_2281215) baseStart_2281215 baseEnd_2281215 := by
    simpa [prefixWord, tailWord_2281215, baseEnd_2281215] using wordTrace_append hprefix tailTrace_2281215
  have hstable : (prefixWord ++ tailWord_2281215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281215).length < 2 ^ (prefixWord ++ tailWord_2281215).sum := by decide
  have hdescent : baseEnd_2281215 < baseStart_2281215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281249 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2281249 : Nat := 118140960795 + 2281249 * 2 ^ 59
def prefixEnd_2281249 : Nat := 4983230072969 + 3 ^ 40 * 2281249 * 2
def baseEnd_2281249 : Nat := 390459076529550112165411

theorem tailTrace_2281249 : CollatzResearch.WordTrace tailWord_2281249 prefixEnd_2281249 390459076529550112165411 := by
  unfold tailWord_2281249
  simp only [CollatzResearch.WordTrace]
  refine ⟨83203986512431954156166801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55469324341621302770777867 83203986512431954156166801)
  ·
    refine ⟨62402989884323965617125101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83203986512431954156166801 62402989884323965617125101)
    ·
      refine ⟨23401121206621487106421913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62402989884323965617125101 23401121206621487106421913)
      ·
        refine ⟨17550840904966115329816435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23401121206621487106421913 17550840904966115329816435)
        ·
          refine ⟨26326261357449172994724653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17550840904966115329816435 26326261357449172994724653)
          ·
            refine ⟨9872348009043439873021745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26326261357449172994724653 9872348009043439873021745)
            ·
              refine ⟨7404261006782579904766309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9872348009043439873021745 7404261006782579904766309)
              ·
                refine ⟨1388298938771733732143683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7404261006782579904766309 1388298938771733732143683)
                ·
                  refine ⟨2082448408157600598215525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388298938771733732143683 2082448408157600598215525)
                  ·
                    refine ⟨390459076529550112165411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082448408157600598215525 390459076529550112165411)
                    ·
                      rfl

theorem cell23_2281249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2281249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281249 prefixEnd_2281249 := by exact prefixLift 2281249
  have htrace : WordTrace (prefixWord ++ tailWord_2281249) baseStart_2281249 baseEnd_2281249 := by
    simpa [prefixWord, tailWord_2281249, baseEnd_2281249] using wordTrace_append hprefix tailTrace_2281249
  have hstable : (prefixWord ++ tailWord_2281249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281249).length < 2 ^ (prefixWord ++ tailWord_2281249).sum := by decide
  have hdescent : baseEnd_2281249 < baseStart_2281249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281326 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2281326 : Nat := 118140960795 + 2281326 * 2 ^ 59
def prefixEnd_2281326 : Nat := 4983230072969 + 3 ^ 40 * 2281326 * 2
def baseEnd_2281326 : Nat := 390472255866348845077793

theorem tailTrace_2281326 : CollatzResearch.WordTrace tailWord_2281326 prefixEnd_2281326 390472255866348845077793 := by
  unfold tailWord_2281326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400849366644124538339979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55471196622101997537813221 10400849366644124538339979)
  ·
    refine ⟨15601274049966186807509969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400849366644124538339979 15601274049966186807509969)
    ·
      refine ⟨11700955537474640105632477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15601274049966186807509969 11700955537474640105632477)
      ·
        refine ⟨4387858326552990039612179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11700955537474640105632477 4387858326552990039612179)
        ·
          refine ⟨6581787489829485059418269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387858326552990039612179 6581787489829485059418269)
          ·
            refine ⟨2468170308686056897281851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6581787489829485059418269 2468170308686056897281851)
            ·
              refine ⟨3702255463029085345922777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468170308686056897281851 3702255463029085345922777)
              ·
                refine ⟨2776691597271814009442083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702255463029085345922777 2776691597271814009442083)
                ·
                  refine ⟨4165037395907721014163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776691597271814009442083 4165037395907721014163125)
                  ·
                    refine ⟨390472255866348845077793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4165037395907721014163125 390472255866348845077793)
                    ·
                      rfl

theorem cell23_2281326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2281326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281326 prefixEnd_2281326 := by exact prefixLift 2281326
  have htrace : WordTrace (prefixWord ++ tailWord_2281326) baseStart_2281326 baseEnd_2281326 := by
    simpa [prefixWord, tailWord_2281326, baseEnd_2281326] using wordTrace_append hprefix tailTrace_2281326
  have hstable : (prefixWord ++ tailWord_2281326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281326).length < 2 ^ (prefixWord ++ tailWord_2281326).sum := by decide
  have hdescent : baseEnd_2281326 < baseStart_2281326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281329 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_2281329 : Nat := 118140960795 + 2281329 * 2 ^ 59
def prefixEnd_2281329 : Nat := 4983230072969 + 3 ^ 40 * 2281329 * 2
def baseEnd_2281329 : Nat := 1171418308041010023495865

theorem tailTrace_2281329 : CollatzResearch.WordTrace tailWord_2281329 prefixEnd_2281329 1171418308041010023495865 := by
  unfold tailWord_2281329
  simp only [CollatzResearch.WordTrace]
  refine ⟨83206904352142127819079041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55471269568094751879386027 83206904352142127819079041)
  ·
    refine ⟨62405178264106595864309281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83206904352142127819079041 62405178264106595864309281)
    ·
      refine ⟨46803883698079946898231961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62405178264106595864309281 46803883698079946898231961)
      ·
        refine ⟨35102912773559960173673971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46803883698079946898231961 35102912773559960173673971)
        ·
          refine ⟨52654369160339940260510957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35102912773559960173673971 52654369160339940260510957)
          ·
            refine ⟨19745388435127477597691609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52654369160339940260510957 19745388435127477597691609)
            ·
              refine ⟨14809041326345608198268707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19745388435127477597691609 14809041326345608198268707)
              ·
                refine ⟨22213561989518412297403061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14809041326345608198268707 22213561989518412297403061)
                ·
                  refine ⟨2082521436517351152881537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22213561989518412297403061 2082521436517351152881537)
                  ·
                    refine ⟨1561891077388013364661153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2082521436517351152881537 1561891077388013364661153)
                    ·
                      refine ⟨1171418308041010023495865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1561891077388013364661153 1171418308041010023495865)
                      ·
                        rfl

theorem cell23_2281329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_2281329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281329 prefixEnd_2281329 := by exact prefixLift 2281329
  have htrace : WordTrace (prefixWord ++ tailWord_2281329) baseStart_2281329 baseEnd_2281329 := by
    simpa [prefixWord, tailWord_2281329, baseEnd_2281329] using wordTrace_append hprefix tailTrace_2281329
  have hstable : (prefixWord ++ tailWord_2281329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281329).length < 2 ^ (prefixWord ++ tailWord_2281329).sum := by decide
  have hdescent : baseEnd_2281329 < baseStart_2281329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281352 : List Nat := [2, 1, 3, 3, 4, 10]
def baseStart_2281352 : Nat := 118140960795 + 2281352 * 2 ^ 59
def prefixEnd_2281352 : Nat := 4983230072969 + 3 ^ 40 * 2281352 * 2
def baseEnd_2281352 : Nat := 4820700074469396845713

theorem tailTrace_2281352 : CollatzResearch.WordTrace tailWord_2281352 prefixEnd_2281352 4820700074469396845713 := by
  unfold tailWord_2281352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41603871615529401373583155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55471828820705868498110873 41603871615529401373583155)
  ·
    refine ⟨62405807423294102060374733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41603871615529401373583155 62405807423294102060374733)
    ·
      refine ⟨23402177783735288272640525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62405807423294102060374733 23402177783735288272640525)
      ·
        refine ⟨8775816668900733102240197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23402177783735288272640525 8775816668900733102240197)
        ·
          refine ⟨1645465625418887456670037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8775816668900733102240197 1645465625418887456670037)
          ·
            refine ⟨4820700074469396845713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1645465625418887456670037 4820700074469396845713)
            ·
              rfl

theorem cell23_2281352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 10].length) (baseStart_2281352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281352 prefixEnd_2281352 := by exact prefixLift 2281352
  have htrace : WordTrace (prefixWord ++ tailWord_2281352) baseStart_2281352 baseEnd_2281352 := by
    simpa [prefixWord, tailWord_2281352, baseEnd_2281352] using wordTrace_append hprefix tailTrace_2281352
  have hstable : (prefixWord ++ tailWord_2281352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281352).length < 2 ^ (prefixWord ++ tailWord_2281352).sum := by decide
  have hdescent : baseEnd_2281352 < baseStart_2281352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281365 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2281365 : Nat := 118140960795 + 2281365 * 2 ^ 59
def prefixEnd_2281365 : Nat := 4983230072969 + 3 ^ 40 * 2281365 * 2
def baseEnd_2281365 : Nat := 390478931114857294215233

theorem tailTrace_2281365 : CollatzResearch.WordTrace tailWord_2281365 prefixEnd_2281365 390478931114857294215233 := by
  unfold tailWord_2281365
  simp only [CollatzResearch.WordTrace]
  refine ⟨83208217380011705967389549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55472144920007803978259699 83208217380011705967389549)
  ·
    refine ⟨31203081517504389737771081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83208217380011705967389549 31203081517504389737771081)
    ·
      refine ⟨23402311138128292303328311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31203081517504389737771081 23402311138128292303328311)
      ·
        refine ⟨35103466707192438454992467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23402311138128292303328311 35103466707192438454992467)
        ·
          refine ⟨52655200060788657682488701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35103466707192438454992467 52655200060788657682488701)
          ·
            refine ⟨19745700022795746630933263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52655200060788657682488701 19745700022795746630933263)
            ·
              refine ⟨29618550034193619946399895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19745700022795746630933263 29618550034193619946399895)
              ·
                refine ⟨44427825051290429919599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29618550034193619946399895 44427825051290429919599843)
                ·
                  refine ⟨66641737576935644879399765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44427825051290429919599843 66641737576935644879399765)
                  ·
                    refine ⟨390478931114857294215233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66641737576935644879399765 390478931114857294215233)
                    ·
                      rfl

theorem cell23_2281365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2281365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281365 prefixEnd_2281365 := by exact prefixLift 2281365
  have htrace : WordTrace (prefixWord ++ tailWord_2281365) baseStart_2281365 baseEnd_2281365 := by
    simpa [prefixWord, tailWord_2281365, baseEnd_2281365] using wordTrace_append hprefix tailTrace_2281365
  have hstable : (prefixWord ++ tailWord_2281365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281365).length < 2 ^ (prefixWord ++ tailWord_2281365).sum := by decide
  have hdescent : baseEnd_2281365 < baseStart_2281365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281395 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 8]
def baseStart_2281395 : Nat := 118140960795 + 2281395 * 2 ^ 59
def prefixEnd_2281395 : Nat := 4983230072969 + 3 ^ 40 * 2281395 * 2
def baseEnd_2281395 : Nat := 390484065921402255090187

theorem tailTrace_2281395 : CollatzResearch.WordTrace tailWord_2281395 prefixEnd_2281395 390484065921402255090187 := by
  unfold tailWord_2281395
  simp only [CollatzResearch.WordTrace]
  refine ⟨83209311569903021090981639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55472874379935347393987759 83209311569903021090981639)
  ·
    refine ⟨124813967354854531636472459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83209311569903021090981639 124813967354854531636472459)
    ·
      refine ⟨187220951032281797454708689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124813967354854531636472459 187220951032281797454708689)
      ·
        refine ⟨140415713274211348091031517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187220951032281797454708689 140415713274211348091031517)
        ·
          refine ⟨52655892477829255534136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140415713274211348091031517 52655892477829255534136819)
          ·
            refine ⟨78983838716743883301205229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52655892477829255534136819 78983838716743883301205229)
            ·
              refine ⟨29618939518778956237951961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78983838716743883301205229 29618939518778956237951961)
              ·
                refine ⟨22214204639084217178463971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29618939518778956237951961 22214204639084217178463971)
                ·
                  refine ⟨33321306958626325767695957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22214204639084217178463971 33321306958626325767695957)
                  ·
                    refine ⟨390484065921402255090187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33321306958626325767695957 390484065921402255090187)
                    ·
                      rfl

theorem cell23_2281395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_2281395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281395 prefixEnd_2281395 := by exact prefixLift 2281395
  have htrace : WordTrace (prefixWord ++ tailWord_2281395) baseStart_2281395 baseEnd_2281395 := by
    simpa [prefixWord, tailWord_2281395, baseEnd_2281395] using wordTrace_append hprefix tailTrace_2281395
  have hstable : (prefixWord ++ tailWord_2281395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281395).length < 2 ^ (prefixWord ++ tailWord_2281395).sum := by decide
  have hdescent : baseEnd_2281395 < baseStart_2281395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281430 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2281430 : Nat := 118140960795 + 2281430 * 2 ^ 59
def prefixEnd_2281430 : Nat := 4983230072969 + 3 ^ 40 * 2281430 * 2
def baseEnd_2281430 : Nat := 1171470169587114128332901

theorem tailTrace_2281430 : CollatzResearch.WordTrace tailWord_2281430 prefixEnd_2281430 1171470169587114128332901 := by
  unfold tailWord_2281430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200661757798513879281609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55473725416517481379003829 5200661757798513879281609)
  ·
    refine ⟨3900496318348885409461207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5200661757798513879281609 3900496318348885409461207)
    ·
      refine ⟨5850744477523328114191811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900496318348885409461207 5850744477523328114191811)
      ·
        refine ⟨8776116716284992171287717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850744477523328114191811 8776116716284992171287717)
        ·
          refine ⟨1645521884303436032116447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8776116716284992171287717 1645521884303436032116447)
          ·
            refine ⟨2468282826455154048174671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645521884303436032116447 2468282826455154048174671)
            ·
              refine ⟨3702424239682731072262007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468282826455154048174671 3702424239682731072262007)
              ·
                refine ⟨5553636359524096608393011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702424239682731072262007 5553636359524096608393011)
                ·
                  refine ⟨8330454539286144912589517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5553636359524096608393011 8330454539286144912589517)
                  ·
                    refine ⟨3123920452232304342221069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8330454539286144912589517 3123920452232304342221069)
                    ·
                      refine ⟨1171470169587114128332901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3123920452232304342221069 1171470169587114128332901)
                      ·
                        rfl

theorem cell23_2281430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2281430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281430 prefixEnd_2281430 := by exact prefixLift 2281430
  have htrace : WordTrace (prefixWord ++ tailWord_2281430) baseStart_2281430 baseEnd_2281430 := by
    simpa [prefixWord, tailWord_2281430, baseEnd_2281430] using wordTrace_append hprefix tailTrace_2281430
  have hstable : (prefixWord ++ tailWord_2281430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281430).length < 2 ^ (prefixWord ++ tailWord_2281430).sum := by decide
  have hdescent : baseEnd_2281430 < baseStart_2281430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2281432 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2281432 : Nat := 118140960795 + 2281432 * 2 ^ 59
def prefixEnd_2281432 : Nat := 4983230072969 + 3 ^ 40 * 2281432 * 2
def baseEnd_2281432 : Nat := 1171471196548423120507891

theorem tailTrace_2281432 : CollatzResearch.WordTrace tailWord_2281432 prefixEnd_2281432 1171471196548423120507891 := by
  unfold tailWord_2281432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605330535384488205039275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55473774047179317606719033 41605330535384488205039275)
  ·
    refine ⟨62407995803076732307558913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41605330535384488205039275 62407995803076732307558913)
    ·
      refine ⟨46805996852307549230669185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62407995803076732307558913 46805996852307549230669185)
      ·
        refine ⟨35104497639230661923001889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46805996852307549230669185 35104497639230661923001889)
        ·
          refine ⟨26328373229422996442251417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35104497639230661923001889 26328373229422996442251417)
          ·
            refine ⟨19746279922067247331688563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26328373229422996442251417 19746279922067247331688563)
            ·
              refine ⟨29619419883100870997532845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19746279922067247331688563 29619419883100870997532845)
              ·
                refine ⟨11107282456162826624074817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29619419883100870997532845 11107282456162826624074817)
                ·
                  refine ⟨8330461842122119968056113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11107282456162826624074817 8330461842122119968056113)
                  ·
                    refine ⟨6247846381591589976042085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8330461842122119968056113 6247846381591589976042085)
                    ·
                      refine ⟨1171471196548423120507891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6247846381591589976042085 1171471196548423120507891)
                      ·
                        rfl

theorem cell23_2281432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2281432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2281432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2281432 prefixEnd_2281432 := by exact prefixLift 2281432
  have htrace : WordTrace (prefixWord ++ tailWord_2281432) baseStart_2281432 baseEnd_2281432 := by
    simpa [prefixWord, tailWord_2281432, baseEnd_2281432] using wordTrace_append hprefix tailTrace_2281432
  have hstable : (prefixWord ++ tailWord_2281432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2281432).length < 2 ^ (prefixWord ++ tailWord_2281432).sum := by decide
  have hdescent : baseEnd_2281432 < baseStart_2281432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2281432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
