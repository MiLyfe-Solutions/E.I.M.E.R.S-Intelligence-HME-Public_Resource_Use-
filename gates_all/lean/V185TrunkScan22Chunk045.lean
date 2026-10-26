import V185TrunkScan22Chunk044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_404101 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 4]
def baseStart_404101 : Nat := 118140960795 + 404101 * 2 ^ 59
def prefixEnd_404101 : Nat := 4983230072969 + 3 ^ 40 * 404101 * 2
def baseEnd_404101 : Nat := 46110676880584152595351

theorem tailTrace_404101 : CollatzResearch.WordTrace tailWord_404101 prefixEnd_404101 46110676880584152595351 := by
  unfold tailWord_404101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738774309018566801348157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9825849539345711200898771 14738774309018566801348157)
  ·
    refine ⟨5527040365881962550505559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14738774309018566801348157 5527040365881962550505559)
    ·
      refine ⟨8290560548822943825758339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527040365881962550505559 8290560548822943825758339)
      ·
        refine ⟨12435840823234415738637509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290560548822943825758339 12435840823234415738637509)
        ·
          refine ⟨2331720154356452950994533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12435840823234415738637509 2331720154356452950994533)
          ·
            refine ⟨437197528941834928311475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2331720154356452950994533 437197528941834928311475)
            ·
              refine ⟨655796293412752392467213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437197528941834928311475 655796293412752392467213)
              ·
                refine ⟨245923610029782147175205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655796293412752392467213 245923610029782147175205)
                ·
                  refine ⟨46110676880584152595351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245923610029782147175205 46110676880584152595351)
                  ·
                    rfl

theorem cell22_404101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_404101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404101 prefixEnd_404101 := by exact prefixLift 404101
  have htrace : WordTrace (prefixWord ++ tailWord_404101) baseStart_404101 baseEnd_404101 := by
    simpa [prefixWord, tailWord_404101, baseEnd_404101] using wordTrace_append hprefix tailTrace_404101
  have hstable : (prefixWord ++ tailWord_404101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404101).length < 2 ^ (prefixWord ++ tailWord_404101).sum := by decide
  have hdescent : baseEnd_404101 < baseStart_404101 := by decide
  rcases family_descends (prefixWord ++ tailWord_404101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404114 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_404114 : Nat := 118140960795 + 404114 * 2 ^ 59
def prefixEnd_404114 : Nat := 4983230072969 + 3 ^ 40 * 404114 * 2
def baseEnd_404114 : Nat := 138336480807424757211013

theorem tailTrace_404114 : CollatzResearch.WordTrace tailWord_404114 prefixEnd_404114 138336480807424757211013 := by
  unfold tailWord_404114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684812114492867505392849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9826165638647646681047597 3684812114492867505392849)
  ·
    refine ⟨2763609085869650629044637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3684812114492867505392849 2763609085869650629044637)
    ·
      refine ⟨1036353407201118985891739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2763609085869650629044637 1036353407201118985891739)
      ·
        refine ⟨1554530110801678478837609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036353407201118985891739 1554530110801678478837609)
        ·
          refine ⟨1165897583101258859128207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554530110801678478837609 1165897583101258859128207)
          ·
            refine ⟨1748846374651888288692311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165897583101258859128207 1748846374651888288692311)
            ·
              refine ⟨2623269561977832433038467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748846374651888288692311 2623269561977832433038467)
              ·
                refine ⟨3934904342966748649557701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623269561977832433038467 3934904342966748649557701)
                ·
                  refine ⟨737794564306265371792069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3934904342966748649557701 737794564306265371792069)
                  ·
                    refine ⟨138336480807424757211013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737794564306265371792069 138336480807424757211013)
                    ·
                      rfl

theorem cell22_404114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_404114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404114 prefixEnd_404114 := by exact prefixLift 404114
  have htrace : WordTrace (prefixWord ++ tailWord_404114) baseStart_404114 baseEnd_404114 := by
    simpa [prefixWord, tailWord_404114, baseEnd_404114] using wordTrace_append hprefix tailTrace_404114
  have hstable : (prefixWord ++ tailWord_404114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404114).length < 2 ^ (prefixWord ++ tailWord_404114).sum := by decide
  have hdescent : baseEnd_404114 < baseStart_404114 := by decide
  rcases family_descends (prefixWord ++ tailWord_404114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404116 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_404116 : Nat := 118140960795 + 404116 * 2 ^ 59
def prefixEnd_404116 : Nat := 4983230072969 + 3 ^ 40 * 404116 * 2
def baseEnd_404116 : Nat := 138337165448297418661007

theorem tailTrace_404116 : CollatzResearch.WordTrace tailWord_404116 prefixEnd_404116 138337165448297418661007 := by
  unfold tailWord_404116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369660701982112181572101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9826214269309482908762801 7369660701982112181572101)
  ·
    refine ⟨1381811381621646034044769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7369660701982112181572101 1381811381621646034044769)
    ·
      refine ⟨1036358536216234525533577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1381811381621646034044769 1036358536216234525533577)
      ·
        refine ⟨777268902162175894150183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036358536216234525533577 777268902162175894150183)
        ·
          refine ⟨1165903353243263841225275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777268902162175894150183 1165903353243263841225275)
          ·
            refine ⟨1748855029864895761837913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165903353243263841225275 1748855029864895761837913)
            ·
              refine ⟨1311641272398671821378435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748855029864895761837913 1311641272398671821378435)
              ·
                refine ⟨1967461908598007732067653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311641272398671821378435 1967461908598007732067653)
                ·
                  refine ⟨368899107862126449762685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967461908598007732067653 368899107862126449762685)
                  ·
                    refine ⟨138337165448297418661007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368899107862126449762685 138337165448297418661007)
                    ·
                      rfl

theorem cell22_404116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_404116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404116 prefixEnd_404116 := by exact prefixLift 404116
  have htrace : WordTrace (prefixWord ++ tailWord_404116) baseStart_404116 baseEnd_404116 := by
    simpa [prefixWord, tailWord_404116, baseEnd_404116] using wordTrace_append hprefix tailTrace_404116
  have hstable : (prefixWord ++ tailWord_404116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404116).length < 2 ^ (prefixWord ++ tailWord_404116).sum := by decide
  have hdescent : baseEnd_404116 < baseStart_404116 := by decide
  rcases family_descends (prefixWord ++ tailWord_404116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404129 : List Nat := [1, 2, 3, 3, 3, 1, 2, 7]
def baseStart_404129 : Nat := 118140960795 + 404129 * 2 ^ 59
def prefixEnd_404129 : Nat := 4983230072969 + 3 ^ 40 * 404129 * 2
def baseEnd_404129 : Nat := 15371290623774413120663

theorem tailTrace_404129 : CollatzResearch.WordTrace tailWord_404129 prefixEnd_404129 15371290623774413120663 := by
  unfold tailWord_404129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739795552917127583367441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9826530368611418388911627 14739795552917127583367441)
  ·
    refine ⟨11054846664687845687525581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14739795552917127583367441 11054846664687845687525581)
    ·
      refine ⟨4145567499257942132822093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11054846664687845687525581 4145567499257942132822093)
      ·
        refine ⟨1554587812221728299808285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4145567499257942132822093 1554587812221728299808285)
        ·
          refine ⟨582970429583148112428107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1554587812221728299808285 582970429583148112428107)
          ·
            refine ⟨874455644374722168642161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582970429583148112428107 874455644374722168642161)
            ·
              refine ⟨655841733281041626481621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874455644374722168642161 655841733281041626481621)
              ·
                refine ⟨15371290623774413120663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 655841733281041626481621 15371290623774413120663)
                ·
                  rfl

theorem cell22_404129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 7].length) (baseStart_404129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404129 prefixEnd_404129 := by exact prefixLift 404129
  have htrace : WordTrace (prefixWord ++ tailWord_404129) baseStart_404129 baseEnd_404129 := by
    simpa [prefixWord, tailWord_404129, baseEnd_404129] using wordTrace_append hprefix tailTrace_404129
  have hstable : (prefixWord ++ tailWord_404129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404129).length < 2 ^ (prefixWord ++ tailWord_404129).sum := by decide
  have hdescent : baseEnd_404129 < baseStart_404129 := by decide
  rcases family_descends (prefixWord ++ tailWord_404129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404174 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_404174 : Nat := 118140960795 + 404174 * 2 ^ 59
def prefixEnd_404174 : Nat := 4983230072969 + 3 ^ 40 * 404174 * 2
def baseEnd_404174 : Nat := 46119006677868200236943

theorem tailTrace_404174 : CollatzResearch.WordTrace tailWord_404174 prefixEnd_404174 46119006677868200236943 := by
  unfold tailWord_404174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842679604719262533594447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9827624558502733512503717 1842679604719262533594447)
  ·
    refine ⟨2764019407078893800391671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842679604719262533594447 2764019407078893800391671)
    ·
      refine ⟨4146029110618340700587507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764019407078893800391671 4146029110618340700587507)
      ·
        refine ⟨6219043665927511050881261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146029110618340700587507 6219043665927511050881261)
        ·
          refine ⟨2332141374722816644080473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6219043665927511050881261 2332141374722816644080473)
          ·
            refine ⟨1749106031042112483060355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332141374722816644080473 1749106031042112483060355)
            ·
              refine ⟨2623659046563168724590533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749106031042112483060355 2623659046563168724590533)
              ·
                refine ⟨491936071230594135860725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2623659046563168724590533 491936071230594135860725)
                ·
                  refine ⟨46119006677868200236943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 491936071230594135860725 46119006677868200236943)
                  ·
                    rfl

theorem cell22_404174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_404174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404174 prefixEnd_404174 := by exact prefixLift 404174
  have htrace : WordTrace (prefixWord ++ tailWord_404174) baseStart_404174 baseEnd_404174 := by
    simpa [prefixWord, tailWord_404174, baseEnd_404174] using wordTrace_append hprefix tailTrace_404174
  have hstable : (prefixWord ++ tailWord_404174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404174).length < 2 ^ (prefixWord ++ tailWord_404174).sum := by decide
  have hdescent : baseEnd_404174 < baseStart_404174 := by decide
  rcases family_descends (prefixWord ++ tailWord_404174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404204 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_404204 : Nat := 118140960795 + 404204 * 2 ^ 59
def prefixEnd_404204 : Nat := 4983230072969 + 3 ^ 40 * 404204 * 2
def baseEnd_404204 : Nat := 138367289646694522460737

theorem tailTrace_404204 : CollatzResearch.WordTrace tailWord_404204 prefixEnd_404204 138367289646694522460737 := by
  unfold tailWord_404204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371265513822707696173833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9828354018430276928231777 7371265513822707696173833)
  ·
    refine ⟨5528449135367030772130375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7371265513822707696173833 5528449135367030772130375)
    ·
      refine ⟨8292673703050546158195563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528449135367030772130375 8292673703050546158195563)
      ·
        refine ⟨12439010554575819237293345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292673703050546158195563 12439010554575819237293345)
        ·
          refine ⟨9329257915931864427970009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439010554575819237293345 9329257915931864427970009)
          ·
            refine ⟨6996943436948898320977507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9329257915931864427970009 6996943436948898320977507)
            ·
              refine ⟨10495415155423347481466261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996943436948898320977507 10495415155423347481466261)
              ·
                refine ⟨491972585410469413193731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10495415155423347481466261 491972585410469413193731)
                ·
                  refine ⟨737958878115704119790597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491972585410469413193731 737958878115704119790597)
                  ·
                    refine ⟨138367289646694522460737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737958878115704119790597 138367289646694522460737)
                    ·
                      rfl

theorem cell22_404204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_404204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404204 prefixEnd_404204 := by exact prefixLift 404204
  have htrace : WordTrace (prefixWord ++ tailWord_404204) baseStart_404204 baseEnd_404204 := by
    simpa [prefixWord, tailWord_404204, baseEnd_404204] using wordTrace_append hprefix tailTrace_404204
  have hstable : (prefixWord ++ tailWord_404204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404204).length < 2 ^ (prefixWord ++ tailWord_404204).sum := by decide
  have hdescent : baseEnd_404204 < baseStart_404204 := by decide
  rcases family_descends (prefixWord ++ tailWord_404204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404264 : List Nat := [2, 1, 5, 1, 1, 1, 3, 8]
def baseStart_404264 : Nat := 118140960795 + 404264 * 2 ^ 59
def prefixEnd_404264 : Nat := 4983230072969 + 3 ^ 40 * 404264 * 2
def baseEnd_404264 : Nat := 15376425430319373995617

theorem tailTrace_404264 : CollatzResearch.WordTrace tailWord_404264 prefixEnd_404264 15376425430319373995617 := by
  unfold tailWord_404264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372359703714022819765923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9829812938285363759687897 7372359703714022819765923)
  ·
    refine ⟨11058539555571034229648885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7372359703714022819765923 11058539555571034229648885)
    ·
      refine ⟨1036738083334784459029583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11058539555571034229648885 1036738083334784459029583)
      ·
        refine ⟨1555107125002176688544375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036738083334784459029583 1555107125002176688544375)
        ·
          refine ⟨2332660687503265032816563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555107125002176688544375 2332660687503265032816563)
          ·
            refine ⟨3498991031254897549224845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332660687503265032816563 3498991031254897549224845)
            ·
              refine ⟨1312121636720586580959317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3498991031254897549224845 1312121636720586580959317)
              ·
                refine ⟨15376425430319373995617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1312121636720586580959317 15376425430319373995617)
                ·
                  rfl

theorem cell22_404264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_404264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404264 prefixEnd_404264 := by exact prefixLift 404264
  have htrace : WordTrace (prefixWord ++ tailWord_404264) baseStart_404264 baseEnd_404264 := by
    simpa [prefixWord, tailWord_404264, baseEnd_404264] using wordTrace_append hprefix tailTrace_404264
  have hstable : (prefixWord ++ tailWord_404264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404264).length < 2 ^ (prefixWord ++ tailWord_404264).sum := by decide
  have hdescent : baseEnd_404264 < baseStart_404264 := by decide
  rcases family_descends (prefixWord ++ tailWord_404264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404270 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_404270 : Nat := 118140960795 + 404270 * 2 ^ 59
def prefixEnd_404270 : Nat := 4983230072969 + 3 ^ 40 * 404270 * 2
def baseEnd_404270 : Nat := 46129960931830783436845

theorem tailTrace_404270 : CollatzResearch.WordTrace tailWord_404270 prefixEnd_404270 46129960931830783436845 := by
  unfold tailWord_404270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843117280675788583031283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9829958830270872442833509 1843117280675788583031283)
  ·
    refine ⟨2764675921013682874546925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843117280675788583031283 2764675921013682874546925)
    ·
      refine ⟨1036753470380131077955097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2764675921013682874546925 1036753470380131077955097)
      ·
        refine ⟨777565102785098308466323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036753470380131077955097 777565102785098308466323)
        ·
          refine ⟨1166347654177647462699485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777565102785098308466323 1166347654177647462699485)
          ·
            refine ⟨437380370316617798512307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1166347654177647462699485 437380370316617798512307)
            ·
              refine ⟨656070555474926697768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437380370316617798512307 656070555474926697768461)
              ·
                refine ⟨246026458303097511663173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656070555474926697768461 246026458303097511663173)
                ·
                  refine ⟨46129960931830783436845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246026458303097511663173 46129960931830783436845)
                  ·
                    rfl

theorem cell22_404270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_404270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404270 prefixEnd_404270 := by exact prefixLift 404270
  have htrace : WordTrace (prefixWord ++ tailWord_404270) baseStart_404270 baseEnd_404270 := by
    simpa [prefixWord, tailWord_404270, baseEnd_404270] using wordTrace_append hprefix tailTrace_404270
  have hstable : (prefixWord ++ tailWord_404270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404270).length < 2 ^ (prefixWord ++ tailWord_404270).sum := by decide
  have hdescent : baseEnd_404270 < baseStart_404270 := by decide
  rcases family_descends (prefixWord ++ tailWord_404270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404388 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_404388 : Nat := 118140960795 + 404388 * 2 ^ 59
def prefixEnd_404388 : Nat := 4983230072969 + 3 ^ 40 * 404388 * 2
def baseEnd_404388 : Nat := 46143425535659791953391

theorem tailTrace_404388 : CollatzResearch.WordTrace tailWord_404388 prefixEnd_404388 46143425535659791953391 := by
  unfold tailWord_404388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374621029489407408522909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9832828039319209878030545 7374621029489407408522909)
  ·
    refine ⟨2765482886058527778196091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7374621029489407408522909 2765482886058527778196091)
    ·
      refine ⟨4148224329087791667294137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765482886058527778196091 4148224329087791667294137)
      ·
        refine ⟨3111168246815843750470603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4148224329087791667294137 3111168246815843750470603)
        ·
          refine ⟨4666752370223765625705905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111168246815843750470603 4666752370223765625705905)
          ·
            refine ⟨3500064277667824219279429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666752370223765625705905 3500064277667824219279429)
            ·
              refine ⟨656262052062717041114893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3500064277667824219279429 656262052062717041114893)
              ·
                refine ⟨246098269523518890418085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656262052062717041114893 246098269523518890418085)
                ·
                  refine ⟨46143425535659791953391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246098269523518890418085 46143425535659791953391)
                  ·
                    rfl

theorem cell22_404388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_404388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404388 prefixEnd_404388 := by exact prefixLift 404388
  have htrace : WordTrace (prefixWord ++ tailWord_404388) baseStart_404388 baseEnd_404388 := by
    simpa [prefixWord, tailWord_404388, baseEnd_404388] using wordTrace_append hprefix tailTrace_404388
  have hstable : (prefixWord ++ tailWord_404388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404388).length < 2 ^ (prefixWord ++ tailWord_404388).sum := by decide
  have hdescent : baseEnd_404388 < baseStart_404388 := by decide
  rcases family_descends (prefixWord ++ tailWord_404388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404465 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_404465 : Nat := 118140960795 + 404465 * 2 ^ 59
def prefixEnd_404465 : Nat := 4983230072969 + 3 ^ 40 * 404465 * 2
def baseEnd_404465 : Nat := 138456635280576841684937

theorem tailTrace_404465 : CollatzResearch.WordTrace tailWord_404465 prefixEnd_404465 138456635280576841684937 := by
  unfold tailWord_404465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752050479699856967598849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9834700319799904645065899 14752050479699856967598849)
  ·
    refine ⟨11064037859774892725699137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14752050479699856967598849 11064037859774892725699137)
    ·
      refine ⟨8298028394831169544274353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11064037859774892725699137 8298028394831169544274353)
      ·
        refine ⟨6223521296123377158205765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8298028394831169544274353 6223521296123377158205765)
        ·
          refine ⟨1166910243023133217163581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6223521296123377158205765 1166910243023133217163581)
          ·
            refine ⟨437591341133674956436343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1166910243023133217163581 437591341133674956436343)
            ·
              refine ⟨656387011700512434654515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437591341133674956436343 656387011700512434654515)
              ·
                refine ⟨984580517550768651981773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656387011700512434654515 984580517550768651981773)
                ·
                  refine ⟨369217694081538244493165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984580517550768651981773 369217694081538244493165)
                  ·
                    refine ⟨138456635280576841684937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369217694081538244493165 138456635280576841684937)
                    ·
                      rfl

theorem cell22_404465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_404465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404465 prefixEnd_404465 := by exact prefixLift 404465
  have htrace : WordTrace (prefixWord ++ tailWord_404465) baseStart_404465 baseEnd_404465 := by
    simpa [prefixWord, tailWord_404465, baseEnd_404465] using wordTrace_append hprefix tailTrace_404465
  have hstable : (prefixWord ++ tailWord_404465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404465).length < 2 ^ (prefixWord ++ tailWord_404465).sum := by decide
  have hdescent : baseEnd_404465 < baseStart_404465 := by decide
  rcases family_descends (prefixWord ++ tailWord_404465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404523 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 4]
def baseStart_404523 : Nat := 118140960795 + 404523 * 2 ^ 59
def prefixEnd_404523 : Nat := 4983230072969 + 3 ^ 40 * 404523 * 2
def baseEnd_404523 : Nat := 46158829955294674578253

theorem tailTrace_404523 : CollatzResearch.WordTrace tailWord_404523 prefixEnd_404523 46158829955294674578253 := by
  unfold tailWord_404523
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754165913489732873210223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9836110608993155248806815 14754165913489732873210223)
  ·
    refine ⟨22131248870234599309815335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754165913489732873210223 22131248870234599309815335)
    ·
      refine ⟨33196873305351898964723003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131248870234599309815335 33196873305351898964723003)
      ·
        refine ⟨49795309958027848447084505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33196873305351898964723003 49795309958027848447084505)
        ·
          refine ⟨37346482468520886335313379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49795309958027848447084505 37346482468520886335313379)
          ·
            refine ⟨56019723702781329502970069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37346482468520886335313379 56019723702781329502970069)
            ·
              refine ⟨1312962274283937410225861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56019723702781329502970069 1312962274283937410225861)
              ·
                refine ⟨246180426428238264417349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1312962274283937410225861 246180426428238264417349)
                ·
                  refine ⟨46158829955294674578253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246180426428238264417349 46158829955294674578253)
                  ·
                    rfl

theorem cell22_404523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 4].length) (baseStart_404523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404523 prefixEnd_404523 := by exact prefixLift 404523
  have htrace : WordTrace (prefixWord ++ tailWord_404523) baseStart_404523 baseEnd_404523 := by
    simpa [prefixWord, tailWord_404523, baseEnd_404523] using wordTrace_append hprefix tailTrace_404523
  have hstable : (prefixWord ++ tailWord_404523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404523).length < 2 ^ (prefixWord ++ tailWord_404523).sum := by decide
  have hdescent : baseEnd_404523 < baseStart_404523 := by decide
  rcases family_descends (prefixWord ++ tailWord_404523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404557 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 4]
def baseStart_404557 : Nat := 118140960795 + 404557 * 2 ^ 59
def prefixEnd_404557 : Nat := 4983230072969 + 3 ^ 40 * 404557 * 2
def baseEnd_404557 : Nat := 46162709586906422794885

theorem tailTrace_404557 : CollatzResearch.WordTrace tailWord_404557 prefixEnd_404557 46162709586906422794885 := by
  unfold tailWord_404557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14755405995366556679947925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9836937330244371119965283 14755405995366556679947925)
  ·
    refine ⟨691659656032807344372559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14755405995366556679947925 691659656032807344372559)
    ·
      refine ⟨1037489484049211016558839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691659656032807344372559 1037489484049211016558839)
      ·
        refine ⟨1556234226073816524838259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037489484049211016558839 1556234226073816524838259)
        ·
          refine ⟨2334351339110724787257389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556234226073816524838259 2334351339110724787257389)
          ·
            refine ⟨875381752166521795221521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2334351339110724787257389 875381752166521795221521)
            ·
              refine ⟨656536314124891346416141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875381752166521795221521 656536314124891346416141)
              ·
                refine ⟨246201117796834254906053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656536314124891346416141 246201117796834254906053)
                ·
                  refine ⟨46162709586906422794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246201117796834254906053 46162709586906422794885)
                  ·
                    rfl

theorem cell22_404557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_404557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404557 prefixEnd_404557 := by exact prefixLift 404557
  have htrace : WordTrace (prefixWord ++ tailWord_404557) baseStart_404557 baseEnd_404557 := by
    simpa [prefixWord, tailWord_404557, baseEnd_404557] using wordTrace_append hprefix tailTrace_404557
  have hstable : (prefixWord ++ tailWord_404557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404557).length < 2 ^ (prefixWord ++ tailWord_404557).sum := by decide
  have hdescent : baseEnd_404557 < baseStart_404557 := by decide
  rcases family_descends (prefixWord ++ tailWord_404557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404574 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_404574 : Nat := 118140960795 + 404574 * 2 ^ 59
def prefixEnd_404574 : Nat := 4983230072969 + 3 ^ 40 * 404574 * 2
def baseEnd_404574 : Nat := 46164649402712296903201

theorem tailTrace_404574 : CollatzResearch.WordTrace tailWord_404574 prefixEnd_404574 46164649402712296903201 := by
  unfold tailWord_404574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844503254538121072914597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9837350690869979055544517 1844503254538121072914597)
  ·
    refine ⟨345844360225897701171487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1844503254538121072914597 345844360225897701171487)
    ·
      refine ⟨518766540338846551757231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345844360225897701171487 518766540338846551757231)
      ·
        refine ⟨778149810508269827635847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518766540338846551757231 778149810508269827635847)
        ·
          refine ⟨1167224715762404741453771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778149810508269827635847 1167224715762404741453771)
          ·
            refine ⟨1750837073643607112180657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167224715762404741453771 1750837073643607112180657)
            ·
              refine ⟨1313127805232705334135493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750837073643607112180657 1313127805232705334135493)
              ·
                refine ⟨246211463481132250150405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1313127805232705334135493 246211463481132250150405)
                ·
                  refine ⟨46164649402712296903201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246211463481132250150405 46164649402712296903201)
                  ·
                    rfl

theorem cell22_404574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_404574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404574 prefixEnd_404574 := by exact prefixLift 404574
  have htrace : WordTrace (prefixWord ++ tailWord_404574) baseStart_404574 baseEnd_404574 := by
    simpa [prefixWord, tailWord_404574, baseEnd_404574] using wordTrace_append hprefix tailTrace_404574
  have hstable : (prefixWord ++ tailWord_404574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404574).length < 2 ^ (prefixWord ++ tailWord_404574).sum := by decide
  have hdescent : baseEnd_404574 < baseStart_404574 := by decide
  rcases family_descends (prefixWord ++ tailWord_404574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404617 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_404617 : Nat := 118140960795 + 404617 * 2 ^ 59
def prefixEnd_404617 : Nat := 4983230072969 + 3 ^ 40 * 404617 * 2
def baseEnd_404617 : Nat := 138508667986899111884471

theorem tailTrace_404617 : CollatzResearch.WordTrace tailWord_404617 prefixEnd_404617 138508667986899111884471 := by
  unfold tailWord_404617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757594375149186927132105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9838396250099457951421403 14757594375149186927132105)
  ·
    refine ⟨11068195781361890195349079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14757594375149186927132105 11068195781361890195349079)
    ·
      refine ⟨16602293672042835293023619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068195781361890195349079 16602293672042835293023619)
      ·
        refine ⟨24903440508064252939535429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602293672042835293023619 24903440508064252939535429)
        ·
          refine ⟨4669395095262047426162893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24903440508064252939535429 4669395095262047426162893)
          ·
            refine ⟨1751023160723267784811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4669395095262047426162893 1751023160723267784811085)
            ·
              refine ⟨656633685271225419304157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1751023160723267784811085 656633685271225419304157)
              ·
                refine ⟨246237631976709532239059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656633685271225419304157 246237631976709532239059)
                ·
                  refine ⟨369356447965064298358589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246237631976709532239059 369356447965064298358589)
                  ·
                    refine ⟨138508667986899111884471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369356447965064298358589 138508667986899111884471)
                    ·
                      rfl

theorem cell22_404617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_404617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404617 prefixEnd_404617 := by exact prefixLift 404617
  have htrace : WordTrace (prefixWord ++ tailWord_404617) baseStart_404617 baseEnd_404617 := by
    simpa [prefixWord, tailWord_404617, baseEnd_404617] using wordTrace_append hprefix tailTrace_404617
  have hstable : (prefixWord ++ tailWord_404617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404617).length < 2 ^ (prefixWord ++ tailWord_404617).sum := by decide
  have hdescent : baseEnd_404617 < baseStart_404617 := by decide
  rcases family_descends (prefixWord ++ tailWord_404617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404647 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 5]
def baseStart_404647 : Nat := 118140960795 + 404647 * 2 ^ 59
def prefixEnd_404647 : Nat := 4983230072969 + 3 ^ 40 * 404647 * 2
def baseEnd_404647 : Nat := 46172979199996344544793

theorem tailTrace_404647 : CollatzResearch.WordTrace tailWord_404647 prefixEnd_404647 46172979199996344544793 := by
  unfold tailWord_404647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14758688565040502050724195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9839125710027001367149463 14758688565040502050724195)
  ·
    refine ⟨22138032847560753076086293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14758688565040502050724195 22138032847560753076086293)
    ·
      refine ⟨1037720289729410300441545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22138032847560753076086293 1037720289729410300441545)
      ·
        refine ⟨778290217297057725331159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1037720289729410300441545 778290217297057725331159)
        ·
          refine ⟨1167435325945586587996739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778290217297057725331159 1167435325945586587996739)
          ·
            refine ⟨1751152988918379881995109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167435325945586587996739 1751152988918379881995109)
            ·
              refine ⟨328341185422196227874083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1751152988918379881995109 328341185422196227874083)
              ·
                refine ⟨492511778133294341811125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328341185422196227874083 492511778133294341811125)
                ·
                  refine ⟨46172979199996344544793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492511778133294341811125 46172979199996344544793)
                  ·
                    rfl

theorem cell22_404647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 5].length) (baseStart_404647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404647 prefixEnd_404647 := by exact prefixLift 404647
  have htrace : WordTrace (prefixWord ++ tailWord_404647) baseStart_404647 baseEnd_404647 := by
    simpa [prefixWord, tailWord_404647, baseEnd_404647] using wordTrace_append hprefix tailTrace_404647
  have hstable : (prefixWord ++ tailWord_404647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404647).length < 2 ^ (prefixWord ++ tailWord_404647).sum := by decide
  have hdescent : baseEnd_404647 < baseStart_404647 := by decide
  rcases family_descends (prefixWord ++ tailWord_404647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404685 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_404685 : Nat := 118140960795 + 404685 * 2 ^ 59
def prefixEnd_404685 : Nat := 4983230072969 + 3 ^ 40 * 404685 * 2
def baseEnd_404685 : Nat := 138531945776569601184263

theorem tailTrace_404685 : CollatzResearch.WordTrace tailWord_404685 prefixEnd_404685 138531945776569601184263 := by
  unfold tailWord_404685
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760074538902834540607509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9840049692601889693738339 14760074538902834540607509)
  ·
    refine ⟨691878494011070369090977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14760074538902834540607509 691878494011070369090977)
    ·
      refine ⟨518908870508302776818233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 691878494011070369090977 518908870508302776818233)
      ·
        refine ⟨389181652881227082613675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518908870508302776818233 389181652881227082613675)
        ·
          refine ⟨583772479321840623920513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389181652881227082613675 583772479321840623920513)
          ·
            refine ⟨437829359491380467940385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583772479321840623920513 437829359491380467940385)
            ·
              refine ⟨328372019618535350955289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437829359491380467940385 328372019618535350955289)
              ·
                refine ⟨246279014713901513216467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328372019618535350955289 246279014713901513216467)
                ·
                  refine ⟨369418522070852269824701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246279014713901513216467 369418522070852269824701)
                  ·
                    refine ⟨138531945776569601184263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369418522070852269824701 138531945776569601184263)
                    ·
                      rfl

theorem cell22_404685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_404685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404685 prefixEnd_404685 := by exact prefixLift 404685
  have htrace : WordTrace (prefixWord ++ tailWord_404685) baseStart_404685 baseEnd_404685 := by
    simpa [prefixWord, tailWord_404685, baseEnd_404685] using wordTrace_append hprefix tailTrace_404685
  have hstable : (prefixWord ++ tailWord_404685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404685).length < 2 ^ (prefixWord ++ tailWord_404685).sum := by decide
  have hdescent : baseEnd_404685 < baseStart_404685 := by decide
  rcases family_descends (prefixWord ++ tailWord_404685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404703 : List Nat := [1, 1, 2, 3, 2, 1, 5, 7]
def baseStart_404703 : Nat := 118140960795 + 404703 * 2 ^ 59
def prefixEnd_404703 : Nat := 4983230072969 + 3 ^ 40 * 404703 * 2
def baseEnd_404703 : Nat := 15393123060491506026023

theorem tailTrace_404703 : CollatzResearch.WordTrace tailWord_404703 prefixEnd_404703 15393123060491506026023 := by
  unfold tailWord_404703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760731052837623614762763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9840487368558415743175175 14760731052837623614762763)
  ·
    refine ⟨22141096579256435422144145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14760731052837623614762763 22141096579256435422144145)
    ·
      refine ⟨16605822434442326566608109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22141096579256435422144145 16605822434442326566608109)
      ·
        refine ⟨6227183412915872462478041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16605822434442326566608109 6227183412915872462478041)
        ·
          refine ⟨4670387559686904346858531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227183412915872462478041 4670387559686904346858531)
          ·
            refine ⟨7005581339530356520287797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670387559686904346858531 7005581339530356520287797)
            ·
              refine ⟨656773250580970923776981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7005581339530356520287797 656773250580970923776981)
              ·
                refine ⟨15393123060491506026023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 656773250580970923776981 15393123060491506026023)
                ·
                  rfl

theorem cell22_404703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 7].length) (baseStart_404703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404703 prefixEnd_404703 := by exact prefixLift 404703
  have htrace : WordTrace (prefixWord ++ tailWord_404703) baseStart_404703 baseEnd_404703 := by
    simpa [prefixWord, tailWord_404703, baseEnd_404703] using wordTrace_append hprefix tailTrace_404703
  have hstable : (prefixWord ++ tailWord_404703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404703).length < 2 ^ (prefixWord ++ tailWord_404703).sum := by decide
  have hdescent : baseEnd_404703 < baseStart_404703 := by decide
  rcases family_descends (prefixWord ++ tailWord_404703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404786 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_404786 : Nat := 118140960795 + 404786 * 2 ^ 59
def prefixEnd_404786 : Nat := 4983230072969 + 3 ^ 40 * 404786 * 2
def baseEnd_404786 : Nat := 138566520140639004408953

theorem tailTrace_404786 : CollatzResearch.WordTrace tailWord_404786 prefixEnd_404786 138566520140639004408953 := by
  unfold tailWord_404786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690939577884232197508553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9842505541024619193356141 3690939577884232197508553)
  ·
    refine ⟨2768204683413174148131415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3690939577884232197508553 2768204683413174148131415)
    ·
      refine ⟨4152307025119761222197123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2768204683413174148131415 4152307025119761222197123)
      ·
        refine ⟨6228460537679641833295685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152307025119761222197123 6228460537679641833295685)
        ·
          refine ⟨1167836350814932843742941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6228460537679641833295685 1167836350814932843742941)
          ·
            refine ⟨437938631555599816403603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1167836350814932843742941 437938631555599816403603)
            ·
              refine ⟨656907947333399724605405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437938631555599816403603 656907947333399724605405)
              ·
                refine ⟨246340480250024896727027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656907947333399724605405 246340480250024896727027)
                ·
                  refine ⟨369510720375037345090541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246340480250024896727027 369510720375037345090541)
                  ·
                    refine ⟨138566520140639004408953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369510720375037345090541 138566520140639004408953)
                    ·
                      rfl

theorem cell22_404786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_404786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404786 prefixEnd_404786 := by exact prefixLift 404786
  have htrace : WordTrace (prefixWord ++ tailWord_404786) baseStart_404786 baseEnd_404786 := by
    simpa [prefixWord, tailWord_404786, baseEnd_404786] using wordTrace_append hprefix tailTrace_404786
  have hstable : (prefixWord ++ tailWord_404786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404786).length < 2 ^ (prefixWord ++ tailWord_404786).sum := by decide
  have hdescent : baseEnd_404786 < baseStart_404786 := by decide
  rcases family_descends (prefixWord ++ tailWord_404786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404872 : List Nat := [2, 1, 3, 3, 1, 4, 1, 7]
def baseStart_404872 : Nat := 118140960795 + 404872 * 2 ^ 59
def prefixEnd_404872 : Nat := 4983230072969 + 3 ^ 40 * 404872 * 2
def baseEnd_404872 : Nat := 15399551077573716306521

theorem tailTrace_404872 : CollatzResearch.WordTrace tailWord_404872 prefixEnd_404872 15399551077573716306521 := by
  unfold tailWord_404872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383447494612682738832435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9844596659483576985109913 7383447494612682738832435)
  ·
    refine ⟨11075171241919024108248653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383447494612682738832435 11075171241919024108248653)
    ·
      refine ⟨4153189215719634040593245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11075171241919024108248653 4153189215719634040593245)
      ·
        refine ⟨1557445955894862765222467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4153189215719634040593245 1557445955894862765222467)
        ·
          refine ⟨2336168933842294147833701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557445955894862765222467 2336168933842294147833701)
          ·
            refine ⟨438031675095430152718819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2336168933842294147833701 438031675095430152718819)
            ·
              refine ⟨657047512643145229078229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438031675095430152718819 657047512643145229078229)
              ·
                refine ⟨15399551077573716306521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 657047512643145229078229 15399551077573716306521)
                ·
                  rfl

theorem cell22_404872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_404872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404872 prefixEnd_404872 := by exact prefixLift 404872
  have htrace : WordTrace (prefixWord ++ tailWord_404872) baseStart_404872 baseEnd_404872 := by
    simpa [prefixWord, tailWord_404872, baseEnd_404872] using wordTrace_append hprefix tailTrace_404872
  have hstable : (prefixWord ++ tailWord_404872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404872).length < 2 ^ (prefixWord ++ tailWord_404872).sum := by decide
  have hdescent : baseEnd_404872 < baseStart_404872 := by decide
  rcases family_descends (prefixWord ++ tailWord_404872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404900 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_404900 : Nat := 118140960795 + 404900 * 2 ^ 59
def prefixEnd_404900 : Nat := 4983230072969 + 3 ^ 40 * 404900 * 2
def baseEnd_404900 : Nat := 46201848223460235686201

theorem tailTrace_404900 : CollatzResearch.WordTrace tailWord_404900 prefixEnd_404900 46201848223460235686201 := by
  unfold tailWord_404900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383958116561963129842077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9845277488749284173122769 7383958116561963129842077)
  ·
    refine ⟨2768984293710736173690779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7383958116561963129842077 2768984293710736173690779)
    ·
      refine ⟨4153476440566104260536169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2768984293710736173690779 4153476440566104260536169)
      ·
        refine ⟨3115107330424578195402127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153476440566104260536169 3115107330424578195402127)
        ·
          refine ⟨4672660995636867293103191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115107330424578195402127 4672660995636867293103191)
          ·
            refine ⟨7008991493455300939654787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672660995636867293103191 7008991493455300939654787)
            ·
              refine ⟨10513487240182951409482181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008991493455300939654787 10513487240182951409482181)
              ·
                refine ⟨1971278857534303389277909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10513487240182951409482181 1971278857534303389277909)
                ·
                  refine ⟨46201848223460235686201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1971278857534303389277909 46201848223460235686201)
                  ·
                    rfl

theorem cell22_404900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_404900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404900 prefixEnd_404900 := by exact prefixLift 404900
  have htrace : WordTrace (prefixWord ++ tailWord_404900) baseStart_404900 baseEnd_404900 := by
    simpa [prefixWord, tailWord_404900, baseEnd_404900] using wordTrace_append hprefix tailTrace_404900
  have hstable : (prefixWord ++ tailWord_404900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404900).length < 2 ^ (prefixWord ++ tailWord_404900).sum := by decide
  have hdescent : baseEnd_404900 < baseStart_404900 := by decide
  rcases family_descends (prefixWord ++ tailWord_404900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404917 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 7]
def baseStart_404917 : Nat := 118140960795 + 404917 * 2 ^ 59
def prefixEnd_404917 : Nat := 4983230072969 + 3 ^ 40 * 404917 * 2
def baseEnd_404917 : Nat := 46203788039266109794517

theorem tailTrace_404917 : CollatzResearch.WordTrace tailWord_404917 prefixEnd_404917 46203788039266109794517 := by
  unfold tailWord_404917
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768536274062338163053005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9845690849374892108702003 14768536274062338163053005)
  ·
    refine ⟨5538201102773376811144877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14768536274062338163053005 5538201102773376811144877)
    ·
      refine ⟨2076825413540016304179329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5538201102773376811144877 2076825413540016304179329)
      ·
        refine ⟨1557619060155012228134497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2076825413540016304179329 1557619060155012228134497)
        ·
          refine ⟨1168214295116259171100873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557619060155012228134497 1168214295116259171100873)
          ·
            refine ⟨876160721337194378325655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168214295116259171100873 876160721337194378325655)
            ·
              refine ⟨1314241082005791567488483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876160721337194378325655 1314241082005791567488483)
              ·
                refine ⟨1971361623008687351232725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314241082005791567488483 1971361623008687351232725)
                ·
                  refine ⟨46203788039266109794517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1971361623008687351232725 46203788039266109794517)
                  ·
                    rfl

theorem cell22_404917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_404917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404917 prefixEnd_404917 := by exact prefixLift 404917
  have htrace : WordTrace (prefixWord ++ tailWord_404917) baseStart_404917 baseEnd_404917 := by
    simpa [prefixWord, tailWord_404917, baseEnd_404917] using wordTrace_append hprefix tailTrace_404917
  have hstable : (prefixWord ++ tailWord_404917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404917).length < 2 ^ (prefixWord ++ tailWord_404917).sum := by decide
  have hdescent : baseEnd_404917 < baseStart_404917 := by decide
  rcases family_descends (prefixWord ++ tailWord_404917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405084 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_405084 : Nat := 118140960795 + 405084 * 2 ^ 59
def prefixEnd_405084 : Nat := 4983230072969 + 3 ^ 40 * 405084 * 2
def baseEnd_405084 : Nat := 138668531630665560458039

theorem tailTrace_405084 : CollatzResearch.WordTrace tailWord_405084 prefixEnd_405084 138668531630665560458039 := by
  unfold tailWord_405084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387313632228662842191153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9849751509638217122921537 7387313632228662842191153)
  ·
    refine ⟨5540485224171497131643365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7387313632228662842191153 5540485224171497131643365)
    ·
      refine ⟨1038840979532155712183131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5540485224171497131643365 1038840979532155712183131)
      ·
        refine ⟨1558261469298233568274697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038840979532155712183131 1558261469298233568274697)
        ·
          refine ⟨1168696101973675176206023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1558261469298233568274697 1168696101973675176206023)
          ·
            refine ⟨1753044152960512764309035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168696101973675176206023 1753044152960512764309035)
            ·
              refine ⟨2629566229440769146463553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753044152960512764309035 2629566229440769146463553)
              ·
                refine ⟨1972174672080576859847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629566229440769146463553 1972174672080576859847665)
                ·
                  refine ⟨1479131004060432644885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972174672080576859847665 1479131004060432644885749)
                  ·
                    refine ⟨138668531630665560458039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1479131004060432644885749 138668531630665560458039)
                    ·
                      rfl

theorem cell22_405084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_405084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405084 prefixEnd_405084 := by exact prefixLift 405084
  have htrace : WordTrace (prefixWord ++ tailWord_405084) baseStart_405084 baseEnd_405084 := by
    simpa [prefixWord, tailWord_405084, baseEnd_405084] using wordTrace_append hprefix tailTrace_405084
  have hstable : (prefixWord ++ tailWord_405084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405084).length < 2 ^ (prefixWord ++ tailWord_405084).sum := by decide
  have hdescent : baseEnd_405084 < baseStart_405084 := by decide
  rcases family_descends (prefixWord ++ tailWord_405084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405097 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 6]
def baseStart_405097 : Nat := 118140960795 + 405097 * 2 ^ 59
def prefixEnd_405097 : Nat := 4983230072969 + 3 ^ 40 * 405097 * 2
def baseEnd_405097 : Nat := 46224327265445953294333

theorem tailTrace_405097 : CollatzResearch.WordTrace tailWord_405097 prefixEnd_405097 46224327265445953294333 := by
  unfold tailWord_405097
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775101413410228904605545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9850067608940152603070363 14775101413410228904605545)
  ·
    refine ⟨11081326060057671678454159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14775101413410228904605545 11081326060057671678454159)
    ·
      refine ⟨16621989090086507517681239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081326060057671678454159 16621989090086507517681239)
      ·
        refine ⟨24932983635129761276521859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16621989090086507517681239 24932983635129761276521859)
        ·
          refine ⟨37399475452694641914782789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24932983635129761276521859 37399475452694641914782789)
          ·
            refine ⟨7012401647380245359021773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37399475452694641914782789 7012401647380245359021773)
            ·
              refine ⟨2629650617767592009633165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7012401647380245359021773 2629650617767592009633165)
              ·
                refine ⟨986118981662847003612437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2629650617767592009633165 986118981662847003612437)
                ·
                  refine ⟨46224327265445953294333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 986118981662847003612437 46224327265445953294333)
                  ·
                    rfl

theorem cell22_405097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_405097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405097 prefixEnd_405097 := by exact prefixLift 405097
  have htrace : WordTrace (prefixWord ++ tailWord_405097) baseStart_405097 baseEnd_405097 := by
    simpa [prefixWord, tailWord_405097, baseEnd_405097] using wordTrace_append hprefix tailTrace_405097
  have hstable : (prefixWord ++ tailWord_405097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405097).length < 2 ^ (prefixWord ++ tailWord_405097).sum := by decide
  have hdescent : baseEnd_405097 < baseStart_405097 := by decide
  rcases family_descends (prefixWord ++ tailWord_405097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405129 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_405129 : Nat := 118140960795 + 405129 * 2 ^ 59
def prefixEnd_405129 : Nat := 4983230072969 + 3 ^ 40 * 405129 * 2
def baseEnd_405129 : Nat := 138683936050300443082901

theorem tailTrace_405129 : CollatzResearch.WordTrace tailWord_405129 prefixEnd_405129 138683936050300443082901 := by
  unfold tailWord_405129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776268549294298369770441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9850845699529532246513627 14776268549294298369770441)
  ·
    refine ⟨11082201411970723777327831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776268549294298369770441 11082201411970723777327831)
    ·
      refine ⟨16623302117956085665991747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082201411970723777327831 16623302117956085665991747)
      ·
        refine ⟨24934953176934128498987621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623302117956085665991747 24934953176934128498987621)
        ·
          refine ⟨4675303720675149093560179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24934953176934128498987621 4675303720675149093560179)
          ·
            refine ⟨7012955581012723640340269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675303720675149093560179 7012955581012723640340269)
            ·
              refine ⟨2629858342879771365127601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7012955581012723640340269 2629858342879771365127601)
              ·
                refine ⟨1972393757159828523845701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629858342879771365127601 1972393757159828523845701)
                ·
                  refine ⟨369823829467467848221069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972393757159828523845701 369823829467467848221069)
                  ·
                    refine ⟨138683936050300443082901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369823829467467848221069 138683936050300443082901)
                    ·
                      rfl

theorem cell22_405129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_405129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405129 prefixEnd_405129 := by exact prefixLift 405129
  have htrace : WordTrace (prefixWord ++ tailWord_405129) baseStart_405129 baseEnd_405129 := by
    simpa [prefixWord, tailWord_405129, baseEnd_405129] using wordTrace_append hprefix tailTrace_405129
  have hstable : (prefixWord ++ tailWord_405129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405129).length < 2 ^ (prefixWord ++ tailWord_405129).sum := by decide
  have hdescent : baseEnd_405129 < baseStart_405129 := by decide
  rcases family_descends (prefixWord ++ tailWord_405129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405144 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_405144 : Nat := 118140960795 + 405144 * 2 ^ 59
def prefixEnd_405144 : Nat := 4983230072969 + 3 ^ 40 * 405144 * 2
def baseEnd_405144 : Nat := 138689070856845403957855

theorem tailTrace_405144 : CollatzResearch.WordTrace tailWord_405144 prefixEnd_405144 138689070856845403957855 := by
  unfold tailWord_405144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388407822119977965783243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9851210429493303954377657 7388407822119977965783243)
  ·
    refine ⟨11082611733179966948674865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7388407822119977965783243 11082611733179966948674865)
    ·
      refine ⟨8311958799884975211506149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11082611733179966948674865 8311958799884975211506149)
      ·
        refine ⟨1558492274978432852157403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8311958799884975211506149 1558492274978432852157403)
        ·
          refine ⟨2337738412467649278236105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558492274978432852157403 2337738412467649278236105)
          ·
            refine ⟨1753303809350736958677079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337738412467649278236105 1753303809350736958677079)
            ·
              refine ⟨2629955714026105438015619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753303809350736958677079 2629955714026105438015619)
              ·
                refine ⟨3944933571039158157023429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629955714026105438015619 3944933571039158157023429)
                ·
                  refine ⟨739675044569842154441893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3944933571039158157023429 739675044569842154441893)
                  ·
                    refine ⟨138689070856845403957855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739675044569842154441893 138689070856845403957855)
                    ·
                      rfl

theorem cell22_405144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_405144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405144 prefixEnd_405144 := by exact prefixLift 405144
  have htrace : WordTrace (prefixWord ++ tailWord_405144) baseStart_405144 baseEnd_405144 := by
    simpa [prefixWord, tailWord_405144, baseEnd_405144] using wordTrace_append hprefix tailTrace_405144
  have hstable : (prefixWord ++ tailWord_405144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405144).length < 2 ^ (prefixWord ++ tailWord_405144).sum := by decide
  have hdescent : baseEnd_405144 < baseStart_405144 := by decide
  rcases family_descends (prefixWord ++ tailWord_405144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405148 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_405148 : Nat := 118140960795 + 405148 * 2 ^ 59
def prefixEnd_405148 : Nat := 4983230072969 + 3 ^ 40 * 405148 * 2
def baseEnd_405148 : Nat := 46230146712863575619281

theorem tailTrace_405148 : CollatzResearch.WordTrace tailWord_405148 prefixEnd_405148 46230146712863575619281 := by
  unfold tailWord_405148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388480768112732307356049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9851307690816976409808065 7388480768112732307356049)
  ·
    refine ⟨5541360576084549230517037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7388480768112732307356049 5541360576084549230517037)
    ·
      refine ⟨2078010216031705961443889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5541360576084549230517037 2078010216031705961443889)
      ·
        refine ⟨1558507662023779471082917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078010216031705961443889 1558507662023779471082917)
        ·
          refine ⟨292220186629458650828047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1558507662023779471082917 292220186629458650828047)
          ·
            refine ⟨438330279944187976242071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292220186629458650828047 438330279944187976242071)
            ·
              refine ⟨657495419916281964363107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438330279944187976242071 657495419916281964363107)
              ·
                refine ⟨986243129874422946544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657495419916281964363107 986243129874422946544661)
                ·
                  refine ⟨46230146712863575619281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 986243129874422946544661 46230146712863575619281)
                  ·
                    rfl

theorem cell22_405148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_405148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405148 prefixEnd_405148 := by exact prefixLift 405148
  have htrace : WordTrace (prefixWord ++ tailWord_405148) baseStart_405148 baseEnd_405148 := by
    simpa [prefixWord, tailWord_405148, baseEnd_405148] using wordTrace_append hprefix tailTrace_405148
  have hstable : (prefixWord ++ tailWord_405148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405148).length < 2 ^ (prefixWord ++ tailWord_405148).sum := by decide
  have hdescent : baseEnd_405148 < baseStart_405148 := by decide
  rcases family_descends (prefixWord ++ tailWord_405148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405208 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_405208 : Nat := 118140960795 + 405208 * 2 ^ 59
def prefixEnd_405208 : Nat := 4983230072969 + 3 ^ 40 * 405208 * 2
def baseEnd_405208 : Nat := 138710979364770570357659

theorem tailTrace_405208 : CollatzResearch.WordTrace tailWord_405208 prefixEnd_405208 138710979364770570357659 := by
  unfold tailWord_405208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389574958004047430948139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9852766610672063241264185 7389574958004047430948139)
  ·
    refine ⟨11084362437006071146422209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389574958004047430948139 11084362437006071146422209)
    ·
      refine ⟨8313271827754553359816657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11084362437006071146422209 8313271827754553359816657)
      ·
        refine ⟨6234953870815915019862493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8313271827754553359816657 6234953870815915019862493)
        ·
          refine ⟨2338107701555968132448435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6234953870815915019862493 2338107701555968132448435)
          ·
            refine ⟨3507161552333952198672653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338107701555968132448435 3507161552333952198672653)
            ·
              refine ⟨1315185582125232074502245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3507161552333952198672653 1315185582125232074502245)
              ·
                refine ⟨246597296648481013969171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1315185582125232074502245 246597296648481013969171)
                ·
                  refine ⟨369895944972721520953757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246597296648481013969171 369895944972721520953757)
                  ·
                    refine ⟨138710979364770570357659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 369895944972721520953757 138710979364770570357659)
                    ·
                      rfl

theorem cell22_405208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_405208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405208 prefixEnd_405208 := by exact prefixLift 405208
  have htrace : WordTrace (prefixWord ++ tailWord_405208) baseStart_405208 baseEnd_405208 := by
    simpa [prefixWord, tailWord_405208, baseEnd_405208] using wordTrace_append hprefix tailTrace_405208
  have hstable : (prefixWord ++ tailWord_405208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405208).length < 2 ^ (prefixWord ++ tailWord_405208).sum := by decide
  have hdescent : baseEnd_405208 < baseStart_405208 := by decide
  rcases family_descends (prefixWord ++ tailWord_405208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405255 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 5]
def baseStart_405255 : Nat := 118140960795 + 405255 * 2 ^ 59
def prefixEnd_405255 : Nat := 4983230072969 + 3 ^ 40 * 405255 * 2
def baseEnd_405255 : Nat := 46242356141759371477505

theorem tailTrace_405255 : CollatzResearch.WordTrace tailWord_405255 prefixEnd_405255 46242356141759371477505 := by
  unfold tailWord_405255
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780864146837821888857219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9853909431225214592571479 14780864146837821888857219)
  ·
    refine ⟨22171296220256732833285829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14780864146837821888857219 22171296220256732833285829)
    ·
      refine ⟨4157118041298137406241093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22171296220256732833285829 4157118041298137406241093)
      ·
        refine ⟨779459632743400763670205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4157118041298137406241093 779459632743400763670205)
        ·
          refine ⟨292297362278775286376327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779459632743400763670205 292297362278775286376327)
          ·
            refine ⟨438446043418162929564491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292297362278775286376327 438446043418162929564491)
            ·
              refine ⟨657669065127244394346737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438446043418162929564491 657669065127244394346737)
              ·
                refine ⟨493251798845433295760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657669065127244394346737 493251798845433295760053)
                ·
                  refine ⟨46242356141759371477505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493251798845433295760053 46242356141759371477505)
                  ·
                    rfl

theorem cell22_405255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 5].length) (baseStart_405255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405255 prefixEnd_405255 := by exact prefixLift 405255
  have htrace : WordTrace (prefixWord ++ tailWord_405255) baseStart_405255 baseEnd_405255 := by
    simpa [prefixWord, tailWord_405255, baseEnd_405255] using wordTrace_append hprefix tailTrace_405255
  have hstable : (prefixWord ++ tailWord_405255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405255).length < 2 ^ (prefixWord ++ tailWord_405255).sum := by decide
  have hdescent : baseEnd_405255 < baseStart_405255 := by decide
  rcases family_descends (prefixWord ++ tailWord_405255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405279 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_405279 : Nat := 118140960795 + 405279 * 2 ^ 59
def prefixEnd_405279 : Nat := 4983230072969 + 3 ^ 40 * 405279 * 2
def baseEnd_405279 : Nat := 138735284115750051832441

theorem tailTrace_405279 : CollatzResearch.WordTrace tailWord_405279 prefixEnd_405279 138735284115750051832441 := by
  unfold tailWord_405279
  simp only [CollatzResearch.WordTrace]
  refine ⟨14781739498750873987730891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9854492999167249325153927 14781739498750873987730891)
  ·
    refine ⟨22172609248126310981596337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14781739498750873987730891 22172609248126310981596337)
    ·
      refine ⟨16629456936094733236197253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22172609248126310981596337 16629456936094733236197253)
      ·
        refine ⟨3118023175517762481786985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16629456936094733236197253 3118023175517762481786985)
        ·
          refine ⟨2338517381638321861340239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118023175517762481786985 2338517381638321861340239)
          ·
            refine ⟨3507776072457482792010359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338517381638321861340239 3507776072457482792010359)
            ·
              refine ⟨5261664108686224188015539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507776072457482792010359 5261664108686224188015539)
              ·
                refine ⟨7892496163029336282023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261664108686224188015539 7892496163029336282023309)
                ·
                  refine ⟨2959686061136001105758741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7892496163029336282023309 2959686061136001105758741)
                  ·
                    refine ⟨138735284115750051832441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2959686061136001105758741 138735284115750051832441)
                    ·
                      rfl

theorem cell22_405279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_405279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405279 prefixEnd_405279 := by exact prefixLift 405279
  have htrace : WordTrace (prefixWord ++ tailWord_405279) baseStart_405279 baseEnd_405279 := by
    simpa [prefixWord, tailWord_405279, baseEnd_405279] using wordTrace_append hprefix tailTrace_405279
  have hstable : (prefixWord ++ tailWord_405279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405279).length < 2 ^ (prefixWord ++ tailWord_405279).sum := by decide
  have hdescent : baseEnd_405279 < baseStart_405279 := by decide
  rcases family_descends (prefixWord ++ tailWord_405279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405281 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_405281 : Nat := 118140960795 + 405281 * 2 ^ 59
def prefixEnd_405281 : Nat := 4983230072969 + 3 ^ 40 * 405281 * 2
def baseEnd_405281 : Nat := 138735968756622713282435

theorem tailTrace_405281 : CollatzResearch.WordTrace tailWord_405281 prefixEnd_405281 138735968756622713282435 := by
  unfold tailWord_405281
  simp only [CollatzResearch.WordTrace]
  refine ⟨14781812444743628329303697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9854541629829085552869131 14781812444743628329303697)
  ·
    refine ⟨11086359333557721246977773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14781812444743628329303697 11086359333557721246977773)
    ·
      refine ⟨4157384750084145467616665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11086359333557721246977773 4157384750084145467616665)
      ·
        refine ⟨3118038562563109100712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157384750084145467616665 3118038562563109100712499)
        ·
          refine ⟨4677057843844663651068749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118038562563109100712499 4677057843844663651068749)
          ·
            refine ⟨1753896691441748869150781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4677057843844663651068749 1753896691441748869150781)
            ·
              refine ⟨657711259290655825931543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753896691441748869150781 657711259290655825931543)
              ·
                refine ⟨986566888935983738897315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657711259290655825931543 986566888935983738897315)
                ·
                  refine ⟨1479850333403975608345973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986566888935983738897315 1479850333403975608345973)
                  ·
                    refine ⟨138735968756622713282435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1479850333403975608345973 138735968756622713282435)
                    ·
                      rfl

theorem cell22_405281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_405281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405281 prefixEnd_405281 := by exact prefixLift 405281
  have htrace : WordTrace (prefixWord ++ tailWord_405281) baseStart_405281 baseEnd_405281 := by
    simpa [prefixWord, tailWord_405281, baseEnd_405281] using wordTrace_append hprefix tailTrace_405281
  have hstable : (prefixWord ++ tailWord_405281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405281).length < 2 ^ (prefixWord ++ tailWord_405281).sum := by decide
  have hdescent : baseEnd_405281 < baseStart_405281 := by decide
  rcases family_descends (prefixWord ++ tailWord_405281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405300 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_405300 : Nat := 118140960795 + 405300 * 2 ^ 59
def prefixEnd_405300 : Nat := 4983230072969 + 3 ^ 40 * 405300 * 2
def baseEnd_405300 : Nat := 46247490948304332352459

theorem tailTrace_405300 : CollatzResearch.WordTrace tailWord_405300 prefixEnd_405300 46247490948304332352459 := by
  unfold tailWord_405300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391252715837397287122677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9855003621116529716163569 7391252715837397287122677)
  ·
    refine ⟨692929942109755995667751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7391252715837397287122677 692929942109755995667751)
    ·
      refine ⟨1039394913164633993501627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692929942109755995667751 1039394913164633993501627)
      ·
        refine ⟨1559092369746950990252441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039394913164633993501627 1559092369746950990252441)
        ·
          refine ⟨1169319277310213242689331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559092369746950990252441 1169319277310213242689331)
          ·
            refine ⟨1753978915965319864033997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169319277310213242689331 1753978915965319864033997)
            ·
              refine ⟨657742093486994949012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753978915965319864033997 657742093486994949012749)
              ·
                refine ⟨246653285057623105879781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 657742093486994949012749 246653285057623105879781)
                ·
                  refine ⟨46247490948304332352459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246653285057623105879781 46247490948304332352459)
                  ·
                    rfl

theorem cell22_405300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_405300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405300 prefixEnd_405300 := by exact prefixLift 405300
  have htrace : WordTrace (prefixWord ++ tailWord_405300) baseStart_405300 baseEnd_405300 := by
    simpa [prefixWord, tailWord_405300, baseEnd_405300] using wordTrace_append hprefix tailTrace_405300
  have hstable : (prefixWord ++ tailWord_405300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405300).length < 2 ^ (prefixWord ++ tailWord_405300).sum := by decide
  have hdescent : baseEnd_405300 < baseStart_405300 := by decide
  rcases family_descends (prefixWord ++ tailWord_405300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405311 : List Nat := [1, 1, 2, 2, 6, 2, 8]
def baseStart_405311 : Nat := 118140960795 + 405311 * 2 ^ 59
def prefixEnd_405311 : Nat := 4983230072969 + 3 ^ 40 * 405311 * 2
def baseEnd_405311 : Nat := 5138749569248616112309

theorem tailTrace_405311 : CollatzResearch.WordTrace tailWord_405311 prefixEnd_405311 5138749569248616112309 := by
  unfold tailWord_405311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782906634634943452895787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9855271089756628968597191 14782906634634943452895787)
  ·
    refine ⟨22174359951952415179343681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14782906634634943452895787 22174359951952415179343681)
    ·
      refine ⟨16630769963964311384507761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22174359951952415179343681 16630769963964311384507761)
      ·
        refine ⟨12473077472973233538380821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16630769963964311384507761 12473077472973233538380821)
        ·
          refine ⟨584675506545620322111601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12473077472973233538380821 584675506545620322111601)
          ·
            refine ⟨438506629909215241583701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584675506545620322111601 438506629909215241583701)
            ·
              refine ⟨5138749569248616112309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 438506629909215241583701 5138749569248616112309)
              ·
                rfl

theorem cell22_405311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 8].length) (baseStart_405311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405311 prefixEnd_405311 := by exact prefixLift 405311
  have htrace : WordTrace (prefixWord ++ tailWord_405311) baseStart_405311 baseEnd_405311 := by
    simpa [prefixWord, tailWord_405311, baseEnd_405311] using wordTrace_append hprefix tailTrace_405311
  have hstable : (prefixWord ++ tailWord_405311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405311).length < 2 ^ (prefixWord ++ tailWord_405311).sum := by decide
  have hdescent : baseEnd_405311 < baseStart_405311 := by decide
  rcases family_descends (prefixWord ++ tailWord_405311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405332 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_405332 : Nat := 118140960795 + 405332 * 2 ^ 59
def prefixEnd_405332 : Nat := 4983230072969 + 3 ^ 40 * 405332 * 2
def baseEnd_405332 : Nat := 138753427098875580257279

theorem tailTrace_405332 : CollatzResearch.WordTrace tailWord_405332 prefixEnd_405332 138753427098875580257279 := by
  unfold tailWord_405332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391836283779432019705125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9855781711705909359606833 7391836283779432019705125)
  ·
    refine ⟨1385969303208643503694711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7391836283779432019705125 1385969303208643503694711)
    ·
      refine ⟨2078953954812965255542067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385969303208643503694711 2078953954812965255542067)
      ·
        refine ⟨3118430932219447883313101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078953954812965255542067 3118430932219447883313101)
        ·
          refine ⟨1169411599582292956242413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3118430932219447883313101 1169411599582292956242413)
          ·
            refine ⟨438529349843359858590905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169411599582292956242413 438529349843359858590905)
            ·
              refine ⟨328897012382519893943179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438529349843359858590905 328897012382519893943179)
              ·
                refine ⟨493345518573779840914769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328897012382519893943179 493345518573779840914769)
                ·
                  refine ⟨370009138930334880686077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493345518573779840914769 370009138930334880686077)
                  ·
                    refine ⟨138753427098875580257279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370009138930334880686077 138753427098875580257279)
                    ·
                      rfl

theorem cell22_405332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_405332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405332 prefixEnd_405332 := by exact prefixLift 405332
  have htrace : WordTrace (prefixWord ++ tailWord_405332) baseStart_405332 baseEnd_405332 := by
    simpa [prefixWord, tailWord_405332, baseEnd_405332] using wordTrace_append hprefix tailTrace_405332
  have hstable : (prefixWord ++ tailWord_405332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405332).length < 2 ^ (prefixWord ++ tailWord_405332).sum := by decide
  have hdescent : baseEnd_405332 < baseStart_405332 := by decide
  rcases family_descends (prefixWord ++ tailWord_405332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_405431 : Nat := 118140960795 + 405431 * 2 ^ 59
def prefixEnd_405431 : Nat := 4983230072969 + 3 ^ 40 * 405431 * 2
def baseEnd_405431 : Nat := 138787316822072322031975

theorem tailTrace_405431 : CollatzResearch.WordTrace tailWord_405431 prefixEnd_405431 138787316822072322031975 := by
  unfold tailWord_405431
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787283394200203947264147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858188929466802631509431 14787283394200203947264147)
  ·
    refine ⟨22180925091300305920896221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787283394200203947264147 22180925091300305920896221)
    ·
      refine ⟨8317846909237614720336083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22180925091300305920896221 8317846909237614720336083)
      ·
        refine ⟨12476770363856422080504125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317846909237614720336083 12476770363856422080504125)
        ·
          refine ⟨4678788886446158280189047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12476770363856422080504125 4678788886446158280189047)
          ·
            refine ⟨7018183329669237420283571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678788886446158280189047 7018183329669237420283571)
            ·
              refine ⟨10527274994503856130425357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018183329669237420283571 10527274994503856130425357)
              ·
                refine ⟨3947728122938946048909509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527274994503856130425357 3947728122938946048909509)
                ·
                  refine ⟨740199023051052384170533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3947728122938946048909509 740199023051052384170533)
                  ·
                    refine ⟨138787316822072322031975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740199023051052384170533 138787316822072322031975)
                    ·
                      rfl

theorem cell22_405431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_405431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405431 prefixEnd_405431 := by exact prefixLift 405431
  have htrace : WordTrace (prefixWord ++ tailWord_405431) baseStart_405431 baseEnd_405431 := by
    simpa [prefixWord, tailWord_405431, baseEnd_405431] using wordTrace_append hprefix tailTrace_405431
  have hstable : (prefixWord ++ tailWord_405431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405431).length < 2 ^ (prefixWord ++ tailWord_405431).sum := by decide
  have hdescent : baseEnd_405431 < baseStart_405431 := by decide
  rcases family_descends (prefixWord ++ tailWord_405431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405433 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_405433 : Nat := 118140960795 + 405433 * 2 ^ 59
def prefixEnd_405433 : Nat := 4983230072969 + 3 ^ 40 * 405433 * 2
def baseEnd_405433 : Nat := 138788001462944983481969

theorem tailTrace_405433 : CollatzResearch.WordTrace tailWord_405433 prefixEnd_405433 138788001462944983481969 := by
  unfold tailWord_405433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787356340192958288836953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858237560128638859224635 14787356340192958288836953)
  ·
    refine ⟨11090517255144718716627715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14787356340192958288836953 11090517255144718716627715)
    ·
      refine ⟨16635775882717078074941573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090517255144718716627715 16635775882717078074941573)
      ·
        refine ⟨3119207978009452139051545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16635775882717078074941573 3119207978009452139051545)
        ·
          refine ⟨2339405983507089104288659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119207978009452139051545 2339405983507089104288659)
          ·
            refine ⟨3509108975260633656432989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339405983507089104288659 3509108975260633656432989)
            ·
              refine ⟨1315915865722737621162371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3509108975260633656432989 1315915865722737621162371)
              ·
                refine ⟨1973873798584106431743557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315915865722737621162371 1973873798584106431743557)
                ·
                  refine ⟨370101337234519955951917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973873798584106431743557 370101337234519955951917)
                  ·
                    refine ⟨138788001462944983481969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370101337234519955951917 138788001462944983481969)
                    ·
                      rfl

theorem cell22_405433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_405433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405433 prefixEnd_405433 := by exact prefixLift 405433
  have htrace : WordTrace (prefixWord ++ tailWord_405433) baseStart_405433 baseEnd_405433 := by
    simpa [prefixWord, tailWord_405433, baseEnd_405433] using wordTrace_append hprefix tailTrace_405433
  have hstable : (prefixWord ++ tailWord_405433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405433).length < 2 ^ (prefixWord ++ tailWord_405433).sum := by decide
  have hdescent : baseEnd_405433 < baseStart_405433 := by decide
  rcases family_descends (prefixWord ++ tailWord_405433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405469 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 4]
def baseStart_405469 : Nat := 118140960795 + 405469 * 2 ^ 59
def prefixEnd_405469 : Nat := 4983230072969 + 3 ^ 40 * 405469 * 2
def baseEnd_405469 : Nat := 46266774999550963193953

theorem tailTrace_405469 : CollatzResearch.WordTrace tailWord_405469 prefixEnd_405469 46266774999550963193953 := by
  unfold tailWord_405469
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788669368062536437147461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9859112912041690958098307 14788669368062536437147461)
  ·
    refine ⟨2772875506511725581965149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14788669368062536437147461 2772875506511725581965149)
    ·
      refine ⟨1039828314941897093236931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2772875506511725581965149 1039828314941897093236931)
      ·
        refine ⟨1559742472412845639855397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039828314941897093236931 1559742472412845639855397)
        ·
          refine ⟨292451713577408557472887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1559742472412845639855397 292451713577408557472887)
          ·
            refine ⟨438677570366112836209331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292451713577408557472887 438677570366112836209331)
            ·
              refine ⟨658016355549169254313997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438677570366112836209331 658016355549169254313997)
              ·
                refine ⟨246756133330938470367749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 658016355549169254313997 246756133330938470367749)
                ·
                  refine ⟨46266774999550963193953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246756133330938470367749 46266774999550963193953)
                  ·
                    rfl

theorem cell22_405469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_405469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405469 prefixEnd_405469 := by exact prefixLift 405469
  have htrace : WordTrace (prefixWord ++ tailWord_405469) baseStart_405469 baseEnd_405469 := by
    simpa [prefixWord, tailWord_405469, baseEnd_405469] using wordTrace_append hprefix tailTrace_405469
  have hstable : (prefixWord ++ tailWord_405469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405469).length < 2 ^ (prefixWord ++ tailWord_405469).sum := by decide
  have hdescent : baseEnd_405469 < baseStart_405469 := by decide
  rcases family_descends (prefixWord ++ tailWord_405469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405546 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_405546 : Nat := 118140960795 + 405546 * 2 ^ 59
def prefixEnd_405546 : Nat := 4983230072969 + 3 ^ 40 * 405546 * 2
def baseEnd_405546 : Nat := 138826683672250355406623

theorem tailTrace_405546 : CollatzResearch.WordTrace tailWord_405546 prefixEnd_405546 138826683672250355406623 := by
  unfold tailWord_405546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697869447195894646925123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9860985192522385725133661 3697869447195894646925123)
  ·
    refine ⟨5546804170793841970387685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3697869447195894646925123 5546804170793841970387685)
    ·
      refine ⟨1040025782023845369447691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5546804170793841970387685 1040025782023845369447691)
      ·
        refine ⟨1560038673035768054171537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040025782023845369447691 1560038673035768054171537)
        ·
          refine ⟨1170029004776826040628653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560038673035768054171537 1170029004776826040628653)
          ·
            refine ⟨438760876791309765235745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1170029004776826040628653 438760876791309765235745)
            ·
              refine ⟨329070657593482323926809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438760876791309765235745 329070657593482323926809)
              ·
                refine ⟨246802993195111742945107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329070657593482323926809 246802993195111742945107)
                ·
                  refine ⟨370204489792667614417661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246802993195111742945107 370204489792667614417661)
                  ·
                    refine ⟨138826683672250355406623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370204489792667614417661 138826683672250355406623)
                    ·
                      rfl

theorem cell22_405546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_405546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405546 prefixEnd_405546 := by exact prefixLift 405546
  have htrace : WordTrace (prefixWord ++ tailWord_405546) baseStart_405546 baseEnd_405546 := by
    simpa [prefixWord, tailWord_405546, baseEnd_405546] using wordTrace_append hprefix tailTrace_405546
  have hstable : (prefixWord ++ tailWord_405546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405546).length < 2 ^ (prefixWord ++ tailWord_405546).sum := by decide
  have hdescent : baseEnd_405546 < baseStart_405546 := by decide
  rcases family_descends (prefixWord ++ tailWord_405546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405568 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_405568 : Nat := 118140960795 + 405568 * 2 ^ 59
def prefixEnd_405568 : Nat := 4983230072969 + 3 ^ 40 * 405568 * 2
def baseEnd_405568 : Nat := 138834214721849631356555

theorem tailTrace_405568 : CollatzResearch.WordTrace tailWord_405568 prefixEnd_405568 138834214721849631356555 := by
  unfold tailWord_405568
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396140097351938172500679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9861520129802584230000905 7396140097351938172500679)
  ·
    refine ⟨11094210146027907258751019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396140097351938172500679 11094210146027907258751019)
    ·
      refine ⟨16641315219041860888126529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094210146027907258751019 16641315219041860888126529)
      ·
        refine ⟨12480986414281395666094897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16641315219041860888126529 12480986414281395666094897)
        ·
          refine ⟨9360739810711046749571173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12480986414281395666094897 9360739810711046749571173)
          ·
            refine ⟨1755138714508321265544595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9360739810711046749571173 1755138714508321265544595)
            ·
              refine ⟨2632708071762481898316893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755138714508321265544595 2632708071762481898316893)
              ·
                refine ⟨987265526910930711868835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632708071762481898316893 987265526910930711868835)
                ·
                  refine ⟨1480898290366396067803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987265526910930711868835 1480898290366396067803253)
                  ·
                    refine ⟨138834214721849631356555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1480898290366396067803253 138834214721849631356555)
                    ·
                      rfl

theorem cell22_405568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_405568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405568 prefixEnd_405568 := by exact prefixLift 405568
  have htrace : WordTrace (prefixWord ++ tailWord_405568) baseStart_405568 baseEnd_405568 := by
    simpa [prefixWord, tailWord_405568, baseEnd_405568] using wordTrace_append hprefix tailTrace_405568
  have hstable : (prefixWord ++ tailWord_405568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405568).length < 2 ^ (prefixWord ++ tailWord_405568).sum := by decide
  have hdescent : baseEnd_405568 < baseStart_405568 := by decide
  rcases family_descends (prefixWord ++ tailWord_405568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405660 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_405660 : Nat := 118140960795 + 405660 * 2 ^ 59
def prefixEnd_405660 : Nat := 4983230072969 + 3 ^ 40 * 405660 * 2
def baseEnd_405660 : Nat := 46288569400664019352091

theorem tailTrace_405660 : CollatzResearch.WordTrace tailWord_405660 prefixEnd_405660 46288569400664019352091 := by
  unfold tailWord_405660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397817855185288028675217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9863757140247050704900289 7397817855185288028675217)
  ·
    refine ⟨5548363391388966021506413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7397817855185288028675217 5548363391388966021506413)
    ·
      refine ⟨2080636271770862258064905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5548363391388966021506413 2080636271770862258064905)
      ·
        refine ⟨1560477203828146693548679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2080636271770862258064905 1560477203828146693548679)
        ·
          refine ⟨2340715805742220040323019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560477203828146693548679 2340715805742220040323019)
          ·
            refine ⟨3511073708613330060484529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340715805742220040323019 3511073708613330060484529)
            ·
              refine ⟨2633305281459997545363397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511073708613330060484529 2633305281459997545363397)
              ·
                refine ⟨493744740273749539755637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2633305281459997545363397 493744740273749539755637)
                ·
                  refine ⟨46288569400664019352091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493744740273749539755637 46288569400664019352091)
                  ·
                    rfl

theorem cell22_405660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_405660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405660 prefixEnd_405660 := by exact prefixLift 405660
  have htrace : WordTrace (prefixWord ++ tailWord_405660) baseStart_405660 baseEnd_405660 := by
    simpa [prefixWord, tailWord_405660, baseEnd_405660] using wordTrace_append hprefix tailTrace_405660
  have hstable : (prefixWord ++ tailWord_405660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405660).length < 2 ^ (prefixWord ++ tailWord_405660).sum := by decide
  have hdescent : baseEnd_405660 < baseStart_405660 := by decide
  rcases family_descends (prefixWord ++ tailWord_405660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405677 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 5]
def baseStart_405677 : Nat := 118140960795 + 405677 * 2 ^ 59
def prefixEnd_405677 : Nat := 4983230072969 + 3 ^ 40 * 405677 * 2
def baseEnd_405677 : Nat := 46290509216469893460407

theorem tailTrace_405677 : CollatzResearch.WordTrace tailWord_405677 prefixEnd_405677 46290509216469893460407 := by
  unfold tailWord_405677
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796255751308987960719285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9864170500872658640479523 14796255751308987960719285)
  ·
    refine ⟨1387148976685217621317433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14796255751308987960719285 1387148976685217621317433)
    ·
      refine ⟨1040361732513913215988075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1387148976685217621317433 1040361732513913215988075)
      ·
        refine ⟨1560542598770869823982113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040361732513913215988075 1560542598770869823982113)
        ·
          refine ⟨1170406949078152367986585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560542598770869823982113 1170406949078152367986585)
          ·
            refine ⟨877805211808614275989939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170406949078152367986585 877805211808614275989939)
            ·
              refine ⟨1316707817712921413984909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877805211808614275989939 1316707817712921413984909)
              ·
                refine ⟨493765431642345530244341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316707817712921413984909 493765431642345530244341)
                ·
                  refine ⟨46290509216469893460407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493765431642345530244341 46290509216469893460407)
                  ·
                    rfl

theorem cell22_405677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_405677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405677 prefixEnd_405677 := by exact prefixLift 405677
  have htrace : WordTrace (prefixWord ++ tailWord_405677) baseStart_405677 baseEnd_405677 := by
    simpa [prefixWord, tailWord_405677, baseEnd_405677] using wordTrace_append hprefix tailTrace_405677
  have hstable : (prefixWord ++ tailWord_405677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405677).length < 2 ^ (prefixWord ++ tailWord_405677).sum := by decide
  have hdescent : baseEnd_405677 < baseStart_405677 := by decide
  rcases family_descends (prefixWord ++ tailWord_405677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405688 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_405688 : Nat := 118140960795 + 405688 * 2 ^ 59
def prefixEnd_405688 : Nat := 4983230072969 + 3 ^ 40 * 405688 * 2
def baseEnd_405688 : Nat := 46291764391403106118729

theorem tailTrace_405688 : CollatzResearch.WordTrace tailWord_405688 prefixEnd_405688 46291764391403106118729 := by
  unfold tailWord_405688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398328477134568419684859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9864437969512757892913145 7398328477134568419684859)
  ·
    refine ⟨11097492715701852629527289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398328477134568419684859 11097492715701852629527289)
    ·
      refine ⟨8323119536776389472145467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097492715701852629527289 8323119536776389472145467)
      ·
        refine ⟨12484679305164584208218201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323119536776389472145467 12484679305164584208218201)
        ·
          refine ⟨9363509478873438156163651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12484679305164584208218201 9363509478873438156163651)
          ·
            refine ⟨14045264218310157234245477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9363509478873438156163651 14045264218310157234245477)
            ·
              refine ⟨2633487040933154481421027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14045264218310157234245477 2633487040933154481421027)
              ·
                refine ⟨3950230561399731722131541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633487040933154481421027 3950230561399731722131541)
                ·
                  refine ⟨46291764391403106118729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3950230561399731722131541 46291764391403106118729)
                  ·
                    rfl

theorem cell22_405688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_405688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405688 prefixEnd_405688 := by exact prefixLift 405688
  have htrace : WordTrace (prefixWord ++ tailWord_405688) baseStart_405688 baseEnd_405688 := by
    simpa [prefixWord, tailWord_405688, baseEnd_405688] using wordTrace_append hprefix tailTrace_405688
  have hstable : (prefixWord ++ tailWord_405688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405688).length < 2 ^ (prefixWord ++ tailWord_405688).sum := by decide
  have hdescent : baseEnd_405688 < baseStart_405688 := by decide
  rcases family_descends (prefixWord ++ tailWord_405688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405707 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 1, 4]
def baseStart_405707 : Nat := 118140960795 + 405707 * 2 ^ 59
def prefixEnd_405707 : Nat := 4983230072969 + 3 ^ 40 * 405707 * 2
def baseEnd_405707 : Nat := 138881797262499602131129

theorem tailTrace_405707 : CollatzResearch.WordTrace tailWord_405707 prefixEnd_405707 138881797262499602131129 := by
  unfold tailWord_405707
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797349941200303084311375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9864899960800202056207583 14797349941200303084311375)
  ·
    refine ⟨22196024911800454626467063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14797349941200303084311375 22196024911800454626467063)
    ·
      refine ⟨33294037367700681939700595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22196024911800454626467063 33294037367700681939700595)
      ·
        refine ⟨49941056051551022909550893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33294037367700681939700595 49941056051551022909550893)
        ·
          refine ⟨18727896019331633591081585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49941056051551022909550893 18727896019331633591081585)
          ·
            refine ⟨14045922014498725193311189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18727896019331633591081585 14045922014498725193311189)
            ·
              refine ⟨329201297214813871718231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14045922014498725193311189 329201297214813871718231)
              ·
                refine ⟨493801945822220807577347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329201297214813871718231 493801945822220807577347)
                ·
                  refine ⟨740702918733331211366021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493801945822220807577347 740702918733331211366021)
                  ·
                    refine ⟨138881797262499602131129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740702918733331211366021 138881797262499602131129)
                    ·
                      rfl

theorem cell22_405707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 4].length) (baseStart_405707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405707 prefixEnd_405707 := by exact prefixLift 405707
  have htrace : WordTrace (prefixWord ++ tailWord_405707) baseStart_405707 baseEnd_405707 := by
    simpa [prefixWord, tailWord_405707, baseEnd_405707] using wordTrace_append hprefix tailTrace_405707
  have hstable : (prefixWord ++ tailWord_405707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405707).length < 2 ^ (prefixWord ++ tailWord_405707).sum := by decide
  have hdescent : baseEnd_405707 < baseStart_405707 := by decide
  rcases family_descends (prefixWord ++ tailWord_405707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405750 : List Nat := [5, 1, 1, 1, 1, 1, 2, 10]
def baseStart_405750 : Nat := 118140960795 + 405750 * 2 ^ 59
def prefixEnd_405750 : Nat := 4983230072969 + 3 ^ 40 * 405750 * 2
def baseEnd_405750 : Nat := 15432946337917980367333

theorem tailTrace_405750 : CollatzResearch.WordTrace tailWord_405750 prefixEnd_405750 15432946337917980367333 := by
  unfold tailWord_405750
  simp only [CollatzResearch.WordTrace]
  refine ⟨924932392502782589257919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9865945520029680952084469 924932392502782589257919)
  ·
    refine ⟨1387398588754173883886879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924932392502782589257919 1387398588754173883886879)
    ·
      refine ⟨2081097883131260825830319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387398588754173883886879 2081097883131260825830319)
      ·
        refine ⟨3121646824696891238745479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081097883131260825830319 3121646824696891238745479)
        ·
          refine ⟨4682470237045336858118219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121646824696891238745479 4682470237045336858118219)
          ·
            refine ⟨7023705355568005287177329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682470237045336858118219 7023705355568005287177329)
            ·
              refine ⟨5267779016676003965382997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7023705355568005287177329 5267779016676003965382997)
              ·
                refine ⟨15432946337917980367333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5267779016676003965382997 15432946337917980367333)
                ·
                  rfl

theorem cell22_405750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_405750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405750 prefixEnd_405750 := by exact prefixLift 405750
  have htrace : WordTrace (prefixWord ++ tailWord_405750) baseStart_405750 baseEnd_405750 := by
    simpa [prefixWord, tailWord_405750, baseEnd_405750] using wordTrace_append hprefix tailTrace_405750
  have hstable : (prefixWord ++ tailWord_405750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405750).length < 2 ^ (prefixWord ++ tailWord_405750).sum := by decide
  have hdescent : baseEnd_405750 < baseStart_405750 := by decide
  rcases family_descends (prefixWord ++ tailWord_405750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405767 : List Nat := [1, 1, 4, 5, 1, 1, 9]
def baseStart_405767 : Nat := 118140960795 + 405767 * 2 ^ 59
def prefixEnd_405767 : Nat := 4983230072969 + 3 ^ 40 * 405767 * 2
def baseEnd_405767 : Nat := 5144530981062201690035

theorem tailTrace_405767 : CollatzResearch.WordTrace tailWord_405767 prefixEnd_405767 5144530981062201690035 := by
  unfold tailWord_405767
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799538320982933331495555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9866358880655288887663703 14799538320982933331495555)
  ·
    refine ⟨22199307481474399997243333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14799538320982933331495555 22199307481474399997243333)
    ·
      refine ⟨4162370152776449999483125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22199307481474399997243333 4162370152776449999483125)
      ·
        refine ⟨390222201822792187451543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4162370152776449999483125 390222201822792187451543)
        ·
          refine ⟨585333302734188281177315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390222201822792187451543 585333302734188281177315)
          ·
            refine ⟨877999954101282421765973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585333302734188281177315 877999954101282421765973)
            ·
              refine ⟨5144530981062201690035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 877999954101282421765973 5144530981062201690035)
              ·
                rfl

theorem cell22_405767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 9].length) (baseStart_405767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405767 prefixEnd_405767 := by exact prefixLift 405767
  have htrace : WordTrace (prefixWord ++ tailWord_405767) baseStart_405767 baseEnd_405767 := by
    simpa [prefixWord, tailWord_405767, baseEnd_405767] using wordTrace_append hprefix tailTrace_405767
  have hstable : (prefixWord ++ tailWord_405767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405767).length < 2 ^ (prefixWord ++ tailWord_405767).sum := by decide
  have hdescent : baseEnd_405767 < baseStart_405767 := by decide
  rcases family_descends (prefixWord ++ tailWord_405767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405812 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_405812 : Nat := 118140960795 + 405812 * 2 ^ 59
def prefixEnd_405812 : Nat := 4983230072969 + 3 ^ 40 * 405812 * 2
def baseEnd_405812 : Nat := 46305913636104776085269

theorem tailTrace_405812 : CollatzResearch.WordTrace tailWord_405812 prefixEnd_405812 46305913636104776085269 := by
  unfold tailWord_405812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400589802909953008441845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9867453070546604011255793 7400589802909953008441845)
  ·
    refine ⟨693805294022808094541423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7400589802909953008441845 693805294022808094541423)
    ·
      refine ⟨1040707941034212141812135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693805294022808094541423 1040707941034212141812135)
      ·
        refine ⟨1561061911551318212718203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040707941034212141812135 1561061911551318212718203)
        ·
          refine ⟨2341592867326977319077305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561061911551318212718203 2341592867326977319077305)
          ·
            refine ⟨1756194650495232989307979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2341592867326977319077305 1756194650495232989307979)
            ·
              refine ⟨2634291975742849483961969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756194650495232989307979 2634291975742849483961969)
              ·
                refine ⟨1975718981807137112971477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634291975742849483961969 1975718981807137112971477)
                ·
                  refine ⟨46305913636104776085269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1975718981807137112971477 46305913636104776085269)
                  ·
                    rfl

theorem cell22_405812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_405812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405812 prefixEnd_405812 := by exact prefixLift 405812
  have htrace : WordTrace (prefixWord ++ tailWord_405812) baseStart_405812 baseEnd_405812 := by
    simpa [prefixWord, tailWord_405812, baseEnd_405812] using wordTrace_append hprefix tailTrace_405812
  have hstable : (prefixWord ++ tailWord_405812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405812).length < 2 ^ (prefixWord ++ tailWord_405812).sum := by decide
  have hdescent : baseEnd_405812 < baseStart_405812 := by decide
  rcases family_descends (prefixWord ++ tailWord_405812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405872 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_405872 : Nat := 118140960795 + 405872 * 2 ^ 59
def prefixEnd_405872 : Nat := 4983230072969 + 3 ^ 40 * 405872 * 2
def baseEnd_405872 : Nat := 138938280134494171755623

theorem tailTrace_405872 : CollatzResearch.WordTrace tailWord_405872 prefixEnd_405872 138938280134494171755623 := by
  unfold tailWord_405872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401683992801268132033935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9868911990401690842711913 7401683992801268132033935)
  ·
    refine ⟨11102525989201902198050903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401683992801268132033935 11102525989201902198050903)
    ·
      refine ⟨16653788983802853297076355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102525989201902198050903 16653788983802853297076355)
      ·
        refine ⟨24980683475704279945614533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16653788983802853297076355 24980683475704279945614533)
        ·
          refine ⟨4683878151694552489802725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24980683475704279945614533 4683878151694552489802725)
          ·
            refine ⟨878227153442728591838011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4683878151694552489802725 878227153442728591838011)
            ·
              refine ⟨1317340730164092887757017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878227153442728591838011 1317340730164092887757017)
              ·
                refine ⟨988005547623069665817763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317340730164092887757017 988005547623069665817763)
                ·
                  refine ⟨1482008321434604498726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988005547623069665817763 1482008321434604498726645)
                  ·
                    refine ⟨138938280134494171755623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1482008321434604498726645 138938280134494171755623)
                    ·
                      rfl

theorem cell22_405872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_405872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405872 prefixEnd_405872 := by exact prefixLift 405872
  have htrace : WordTrace (prefixWord ++ tailWord_405872) baseStart_405872 baseEnd_405872 := by
    simpa [prefixWord, tailWord_405872, baseEnd_405872] using wordTrace_append hprefix tailTrace_405872
  have hstable : (prefixWord ++ tailWord_405872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405872).length < 2 ^ (prefixWord ++ tailWord_405872).sum := by decide
  have hdescent : baseEnd_405872 < baseStart_405872 := by decide
  rcases family_descends (prefixWord ++ tailWord_405872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405885 : List Nat := [1, 4, 1, 1, 2, 13]
def baseStart_405885 : Nat := 118140960795 + 405885 * 2 ^ 59
def prefixEnd_405885 : Nat := 4983230072969 + 3 ^ 40 * 405885 * 2
def baseEnd_405885 : Nat := 1715342349384771249143

theorem tailTrace_405885 : CollatzResearch.WordTrace tailWord_405885 prefixEnd_405885 1715342349384771249143 := by
  unfold tailWord_405885
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803842134555439484291109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9869228089703626322860739 14803842134555439484291109)
  ·
    refine ⟨2775720400229144903304583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14803842134555439484291109 2775720400229144903304583)
    ·
      refine ⟨4163580600343717354956875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775720400229144903304583 4163580600343717354956875)
      ·
        refine ⟨6245370900515576032435313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163580600343717354956875 6245370900515576032435313)
        ·
          refine ⟨4684028175386682024326485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6245370900515576032435313 4684028175386682024326485)
          ·
            refine ⟨1715342349384771249143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4684028175386682024326485 1715342349384771249143)
            ·
              rfl

theorem cell22_405885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 13].length) (baseStart_405885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405885 prefixEnd_405885 := by exact prefixLift 405885
  have htrace : WordTrace (prefixWord ++ tailWord_405885) baseStart_405885 baseEnd_405885 := by
    simpa [prefixWord, tailWord_405885, baseEnd_405885] using wordTrace_append hprefix tailTrace_405885
  have hstable : (prefixWord ++ tailWord_405885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405885).length < 2 ^ (prefixWord ++ tailWord_405885).sum := by decide
  have hdescent : baseEnd_405885 < baseStart_405885 := by decide
  rcases family_descends (prefixWord ++ tailWord_405885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405962 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_405962 : Nat := 118140960795 + 405962 * 2 ^ 59
def prefixEnd_405962 : Nat := 4983230072969 + 3 ^ 40 * 405962 * 2
def baseEnd_405962 : Nat := 138969088973763937005347

theorem tailTrace_405962 : CollatzResearch.WordTrace tailWord_405962 prefixEnd_405962 138969088973763937005347 := by
  unfold tailWord_405962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701662638819120408711035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9871100370184321089896093 3701662638819120408711035)
  ·
    refine ⟨5552493958228680613066553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701662638819120408711035 5552493958228680613066553)
    ·
      refine ⟨4164370468671510459799915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5552493958228680613066553 4164370468671510459799915)
      ·
        refine ⟨6246555703007265689699873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164370468671510459799915 6246555703007265689699873)
        ·
          refine ⟨4684916777255449267274905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6246555703007265689699873 4684916777255449267274905)
          ·
            refine ⟨3513687582941586950456179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4684916777255449267274905 3513687582941586950456179)
            ·
              refine ⟨5270531374412380425684269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513687582941586950456179 5270531374412380425684269)
              ·
                refine ⟨1976449265404642659631601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5270531374412380425684269 1976449265404642659631601)
                ·
                  refine ⟨1482336949053481994723701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976449265404642659631601 1482336949053481994723701)
                  ·
                    refine ⟨138969088973763937005347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1482336949053481994723701 138969088973763937005347)
                    ·
                      rfl

theorem cell22_405962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_405962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_405962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_405962 prefixEnd_405962 := by exact prefixLift 405962
  have htrace : WordTrace (prefixWord ++ tailWord_405962) baseStart_405962 baseEnd_405962 := by
    simpa [prefixWord, tailWord_405962, baseEnd_405962] using wordTrace_append hprefix tailTrace_405962
  have hstable : (prefixWord ++ tailWord_405962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405962).length < 2 ^ (prefixWord ++ tailWord_405962).sum := by decide
  have hdescent : baseEnd_405962 < baseStart_405962 := by decide
  rcases family_descends (prefixWord ++ tailWord_405962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406009 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 4]
def baseStart_406009 : Nat := 118140960795 + 406009 * 2 ^ 59
def prefixEnd_406009 : Nat := 4983230072969 + 3 ^ 40 * 406009 * 2
def baseEnd_406009 : Nat := 46328392678090493693401

theorem tailTrace_406009 : CollatzResearch.WordTrace tailWord_406009 prefixEnd_406009 46328392678090493693401 := by
  unfold tailWord_406009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808364786106208661805081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872243190737472441203387 14808364786106208661805081)
  ·
    refine ⟨11106273589579656496353811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14808364786106208661805081 11106273589579656496353811)
    ·
      refine ⟨16659410384369484744530717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106273589579656496353811 16659410384369484744530717)
      ·
        refine ⟨6247278894138556779199019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16659410384369484744530717 6247278894138556779199019)
        ·
          refine ⟨9370918341207835168798529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247278894138556779199019 9370918341207835168798529)
          ·
            refine ⟨7028188755905876376598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370918341207835168798529 7028188755905876376598897)
            ·
              refine ⟨5271141566929407282449173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028188755905876376598897 5271141566929407282449173)
              ·
                refine ⟨247084760949815966364805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5271141566929407282449173 247084760949815966364805)
                ·
                  refine ⟨46328392678090493693401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247084760949815966364805 46328392678090493693401)
                  ·
                    rfl

theorem cell22_406009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_406009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406009 prefixEnd_406009 := by exact prefixLift 406009
  have htrace : WordTrace (prefixWord ++ tailWord_406009) baseStart_406009 baseEnd_406009 := by
    simpa [prefixWord, tailWord_406009, baseEnd_406009] using wordTrace_append hprefix tailTrace_406009
  have hstable : (prefixWord ++ tailWord_406009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406009).length < 2 ^ (prefixWord ++ tailWord_406009).sum := by decide
  have hdescent : baseEnd_406009 < baseStart_406009 := by decide
  rcases family_descends (prefixWord ++ tailWord_406009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406037 : List Nat := [1, 3, 2, 1, 3, 1, 1, 10]
def baseStart_406037 : Nat := 118140960795 + 406037 * 2 ^ 59
def prefixEnd_406037 : Nat := 4983230072969 + 3 ^ 40 * 406037 * 2
def baseEnd_406037 : Nat := 15443862556276526820013

theorem tailTrace_406037 : CollatzResearch.WordTrace tailWord_406037 prefixEnd_406037 15443862556276526820013 := by
  unfold tailWord_406037
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809386030004769443824365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872924020003179629216243 14809386030004769443824365)
  ·
    refine ⟨5553519761251788541434137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14809386030004769443824365 5553519761251788541434137)
    ·
      refine ⟨4165139820938841406075603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5553519761251788541434137 4165139820938841406075603)
      ·
        refine ⟨6247709731408262109113405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165139820938841406075603 6247709731408262109113405)
        ·
          refine ⟨2342891149278098290917527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6247709731408262109113405 2342891149278098290917527)
          ·
            refine ⟨3514336723917147436376291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342891149278098290917527 3514336723917147436376291)
            ·
              refine ⟨5271505085875721154564437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514336723917147436376291 5271505085875721154564437)
              ·
                refine ⟨15443862556276526820013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5271505085875721154564437 15443862556276526820013)
                ·
                  rfl

theorem cell22_406037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 10].length) (baseStart_406037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406037 prefixEnd_406037 := by exact prefixLift 406037
  have htrace : WordTrace (prefixWord ++ tailWord_406037) baseStart_406037 baseEnd_406037 := by
    simpa [prefixWord, tailWord_406037, baseEnd_406037] using wordTrace_append hprefix tailTrace_406037
  have hstable : (prefixWord ++ tailWord_406037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406037).length < 2 ^ (prefixWord ++ tailWord_406037).sum := by decide
  have hdescent : baseEnd_406037 < baseStart_406037 := by decide
  rcases family_descends (prefixWord ++ tailWord_406037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406056 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_406056 : Nat := 118140960795 + 406056 * 2 ^ 59
def prefixEnd_406056 : Nat := 4983230072969 + 3 ^ 40 * 406056 * 2
def baseEnd_406056 : Nat := 139001267094779025155059

theorem tailTrace_406056 : CollatzResearch.WordTrace tailWord_406056 prefixEnd_406056 139001267094779025155059 := by
  unfold tailWord_406056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405039508467967844383011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9873386011290623792510681 7405039508467967844383011)
  ·
    refine ⟨11107559262701951766574517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405039508467967844383011 11107559262701951766574517)
    ·
      refine ⟨1041333680878307978116361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11107559262701951766574517 1041333680878307978116361)
      ·
        refine ⟨781000260658730983587271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1041333680878307978116361 781000260658730983587271)
        ·
          refine ⟨1171500390988096475380907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781000260658730983587271 1171500390988096475380907)
          ·
            refine ⟨1757250586482144713071361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171500390988096475380907 1757250586482144713071361)
            ·
              refine ⟨1317937939861608534803521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757250586482144713071361 1317937939861608534803521)
              ·
                refine ⟨988453454896206401102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317937939861608534803521 988453454896206401102641)
                ·
                  refine ⟨741340091172154800826981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 988453454896206401102641 741340091172154800826981)
                  ·
                    refine ⟨139001267094779025155059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 741340091172154800826981 139001267094779025155059)
                    ·
                      rfl

theorem cell22_406056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_406056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406056 prefixEnd_406056 := by exact prefixLift 406056
  have htrace : WordTrace (prefixWord ++ tailWord_406056) baseStart_406056 baseEnd_406056 := by
    simpa [prefixWord, tailWord_406056, baseEnd_406056] using wordTrace_append hprefix tailTrace_406056
  have hstable : (prefixWord ++ tailWord_406056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406056).length < 2 ^ (prefixWord ++ tailWord_406056).sum := by decide
  have hdescent : baseEnd_406056 < baseStart_406056 := by decide
  rcases family_descends (prefixWord ++ tailWord_406056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406058 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_406058 : Nat := 118140960795 + 406058 * 2 ^ 59
def prefixEnd_406058 : Nat := 4983230072969 + 3 ^ 40 * 406058 * 2
def baseEnd_406058 : Nat := 139001951735651686605053

theorem tailTrace_406058 : CollatzResearch.WordTrace tailWord_406058 prefixEnd_406058 139001951735651686605053 := by
  unfold tailWord_406058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702537990732172507584707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9873434641952460020225885 3702537990732172507584707)
  ·
    refine ⟨5553806986098258761377061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3702537990732172507584707 5553806986098258761377061)
    ·
      refine ⟨1041338809893423517758199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5553806986098258761377061 1041338809893423517758199)
      ·
        refine ⟨1562008214840135276637299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041338809893423517758199 1562008214840135276637299)
        ·
          refine ⟨2343012322260202914955949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562008214840135276637299 2343012322260202914955949)
          ·
            refine ⟨878629620847576093108481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2343012322260202914955949 878629620847576093108481)
            ·
              refine ⟨658972215635682069831361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878629620847576093108481 658972215635682069831361)
              ·
                refine ⟨494229161726761552373521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658972215635682069831361 494229161726761552373521)
                ·
                  refine ⟨370671871295071164280141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494229161726761552373521 370671871295071164280141)
                  ·
                    refine ⟨139001951735651686605053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370671871295071164280141 139001951735651686605053)
                    ·
                      rfl

theorem cell22_406058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_406058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406058 prefixEnd_406058 := by exact prefixLift 406058
  have htrace : WordTrace (prefixWord ++ tailWord_406058) baseStart_406058 baseEnd_406058 := by
    simpa [prefixWord, tailWord_406058, baseEnd_406058] using wordTrace_append hprefix tailTrace_406058
  have hstable : (prefixWord ++ tailWord_406058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406058).length < 2 ^ (prefixWord ++ tailWord_406058).sum := by decide
  have hdescent : baseEnd_406058 < baseStart_406058 := by decide
  rcases family_descends (prefixWord ++ tailWord_406058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406067 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_406067 : Nat := 118140960795 + 406067 * 2 ^ 59
def prefixEnd_406067 : Nat := 4983230072969 + 3 ^ 40 * 406067 * 2
def baseEnd_406067 : Nat := 139005032619578663130025

theorem tailTrace_406067 : CollatzResearch.WordTrace tailWord_406067 prefixEnd_406067 139005032619578663130025 := by
  unfold tailWord_406067
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810480219896084567416455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9873653479930723044944303 14810480219896084567416455)
  ·
    refine ⟨22215720329844126851124683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14810480219896084567416455 22215720329844126851124683)
    ·
      refine ⟨33323580494766190276687025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22215720329844126851124683 33323580494766190276687025)
      ·
        refine ⟨24992685371074642707515269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33323580494766190276687025 24992685371074642707515269)
        ·
          refine ⟨4686128507076495507659113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24992685371074642707515269 4686128507076495507659113)
          ·
            refine ⟨3514596380307371630744335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686128507076495507659113 3514596380307371630744335)
            ·
              refine ⟨5271894570461057446116503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514596380307371630744335 5271894570461057446116503)
              ·
                refine ⟨7907841855691586169174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271894570461057446116503 7907841855691586169174755)
                ·
                  refine ⟨11861762783537379253762133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907841855691586169174755 11861762783537379253762133)
                  ·
                    refine ⟨139005032619578663130025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11861762783537379253762133 139005032619578663130025)
                    ·
                      rfl

theorem cell22_406067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_406067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406067 prefixEnd_406067 := by exact prefixLift 406067
  have htrace : WordTrace (prefixWord ++ tailWord_406067) baseStart_406067 baseEnd_406067 := by
    simpa [prefixWord, tailWord_406067, baseEnd_406067] using wordTrace_append hprefix tailTrace_406067
  have hstable : (prefixWord ++ tailWord_406067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406067).length < 2 ^ (prefixWord ++ tailWord_406067).sum := by decide
  have hdescent : baseEnd_406067 < baseStart_406067 := by decide
  rcases family_descends (prefixWord ++ tailWord_406067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406103 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 1, 3]
def baseStart_406103 : Nat := 118140960795 + 406103 * 2 ^ 59
def prefixEnd_406103 : Nat := 4983230072969 + 3 ^ 40 * 406103 * 2
def baseEnd_406103 : Nat := 139017356155286569229915

theorem tailTrace_406103 : CollatzResearch.WordTrace tailWord_406103 prefixEnd_406103 139017356155286569229915 := by
  unfold tailWord_406103
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811793247765662715726963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9874528831843775143817975 14811793247765662715726963)
  ·
    refine ⟨22217689871648494073590445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14811793247765662715726963 22217689871648494073590445)
    ·
      refine ⟨8331633701868185277596417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22217689871648494073590445 8331633701868185277596417)
      ·
        refine ⟨6248725276401138958197313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8331633701868185277596417 6248725276401138958197313)
        ·
          refine ⟨4686543957300854218647985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248725276401138958197313 4686543957300854218647985)
          ·
            refine ⟨3514907967975640663985989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686543957300854218647985 3514907967975640663985989)
            ·
              refine ⟨659045243995432624497373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3514907967975640663985989 659045243995432624497373)
              ·
                refine ⟨247141966498287234186515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659045243995432624497373 247141966498287234186515)
                ·
                  refine ⟨370712949747430851279773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247141966498287234186515 370712949747430851279773)
                  ·
                    refine ⟨139017356155286569229915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370712949747430851279773 139017356155286569229915)
                    ·
                      rfl

theorem cell22_406103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_406103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406103 prefixEnd_406103 := by exact prefixLift 406103
  have htrace : WordTrace (prefixWord ++ tailWord_406103) baseStart_406103 baseEnd_406103 := by
    simpa [prefixWord, tailWord_406103, baseEnd_406103] using wordTrace_append hprefix tailTrace_406103
  have hstable : (prefixWord ++ tailWord_406103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406103).length < 2 ^ (prefixWord ++ tailWord_406103).sum := by decide
  have hdescent : baseEnd_406103 < baseStart_406103 := by decide
  rcases family_descends (prefixWord ++ tailWord_406103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406144 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_406144 : Nat := 118140960795 + 406144 * 2 ^ 59
def prefixEnd_406144 : Nat := 4983230072969 + 3 ^ 40 * 406144 * 2
def baseEnd_406144 : Nat := 46343797097725376318263

theorem tailTrace_406144 : CollatzResearch.WordTrace tailWord_406144 prefixEnd_406144 46343797097725376318263 := by
  unfold tailWord_406144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406644320308563358984743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9875525760411417811979657 7406644320308563358984743)
  ·
    refine ⟨11109966480462845038477115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7406644320308563358984743 11109966480462845038477115)
    ·
      refine ⟨16664949720694267557715673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11109966480462845038477115 16664949720694267557715673)
      ·
        refine ⟨12498712290520700668286755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16664949720694267557715673 12498712290520700668286755)
        ·
          refine ⟨18748068435781051002430133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498712290520700668286755 18748068435781051002430133)
          ·
            refine ⟨1757631415854473531477825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18748068435781051002430133 1757631415854473531477825)
            ·
              refine ⟨1318223561890855148608369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757631415854473531477825 1318223561890855148608369)
              ·
                refine ⟨988667671418141361456277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318223561890855148608369 988667671418141361456277)
                ·
                  refine ⟨46343797097725376318263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 988667671418141361456277 46343797097725376318263)
                  ·
                    rfl

theorem cell22_406144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_406144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406144 prefixEnd_406144 := by exact prefixLift 406144
  have htrace : WordTrace (prefixWord ++ tailWord_406144) baseStart_406144 baseEnd_406144 := by
    simpa [prefixWord, tailWord_406144, baseEnd_406144] using wordTrace_append hprefix tailTrace_406144
  have hstable : (prefixWord ++ tailWord_406144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406144).length < 2 ^ (prefixWord ++ tailWord_406144).sum := by decide
  have hdescent : baseEnd_406144 < baseStart_406144 := by decide
  rcases family_descends (prefixWord ++ tailWord_406144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406214 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_406214 : Nat := 118140960795 + 406214 * 2 ^ 59
def prefixEnd_406214 : Nat := 4983230072969 + 3 ^ 40 * 406214 * 2
def baseEnd_406214 : Nat := 139055353723719279704575

theorem tailTrace_406214 : CollatzResearch.WordTrace tailWord_406214 prefixEnd_406214 139055353723719279704575 := by
  unfold tailWord_406214
  simp only [CollatzResearch.WordTrace]
  refine ⟨462995054698860271031803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9877227833575685782011797 462995054698860271031803)
  ·
    refine ⟨694492582048290406547705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 462995054698860271031803 694492582048290406547705)
    ·
      refine ⟨520869436536217804910779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694492582048290406547705 520869436536217804910779)
      ·
        refine ⟨781304154804326707366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520869436536217804910779 781304154804326707366169)
        ·
          refine ⟨585978116103245030524627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781304154804326707366169 585978116103245030524627)
          ·
            refine ⟨878967174154867545786941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585978116103245030524627 878967174154867545786941)
            ·
              refine ⟨329612690308075329670103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878967174154867545786941 329612690308075329670103)
              ·
                refine ⟨494419035462112994505155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329612690308075329670103 494419035462112994505155)
                ·
                  refine ⟨741628553193169491757733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494419035462112994505155 741628553193169491757733)
                  ·
                    refine ⟨139055353723719279704575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 741628553193169491757733 139055353723719279704575)
                    ·
                      rfl

theorem cell22_406214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_406214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406214 prefixEnd_406214 := by exact prefixLift 406214
  have htrace : WordTrace (prefixWord ++ tailWord_406214) baseStart_406214 baseEnd_406214 := by
    simpa [prefixWord, tailWord_406214, baseEnd_406214] using wordTrace_append hprefix tailTrace_406214
  have hstable : (prefixWord ++ tailWord_406214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406214).length < 2 ^ (prefixWord ++ tailWord_406214).sum := by decide
  have hdescent : baseEnd_406214 < baseStart_406214 := by decide
  rcases family_descends (prefixWord ++ tailWord_406214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406229 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 4]
def baseStart_406229 : Nat := 118140960795 + 406229 * 2 ^ 59
def prefixEnd_406229 : Nat := 4983230072969 + 3 ^ 40 * 406229 * 2
def baseEnd_406229 : Nat := 46353496176754746859843

theorem tailTrace_406229 : CollatzResearch.WordTrace tailWord_406229 prefixEnd_406229 46353496176754746859843 := by
  unfold tailWord_406229
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816388845309186234813741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9877592563539457489875827 14816388845309186234813741)
  ·
    refine ⟨5556145816990944838055153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14816388845309186234813741 5556145816990944838055153)
    ·
      refine ⟨4167109362743208628541365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5556145816990944838055153 4167109362743208628541365)
      ·
        refine ⟨390666502757175808925753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4167109362743208628541365 390666502757175808925753)
        ·
          refine ⟨292999877067881856694315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390666502757175808925753 292999877067881856694315)
          ·
            refine ⟨439499815601822785041473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292999877067881856694315 439499815601822785041473)
            ·
              refine ⟨329624861701367088781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439499815601822785041473 329624861701367088781105)
              ·
                refine ⟨247218646276025316585829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329624861701367088781105 247218646276025316585829)
                ·
                  refine ⟨46353496176754746859843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247218646276025316585829 46353496176754746859843)
                  ·
                    rfl

theorem cell22_406229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_406229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406229 prefixEnd_406229 := by exact prefixLift 406229
  have htrace : WordTrace (prefixWord ++ tailWord_406229) baseStart_406229 baseEnd_406229 := by
    simpa [prefixWord, tailWord_406229, baseEnd_406229] using wordTrace_append hprefix tailTrace_406229
  have hstable : (prefixWord ++ tailWord_406229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406229).length < 2 ^ (prefixWord ++ tailWord_406229).sum := by decide
  have hdescent : baseEnd_406229 < baseStart_406229 := by decide
  rcases family_descends (prefixWord ++ tailWord_406229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406249 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_406249 : Nat := 118140960795 + 406249 * 2 ^ 59
def prefixEnd_406249 : Nat := 4983230072969 + 3 ^ 40 * 406249 * 2
def baseEnd_406249 : Nat := 139067334938990855079467

theorem tailTrace_406249 : CollatzResearch.WordTrace tailWord_406249 prefixEnd_406249 139067334938990855079467 := by
  unfold tailWord_406249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14817118305236729650541801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9878078870157819767027867 14817118305236729650541801)
  ·
    refine ⟨11112838728927547237906351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14817118305236729650541801 11112838728927547237906351)
    ·
      refine ⟨16669258093391320856859527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11112838728927547237906351 16669258093391320856859527)
      ·
        refine ⟨25003887140086981285289291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16669258093391320856859527 25003887140086981285289291)
        ·
          refine ⟨37505830710130471927933937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25003887140086981285289291 37505830710130471927933937)
          ·
            refine ⟨28129373032597853945950453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37505830710130471927933937 28129373032597853945950453)
            ·
              refine ⟨2637128721806048807432855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28129373032597853945950453 2637128721806048807432855)
              ·
                refine ⟨3955693082709073211149283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637128721806048807432855 3955693082709073211149283)
                ·
                  refine ⟨5933539624063609816723925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955693082709073211149283 5933539624063609816723925)
                  ·
                    refine ⟨139067334938990855079467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5933539624063609816723925 139067334938990855079467)
                    ·
                      rfl

theorem cell22_406249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_406249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406249 prefixEnd_406249 := by exact prefixLift 406249
  have htrace : WordTrace (prefixWord ++ tailWord_406249) baseStart_406249 baseEnd_406249 := by
    simpa [prefixWord, tailWord_406249, baseEnd_406249] using wordTrace_append hprefix tailTrace_406249
  have hstable : (prefixWord ++ tailWord_406249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406249).length < 2 ^ (prefixWord ++ tailWord_406249).sum := by decide
  have hdescent : baseEnd_406249 < baseStart_406249 := by decide
  rcases family_descends (prefixWord ++ tailWord_406249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406362 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_406362 : Nat := 118140960795 + 406362 * 2 ^ 59
def prefixEnd_406362 : Nat := 4983230072969 + 3 ^ 40 * 406362 * 2
def baseEnd_406362 : Nat := 139106017148296227004121

theorem tailTrace_406362 : CollatzResearch.WordTrace tailWord_406362 prefixEnd_406362 139106017148296227004121 := by
  unfold tailWord_406362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705309938456837487351335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9880826502551566632936893 3705309938456837487351335)
  ·
    refine ⟨5557964907685256231027003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3705309938456837487351335 5557964907685256231027003)
    ·
      refine ⟨8336947361527884346540505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5557964907685256231027003 8336947361527884346540505)
      ·
        refine ⟨6252710521145913259905379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8336947361527884346540505 6252710521145913259905379)
        ·
          refine ⟨9379065781718869889858069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252710521145913259905379 9379065781718869889858069)
          ·
            refine ⟨439643708518072026087097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9379065781718869889858069 439643708518072026087097)
            ·
              refine ⟨329732781388554019565323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439643708518072026087097 329732781388554019565323)
              ·
                refine ⟨494599172082831029347985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329732781388554019565323 494599172082831029347985)
                ·
                  refine ⟨370949379062123272010989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494599172082831029347985 370949379062123272010989)
                  ·
                    refine ⟨139106017148296227004121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370949379062123272010989 139106017148296227004121)
                    ·
                      rfl

theorem cell22_406362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_406362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406362 prefixEnd_406362 := by exact prefixLift 406362
  have htrace : WordTrace (prefixWord ++ tailWord_406362) baseStart_406362 baseEnd_406362 := by
    simpa [prefixWord, tailWord_406362, baseEnd_406362] using wordTrace_append hprefix tailTrace_406362
  have hstable : (prefixWord ++ tailWord_406362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406362).length < 2 ^ (prefixWord ++ tailWord_406362).sum := by decide
  have hdescent : baseEnd_406362 < baseStart_406362 := by decide
  rcases family_descends (prefixWord ++ tailWord_406362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406373 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_406373 : Nat := 118140960795 + 406373 * 2 ^ 59
def prefixEnd_406373 : Nat := 4983230072969 + 3 ^ 40 * 406373 * 2
def baseEnd_406373 : Nat := 139109782673095864979087

theorem tailTrace_406373 : CollatzResearch.WordTrace tailWord_406373 prefixEnd_406373 139109782673095864979087 := by
  unfold tailWord_406373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821640956787498828055773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9881093971191665885370515 14821640956787498828055773)
  ·
    refine ⟨5558115358795312060520915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14821640956787498828055773 5558115358795312060520915)
    ·
      refine ⟨8337173038192968090781373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558115358795312060520915 8337173038192968090781373)
      ·
        refine ⟨3126439889322363034043015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8337173038192968090781373 3126439889322363034043015)
        ·
          refine ⟨4689659833983544551064523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126439889322363034043015 4689659833983544551064523)
          ·
            refine ⟨7034489750975316826596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689659833983544551064523 7034489750975316826596785)
            ·
              refine ⟨5275867313231487619947589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034489750975316826596785 5275867313231487619947589)
              ·
                refine ⟨989225121230903928740173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5275867313231487619947589 989225121230903928740173)
                ·
                  refine ⟨370959420461588973277565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989225121230903928740173 370959420461588973277565)
                  ·
                    refine ⟨139109782673095864979087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370959420461588973277565 139109782673095864979087)
                    ·
                      rfl

theorem cell22_406373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_406373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406373 prefixEnd_406373 := by exact prefixLift 406373
  have htrace : WordTrace (prefixWord ++ tailWord_406373) baseStart_406373 baseEnd_406373 := by
    simpa [prefixWord, tailWord_406373, baseEnd_406373] using wordTrace_append hprefix tailTrace_406373
  have hstable : (prefixWord ++ tailWord_406373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406373).length < 2 ^ (prefixWord ++ tailWord_406373).sum := by decide
  have hdescent : baseEnd_406373 < baseStart_406373 := by decide
  rcases family_descends (prefixWord ++ tailWord_406373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406386 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_406386 : Nat := 118140960795 + 406386 * 2 ^ 59
def prefixEnd_406386 : Nat := 4983230072969 + 3 ^ 40 * 406386 * 2
def baseEnd_406386 : Nat := 46371410946256054801349

theorem tailTrace_406386 : CollatzResearch.WordTrace tailWord_406386 prefixEnd_406386 46371410946256054801349 := by
  unfold tailWord_406386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705528776435100512069753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9881410070493601365519341 3705528776435100512069753)
  ·
    refine ⟨2779146582326325384052315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3705528776435100512069753 2779146582326325384052315)
    ·
      refine ⟨4168719873489488076078473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779146582326325384052315 4168719873489488076078473)
      ·
        refine ⟨3126539905117116057058855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168719873489488076078473 3126539905117116057058855)
        ·
          refine ⟨4689809857675674085588283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126539905117116057058855 4689809857675674085588283)
          ·
            refine ⟨7034714786513511128382425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689809857675674085588283 7034714786513511128382425)
            ·
              refine ⟨5276036089885133346286819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034714786513511128382425 5276036089885133346286819)
              ·
                refine ⟨7914054134827700019430229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276036089885133346286819 7914054134827700019430229)
                ·
                  refine ⟨46371410946256054801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7914054134827700019430229 46371410946256054801349)
                  ·
                    rfl

theorem cell22_406386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_406386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406386 prefixEnd_406386 := by exact prefixLift 406386
  have htrace : WordTrace (prefixWord ++ tailWord_406386) baseStart_406386 baseEnd_406386 := by
    simpa [prefixWord, tailWord_406386, baseEnd_406386] using wordTrace_append hprefix tailTrace_406386
  have hstable : (prefixWord ++ tailWord_406386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406386).length < 2 ^ (prefixWord ++ tailWord_406386).sum := by decide
  have hdescent : baseEnd_406386 < baseStart_406386 := by decide
  rcases family_descends (prefixWord ++ tailWord_406386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406403 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 5]
def baseStart_406403 : Nat := 118140960795 + 406403 * 2 ^ 59
def prefixEnd_406403 : Nat := 4983230072969 + 3 ^ 40 * 406403 * 2
def baseEnd_406403 : Nat := 46373350762061928909665

theorem tailTrace_406403 : CollatzResearch.WordTrace tailWord_406403 prefixEnd_406403 46373350762061928909665 := by
  unfold tailWord_406403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822735146678813951647863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9881823431119209301098575 14822735146678813951647863)
  ·
    refine ⟨22234102720018220927471795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14822735146678813951647863 22234102720018220927471795)
    ·
      refine ⟨33351154080027331391207693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234102720018220927471795 33351154080027331391207693)
      ·
        refine ⟨12506682780010249271702885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33351154080027331391207693 12506682780010249271702885)
        ·
          refine ⟨2345003021251921738444291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12506682780010249271702885 2345003021251921738444291)
          ·
            refine ⟨3517504531877882607666437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345003021251921738444291 3517504531877882607666437)
            ·
              refine ⟨659532099727102988937457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3517504531877882607666437 659532099727102988937457)
              ·
                refine ⟨494649074795327241703093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659532099727102988937457 494649074795327241703093)
                ·
                  refine ⟨46373350762061928909665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 494649074795327241703093 46373350762061928909665)
                  ·
                    rfl

theorem cell22_406403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].length) (baseStart_406403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406403 prefixEnd_406403 := by exact prefixLift 406403
  have htrace : WordTrace (prefixWord ++ tailWord_406403) baseStart_406403 baseEnd_406403 := by
    simpa [prefixWord, tailWord_406403, baseEnd_406403] using wordTrace_append hprefix tailTrace_406403
  have hstable : (prefixWord ++ tailWord_406403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406403).length < 2 ^ (prefixWord ++ tailWord_406403).sum := by decide
  have hdescent : baseEnd_406403 < baseStart_406403 := by decide
  rcases family_descends (prefixWord ++ tailWord_406403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406407 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 1, 3]
def baseStart_406407 : Nat := 118140960795 + 406407 * 2 ^ 59
def prefixEnd_406407 : Nat := 4983230072969 + 3 ^ 40 * 406407 * 2
def baseEnd_406407 : Nat := 139121421567931109628983

theorem tailTrace_406407 : CollatzResearch.WordTrace tailWord_406407 prefixEnd_406407 139121421567931109628983 := by
  unfold tailWord_406407
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822881038664322634793475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9881920692442881756528983 14822881038664322634793475)
  ·
    refine ⟨22234321557996483952190213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14822881038664322634793475 22234321557996483952190213)
    ·
      refine ⟨4168935292124340741035665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22234321557996483952190213 4168935292124340741035665)
      ·
        refine ⟨3126701469093255555776749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168935292124340741035665 3126701469093255555776749)
        ·
          refine ⟨1172513050909970833416281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3126701469093255555776749 1172513050909970833416281)
          ·
            refine ⟨879384788182478125062211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172513050909970833416281 879384788182478125062211)
            ·
              refine ⟨1319077182273717187593317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879384788182478125062211 1319077182273717187593317)
              ·
                refine ⟨247326971676321972673747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1319077182273717187593317 247326971676321972673747)
                ·
                  refine ⟨370990457514482959010621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247326971676321972673747 370990457514482959010621)
                  ·
                    refine ⟨139121421567931109628983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370990457514482959010621 139121421567931109628983)
                    ·
                      rfl

theorem cell22_406407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_406407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406407 prefixEnd_406407 := by exact prefixLift 406407
  have htrace : WordTrace (prefixWord ++ tailWord_406407) baseStart_406407 baseEnd_406407 := by
    simpa [prefixWord, tailWord_406407, baseEnd_406407] using wordTrace_append hprefix tailTrace_406407
  have hstable : (prefixWord ++ tailWord_406407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406407).length < 2 ^ (prefixWord ++ tailWord_406407).sum := by decide
  have hdescent : baseEnd_406407 < baseStart_406407 := by decide
  rcases family_descends (prefixWord ++ tailWord_406407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406454 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_406454 : Nat := 118140960795 + 406454 * 2 ^ 59
def prefixEnd_406454 : Nat := 4983230072969 + 3 ^ 40 * 406454 * 2
def baseEnd_406454 : Nat := 46379170209479551234613

theorem tailTrace_406454 : CollatzResearch.WordTrace tailWord_406454 prefixEnd_406454 46379170209479551234613 := by
  unfold tailWord_406454
  simp only [CollatzResearch.WordTrace]
  refine ⟨926537204343378103859651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9883063512996033107836277 926537204343378103859651)
  ·
    refine ⟨1389805806515067155789477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926537204343378103859651 1389805806515067155789477)
    ·
      refine ⟨260588588721575091710527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1389805806515067155789477 260588588721575091710527)
      ·
        refine ⟨390882883082362637565791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260588588721575091710527 390882883082362637565791)
        ·
          refine ⟨586324324623543956348687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390882883082362637565791 586324324623543956348687)
          ·
            refine ⟨879486486935315934523031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586324324623543956348687 879486486935315934523031)
            ·
              refine ⟨1319229730402973901784547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879486486935315934523031 1319229730402973901784547)
              ·
                refine ⟨1978844595604460852676821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319229730402973901784547 1978844595604460852676821)
                ·
                  refine ⟨46379170209479551234613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1978844595604460852676821 46379170209479551234613)
                  ·
                    rfl

theorem cell22_406454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_406454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406454 prefixEnd_406454 := by exact prefixLift 406454
  have htrace : WordTrace (prefixWord ++ tailWord_406454) baseStart_406454 baseEnd_406454 := by
    simpa [prefixWord, tailWord_406454, baseEnd_406454] using wordTrace_append hprefix tailTrace_406454
  have hstable : (prefixWord ++ tailWord_406454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406454).length < 2 ^ (prefixWord ++ tailWord_406454).sum := by decide
  have hdescent : baseEnd_406454 < baseStart_406454 := by decide
  rcases family_descends (prefixWord ++ tailWord_406454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406478 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_406478 : Nat := 118140960795 + 406478 * 2 ^ 59
def prefixEnd_406478 : Nat := 4983230072969 + 3 ^ 40 * 406478 * 2
def baseEnd_406478 : Nat := 139145726318910591103765

theorem tailTrace_406478 : CollatzResearch.WordTrace tailWord_406478 prefixEnd_406478 139145726318910591103765 := by
  unfold tailWord_406478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853183827675887720078511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9883647080938067840418725 1853183827675887720078511)
  ·
    refine ⟨2779775741513831580117767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853183827675887720078511 2779775741513831580117767)
    ·
      refine ⟨4169663612270747370176651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779775741513831580117767 4169663612270747370176651)
      ·
        refine ⟨6254495418406121055264977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169663612270747370176651 6254495418406121055264977)
        ·
          refine ⟨4690871563804590791448733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254495418406121055264977 4690871563804590791448733)
          ·
            refine ⟨1759076836426721546793275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4690871563804590791448733 1759076836426721546793275)
            ·
              refine ⟨2638615254640082320189913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759076836426721546793275 2638615254640082320189913)
              ·
                refine ⟨1978961440980061740142435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638615254640082320189913 1978961440980061740142435)
                ·
                  refine ⟨2968442161470092610213653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978961440980061740142435 2968442161470092610213653)
                  ·
                    refine ⟨139145726318910591103765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2968442161470092610213653 139145726318910591103765)
                    ·
                      rfl

theorem cell22_406478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_406478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406478 prefixEnd_406478 := by exact prefixLift 406478
  have htrace : WordTrace (prefixWord ++ tailWord_406478) baseStart_406478 baseEnd_406478 := by
    simpa [prefixWord, tailWord_406478, baseEnd_406478] using wordTrace_append hprefix tailTrace_406478
  have hstable : (prefixWord ++ tailWord_406478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406478).length < 2 ^ (prefixWord ++ tailWord_406478).sum := by decide
  have hdescent : baseEnd_406478 < baseStart_406478 := by decide
  rcases family_descends (prefixWord ++ tailWord_406478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406510 : List Nat := [4, 1, 2, 1, 4, 2, 8]
def baseStart_406510 : Nat := 118140960795 + 406510 * 2 ^ 59
def prefixEnd_406510 : Nat := 4983230072969 + 3 ^ 40 * 406510 * 2
def baseEnd_406510 : Nat := 5153951132328636085321

theorem tailTrace_406510 : CollatzResearch.WordTrace tailWord_406510 prefixEnd_406510 5153951132328636085321 := by
  unfold tailWord_406510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853329719661396403224123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9884425171527447483861989 1853329719661396403224123)
  ·
    refine ⟨2779994579492094604836185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853329719661396403224123 2779994579492094604836185)
    ·
      refine ⟨2084995934619070953627139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2779994579492094604836185 2084995934619070953627139)
      ·
        refine ⟨3127493901928606430440709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084995934619070953627139 3127493901928606430440709)
        ·
          refine ⟨586405106611613705707633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3127493901928606430440709 586405106611613705707633)
          ·
            refine ⟨439803829958710279280725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586405106611613705707633 439803829958710279280725)
            ·
              refine ⟨5153951132328636085321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 439803829958710279280725 5153951132328636085321)
              ·
                rfl

theorem cell22_406510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 8].length) (baseStart_406510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406510 prefixEnd_406510 := by exact prefixLift 406510
  have htrace : WordTrace (prefixWord ++ tailWord_406510) baseStart_406510 baseEnd_406510 := by
    simpa [prefixWord, tailWord_406510, baseEnd_406510] using wordTrace_append hprefix tailTrace_406510
  have hstable : (prefixWord ++ tailWord_406510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406510).length < 2 ^ (prefixWord ++ tailWord_406510).sum := by decide
  have hdescent : baseEnd_406510 < baseStart_406510 := by decide
  rcases family_descends (prefixWord ++ tailWord_406510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406546 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_406546 : Nat := 118140960795 + 406546 * 2 ^ 59
def prefixEnd_406546 : Nat := 4983230072969 + 3 ^ 40 * 406546 * 2
def baseEnd_406546 : Nat := 139169004108581080403557

theorem tailTrace_406546 : CollatzResearch.WordTrace tailWord_406546 prefixEnd_406546 139169004108581080403557 := by
  unfold tailWord_406546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706987696290187343525873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9885300523440499582735661 3706987696290187343525873)
  ·
    refine ⟨2780240772217640507644405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3706987696290187343525873 2780240772217640507644405)
    ·
      refine ⟨260647572395403797591663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2780240772217640507644405 260647572395403797591663)
      ·
        refine ⟨390971358593105696387495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260647572395403797591663 390971358593105696387495)
        ·
          refine ⟨586457037889658544581243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390971358593105696387495 586457037889658544581243)
          ·
            refine ⟨879685556834487816871865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586457037889658544581243 879685556834487816871865)
            ·
              refine ⟨659764167625865862653899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879685556834487816871865 659764167625865862653899)
              ·
                refine ⟨989646251438798793980849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659764167625865862653899 989646251438798793980849)
                ·
                  refine ⟨742234688579099095485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989646251438798793980849 742234688579099095485637)
                  ·
                    refine ⟨139169004108581080403557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742234688579099095485637 139169004108581080403557)
                    ·
                      rfl

theorem cell22_406546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_406546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406546 prefixEnd_406546 := by exact prefixLift 406546
  have htrace : WordTrace (prefixWord ++ tailWord_406546) baseStart_406546 baseEnd_406546 := by
    simpa [prefixWord, tailWord_406546, baseEnd_406546] using wordTrace_append hprefix tailTrace_406546
  have hstable : (prefixWord ++ tailWord_406546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406546).length < 2 ^ (prefixWord ++ tailWord_406546).sum := by decide
  have hdescent : baseEnd_406546 < baseStart_406546 := by decide
  rcases family_descends (prefixWord ++ tailWord_406546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406583 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 6]
def baseStart_406583 : Nat := 118140960795 + 406583 * 2 ^ 59
def prefixEnd_406583 : Nat := 4983230072969 + 3 ^ 40 * 406583 * 2
def baseEnd_406583 : Nat := 46393889988241772409481

theorem tailTrace_406583 : CollatzResearch.WordTrace tailWord_406583 prefixEnd_406583 46393889988241772409481 := by
  unfold tailWord_406583
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829300286026704693200403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886200190684469795466935 14829300286026704693200403)
  ·
    refine ⟨22243950429040057039800605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14829300286026704693200403 22243950429040057039800605)
    ·
      refine ⟨8341481410890021389925227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22243950429040057039800605 8341481410890021389925227)
      ·
        refine ⟨12512222116335032084887841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341481410890021389925227 12512222116335032084887841)
        ·
          refine ⟨9384166587251274063665881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12512222116335032084887841 9384166587251274063665881)
          ·
            refine ⟨7038124940438455547749411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384166587251274063665881 7038124940438455547749411)
            ·
              refine ⟨10557187410657683321624117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038124940438455547749411 10557187410657683321624117)
              ·
                refine ⟨989736319749157811402261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10557187410657683321624117 989736319749157811402261)
                ·
                  refine ⟨46393889988241772409481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 989736319749157811402261 46393889988241772409481)
                  ·
                    rfl

theorem cell22_406583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_406583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406583 prefixEnd_406583 := by exact prefixLift 406583
  have htrace : WordTrace (prefixWord ++ tailWord_406583) baseStart_406583 baseEnd_406583 := by
    simpa [prefixWord, tailWord_406583, baseEnd_406583] using wordTrace_append hprefix tailTrace_406583
  have hstable : (prefixWord ++ tailWord_406583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406583).length < 2 ^ (prefixWord ++ tailWord_406583).sum := by decide
  have hdescent : baseEnd_406583 < baseStart_406583 := by decide
  rcases family_descends (prefixWord ++ tailWord_406583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406585 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_406585 : Nat := 118140960795 + 406585 * 2 ^ 59
def prefixEnd_406585 : Nat := 4983230072969 + 3 ^ 40 * 406585 * 2
def baseEnd_406585 : Nat := 139182354605597978678437

theorem tailTrace_406585 : CollatzResearch.WordTrace tailWord_406585 prefixEnd_406585 139182354605597978678437 := by
  unfold tailWord_406585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829373232019459034773209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886248821346306023182139 14829373232019459034773209)
  ·
    refine ⟨11122029924014594276079907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14829373232019459034773209 11122029924014594276079907)
    ·
      refine ⟨16683044886021891414119861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11122029924014594276079907 16683044886021891414119861)
      ·
        refine ⟨1564035458064552320073737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16683044886021891414119861 1564035458064552320073737)
        ·
          refine ⟨1173026593548414240055303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564035458064552320073737 1173026593548414240055303)
          ·
            refine ⟨1759539890322621360082955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173026593548414240055303 1759539890322621360082955)
            ·
              refine ⟨2639309835483932040124433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759539890322621360082955 2639309835483932040124433)
              ·
                refine ⟨1979482376612949030093325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639309835483932040124433 1979482376612949030093325)
                ·
                  refine ⟨742305891229855886284997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1979482376612949030093325 742305891229855886284997)
                  ·
                    refine ⟨139182354605597978678437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742305891229855886284997 139182354605597978678437)
                    ·
                      rfl

theorem cell22_406585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_406585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406585 prefixEnd_406585 := by exact prefixLift 406585
  have htrace : WordTrace (prefixWord ++ tailWord_406585) baseStart_406585 baseEnd_406585 := by
    simpa [prefixWord, tailWord_406585, baseEnd_406585] using wordTrace_append hprefix tailTrace_406585
  have hstable : (prefixWord ++ tailWord_406585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406585).length < 2 ^ (prefixWord ++ tailWord_406585).sum := by decide
  have hdescent : baseEnd_406585 < baseStart_406585 := by decide
  rcases family_descends (prefixWord ++ tailWord_406585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406615 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 4, 3]
def baseStart_406615 : Nat := 118140960795 + 406615 * 2 ^ 59
def prefixEnd_406615 : Nat := 4983230072969 + 3 ^ 40 * 406615 * 2
def baseEnd_406615 : Nat := 139192624218687900428345

theorem tailTrace_406615 : CollatzResearch.WordTrace tailWord_406615 prefixEnd_406615 139192624218687900428345 := by
  unfold tailWord_406615
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830467421910774158365299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886978281273849438910199 14830467421910774158365299)
  ·
    refine ⟨22245701132866161237547949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14830467421910774158365299 22245701132866161237547949)
    ·
      refine ⟨8342137924824810464080481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22245701132866161237547949 8342137924824810464080481)
      ·
        refine ⟨6256603443618607848060361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8342137924824810464080481 6256603443618607848060361)
        ·
          refine ⟨4692452582713955886045271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6256603443618607848060361 4692452582713955886045271)
          ·
            refine ⟨7038678874070933829067907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692452582713955886045271 7038678874070933829067907)
            ·
              refine ⟨10558018311106400743601861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038678874070933829067907 10558018311106400743601861)
              ·
                refine ⟨1979628433332450139425349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10558018311106400743601861 1979628433332450139425349)
                ·
                  refine ⟨371180331249834401142253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979628433332450139425349 371180331249834401142253)
                  ·
                    refine ⟨139192624218687900428345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371180331249834401142253 139192624218687900428345)
                    ·
                      rfl

theorem cell22_406615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_406615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406615 prefixEnd_406615 := by exact prefixLift 406615
  have htrace : WordTrace (prefixWord ++ tailWord_406615) baseStart_406615 baseEnd_406615 := by
    simpa [prefixWord, tailWord_406615, baseEnd_406615] using wordTrace_append hprefix tailTrace_406615
  have hstable : (prefixWord ++ tailWord_406615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406615).length < 2 ^ (prefixWord ++ tailWord_406615).sum := by decide
  have hdescent : baseEnd_406615 < baseStart_406615 := by decide
  rcases family_descends (prefixWord ++ tailWord_406615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406649 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_406649 : Nat := 118140960795 + 406649 * 2 ^ 59
def prefixEnd_406649 : Nat := 4983230072969 + 3 ^ 40 * 406649 * 2
def baseEnd_406649 : Nat := 139204263113523145078241

theorem tailTrace_406649 : CollatzResearch.WordTrace tailWord_406649 prefixEnd_406649 139204263113523145078241 := by
  unfold tailWord_406649
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831707503787597965103001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887805002525065310068667 14831707503787597965103001)
  ·
    refine ⟨11123780627840698473827251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14831707503787597965103001 11123780627840698473827251)
    ·
      refine ⟨16685670941761047710740877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123780627840698473827251 16685670941761047710740877)
      ·
        refine ⟨6257126603160392891527829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16685670941761047710740877 6257126603160392891527829)
        ·
          refine ⟨293302809523143416790367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6257126603160392891527829 293302809523143416790367)
          ·
            refine ⟨439954214284715125185551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293302809523143416790367 439954214284715125185551)
            ·
              refine ⟨659931321427072687778327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439954214284715125185551 659931321427072687778327)
              ·
                refine ⟨989896982140609031667491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659931321427072687778327 989896982140609031667491)
                ·
                  refine ⟨1484845473210913547501237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989896982140609031667491 1484845473210913547501237)
                  ·
                    refine ⟨139204263113523145078241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1484845473210913547501237 139204263113523145078241)
                    ·
                      rfl

theorem cell22_406649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_406649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406649 prefixEnd_406649 := by exact prefixLift 406649
  have htrace : WordTrace (prefixWord ++ tailWord_406649) baseStart_406649 baseEnd_406649 := by
    simpa [prefixWord, tailWord_406649, baseEnd_406649] using wordTrace_append hprefix tailTrace_406649
  have hstable : (prefixWord ++ tailWord_406649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406649).length < 2 ^ (prefixWord ++ tailWord_406649).sum := by decide
  have hdescent : baseEnd_406649 < baseStart_406649 := by decide
  rcases family_descends (prefixWord ++ tailWord_406649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406707 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 5]
def baseStart_406707 : Nat := 118140960795 + 406707 * 2 ^ 59
def prefixEnd_406707 : Nat := 4983230072969 + 3 ^ 40 * 406707 * 2
def baseEnd_406707 : Nat := 46408039232943442376021

theorem tailTrace_406707 : CollatzResearch.WordTrace tailWord_406707 prefixEnd_406707 46408039232943442376021 := by
  unfold tailWord_406707
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833822937577473870714375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9889215291718315913809583 14833822937577473870714375)
  ·
    refine ⟨22250734406366210806071563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14833822937577473870714375 22250734406366210806071563)
    ·
      refine ⟨33376101609549316209107345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22250734406366210806071563 33376101609549316209107345)
      ·
        refine ⟨25032076207161987156830509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33376101609549316209107345 25032076207161987156830509)
        ·
          refine ⟨9387028577685745183811441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25032076207161987156830509 9387028577685745183811441)
          ·
            refine ⟨7040271433264308887858581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387028577685745183811441 7040271433264308887858581)
            ·
              refine ⟨330012723434264479118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7040271433264308887858581 330012723434264479118371)
              ·
                refine ⟨495019085151396718677557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330012723434264479118371 495019085151396718677557)
                ·
                  refine ⟨46408039232943442376021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495019085151396718677557 46408039232943442376021)
                  ·
                    rfl

theorem cell22_406707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 5].length) (baseStart_406707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406707 prefixEnd_406707 := by exact prefixLift 406707
  have htrace : WordTrace (prefixWord ++ tailWord_406707) baseStart_406707 baseEnd_406707 := by
    simpa [prefixWord, tailWord_406707, baseEnd_406707] using wordTrace_append hprefix tailTrace_406707
  have hstable : (prefixWord ++ tailWord_406707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406707).length < 2 ^ (prefixWord ++ tailWord_406707).sum := by decide
  have hdescent : baseEnd_406707 < baseStart_406707 := by decide
  rcases family_descends (prefixWord ++ tailWord_406707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406818 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_406818 : Nat := 118140960795 + 406818 * 2 ^ 59
def prefixEnd_406818 : Nat := 4983230072969 + 3 ^ 40 * 406818 * 2
def baseEnd_406818 : Nat := 139262115267263037602723

theorem tailTrace_406818 : CollatzResearch.WordTrace tailWord_406818 prefixEnd_406818 139262115267263037602723 := by
  unfold tailWord_406818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709467860043834957001277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9891914293450226552003405 3709467860043834957001277)
  ·
    refine ⟨1391050447516438108875479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3709467860043834957001277 1391050447516438108875479)
    ·
      refine ⟨2086575671274657163313219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391050447516438108875479 2086575671274657163313219)
      ·
        refine ⟨3129863506911985744969829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086575671274657163313219 3129863506911985744969829)
        ·
          refine ⟨586849407545997327181843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3129863506911985744969829 586849407545997327181843)
          ·
            refine ⟨880274111318995990772765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586849407545997327181843 880274111318995990772765)
            ·
              refine ⟨330102791744623496539787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 880274111318995990772765 330102791744623496539787)
              ·
                refine ⟨495154187616935244809681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330102791744623496539787 495154187616935244809681)
                ·
                  refine ⟨371365640712701433607261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495154187616935244809681 371365640712701433607261)
                  ·
                    refine ⟨139262115267263037602723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371365640712701433607261 139262115267263037602723)
                    ·
                      rfl

theorem cell22_406818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_406818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406818 prefixEnd_406818 := by exact prefixLift 406818
  have htrace : WordTrace (prefixWord ++ tailWord_406818) baseStart_406818 baseEnd_406818 := by
    simpa [prefixWord, tailWord_406818, baseEnd_406818] using wordTrace_append hprefix tailTrace_406818
  have hstable : (prefixWord ++ tailWord_406818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406818).length < 2 ^ (prefixWord ++ tailWord_406818).sum := by decide
  have hdescent : baseEnd_406818 < baseStart_406818 := by decide
  rcases family_descends (prefixWord ++ tailWord_406818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406872 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_406872 : Nat := 118140960795 + 406872 * 2 ^ 59
def prefixEnd_406872 : Nat := 4983230072969 + 3 ^ 40 * 406872 * 2
def baseEnd_406872 : Nat := 139280600570824896752557

theorem tailTrace_406872 : CollatzResearch.WordTrace tailWord_406872 prefixEnd_406872 139280600570824896752557 := by
  unfold tailWord_406872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419920490989853525235435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9893227321319804700313913 7419920490989853525235435)
  ·
    refine ⟨11129880736484780287853153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7419920490989853525235435 11129880736484780287853153)
    ·
      refine ⟨8347410552363585215889865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11129880736484780287853153 8347410552363585215889865)
      ·
        refine ⟨6260557914272688911917399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8347410552363585215889865 6260557914272688911917399)
        ·
          refine ⟨9390836871409033367876099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260557914272688911917399 9390836871409033367876099)
          ·
            refine ⟨14086255307113550051814149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390836871409033367876099 14086255307113550051814149)
            ·
              refine ⟨2641172870083790634715153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14086255307113550051814149 2641172870083790634715153)
              ·
                refine ⟨1980879652562842976036365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641172870083790634715153 1980879652562842976036365)
                ·
                  refine ⟨742829869711066116013637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1980879652562842976036365 742829869711066116013637)
                  ·
                    refine ⟨139280600570824896752557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742829869711066116013637 139280600570824896752557)
                    ·
                      rfl

theorem cell22_406872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_406872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406872 prefixEnd_406872 := by exact prefixLift 406872
  have htrace : WordTrace (prefixWord ++ tailWord_406872) baseStart_406872 baseEnd_406872 := by
    simpa [prefixWord, tailWord_406872, baseEnd_406872] using wordTrace_append hprefix tailTrace_406872
  have hstable : (prefixWord ++ tailWord_406872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406872).length < 2 ^ (prefixWord ++ tailWord_406872).sum := by decide
  have hdescent : baseEnd_406872 < baseStart_406872 := by decide
  rcases family_descends (prefixWord ++ tailWord_406872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406921 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 4]
def baseStart_406921 : Nat := 118140960795 + 406921 * 2 ^ 59
def prefixEnd_406921 : Nat := 4983230072969 + 3 ^ 40 * 406921 * 2
def baseEnd_406921 : Nat := 46432458090735034092469

theorem tailTrace_406921 : CollatzResearch.WordTrace tailWord_406921 prefixEnd_406921 46432458090735034092469 := by
  unfold tailWord_406921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841628158802188419004617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9894418772534792279336411 14841628158802188419004617)
  ·
    refine ⟨11131221119101641314253463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14841628158802188419004617 11131221119101641314253463)
    ·
      refine ⟨16696831678652461971380195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11131221119101641314253463 16696831678652461971380195)
      ·
        refine ⟨25045247517978692957070293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16696831678652461971380195 25045247517978692957070293)
        ·
          refine ⟨586997988702625616181335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25045247517978692957070293 586997988702625616181335)
          ·
            refine ⟨880496983053938424272003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586997988702625616181335 880496983053938424272003)
            ·
              refine ⟨1320745474580907636408005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880496983053938424272003 1320745474580907636408005)
              ·
                refine ⟨247639776483920181826501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1320745474580907636408005 247639776483920181826501)
                ·
                  refine ⟨46432458090735034092469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247639776483920181826501 46432458090735034092469)
                  ·
                    rfl

theorem cell22_406921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_406921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406921 prefixEnd_406921 := by exact prefixLift 406921
  have htrace : WordTrace (prefixWord ++ tailWord_406921) baseStart_406921 baseEnd_406921 := by
    simpa [prefixWord, tailWord_406921, baseEnd_406921] using wordTrace_append hprefix tailTrace_406921
  have hstable : (prefixWord ++ tailWord_406921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406921).length < 2 ^ (prefixWord ++ tailWord_406921).sum := by decide
  have hdescent : baseEnd_406921 < baseStart_406921 := by decide
  rcases family_descends (prefixWord ++ tailWord_406921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406936 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_406936 : Nat := 118140960795 + 406936 * 2 ^ 59
def prefixEnd_406936 : Nat := 4983230072969 + 3 ^ 40 * 406936 * 2
def baseEnd_406936 : Nat := 139302509078750063152361

theorem tailTrace_406936 : CollatzResearch.WordTrace tailWord_406936 prefixEnd_406936 139302509078750063152361 := by
  unfold tailWord_406936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421087626873922990400331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9894783502498563987200441 7421087626873922990400331)
  ·
    refine ⟨11131631440310884485600497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421087626873922990400331 11131631440310884485600497)
    ·
      refine ⟨8348723580233163364200373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11131631440310884485600497 8348723580233163364200373)
      ·
        refine ⟨782692835646859065393785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8348723580233163364200373 782692835646859065393785)
        ·
          refine ⟨587019626735144299045339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782692835646859065393785 587019626735144299045339)
          ·
            refine ⟨880529440102716448568009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587019626735144299045339 880529440102716448568009)
            ·
              refine ⟨660397080077037336426007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880529440102716448568009 660397080077037336426007)
              ·
                refine ⟨990595620115556004639011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660397080077037336426007 990595620115556004639011)
                ·
                  refine ⟨1485893430173334006958517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990595620115556004639011 1485893430173334006958517)
                  ·
                    refine ⟨139302509078750063152361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1485893430173334006958517 139302509078750063152361)
                    ·
                      rfl

theorem cell22_406936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_406936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406936 prefixEnd_406936 := by exact prefixLift 406936
  have htrace : WordTrace (prefixWord ++ tailWord_406936) baseStart_406936 baseEnd_406936 := by
    simpa [prefixWord, tailWord_406936, baseEnd_406936] using wordTrace_append hprefix tailTrace_406936
  have hstable : (prefixWord ++ tailWord_406936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406936).length < 2 ^ (prefixWord ++ tailWord_406936).sum := by decide
  have hdescent : baseEnd_406936 < baseStart_406936 := by decide
  rcases family_descends (prefixWord ++ tailWord_406936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406962 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_406962 : Nat := 118140960795 + 406962 * 2 ^ 59
def prefixEnd_406962 : Nat := 4983230072969 + 3 ^ 40 * 406962 * 2
def baseEnd_406962 : Nat := 139311409410094662002281

theorem tailTrace_406962 : CollatzResearch.WordTrace tailWord_406962 prefixEnd_406962 139311409410094662002281 := by
  unfold tailWord_406962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710780887913413105311785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9895415701102434947498093 3710780887913413105311785)
  ·
    refine ⟨2783085665935059828983839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3710780887913413105311785 2783085665935059828983839)
    ·
      refine ⟨4174628498902589743475759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783085665935059828983839 4174628498902589743475759)
      ·
        refine ⟨6261942748353884615213639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174628498902589743475759 6261942748353884615213639)
        ·
          refine ⟨9392914122530826922820459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261942748353884615213639 9392914122530826922820459)
          ·
            refine ⟨14089371183796240384230689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392914122530826922820459 14089371183796240384230689)
            ·
              refine ⟨10567028387847180288173017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14089371183796240384230689 10567028387847180288173017)
              ·
                refine ⟨7925271290885385216129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10567028387847180288173017 7925271290885385216129763)
                ·
                  refine ⟨11887906936328077824194645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925271290885385216129763 11887906936328077824194645)
                  ·
                    refine ⟨139311409410094662002281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11887906936328077824194645 139311409410094662002281)
                    ·
                      rfl

theorem cell22_406962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_406962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406962 prefixEnd_406962 := by exact prefixLift 406962
  have htrace : WordTrace (prefixWord ++ tailWord_406962) baseStart_406962 baseEnd_406962 := by
    simpa [prefixWord, tailWord_406962, baseEnd_406962] using wordTrace_append hprefix tailTrace_406962
  have hstable : (prefixWord ++ tailWord_406962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406962).length < 2 ^ (prefixWord ++ tailWord_406962).sum := by decide
  have hdescent : baseEnd_406962 < baseStart_406962 := by decide
  rcases family_descends (prefixWord ++ tailWord_406962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406998 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_406998 : Nat := 118140960795 + 406998 * 2 ^ 59
def prefixEnd_406998 : Nat := 4983230072969 + 3 ^ 40 * 406998 * 2
def baseEnd_406998 : Nat := 139323732945802568102171

theorem tailTrace_406998 : CollatzResearch.WordTrace tailWord_406998 prefixEnd_406998 139323732945802568102171 := by
  unfold tailWord_406998
  simp only [CollatzResearch.WordTrace]
  refine ⟨927777286220201910597353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9896291053015487046371765 927777286220201910597353)
  ·
    refine ⟨695832964665151432948015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 927777286220201910597353 695832964665151432948015)
    ·
      refine ⟨1043749446997727149422023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695832964665151432948015 1043749446997727149422023)
      ·
        refine ⟨1565624170496590724133035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043749446997727149422023 1565624170496590724133035)
        ·
          refine ⟨2348436255744886086199553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565624170496590724133035 2348436255744886086199553)
          ·
            refine ⟨1761327191808664564649665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348436255744886086199553 1761327191808664564649665)
            ·
              refine ⟨1320995393856498423487249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761327191808664564649665 1320995393856498423487249)
              ·
                refine ⟨990746545392373817615437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320995393856498423487249 990746545392373817615437)
                ·
                  refine ⟨371529954522140181605789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990746545392373817615437 371529954522140181605789)
                  ·
                    refine ⟨139323732945802568102171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371529954522140181605789 139323732945802568102171)
                    ·
                      rfl

theorem cell22_406998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_406998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_406998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_406998 prefixEnd_406998 := by exact prefixLift 406998
  have htrace : WordTrace (prefixWord ++ tailWord_406998) baseStart_406998 baseEnd_406998 := by
    simpa [prefixWord, tailWord_406998, baseEnd_406998] using wordTrace_append hprefix tailTrace_406998
  have hstable : (prefixWord ++ tailWord_406998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406998).length < 2 ^ (prefixWord ++ tailWord_406998).sum := by decide
  have hdescent : baseEnd_406998 < baseStart_406998 := by decide
  rcases family_descends (prefixWord ++ tailWord_406998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407015 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 1, 3]
def baseStart_407015 : Nat := 118140960795 + 407015 * 2 ^ 59
def prefixEnd_407015 : Nat := 4983230072969 + 3 ^ 40 * 407015 * 2
def baseEnd_407015 : Nat := 139329552393220190427119

theorem tailTrace_407015 : CollatzResearch.WordTrace tailWord_407015 prefixEnd_407015 139329552393220190427119 := by
  unfold tailWord_407015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845056620461642472926499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9896704413641094981950999 14845056620461642472926499)
  ·
    refine ⟨22267584930692463709389749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14845056620461642472926499 22267584930692463709389749)
    ·
      refine ⟨2087586087252418472755289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22267584930692463709389749 2087586087252418472755289)
      ·
        refine ⟨1565689565439313854566467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087586087252418472755289 1565689565439313854566467)
        ·
          refine ⟨2348534348158970781849701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565689565439313854566467 2348534348158970781849701)
          ·
            refine ⟨440350190279807021596819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2348534348158970781849701 440350190279807021596819)
            ·
              refine ⟨660525285419710532395229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440350190279807021596819 660525285419710532395229)
              ·
                refine ⟨247696982032391449648211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660525285419710532395229 247696982032391449648211)
                ·
                  refine ⟨371545473048587174472317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247696982032391449648211 371545473048587174472317)
                  ·
                    refine ⟨139329552393220190427119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371545473048587174472317 139329552393220190427119)
                    ·
                      rfl

theorem cell22_407015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_407015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407015 prefixEnd_407015 := by exact prefixLift 407015
  have htrace : WordTrace (prefixWord ++ tailWord_407015) baseStart_407015 baseEnd_407015 := by
    simpa [prefixWord, tailWord_407015, baseEnd_407015] using wordTrace_append hprefix tailTrace_407015
  have hstable : (prefixWord ++ tailWord_407015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407015).length < 2 ^ (prefixWord ++ tailWord_407015).sum := by decide
  have hdescent : baseEnd_407015 < baseStart_407015 := by decide
  rcases family_descends (prefixWord ++ tailWord_407015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407114 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_407114 : Nat := 118140960795 + 407114 * 2 ^ 59
def prefixEnd_407114 : Nat := 4983230072969 + 3 ^ 40 * 407114 * 2
def baseEnd_407114 : Nat := 139363442116416932201815

theorem tailTrace_407114 : CollatzResearch.WordTrace tailWord_407114 prefixEnd_407114 139363442116416932201815 := by
  unfold tailWord_407114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712166861775745595195099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9899111631401988253853597 3712166861775745595195099)
  ·
    refine ⟨5568250292663618392792649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712166861775745595195099 5568250292663618392792649)
    ·
      refine ⟨4176187719497713794594487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5568250292663618392792649 4176187719497713794594487)
      ·
        refine ⟨6264281579246570691891731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176187719497713794594487 6264281579246570691891731)
        ·
          refine ⟨9396422368869856037837597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264281579246570691891731 9396422368869856037837597)
          ·
            refine ⟨3523658388326196014189099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9396422368869856037837597 3523658388326196014189099)
            ·
              refine ⟨5285487582489294021283649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523658388326196014189099 5285487582489294021283649)
              ·
                refine ⟨3964115686866970515962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285487582489294021283649 3964115686866970515962737)
                ·
                  refine ⟨2973086765150227886972053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964115686866970515962737 2973086765150227886972053)
                  ·
                    refine ⟨139363442116416932201815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2973086765150227886972053 139363442116416932201815)
                    ·
                      rfl

theorem cell22_407114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_407114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407114 prefixEnd_407114 := by exact prefixLift 407114
  have htrace : WordTrace (prefixWord ++ tailWord_407114) baseStart_407114 baseEnd_407114 := by
    simpa [prefixWord, tailWord_407114, baseEnd_407114] using wordTrace_append hprefix tailTrace_407114
  have hstable : (prefixWord ++ tailWord_407114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407114).length < 2 ^ (prefixWord ++ tailWord_407114).sum := by decide
  have hdescent : baseEnd_407114 < baseStart_407114 := by decide
  rcases family_descends (prefixWord ++ tailWord_407114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407116 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_407116 : Nat := 118140960795 + 407116 * 2 ^ 59
def prefixEnd_407116 : Nat := 4983230072969 + 3 ^ 40 * 407116 * 2
def baseEnd_407116 : Nat := 139364126757289593651809

theorem tailTrace_407116 : CollatzResearch.WordTrace tailWord_407116 prefixEnd_407116 139364126757289593651809 := by
  unfold tailWord_407116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424370196547868361176601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9899160262063824481568801 7424370196547868361176601)
  ·
    refine ⟨5568277647410901270882451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7424370196547868361176601 5568277647410901270882451)
    ·
      refine ⟨8352416471116351906323677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568277647410901270882451 8352416471116351906323677)
      ·
        refine ⟨3132156176668631964871379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8352416471116351906323677 3132156176668631964871379)
        ·
          refine ⟨4698234265002947947307069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132156176668631964871379 4698234265002947947307069)
          ·
            refine ⟨1761837849376105480240151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4698234265002947947307069 1761837849376105480240151)
            ·
              refine ⟨2642756774064158220360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761837849376105480240151 2642756774064158220360227)
              ·
                refine ⟨3964135161096237330540341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642756774064158220360227 3964135161096237330540341)
                ·
                  refine ⟨371637671352772249738157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3964135161096237330540341 371637671352772249738157)
                  ·
                    refine ⟨139364126757289593651809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371637671352772249738157 139364126757289593651809)
                    ·
                      rfl

theorem cell22_407116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_407116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407116 prefixEnd_407116 := by exact prefixLift 407116
  have htrace : WordTrace (prefixWord ++ tailWord_407116) baseStart_407116 baseEnd_407116 := by
    simpa [prefixWord, tailWord_407116, baseEnd_407116] using wordTrace_append hprefix tailTrace_407116
  have hstable : (prefixWord ++ tailWord_407116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407116).length < 2 ^ (prefixWord ++ tailWord_407116).sum := by decide
  have hdescent : baseEnd_407116 < baseStart_407116 := by decide
  rcases family_descends (prefixWord ++ tailWord_407116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407126 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_407126 : Nat := 118140960795 + 407126 * 2 ^ 59
def prefixEnd_407126 : Nat := 4983230072969 + 3 ^ 40 * 407126 * 2
def baseEnd_407126 : Nat := 139367549961652900901779

theorem tailTrace_407126 : CollatzResearch.WordTrace tailWord_407126 prefixEnd_407126 139367549961652900901779 := by
  unfold tailWord_407126
  simp only [CollatzResearch.WordTrace]
  refine ⟨928069070191219276888577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9899403415373005620144821 928069070191219276888577)
  ·
    refine ⟨696051802643414457666433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 928069070191219276888577 696051802643414457666433)
    ·
      refine ⟨522038851982560843249825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696051802643414457666433 522038851982560843249825)
      ·
        refine ⟨391529138986920632437369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522038851982560843249825 391529138986920632437369)
        ·
          refine ⟨293646854240190474328027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391529138986920632437369 293646854240190474328027)
          ·
            refine ⟨440470281360285711492041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293646854240190474328027 440470281360285711492041)
            ·
              refine ⟨330352711020214283619031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440470281360285711492041 330352711020214283619031)
              ·
                refine ⟨495529066530321425428547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330352711020214283619031 495529066530321425428547)
                ·
                  refine ⟨743293599795482138142821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495529066530321425428547 743293599795482138142821)
                  ·
                    refine ⟨139367549961652900901779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743293599795482138142821 139367549961652900901779)
                    ·
                      rfl

theorem cell22_407126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_407126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407126 prefixEnd_407126 := by exact prefixLift 407126
  have htrace : WordTrace (prefixWord ++ tailWord_407126) baseStart_407126 baseEnd_407126 := by
    simpa [prefixWord, tailWord_407126, baseEnd_407126] using wordTrace_append hprefix tailTrace_407126
  have hstable : (prefixWord ++ tailWord_407126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407126).length < 2 ^ (prefixWord ++ tailWord_407126).sum := by decide
  have hdescent : baseEnd_407126 < baseStart_407126 := by decide
  rcases family_descends (prefixWord ++ tailWord_407126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407146 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_407146 : Nat := 118140960795 + 407146 * 2 ^ 59
def prefixEnd_407146 : Nat := 4983230072969 + 3 ^ 40 * 407146 * 2
def baseEnd_407146 : Nat := 46458132123459838467239

theorem tailTrace_407146 : CollatzResearch.WordTrace tailWord_407146 prefixEnd_407146 46458132123459838467239 := by
  unfold tailWord_407146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712458645746762961486323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9899889721991367897296861 3712458645746762961486323)
  ·
    refine ⟨5568687968620144442229485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712458645746762961486323 5568687968620144442229485)
    ·
      refine ⟨2088257988232554165836057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5568687968620144442229485 2088257988232554165836057)
      ·
        refine ⟨1566193491174415624377043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088257988232554165836057 1566193491174415624377043)
        ·
          refine ⟨2349290236761623436565565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566193491174415624377043 2349290236761623436565565)
          ·
            refine ⟨880983838785608788712087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2349290236761623436565565 880983838785608788712087)
            ·
              refine ⟨1321475758178413183068131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880983838785608788712087 1321475758178413183068131)
              ·
                refine ⟨1982213637267619774602197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321475758178413183068131 1982213637267619774602197)
                ·
                  refine ⟨46458132123459838467239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1982213637267619774602197 46458132123459838467239)
                  ·
                    rfl

theorem cell22_407146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_407146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407146 prefixEnd_407146 := by exact prefixLift 407146
  have htrace : WordTrace (prefixWord ++ tailWord_407146) baseStart_407146 baseEnd_407146 := by
    simpa [prefixWord, tailWord_407146, baseEnd_407146] using wordTrace_append hprefix tailTrace_407146
  have hstable : (prefixWord ++ tailWord_407146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407146).length < 2 ^ (prefixWord ++ tailWord_407146).sum := by decide
  have hdescent : baseEnd_407146 < baseStart_407146 := by decide
  rcases family_descends (prefixWord ++ tailWord_407146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407150 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_407150 : Nat := 118140960795 + 407150 * 2 ^ 59
def prefixEnd_407150 : Nat := 4983230072969 + 3 ^ 40 * 407150 * 2
def baseEnd_407150 : Nat := 139375765652124838301705

theorem tailTrace_407150 : CollatzResearch.WordTrace tailWord_407150 prefixEnd_407150 139375765652124838301705 := by
  unfold tailWord_407150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856247559371570066136363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9899986983315040352727269 1856247559371570066136363)
  ·
    refine ⟨2784371339057355099204545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856247559371570066136363 2784371339057355099204545)
    ·
      refine ⟨2088278504293016324403409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2784371339057355099204545 2088278504293016324403409)
      ·
        refine ⟨1566208878219762243302557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088278504293016324403409 1566208878219762243302557)
        ·
          refine ⟨587328329332410841238459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1566208878219762243302557 587328329332410841238459)
          ·
            refine ⟨880992493998616261857689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587328329332410841238459 880992493998616261857689)
            ·
              refine ⟨660744370498962196393267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880992493998616261857689 660744370498962196393267)
              ·
                refine ⟨991116555748443294589901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660744370498962196393267 991116555748443294589901)
                ·
                  refine ⟨371668708405666235471213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991116555748443294589901 371668708405666235471213)
                  ·
                    refine ⟨139375765652124838301705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371668708405666235471213 139375765652124838301705)
                    ·
                      rfl

theorem cell22_407150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_407150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407150 prefixEnd_407150 := by exact prefixLift 407150
  have htrace : WordTrace (prefixWord ++ tailWord_407150) baseStart_407150 baseEnd_407150 := by
    simpa [prefixWord, tailWord_407150, baseEnd_407150] using wordTrace_append hprefix tailTrace_407150
  have hstable : (prefixWord ++ tailWord_407150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407150).length < 2 ^ (prefixWord ++ tailWord_407150).sum := by decide
  have hdescent : baseEnd_407150 < baseStart_407150 := by decide
  rcases family_descends (prefixWord ++ tailWord_407150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407214 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_407214 : Nat := 118140960795 + 407214 * 2 ^ 59
def prefixEnd_407214 : Nat := 4983230072969 + 3 ^ 40 * 407214 * 2
def baseEnd_407214 : Nat := 46465891386683334900503

theorem tailTrace_407214 : CollatzResearch.WordTrace tailWord_407214 prefixEnd_407214 46465891386683334900503 := by
  unfold tailWord_407214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856539343342587432427587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9901543164493799639613797 1856539343342587432427587)
  ·
    refine ⟨2784809015013881148641381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856539343342587432427587 2784809015013881148641381)
    ·
      refine ⟨522151690315102715370259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2784809015013881148641381 522151690315102715370259)
      ·
        refine ⟨783227535472654073055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522151690315102715370259 783227535472654073055389)
        ·
          refine ⟨293710325802245277395771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783227535472654073055389 293710325802245277395771)
          ·
            refine ⟨440565488703367916093657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293710325802245277395771 440565488703367916093657)
            ·
              refine ⟨330424116527525937070243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440565488703367916093657 330424116527525937070243)
              ·
                refine ⟨495636174791288905605365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330424116527525937070243 495636174791288905605365)
                ·
                  refine ⟨46465891386683334900503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495636174791288905605365 46465891386683334900503)
                  ·
                    rfl

theorem cell22_407214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_407214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407214 prefixEnd_407214 := by exact prefixLift 407214
  have htrace : WordTrace (prefixWord ++ tailWord_407214) baseStart_407214 baseEnd_407214 := by
    simpa [prefixWord, tailWord_407214, baseEnd_407214] using wordTrace_append hprefix tailTrace_407214
  have hstable : (prefixWord ++ tailWord_407214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407214).length < 2 ^ (prefixWord ++ tailWord_407214).sum := by decide
  have hdescent : baseEnd_407214 < baseStart_407214 := by decide
  rcases family_descends (prefixWord ++ tailWord_407214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407236 : List Nat := [2, 3, 3, 1, 1, 1, 1, 10]
def baseStart_407236 : Nat := 118140960795 + 407236 * 2 ^ 59
def prefixEnd_407236 : Nat := 4983230072969 + 3 ^ 40 * 407236 * 2
def baseEnd_407236 : Nat := 15489467245516586739049

theorem tailTrace_407236 : CollatzResearch.WordTrace tailWord_407236 prefixEnd_407236 15489467245516586739049 := by
  unfold tailWord_407236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426558576330498608360781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9902078101773998144481041 7426558576330498608360781)
  ·
    refine ⟨2784959466123936978135293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7426558576330498608360781 2784959466123936978135293)
    ·
      refine ⟨1044359799796476366800735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2784959466123936978135293 1044359799796476366800735)
      ·
        refine ⟨1566539699694714550201103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044359799796476366800735 1566539699694714550201103)
        ·
          refine ⟨2349809549542071825301655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566539699694714550201103 2349809549542071825301655)
          ·
            refine ⟨3524714324313107737952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349809549542071825301655 3524714324313107737952483)
            ·
              refine ⟨5287071486469661606928725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524714324313107737952483 5287071486469661606928725)
              ·
                refine ⟨15489467245516586739049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5287071486469661606928725 15489467245516586739049)
                ·
                  rfl

theorem cell22_407236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_407236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407236 prefixEnd_407236 := by exact prefixLift 407236
  have htrace : WordTrace (prefixWord ++ tailWord_407236) baseStart_407236 baseEnd_407236 := by
    simpa [prefixWord, tailWord_407236, baseEnd_407236] using wordTrace_append hprefix tailTrace_407236
  have hstable : (prefixWord ++ tailWord_407236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407236).length < 2 ^ (prefixWord ++ tailWord_407236).sum := by decide
  have hdescent : baseEnd_407236 < baseStart_407236 := by decide
  rcases family_descends (prefixWord ++ tailWord_407236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407268 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_407268 : Nat := 118140960795 + 407268 * 2 ^ 59
def prefixEnd_407268 : Nat := 4983230072969 + 3 ^ 40 * 407268 * 2
def baseEnd_407268 : Nat := 139416159463611863851343

theorem tailTrace_407268 : CollatzResearch.WordTrace tailWord_407268 prefixEnd_407268 139416159463611863851343 := by
  unfold tailWord_407268
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427142144272533340943229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9902856192363377787924305 7427142144272533340943229)
  ·
    refine ⟨2785178304102200002853711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7427142144272533340943229 2785178304102200002853711)
    ·
      refine ⟨4177767456153300004280567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785178304102200002853711 4177767456153300004280567)
      ·
        refine ⟨6266651184229950006420851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177767456153300004280567 6266651184229950006420851)
        ·
          refine ⟨9399976776344925009631277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266651184229950006420851 9399976776344925009631277)
          ·
            refine ⟨3524991291129346878611729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399976776344925009631277 3524991291129346878611729)
            ·
              refine ⟨2643743468347010158958797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524991291129346878611729 2643743468347010158958797)
              ·
                refine ⟨991403800630128809609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2643743468347010158958797 991403800630128809609549)
                ·
                  refine ⟨371776425236298303603581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991403800630128809609549 371776425236298303603581)
                  ·
                    refine ⟨139416159463611863851343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371776425236298303603581 139416159463611863851343)
                    ·
                      rfl

theorem cell22_407268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_407268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407268 prefixEnd_407268 := by exact prefixLift 407268
  have htrace : WordTrace (prefixWord ++ tailWord_407268) baseStart_407268 baseEnd_407268 := by
    simpa [prefixWord, tailWord_407268, baseEnd_407268] using wordTrace_append hprefix tailTrace_407268
  have hstable : (prefixWord ++ tailWord_407268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407268).length < 2 ^ (prefixWord ++ tailWord_407268).sum := by decide
  have hdescent : baseEnd_407268 < baseStart_407268 := by decide
  rcases family_descends (prefixWord ++ tailWord_407268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407298 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_407298 : Nat := 118140960795 + 407298 * 2 ^ 59
def prefixEnd_407298 : Nat := 4983230072969 + 3 ^ 40 * 407298 * 2
def baseEnd_407298 : Nat := 46475476358900595200417

theorem tailTrace_407298 : CollatzResearch.WordTrace tailWord_407298 prefixEnd_407298 46475476358900595200417 := by
  unfold tailWord_407298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713844619609095451369637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9903585652290921203652365 3713844619609095451369637)
  ·
    refine ⟨696345866176705397131807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3713844619609095451369637 696345866176705397131807)
    ·
      refine ⟨1044518799265058095697711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696345866176705397131807 1044518799265058095697711)
      ·
        refine ⟨1566778198897587143546567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044518799265058095697711 1566778198897587143546567)
        ·
          refine ⟨2350167298346380715319851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566778198897587143546567 2350167298346380715319851)
          ·
            refine ⟨3525250947519571072979777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350167298346380715319851 3525250947519571072979777)
            ·
              refine ⟨2643938210639678304734833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525250947519571072979777 2643938210639678304734833)
              ·
                refine ⟨1982953657979758728551125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643938210639678304734833 1982953657979758728551125)
                ·
                  refine ⟨46475476358900595200417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1982953657979758728551125 46475476358900595200417)
                  ·
                    rfl

theorem cell22_407298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_407298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407298 prefixEnd_407298 := by exact prefixLift 407298
  have htrace : WordTrace (prefixWord ++ tailWord_407298) baseStart_407298 baseEnd_407298 := by
    simpa [prefixWord, tailWord_407298, baseEnd_407298] using wordTrace_append hprefix tailTrace_407298
  have hstable : (prefixWord ++ tailWord_407298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407298).length < 2 ^ (prefixWord ++ tailWord_407298).sum := by decide
  have hdescent : baseEnd_407298 < baseStart_407298 := by decide
  rcases family_descends (prefixWord ++ tailWord_407298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_407311 : Nat := 118140960795 + 407311 * 2 ^ 59
def prefixEnd_407311 : Nat := 4983230072969 + 3 ^ 40 * 407311 * 2
def baseEnd_407311 : Nat := 139430879242374085026211

theorem tailTrace_407311 : CollatzResearch.WordTrace tailWord_407311 prefixEnd_407311 139430879242374085026211 := by
  unfold tailWord_407311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14855852627389285025701787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9903901751592856683801191 14855852627389285025701787)
  ·
    refine ⟨22283778941083927538552681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14855852627389285025701787 22283778941083927538552681)
    ·
      refine ⟨16712834205812945653914511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22283778941083927538552681 16712834205812945653914511)
      ·
        refine ⟨25069251308719418480871767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16712834205812945653914511 25069251308719418480871767)
        ·
          refine ⟨37603876963079127721307651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25069251308719418480871767 37603876963079127721307651)
          ·
            refine ⟨56405815444618691581961477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37603876963079127721307651 56405815444618691581961477)
            ·
              refine ⟨10576090395866004671617777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56405815444618691581961477 10576090395866004671617777)
              ·
                refine ⟨7932067796899503503713333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10576090395866004671617777 7932067796899503503713333)
                ·
                  refine ⟨743631355959328453473125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7932067796899503503713333 743631355959328453473125)
                  ·
                    refine ⟨139430879242374085026211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743631355959328453473125 139430879242374085026211)
                    ·
                      rfl

theorem cell22_407311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_407311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407311 prefixEnd_407311 := by exact prefixLift 407311
  have htrace : WordTrace (prefixWord ++ tailWord_407311) baseStart_407311 baseEnd_407311 := by
    simpa [prefixWord, tailWord_407311, baseEnd_407311] using wordTrace_append hprefix tailTrace_407311
  have hstable : (prefixWord ++ tailWord_407311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407311).length < 2 ^ (prefixWord ++ tailWord_407311).sum := by decide
  have hdescent : baseEnd_407311 < baseStart_407311 := by decide
  rcases family_descends (prefixWord ++ tailWord_407311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407345 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_407345 : Nat := 118140960795 + 407345 * 2 ^ 59
def prefixEnd_407345 : Nat := 4983230072969 + 3 ^ 40 * 407345 * 2
def baseEnd_407345 : Nat := 139442518137209329676107

theorem tailTrace_407345 : CollatzResearch.WordTrace tailWord_407345 prefixEnd_407345 139442518137209329676107 := by
  unfold tailWord_407345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857092709266108832439489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9904728472844072554959659 14857092709266108832439489)
  ·
    refine ⟨11142819531949581624329617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14857092709266108832439489 11142819531949581624329617)
    ·
      refine ⟨8357114648962186218247213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11142819531949581624329617 8357114648962186218247213)
      ·
        refine ⟨3133917993360819831842705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8357114648962186218247213 3133917993360819831842705)
        ·
          refine ⟨2350438495020614873882029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3133917993360819831842705 2350438495020614873882029)
          ·
            refine ⟨881414435632730577705761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2350438495020614873882029 881414435632730577705761)
            ·
              refine ⟨661060826724547933279321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881414435632730577705761 661060826724547933279321)
              ·
                refine ⟨495795620043410949959491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661060826724547933279321 495795620043410949959491)
                ·
                  refine ⟨743693430065116424939237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495795620043410949959491 743693430065116424939237)
                  ·
                    refine ⟨139442518137209329676107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743693430065116424939237 139442518137209329676107)
                    ·
                      rfl

theorem cell22_407345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_407345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407345 prefixEnd_407345 := by exact prefixLift 407345
  have htrace : WordTrace (prefixWord ++ tailWord_407345) baseStart_407345 baseEnd_407345 := by
    simpa [prefixWord, tailWord_407345, baseEnd_407345] using wordTrace_append hprefix tailTrace_407345
  have hstable : (prefixWord ++ tailWord_407345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407345).length < 2 ^ (prefixWord ++ tailWord_407345).sum := by decide
  have hdescent : baseEnd_407345 < baseStart_407345 := by decide
  rcases family_descends (prefixWord ++ tailWord_407345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407377 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 4]
def baseStart_407377 : Nat := 118140960795 + 407377 * 2 ^ 59
def prefixEnd_407377 : Nat := 4983230072969 + 3 ^ 40 * 407377 * 2
def baseEnd_407377 : Nat := 46484490797057304292003

theorem tailTrace_407377 : CollatzResearch.WordTrace tailWord_407377 prefixEnd_407377 46484490797057304292003 := by
  unfold tailWord_407377
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858259845150178297604385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9905506563433452198402923 14858259845150178297604385)
  ·
    refine ⟨11143694883862633723203289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14858259845150178297604385 11143694883862633723203289)
    ·
      refine ⟨8357771162896975292402467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11143694883862633723203289 8357771162896975292402467)
      ·
        refine ⟨12536656744345462938603701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357771162896975292402467 12536656744345462938603701)
        ·
          refine ⟨1175311569782387150494097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12536656744345462938603701 1175311569782387150494097)
          ·
            refine ⟨881483677336790362870573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175311569782387150494097 881483677336790362870573)
            ·
              refine ⟨330556379001296386076465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881483677336790362870573 330556379001296386076465)
              ·
                refine ⟨247917284250972289557349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330556379001296386076465 247917284250972289557349)
                ·
                  refine ⟨46484490797057304292003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247917284250972289557349 46484490797057304292003)
                  ·
                    rfl

theorem cell22_407377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_407377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407377 prefixEnd_407377 := by exact prefixLift 407377
  have htrace : WordTrace (prefixWord ++ tailWord_407377) baseStart_407377 baseEnd_407377 := by
    simpa [prefixWord, tailWord_407377, baseEnd_407377] using wordTrace_append hprefix tailTrace_407377
  have hstable : (prefixWord ++ tailWord_407377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407377).length < 2 ^ (prefixWord ++ tailWord_407377).sum := by decide
  have hdescent : baseEnd_407377 < baseStart_407377 := by decide
  rcases family_descends (prefixWord ++ tailWord_407377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407392 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_407392 : Nat := 118140960795 + 407392 * 2 ^ 59
def prefixEnd_407392 : Nat := 4983230072969 + 3 ^ 40 * 407392 * 2
def baseEnd_407392 : Nat := 139458607197716873750963

theorem tailTrace_407392 : CollatzResearch.WordTrace tailWord_407392 prefixEnd_407392 139458607197716873750963 := by
  unfold tailWord_407392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429403470047917929700215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9905871293397223906266953 7429403470047917929700215)
  ·
    refine ⟨11144105205071876894550323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429403470047917929700215 11144105205071876894550323)
    ·
      refine ⟨16716157807607815341825485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11144105205071876894550323 16716157807607815341825485)
      ·
        refine ⟨6268559177852930753184557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16716157807607815341825485 6268559177852930753184557)
        ·
          refine ⟨2350709691694849032444209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6268559177852930753184557 2350709691694849032444209)
          ·
            refine ⟨1763032268771136774333157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350709691694849032444209 1763032268771136774333157)
            ·
              refine ⟨330568550394588145187467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1763032268771136774333157 330568550394588145187467)
              ·
                refine ⟨495852825591882217781201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330568550394588145187467 495852825591882217781201)
                ·
                  refine ⟨371889619193911663335901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495852825591882217781201 371889619193911663335901)
                  ·
                    refine ⟨139458607197716873750963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371889619193911663335901 139458607197716873750963)
                    ·
                      rfl

theorem cell22_407392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_407392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407392 prefixEnd_407392 := by exact prefixLift 407392
  have htrace : WordTrace (prefixWord ++ tailWord_407392) baseStart_407392 baseEnd_407392 := by
    simpa [prefixWord, tailWord_407392, baseEnd_407392] using wordTrace_append hprefix tailTrace_407392
  have hstable : (prefixWord ++ tailWord_407392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407392).length < 2 ^ (prefixWord ++ tailWord_407392).sum := by decide
  have hdescent : baseEnd_407392 < baseStart_407392 := by decide
  rcases family_descends (prefixWord ++ tailWord_407392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407403 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 5, 3]
def baseStart_407403 : Nat := 118140960795 + 407403 * 2 ^ 59
def prefixEnd_407403 : Nat := 4983230072969 + 3 ^ 40 * 407403 * 2
def baseEnd_407403 : Nat := 139462372722516511725929

theorem tailTrace_407403 : CollatzResearch.WordTrace tailWord_407403 prefixEnd_407403 139462372722516511725929 := by
  unfold tailWord_407403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859208143055984738050863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9906138762037323158700575 14859208143055984738050863)
  ·
    refine ⟨22288812214583977107076295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14859208143055984738050863 22288812214583977107076295)
    ·
      refine ⟨33433218321875965660614443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22288812214583977107076295 33433218321875965660614443)
      ·
        refine ⟨50149827482813948490921665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33433218321875965660614443 50149827482813948490921665)
        ·
          refine ⟨37612370612110461368191249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50149827482813948490921665 37612370612110461368191249)
          ·
            refine ⟨28209277959082846026143437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37612370612110461368191249 28209277959082846026143437)
            ·
              refine ⟨10578479234656067259803789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28209277959082846026143437 10578479234656067259803789)
              ·
                refine ⟨3966929712996025222426421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10578479234656067259803789 3966929712996025222426421)
                ·
                  refine ⟨371899660593377364602477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3966929712996025222426421 371899660593377364602477)
                  ·
                    refine ⟨139462372722516511725929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 371899660593377364602477 139462372722516511725929)
                    ·
                      rfl

theorem cell22_407403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].length) (baseStart_407403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407403 prefixEnd_407403 := by exact prefixLift 407403
  have htrace : WordTrace (prefixWord ++ tailWord_407403) baseStart_407403 baseEnd_407403 := by
    simpa [prefixWord, tailWord_407403, baseEnd_407403] using wordTrace_append hprefix tailTrace_407403
  have hstable : (prefixWord ++ tailWord_407403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407403).length < 2 ^ (prefixWord ++ tailWord_407403).sum := by decide
  have hdescent : baseEnd_407403 < baseStart_407403 := by decide
  rcases family_descends (prefixWord ++ tailWord_407403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407450 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_407450 : Nat := 118140960795 + 407450 * 2 ^ 59
def prefixEnd_407450 : Nat := 4983230072969 + 3 ^ 40 * 407450 * 2
def baseEnd_407450 : Nat := 46492820594341351933595

theorem tailTrace_407450 : CollatzResearch.WordTrace tailWord_407450 prefixEnd_407450 46492820594341351933595 := by
  unfold tailWord_407450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715230593471427941252951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9907281582590474510007869 3715230593471427941252951)
  ·
    refine ⟨5572845890207141911879427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715230593471427941252951 5572845890207141911879427)
    ·
      refine ⟨8359268835310712867819141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572845890207141911879427 8359268835310712867819141)
      ·
        refine ⟨1567362906620758662716089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8359268835310712867819141 1567362906620758662716089)
        ·
          refine ⟨1175522179965568997037067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567362906620758662716089 1175522179965568997037067)
          ·
            refine ⟨1763283269948353495555601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175522179965568997037067 1763283269948353495555601)
            ·
              refine ⟨1322462452461265121666701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763283269948353495555601 1322462452461265121666701)
              ·
                refine ⟨495923419672974420625013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322462452461265121666701 495923419672974420625013)
                ·
                  refine ⟨46492820594341351933595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495923419672974420625013 46492820594341351933595)
                  ·
                    rfl

theorem cell22_407450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_407450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407450 prefixEnd_407450 := by exact prefixLift 407450
  have htrace : WordTrace (prefixWord ++ tailWord_407450) baseStart_407450 baseEnd_407450 := by
    simpa [prefixWord, tailWord_407450, baseEnd_407450] using wordTrace_append hprefix tailTrace_407450
  have hstable : (prefixWord ++ tailWord_407450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407450).length < 2 ^ (prefixWord ++ tailWord_407450).sum := by decide
  have hdescent : baseEnd_407450 < baseStart_407450 := by decide
  rcases family_descends (prefixWord ++ tailWord_407450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407480 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_407480 : Nat := 118140960795 + 407480 * 2 ^ 59
def prefixEnd_407480 : Nat := 4983230072969 + 3 ^ 40 * 407480 * 2
def baseEnd_407480 : Nat := 139488731396113977550693

theorem tailTrace_407480 : CollatzResearch.WordTrace tailWord_407480 prefixEnd_407480 139488731396113977550693 := by
  unfold tailWord_407480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431008281888513444301947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9908011042518017925735929 7431008281888513444301947)
  ·
    refine ⟨11146512422832770166452921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431008281888513444301947 11146512422832770166452921)
    ·
      refine ⟨8359884317124577624839691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11146512422832770166452921 8359884317124577624839691)
      ·
        refine ⟨12539826475686866437259537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359884317124577624839691 12539826475686866437259537)
        ·
          refine ⟨9404869856765149827944653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12539826475686866437259537 9404869856765149827944653)
          ·
            refine ⟨3526826196286931185479245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9404869856765149827944653 3526826196286931185479245)
            ·
              refine ⟨1322559823607599194554717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526826196286931185479245 1322559823607599194554717)
              ·
                refine ⟨495959933852849697958019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322559823607599194554717 495959933852849697958019)
                ·
                  refine ⟨743939900779274546937029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495959933852849697958019 743939900779274546937029)
                  ·
                    refine ⟨139488731396113977550693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743939900779274546937029 139488731396113977550693)
                    ·
                      rfl

theorem cell22_407480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_407480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407480 prefixEnd_407480 := by exact prefixLift 407480
  have htrace : WordTrace (prefixWord ++ tailWord_407480) baseStart_407480 baseEnd_407480 := by
    simpa [prefixWord, tailWord_407480, baseEnd_407480] using wordTrace_append hprefix tailTrace_407480
  have hstable : (prefixWord ++ tailWord_407480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407480).length < 2 ^ (prefixWord ++ tailWord_407480).sum := by decide
  have hdescent : baseEnd_407480 < baseStart_407480 := by decide
  rcases family_descends (prefixWord ++ tailWord_407480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407484 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_407484 : Nat := 118140960795 + 407484 * 2 ^ 59
def prefixEnd_407484 : Nat := 4983230072969 + 3 ^ 40 * 407484 * 2
def baseEnd_407484 : Nat := 46496700225953100150227

theorem tailTrace_407484 : CollatzResearch.WordTrace tailWord_407484 prefixEnd_407484 46496700225953100150227 := by
  unfold tailWord_407484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431081227881267785874753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9908108303841690381166337 7431081227881267785874753)
  ·
    refine ⟨5573310920910950839406065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7431081227881267785874753 5573310920910950839406065)
    ·
      refine ⟨4179983190683213129554549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573310920910950839406065 4179983190683213129554549)
      ·
        refine ⟨391873424126551230895739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4179983190683213129554549 391873424126551230895739)
        ·
          refine ⟨587810136189826846343609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391873424126551230895739 587810136189826846343609)
          ·
            refine ⟨440857602142370134757707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587810136189826846343609 440857602142370134757707)
            ·
              refine ⟨661286403213555202136561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440857602142370134757707 661286403213555202136561)
              ·
                refine ⟨495964802410166401602421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661286403213555202136561 495964802410166401602421)
                ·
                  refine ⟨46496700225953100150227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495964802410166401602421 46496700225953100150227)
                  ·
                    rfl

theorem cell22_407484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_407484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407484 prefixEnd_407484 := by exact prefixLift 407484
  have htrace : WordTrace (prefixWord ++ tailWord_407484) baseStart_407484 baseEnd_407484 := by
    simpa [prefixWord, tailWord_407484, baseEnd_407484] using wordTrace_append hprefix tailTrace_407484
  have hstable : (prefixWord ++ tailWord_407484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407484).length < 2 ^ (prefixWord ++ tailWord_407484).sum := by decide
  have hdescent : baseEnd_407484 < baseStart_407484 := by decide
  rcases family_descends (prefixWord ++ tailWord_407484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407565 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_407565 : Nat := 118140960795 + 407565 * 2 ^ 59
def prefixEnd_407565 : Nat := 4983230072969 + 3 ^ 40 * 407565 * 2
def baseEnd_407565 : Nat := 139517828633202089175433

theorem tailTrace_407565 : CollatzResearch.WordTrace tailWord_407565 prefixEnd_407565 139517828633202089175433 := by
  unfold tailWord_407565
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865116768469086405448149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9910077845646057603632099 14865116768469086405448149)
  ·
    refine ⟨348401174260994212627691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14865116768469086405448149 348401174260994212627691)
    ·
      refine ⟨522601761391491318941537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348401174260994212627691 522601761391491318941537)
      ·
        refine ⟨391951321043618489206153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522601761391491318941537 391951321043618489206153)
        ·
          refine ⟨293963490782713866904615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391951321043618489206153 293963490782713866904615)
          ·
            refine ⟨440945236174070800356923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293963490782713866904615 440945236174070800356923)
            ·
              refine ⟨661417854261106200535385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440945236174070800356923 661417854261106200535385)
              ·
                refine ⟨496063390695829650401539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661417854261106200535385 496063390695829650401539)
                ·
                  refine ⟨744095086043744475602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496063390695829650401539 744095086043744475602309)
                  ·
                    refine ⟨139517828633202089175433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744095086043744475602309 139517828633202089175433)
                    ·
                      rfl

theorem cell22_407565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_407565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407565 prefixEnd_407565 := by exact prefixLift 407565
  have htrace : WordTrace (prefixWord ++ tailWord_407565) baseStart_407565 baseEnd_407565 := by
    simpa [prefixWord, tailWord_407565, baseEnd_407565] using wordTrace_append hprefix tailTrace_407565
  have hstable : (prefixWord ++ tailWord_407565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407565).length < 2 ^ (prefixWord ++ tailWord_407565).sum := by decide
  have hdescent : baseEnd_407565 < baseStart_407565 := by decide
  rcases family_descends (prefixWord ++ tailWord_407565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407602 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_407602 : Nat := 118140960795 + 407602 * 2 ^ 59
def prefixEnd_407602 : Nat := 4983230072969 + 3 ^ 40 * 407602 * 2
def baseEnd_407602 : Nat := 46510164829782108666773

theorem tailTrace_407602 : CollatzResearch.WordTrace tailWord_407602 prefixEnd_407602 46510164829782108666773 := by
  unfold tailWord_407602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716616567333760431136265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9910977512890027816363373 3716616567333760431136265)
  ·
    refine ⟨2787462425500320323352199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3716616567333760431136265 2787462425500320323352199)
    ·
      refine ⟨4181193638250480485028299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787462425500320323352199 4181193638250480485028299)
      ·
        refine ⟨6271790457375720727542449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181193638250480485028299 6271790457375720727542449)
        ·
          refine ⟨4703842843031790545656837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271790457375720727542449 4703842843031790545656837)
          ·
            refine ⟨881970533068460727310657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4703842843031790545656837 881970533068460727310657)
            ·
              refine ⟨661477899801345545482993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881970533068460727310657 661477899801345545482993)
              ·
                refine ⟨496108424851009159112245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661477899801345545482993 496108424851009159112245)
                ·
                  refine ⟨46510164829782108666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496108424851009159112245 46510164829782108666773)
                  ·
                    rfl

theorem cell22_407602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_407602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407602 prefixEnd_407602 := by exact prefixLift 407602
  have htrace : WordTrace (prefixWord ++ tailWord_407602) baseStart_407602 baseEnd_407602 := by
    simpa [prefixWord, tailWord_407602, baseEnd_407602] using wordTrace_append hprefix tailTrace_407602
  have hstable : (prefixWord ++ tailWord_407602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407602).length < 2 ^ (prefixWord ++ tailWord_407602).sum := by decide
  have hdescent : baseEnd_407602 < baseStart_407602 := by decide
  rcases family_descends (prefixWord ++ tailWord_407602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407606 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_407606 : Nat := 118140960795 + 407606 * 2 ^ 59
def prefixEnd_407606 : Nat := 4983230072969 + 3 ^ 40 * 407606 * 2
def baseEnd_407606 : Nat := 139531863771091648900307

theorem tailTrace_407606 : CollatzResearch.WordTrace tailWord_407606 prefixEnd_407606 139531863771091648900307 := by
  unfold tailWord_407606
  simp only [CollatzResearch.WordTrace]
  refine ⟨929163260082534400480667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9911074774213700271793781 929163260082534400480667)
  ·
    refine ⟨1393744890123801600721001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929163260082534400480667 1393744890123801600721001)
    ·
      refine ⟨1045308667592851200540751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393744890123801600721001 1045308667592851200540751)
      ·
        refine ⟨1567963001389276800811127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045308667592851200540751 1567963001389276800811127)
        ·
          refine ⟨2351944502083915201216691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567963001389276800811127 2351944502083915201216691)
          ·
            refine ⟨3527916753125872801825037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351944502083915201216691 3527916753125872801825037)
            ·
              refine ⟨1322968782422202300684389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3527916753125872801825037 1322968782422202300684389)
              ·
                refine ⟨248056646704162931378323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1322968782422202300684389 248056646704162931378323)
                ·
                  refine ⟨372084970056244397067485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248056646704162931378323 372084970056244397067485)
                  ·
                    refine ⟨139531863771091648900307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372084970056244397067485 139531863771091648900307)
                    ·
                      rfl

theorem cell22_407606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_407606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407606 prefixEnd_407606 := by exact prefixLift 407606
  have htrace : WordTrace (prefixWord ++ tailWord_407606) baseStart_407606 baseEnd_407606 := by
    simpa [prefixWord, tailWord_407606, baseEnd_407606] using wordTrace_append hprefix tailTrace_407606
  have hstable : (prefixWord ++ tailWord_407606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407606).length < 2 ^ (prefixWord ++ tailWord_407606).sum := by decide
  have hdescent : baseEnd_407606 < baseStart_407606 := by decide
  rcases family_descends (prefixWord ++ tailWord_407606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407615 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_407615 : Nat := 118140960795 + 407615 * 2 ^ 59
def prefixEnd_407615 : Nat := 4983230072969 + 3 ^ 40 * 407615 * 2
def baseEnd_407615 : Nat := 139534944655018625425279

theorem tailTrace_407615 : CollatzResearch.WordTrace tailWord_407615 prefixEnd_407615 139534944655018625425279 := by
  unfold tailWord_407615
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866940418287944944768299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911293612191963296512199 14866940418287944944768299)
  ·
    refine ⟨22300410627431917417152449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14866940418287944944768299 22300410627431917417152449)
    ·
      refine ⟨16725307970573938062864337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22300410627431917417152449 16725307970573938062864337)
      ·
        refine ⟨12543980977930453547148253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16725307970573938062864337 12543980977930453547148253)
        ·
          refine ⟨4703992866723920080180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12543980977930453547148253 4703992866723920080180595)
          ·
            refine ⟨7055989300085880120270893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703992866723920080180595 7055989300085880120270893)
            ·
              refine ⟨2645995987532205045101585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7055989300085880120270893 2645995987532205045101585)
              ·
                refine ⟨1984496990649153783826189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645995987532205045101585 1984496990649153783826189)
                ·
                  refine ⟨744186371493432668934821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1984496990649153783826189 744186371493432668934821)
                  ·
                    refine ⟨139534944655018625425279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744186371493432668934821 139534944655018625425279)
                    ·
                      rfl

theorem cell22_407615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_407615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407615 prefixEnd_407615 := by exact prefixLift 407615
  have htrace : WordTrace (prefixWord ++ tailWord_407615) baseStart_407615 baseEnd_407615 := by
    simpa [prefixWord, tailWord_407615, baseEnd_407615] using wordTrace_append hprefix tailTrace_407615
  have hstable : (prefixWord ++ tailWord_407615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407615).length < 2 ^ (prefixWord ++ tailWord_407615).sum := by decide
  have hdescent : baseEnd_407615 < baseStart_407615 := by decide
  rcases family_descends (prefixWord ++ tailWord_407615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407617 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_407617 : Nat := 118140960795 + 407617 * 2 ^ 59
def prefixEnd_407617 : Nat := 4983230072969 + 3 ^ 40 * 407617 * 2
def baseEnd_407617 : Nat := 139535629295891286875273

theorem tailTrace_407617 : CollatzResearch.WordTrace tailWord_407617 prefixEnd_407617 139535629295891286875273 := by
  unfold tailWord_407617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867013364280699286341105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911342242853799524227403 14867013364280699286341105)
  ·
    refine ⟨11150260023210524464755829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14867013364280699286341105 11150260023210524464755829)
    ·
      refine ⟨1045336877175986668570859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11150260023210524464755829 1045336877175986668570859)
      ·
        refine ⟨1568005315763980002856289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045336877175986668570859 1568005315763980002856289)
        ·
          refine ⟨1176003986822985002142217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1568005315763980002856289 1176003986822985002142217)
          ·
            refine ⟨882002990117238751606663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176003986822985002142217 882002990117238751606663)
            ·
              refine ⟨1323004485175858127409995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882002990117238751606663 1323004485175858127409995)
              ·
                refine ⟨1984506727763787191114993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323004485175858127409995 1984506727763787191114993)
                ·
                  refine ⟨1488380045822840393336245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984506727763787191114993 1488380045822840393336245)
                  ·
                    refine ⟨139535629295891286875273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1488380045822840393336245 139535629295891286875273)
                    ·
                      rfl

theorem cell22_407617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_407617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407617 prefixEnd_407617 := by exact prefixLift 407617
  have htrace : WordTrace (prefixWord ++ tailWord_407617) baseStart_407617 baseEnd_407617 := by
    simpa [prefixWord, tailWord_407617, baseEnd_407617] using wordTrace_append hprefix tailTrace_407617
  have hstable : (prefixWord ++ tailWord_407617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407617).length < 2 ^ (prefixWord ++ tailWord_407617).sum := by decide
  have hdescent : baseEnd_407617 < baseStart_407617 := by decide
  rcases family_descends (prefixWord ++ tailWord_407617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407630 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_407630 : Nat := 118140960795 + 407630 * 2 ^ 59
def prefixEnd_407630 : Nat := 4983230072969 + 3 ^ 40 * 407630 * 2
def baseEnd_407630 : Nat := 46513359820521195433411

theorem tailTrace_407630 : CollatzResearch.WordTrace tailWord_407630 prefixEnd_407630 46513359820521195433411 := by
  unfold tailWord_407630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858435939154200313320543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9911658342155735004376229 1858435939154200313320543)
  ·
    refine ⟨2787653908731300469980815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858435939154200313320543 2787653908731300469980815)
    ·
      refine ⟨4181480863096950704971223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787653908731300469980815 4181480863096950704971223)
      ·
        refine ⟨6272221294645426057456835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181480863096950704971223 6272221294645426057456835)
        ·
          refine ⟨9408331941968139086185253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272221294645426057456835 9408331941968139086185253)
          ·
            refine ⟨1764062239119026078659735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9408331941968139086185253 1764062239119026078659735)
            ·
              refine ⟨2646093358678539117989603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764062239119026078659735 2646093358678539117989603)
              ·
                refine ⟨3969140038017808676984405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646093358678539117989603 3969140038017808676984405)
                ·
                  refine ⟨46513359820521195433411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3969140038017808676984405 46513359820521195433411)
                  ·
                    rfl

theorem cell22_407630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_407630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407630 prefixEnd_407630 := by exact prefixLift 407630
  have htrace : WordTrace (prefixWord ++ tailWord_407630) baseStart_407630 baseEnd_407630 := by
    simpa [prefixWord, tailWord_407630, baseEnd_407630] using wordTrace_append hprefix tailTrace_407630
  have hstable : (prefixWord ++ tailWord_407630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407630).length < 2 ^ (prefixWord ++ tailWord_407630).sum := by decide
  have hdescent : baseEnd_407630 < baseStart_407630 := by decide
  rcases family_descends (prefixWord ++ tailWord_407630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407726 : List Nat := [4, 1, 4, 2, 1, 1, 2, 7]
def baseStart_407726 : Nat := 118140960795 + 407726 * 2 ^ 59
def prefixEnd_407726 : Nat := 4983230072969 + 3 ^ 40 * 407726 * 2
def baseEnd_407726 : Nat := 15508104691494592877771

theorem tailTrace_407726 : CollatzResearch.WordTrace tailWord_407726 prefixEnd_407726 15508104691494592877771 := by
  unfold tailWord_407726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858873615110726362757379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9913992613923873934706021 1858873615110726362757379)
  ·
    refine ⟨2788310422666089544136069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858873615110726362757379 2788310422666089544136069)
    ·
      refine ⟨522808204249891789525513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2788310422666089544136069 522808204249891789525513)
      ·
        refine ⟨392106153187418842144135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522808204249891789525513 392106153187418842144135)
        ·
          refine ⟨588159229781128263216203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392106153187418842144135 588159229781128263216203)
          ·
            refine ⟨882238844671692394824305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588159229781128263216203 882238844671692394824305)
            ·
              refine ⟨661679133503769296118229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882238844671692394824305 661679133503769296118229)
              ·
                refine ⟨15508104691494592877771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 661679133503769296118229 15508104691494592877771)
                ·
                  rfl

theorem cell22_407726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_407726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407726 prefixEnd_407726 := by exact prefixLift 407726
  have htrace : WordTrace (prefixWord ++ tailWord_407726) baseStart_407726 baseEnd_407726 := by
    simpa [prefixWord, tailWord_407726, baseEnd_407726] using wordTrace_append hprefix tailTrace_407726
  have hstable : (prefixWord ++ tailWord_407726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407726).length < 2 ^ (prefixWord ++ tailWord_407726).sum := by decide
  have hdescent : baseEnd_407726 < baseStart_407726 := by decide
  rcases family_descends (prefixWord ++ tailWord_407726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407737 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 5]
def baseStart_407737 : Nat := 118140960795 + 407737 * 2 ^ 59
def prefixEnd_407737 : Nat := 4983230072969 + 3 ^ 40 * 407737 * 2
def baseEnd_407737 : Nat := 46525569249416991291635

theorem tailTrace_407737 : CollatzResearch.WordTrace tailWord_407737 prefixEnd_407737 46525569249416991291635 := by
  unfold tailWord_407737
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871390123845959780709465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9914260082563973187139643 14871390123845959780709465)
  ·
    refine ⟨11153542592884469835532099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14871390123845959780709465 11153542592884469835532099)
    ·
      refine ⟨16730313889326704753298149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11153542592884469835532099 16730313889326704753298149)
      ·
        refine ⟨3136933854248757141243403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16730313889326704753298149 3136933854248757141243403)
        ·
          refine ⟨4705400781373135711865105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136933854248757141243403 4705400781373135711865105)
          ·
            refine ⟨3529050586029851783898829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705400781373135711865105 3529050586029851783898829)
            ·
              refine ⟨1323393969761194418962061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3529050586029851783898829 1323393969761194418962061)
              ·
                refine ⟨496272738660447907110773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323393969761194418962061 496272738660447907110773)
                ·
                  refine ⟨46525569249416991291635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496272738660447907110773 46525569249416991291635)
                  ·
                    rfl

theorem cell22_407737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_407737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407737 prefixEnd_407737 := by exact prefixLift 407737
  have htrace : WordTrace (prefixWord ++ tailWord_407737) baseStart_407737 baseEnd_407737 := by
    simpa [prefixWord, tailWord_407737, baseEnd_407737] using wordTrace_append hprefix tailTrace_407737
  have hstable : (prefixWord ++ tailWord_407737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407737).length < 2 ^ (prefixWord ++ tailWord_407737).sum := by decide
  have hdescent : baseEnd_407737 < baseStart_407737 := by decide
  rcases family_descends (prefixWord ++ tailWord_407737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407816 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_407816 : Nat := 118140960795 + 407816 * 2 ^ 59
def prefixEnd_407816 : Nat := 4983230072969 + 3 ^ 40 * 407816 * 2
def baseEnd_407816 : Nat := 46534583687573700383221

theorem tailTrace_407816 : CollatzResearch.WordTrace tailWord_407816 prefixEnd_407816 46534583687573700383221 := by
  unfold tailWord_407816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437135745279878136417651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9916180993706504181890201 7437135745279878136417651)
  ·
    refine ⟨11155703617919817204626477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7437135745279878136417651 11155703617919817204626477)
    ·
      refine ⟨4183388856719931451734929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11155703617919817204626477 4183388856719931451734929)
      ·
        refine ⟨3137541642539948588801197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183388856719931451734929 3137541642539948588801197)
        ·
          refine ⟨1176578115952480720800449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3137541642539948588801197 1176578115952480720800449)
          ·
            refine ⟨882433586964360540600337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176578115952480720800449 882433586964360540600337)
            ·
              refine ⟨661825190223270405450253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882433586964360540600337 661825190223270405450253)
              ·
                refine ⟨248184446333726402043845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661825190223270405450253 248184446333726402043845)
                ·
                  refine ⟨46534583687573700383221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248184446333726402043845 46534583687573700383221)
                  ·
                    rfl

theorem cell22_407816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_407816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407816 prefixEnd_407816 := by exact prefixLift 407816
  have htrace : WordTrace (prefixWord ++ tailWord_407816) baseStart_407816 baseEnd_407816 := by
    simpa [prefixWord, tailWord_407816, baseEnd_407816] using wordTrace_append hprefix tailTrace_407816
  have hstable : (prefixWord ++ tailWord_407816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407816).length < 2 ^ (prefixWord ++ tailWord_407816).sum := by decide
  have hdescent : baseEnd_407816 < baseStart_407816 := by decide
  rcases family_descends (prefixWord ++ tailWord_407816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407831 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 2, 3]
def baseStart_407831 : Nat := 118140960795 + 407831 * 2 ^ 59
def prefixEnd_407831 : Nat := 4983230072969 + 3 ^ 40 * 407831 * 2
def baseEnd_407831 : Nat := 139608885869266062024617

theorem tailTrace_407831 : CollatzResearch.WordTrace tailWord_407831 prefixEnd_407831 139608885869266062024617 := by
  unfold tailWord_407831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14874818585505413834631347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9916545723670275889754231 14874818585505413834631347)
  ·
    refine ⟨22312227878258120751947021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14874818585505413834631347 22312227878258120751947021)
    ·
      refine ⟨8367085454346795281980133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22312227878258120751947021 8367085454346795281980133)
      ·
        refine ⟨1568828522690024115371275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8367085454346795281980133 1568828522690024115371275)
        ·
          refine ⟨2353242784035036173056913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568828522690024115371275 2353242784035036173056913)
          ·
            refine ⟨1764932088026277129792685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353242784035036173056913 1764932088026277129792685)
            ·
              refine ⟨661849533009853923672257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1764932088026277129792685 661849533009853923672257)
              ·
                refine ⟨496387149757390442754193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661849533009853923672257 496387149757390442754193)
                ·
                  refine ⟨372290362318042832065645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496387149757390442754193 372290362318042832065645)
                  ·
                    refine ⟨139608885869266062024617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372290362318042832065645 139608885869266062024617)
                    ·
                      rfl

theorem cell22_407831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_407831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407831 prefixEnd_407831 := by exact prefixLift 407831
  have htrace : WordTrace (prefixWord ++ tailWord_407831) baseStart_407831 baseEnd_407831 := by
    simpa [prefixWord, tailWord_407831, baseEnd_407831] using wordTrace_append hprefix tailTrace_407831
  have hstable : (prefixWord ++ tailWord_407831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407831).length < 2 ^ (prefixWord ++ tailWord_407831).sum := by decide
  have hdescent : baseEnd_407831 < baseStart_407831 := by decide
  rcases family_descends (prefixWord ++ tailWord_407831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407848 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_407848 : Nat := 118140960795 + 407848 * 2 ^ 59
def prefixEnd_407848 : Nat := 4983230072969 + 3 ^ 40 * 407848 * 2
def baseEnd_407848 : Nat := 139614705316683684349565

theorem tailTrace_407848 : CollatzResearch.WordTrace tailWord_407848 prefixEnd_407848 139614705316683684349565 := by
  unfold tailWord_407848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437719313221912869000099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9916959084295883825333465 7437719313221912869000099)
  ·
    refine ⟨11156578969832869303500149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7437719313221912869000099 11156578969832869303500149)
    ·
      refine ⟨1045929278421831497203139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11156578969832869303500149 1045929278421831497203139)
      ·
        refine ⟨1568893917632747245804709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045929278421831497203139 1568893917632747245804709)
        ·
          refine ⟨294167609556140108588383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1568893917632747245804709 294167609556140108588383)
          ·
            refine ⟨441251414334210162882575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294167609556140108588383 441251414334210162882575)
            ·
              refine ⟨661877121501315244323863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441251414334210162882575 661877121501315244323863)
              ·
                refine ⟨992815682251972866485795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661877121501315244323863 992815682251972866485795)
                ·
                  refine ⟨1489223523377959299728693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992815682251972866485795 1489223523377959299728693)
                  ·
                    refine ⟨139614705316683684349565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1489223523377959299728693 139614705316683684349565)
                    ·
                      rfl

theorem cell22_407848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_407848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407848 prefixEnd_407848 := by exact prefixLift 407848
  have htrace : WordTrace (prefixWord ++ tailWord_407848) baseStart_407848 baseEnd_407848 := by
    simpa [prefixWord, tailWord_407848, baseEnd_407848] using wordTrace_append hprefix tailTrace_407848
  have hstable : (prefixWord ++ tailWord_407848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407848).length < 2 ^ (prefixWord ++ tailWord_407848).sum := by decide
  have hdescent : baseEnd_407848 < baseStart_407848 := by decide
  rcases family_descends (prefixWord ++ tailWord_407848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407859 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 3, 3]
def baseStart_407859 : Nat := 118140960795 + 407859 * 2 ^ 59
def prefixEnd_407859 : Nat := 4983230072969 + 3 ^ 40 * 407859 * 2
def baseEnd_407859 : Nat := 139618470841483322324531

theorem tailTrace_407859 : CollatzResearch.WordTrace tailWord_407859 prefixEnd_407859 139618470841483322324531 := by
  unfold tailWord_407859
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875839829403974616650631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9917226552935983077767087 14875839829403974616650631)
  ·
    refine ⟨22313759744105961924975947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875839829403974616650631 22313759744105961924975947)
    ·
      refine ⟨33470639616158942887463921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22313759744105961924975947 33470639616158942887463921)
      ·
        refine ⟨25102979712119207165597941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33470639616158942887463921 25102979712119207165597941)
        ·
          refine ⟨2353404348011175671774807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25102979712119207165597941 2353404348011175671774807)
          ·
            refine ⟨3530106522016763507662211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353404348011175671774807 3530106522016763507662211)
            ·
              refine ⟨5295159783025145261493317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530106522016763507662211 5295159783025145261493317)
              ·
                refine ⟨992842459317214736529997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5295159783025145261493317 992842459317214736529997)
                ·
                  refine ⟨372315922243955526198749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992842459317214736529997 372315922243955526198749)
                  ·
                    refine ⟨139618470841483322324531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372315922243955526198749 139618470841483322324531)
                    ·
                      rfl

theorem cell22_407859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 3].length) (baseStart_407859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407859 prefixEnd_407859 := by exact prefixLift 407859
  have htrace : WordTrace (prefixWord ++ tailWord_407859) baseStart_407859 baseEnd_407859 := by
    simpa [prefixWord, tailWord_407859, baseEnd_407859] using wordTrace_append hprefix tailTrace_407859
  have hstable : (prefixWord ++ tailWord_407859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407859).length < 2 ^ (prefixWord ++ tailWord_407859).sum := by decide
  have hdescent : baseEnd_407859 < baseStart_407859 := by decide
  rcases family_descends (prefixWord ++ tailWord_407859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_407887 : Nat := 118140960795 + 407887 * 2 ^ 59
def prefixEnd_407887 : Nat := 4983230072969 + 3 ^ 40 * 407887 * 2
def baseEnd_407887 : Nat := 139628055813700582624445

theorem tailTrace_407887 : CollatzResearch.WordTrace tailWord_407887 prefixEnd_407887 139628055813700582624445 := by
  unfold tailWord_407887
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876861073302535398669915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9917907382201690265779943 14876861073302535398669915)
  ·
    refine ⟨22315291609953803098004873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876861073302535398669915 22315291609953803098004873)
    ·
      refine ⟨16736468707465352323503655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22315291609953803098004873 16736468707465352323503655)
      ·
        refine ⟨25104703061198028485255483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736468707465352323503655 25104703061198028485255483)
        ·
          refine ⟨37657054591797042727883225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25104703061198028485255483 37657054591797042727883225)
          ·
            refine ⟨28242790943847782045912419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37657054591797042727883225 28242790943847782045912419)
            ·
              refine ⟨42364186415771673068868629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28242790943847782045912419 42364186415771673068868629)
              ·
                refine ⟨1985821238239297175103217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42364186415771673068868629 1985821238239297175103217)
                ·
                  refine ⟨1489365928679472881327413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985821238239297175103217 1489365928679472881327413)
                  ·
                    refine ⟨139628055813700582624445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1489365928679472881327413 139628055813700582624445)
                    ·
                      rfl

theorem cell22_407887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_407887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407887 prefixEnd_407887 := by exact prefixLift 407887
  have htrace : WordTrace (prefixWord ++ tailWord_407887) baseStart_407887 baseEnd_407887 := by
    simpa [prefixWord, tailWord_407887, baseEnd_407887] using wordTrace_append hprefix tailTrace_407887
  have hstable : (prefixWord ++ tailWord_407887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407887).length < 2 ^ (prefixWord ++ tailWord_407887).sum := by decide
  have hdescent : baseEnd_407887 < baseStart_407887 := by decide
  rcases family_descends (prefixWord ++ tailWord_407887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407893 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_407893 : Nat := 118140960795 + 407893 * 2 ^ 59
def prefixEnd_407893 : Nat := 4983230072969 + 3 ^ 40 * 407893 * 2
def baseEnd_407893 : Nat := 139630109736318566974427

theorem tailTrace_407893 : CollatzResearch.WordTrace tailWord_407893 prefixEnd_407893 139630109736318566974427 := by
  unfold tailWord_407893
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877079911280798423388333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9918053274187198948925555 14877079911280798423388333)
  ·
    refine ⟨5578904966730299408770625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14877079911280798423388333 5578904966730299408770625)
    ·
      refine ⟨4184178725047724556577969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5578904966730299408770625 4184178725047724556577969)
      ·
        refine ⟨3138134043785793417433477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4184178725047724556577969 3138134043785793417433477)
        ·
          refine ⟨588400133209836265768777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3138134043785793417433477 588400133209836265768777)
          ·
            refine ⟨441300099907377199326583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588400133209836265768777 441300099907377199326583)
            ·
              refine ⟨661950149861065798989875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441300099907377199326583 661950149861065798989875)
              ·
                refine ⟨992925224791598698484813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661950149861065798989875 992925224791598698484813)
                ·
                  refine ⟨372346959296849511931805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992925224791598698484813 372346959296849511931805)
                  ·
                    refine ⟨139630109736318566974427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372346959296849511931805 139630109736318566974427)
                    ·
                      rfl

theorem cell22_407893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_407893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407893 prefixEnd_407893 := by exact prefixLift 407893
  have htrace : WordTrace (prefixWord ++ tailWord_407893) baseStart_407893 baseEnd_407893 := by
    simpa [prefixWord, tailWord_407893, baseEnd_407893] using wordTrace_append hprefix tailTrace_407893
  have hstable : (prefixWord ++ tailWord_407893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407893).length < 2 ^ (prefixWord ++ tailWord_407893).sum := by decide
  have hdescent : baseEnd_407893 < baseStart_407893 := by decide
  rcases family_descends (prefixWord ++ tailWord_407893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407906 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_407906 : Nat := 118140960795 + 407906 * 2 ^ 59
def prefixEnd_407906 : Nat := 4983230072969 + 3 ^ 40 * 407906 * 2
def baseEnd_407906 : Nat := 46544853300663622133129

theorem tailTrace_407906 : CollatzResearch.WordTrace tailWord_407906 prefixEnd_407906 46544853300663622133129 := by
  unfold tailWord_407906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719388515058425410902893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9918369373489134429074381 3719388515058425410902893)
  ·
    refine ⟨1394770693146909529088585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3719388515058425410902893 1394770693146909529088585)
    ·
      refine ⟨1046078019860182146816439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394770693146909529088585 1046078019860182146816439)
      ·
        refine ⟨1569117029790273220224659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046078019860182146816439 1569117029790273220224659)
        ·
          refine ⟨2353675544685409830336989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569117029790273220224659 2353675544685409830336989)
          ·
            refine ⟨882628329257028686376371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2353675544685409830336989 882628329257028686376371)
            ·
              refine ⟨1323942493885543029564557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882628329257028686376371 1323942493885543029564557)
              ·
                refine ⟨496478435207078636086709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323942493885543029564557 496478435207078636086709)
                ·
                  refine ⟨46544853300663622133129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496478435207078636086709 46544853300663622133129)
                  ·
                    rfl

theorem cell22_407906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_407906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407906 prefixEnd_407906 := by exact prefixLift 407906
  have htrace : WordTrace (prefixWord ++ tailWord_407906) baseStart_407906 baseEnd_407906 := by
    simpa [prefixWord, tailWord_407906, baseEnd_407906] using wordTrace_append hprefix tailTrace_407906
  have hstable : (prefixWord ++ tailWord_407906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407906).length < 2 ^ (prefixWord ++ tailWord_407906).sum := by decide
  have hdescent : baseEnd_407906 < baseStart_407906 := by decide
  rcases family_descends (prefixWord ++ tailWord_407906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407919 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 1, 4]
def baseStart_407919 : Nat := 118140960795 + 407919 * 2 ^ 59
def prefixEnd_407919 : Nat := 4983230072969 + 3 ^ 40 * 407919 * 2
def baseEnd_407919 : Nat := 139639010067663165824347

theorem tailTrace_407919 : CollatzResearch.WordTrace tailWord_407919 prefixEnd_407919 139639010067663165824347 := by
  unfold tailWord_407919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878028209186604863834811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9918685472791069909223207 14878028209186604863834811)
  ·
    refine ⟨22317042313779907295752217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14878028209186604863834811 22317042313779907295752217)
    ·
      refine ⟨16737781735334930471814163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22317042313779907295752217 16737781735334930471814163)
      ·
        refine ⟨25106672603002395707721245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16737781735334930471814163 25106672603002395707721245)
        ·
          refine ⟨9415002226125898390395467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25106672603002395707721245 9415002226125898390395467)
          ·
            refine ⟨14122503339188847585593201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415002226125898390395467 14122503339188847585593201)
            ·
              refine ⟨10591877504391635689194901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14122503339188847585593201 10591877504391635689194901)
              ·
                refine ⟨496494258018357922931011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10591877504391635689194901 496494258018357922931011)
                ·
                  refine ⟨744741387027536884396517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496494258018357922931011 744741387027536884396517)
                  ·
                    refine ⟨139639010067663165824347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744741387027536884396517 139639010067663165824347)
                    ·
                      rfl

theorem cell22_407919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_407919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_407919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_407919 prefixEnd_407919 := by exact prefixLift 407919
  have htrace : WordTrace (prefixWord ++ tailWord_407919) baseStart_407919 baseEnd_407919 := by
    simpa [prefixWord, tailWord_407919, baseEnd_407919] using wordTrace_append hprefix tailTrace_407919
  have hstable : (prefixWord ++ tailWord_407919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407919).length < 2 ^ (prefixWord ++ tailWord_407919).sum := by decide
  have hdescent : baseEnd_407919 < baseStart_407919 := by decide
  rcases family_descends (prefixWord ++ tailWord_407919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408088 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_408088 : Nat := 118140960795 + 408088 * 2 ^ 59
def prefixEnd_408088 : Nat := 4983230072969 + 3 ^ 40 * 408088 * 2
def baseEnd_408088 : Nat := 139696862221403058348829

theorem tailTrace_408088 : CollatzResearch.WordTrace tailWord_408088 prefixEnd_408088 139696862221403058348829 := by
  unfold tailWord_408088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442096072787173363368459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9922794763716231151157945 7442096072787173363368459)
  ·
    refine ⟨11163144109180760045052689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7442096072787173363368459 11163144109180760045052689)
    ·
      refine ⟨8372358081885570033789517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11163144109180760045052689 8372358081885570033789517)
      ·
        refine ⟨3139634280707088762671069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8372358081885570033789517 3139634280707088762671069)
        ·
          refine ⟨1177362855265158286001651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3139634280707088762671069 1177362855265158286001651)
          ·
            refine ⟨1766044282897737429002477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177362855265158286001651 1766044282897737429002477)
            ·
              refine ⟨662266606086651535875929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766044282897737429002477 662266606086651535875929)
              ·
                refine ⟨496699954564988651906947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662266606086651535875929 496699954564988651906947)
                ·
                  refine ⟨745049931847482977860421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496699954564988651906947 745049931847482977860421)
                  ·
                    refine ⟨139696862221403058348829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745049931847482977860421 139696862221403058348829)
                    ·
                      rfl

theorem cell22_408088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_408088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408088 prefixEnd_408088 := by exact prefixLift 408088
  have htrace : WordTrace (prefixWord ++ tailWord_408088) baseStart_408088 baseEnd_408088 := by
    simpa [prefixWord, tailWord_408088, baseEnd_408088] using wordTrace_append hprefix tailTrace_408088
  have hstable : (prefixWord ++ tailWord_408088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408088).length < 2 ^ (prefixWord ++ tailWord_408088).sum := by decide
  have hdescent : baseEnd_408088 < baseStart_408088 := by decide
  rcases family_descends (prefixWord ++ tailWord_408088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408101 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_408101 : Nat := 118140960795 + 408101 * 2 ^ 59
def prefixEnd_408101 : Nat := 4983230072969 + 3 ^ 40 * 408101 * 2
def baseEnd_408101 : Nat := 139701312387075357773789

theorem tailTrace_408101 : CollatzResearch.WordTrace tailWord_408101 prefixEnd_408101 139701312387075357773789 := by
  unfold tailWord_408101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884666294527249946960157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9923110863018166631306771 14884666294527249946960157)
  ·
    refine ⟨5581749860447718730110059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14884666294527249946960157 5581749860447718730110059)
    ·
      refine ⟨8372624790671578095165089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581749860447718730110059 8372624790671578095165089)
      ·
        refine ⟨6279468593003683571373817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372624790671578095165089 6279468593003683571373817)
        ·
          refine ⟨4709601444752762678530363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279468593003683571373817 4709601444752762678530363)
          ·
            refine ⟨7064402167129144017795545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709601444752762678530363 7064402167129144017795545)
            ·
              refine ⟨5298301625346858013346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7064402167129144017795545 5298301625346858013346659)
              ·
                refine ⟨7947452438020287020019989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298301625346858013346659 7947452438020287020019989)
                ·
                  refine ⟨372536833032200954063437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7947452438020287020019989 372536833032200954063437)
                  ·
                    refine ⟨139701312387075357773789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372536833032200954063437 139701312387075357773789)
                    ·
                      rfl

theorem cell22_408101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_408101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408101 prefixEnd_408101 := by exact prefixLift 408101
  have htrace : WordTrace (prefixWord ++ tailWord_408101) baseStart_408101 baseEnd_408101 := by
    simpa [prefixWord, tailWord_408101, baseEnd_408101] using wordTrace_append hprefix tailTrace_408101
  have hstable : (prefixWord ++ tailWord_408101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408101).length < 2 ^ (prefixWord ++ tailWord_408101).sum := by decide
  have hdescent : baseEnd_408101 < baseStart_408101 := by decide
  rcases family_descends (prefixWord ++ tailWord_408101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408148 : List Nat := [2, 4, 1, 1, 1, 4, 3, 6]
def baseStart_408148 : Nat := 118140960795 + 408148 * 2 ^ 59
def prefixEnd_408148 : Nat := 4983230072969 + 3 ^ 40 * 408148 * 2
def baseEnd_408148 : Nat := 15524155716398100205405

theorem tailTrace_408148 : CollatzResearch.WordTrace tailWord_408148 prefixEnd_408148 15524155716398100205405 := by
  unfold tailWord_408148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443190262678488486960549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9924253683571317982614065 7443190262678488486960549)
  ·
    refine ⟨1395598174252216591305103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7443190262678488486960549 1395598174252216591305103)
    ·
      refine ⟨2093397261378324886957655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395598174252216591305103 2093397261378324886957655)
      ·
        refine ⟨3140095892067487330436483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093397261378324886957655 3140095892067487330436483)
        ·
          refine ⟨4710143838101230995654725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140095892067487330436483 4710143838101230995654725)
          ·
            refine ⟨883151969643980811685261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4710143838101230995654725 883151969643980811685261)
            ·
              refine ⟨331181988616492804381973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883151969643980811685261 331181988616492804381973)
              ·
                refine ⟨15524155716398100205405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331181988616492804381973 15524155716398100205405)
                ·
                  rfl

theorem cell22_408148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_408148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408148 prefixEnd_408148 := by exact prefixLift 408148
  have htrace : WordTrace (prefixWord ++ tailWord_408148) baseStart_408148 baseEnd_408148 := by
    simpa [prefixWord, tailWord_408148, baseEnd_408148] using wordTrace_append hprefix tailTrace_408148
  have hstable : (prefixWord ++ tailWord_408148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408148).length < 2 ^ (prefixWord ++ tailWord_408148).sum := by decide
  have hdescent : baseEnd_408148 < baseStart_408148 := by decide
  rcases family_descends (prefixWord ++ tailWord_408148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408221 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 8]
def baseStart_408221 : Nat := 118140960795 + 408221 * 2 ^ 59
def prefixEnd_408221 : Nat := 4983230072969 + 3 ^ 40 * 408221 * 2
def baseEnd_408221 : Nat := 46580796946478348257807

theorem tailTrace_408221 : CollatzResearch.WordTrace tailWord_408221 prefixEnd_408221 46580796946478348257807 := by
  unfold tailWord_408221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889043054092510441328517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926028702728340294219011 14889043054092510441328517)
  ·
    refine ⟨2791695572642345707749097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14889043054092510441328517 2791695572642345707749097)
    ·
      refine ⟨2093771679481759280811823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791695572642345707749097 2093771679481759280811823)
      ·
        refine ⟨3140657519222638921217735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093771679481759280811823 3140657519222638921217735)
        ·
          refine ⟨4710986278833958381826603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140657519222638921217735 4710986278833958381826603)
          ·
            refine ⟨7066479418250937572739905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710986278833958381826603 7066479418250937572739905)
            ·
              refine ⟨5299859563688203179554929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066479418250937572739905 5299859563688203179554929)
              ·
                refine ⟨3974894672766152384666197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299859563688203179554929 3974894672766152384666197)
                ·
                  refine ⟨46580796946478348257807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3974894672766152384666197 46580796946478348257807)
                  ·
                    rfl

theorem cell22_408221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_408221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408221 prefixEnd_408221 := by exact prefixLift 408221
  have htrace : WordTrace (prefixWord ++ tailWord_408221) baseStart_408221 baseEnd_408221 := by
    simpa [prefixWord, tailWord_408221, baseEnd_408221] using wordTrace_append hprefix tailTrace_408221
  have hstable : (prefixWord ++ tailWord_408221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408221).length < 2 ^ (prefixWord ++ tailWord_408221).sum := by decide
  have hdescent : baseEnd_408221 < baseStart_408221 := by decide
  rcases family_descends (prefixWord ++ tailWord_408221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408231 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 1, 3]
def baseStart_408231 : Nat := 118140960795 + 408231 * 2 ^ 59
def prefixEnd_408231 : Nat := 4983230072969 + 3 ^ 40 * 408231 * 2
def baseEnd_408231 : Nat := 139745814043798352023391

theorem tailTrace_408231 : CollatzResearch.WordTrace tailWord_408231 prefixEnd_408231 139745814043798352023391 := by
  unfold tailWord_408231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889407784056282149192547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926271856037521432795031 14889407784056282149192547)
  ·
    refine ⟨22334111676084423223788821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889407784056282149192547 22334111676084423223788821)
    ·
      refine ⟨1046911484816457338615101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22334111676084423223788821 1046911484816457338615101)
      ·
        refine ⟨392591806806171501980663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046911484816457338615101 392591806806171501980663)
        ·
          refine ⟨588887710209257252970995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392591806806171501980663 588887710209257252970995)
          ·
            refine ⟨883331565313885879456493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588887710209257252970995 883331565313885879456493)
            ·
              refine ⟨331249336992707204796185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883331565313885879456493 331249336992707204796185)
              ·
                refine ⟨248437002744530403597139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331249336992707204796185 248437002744530403597139)
                ·
                  refine ⟨372655504116795605395709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248437002744530403597139 372655504116795605395709)
                  ·
                    refine ⟨139745814043798352023391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372655504116795605395709 139745814043798352023391)
                    ·
                      rfl

theorem cell22_408231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_408231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408231 prefixEnd_408231 := by exact prefixLift 408231
  have htrace : WordTrace (prefixWord ++ tailWord_408231) baseStart_408231 baseEnd_408231 := by
    simpa [prefixWord, tailWord_408231, baseEnd_408231] using wordTrace_append hprefix tailTrace_408231
  have hstable : (prefixWord ++ tailWord_408231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408231).length < 2 ^ (prefixWord ++ tailWord_408231).sum := by decide
  have hdescent : baseEnd_408231 < baseStart_408231 := by decide
  rcases family_descends (prefixWord ++ tailWord_408231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408257 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_408257 : Nat := 118140960795 + 408257 * 2 ^ 59
def prefixEnd_408257 : Nat := 4983230072969 + 3 ^ 40 * 408257 * 2
def baseEnd_408257 : Nat := 139754714375142950873311

theorem tailTrace_408257 : CollatzResearch.WordTrace tailWord_408257 prefixEnd_408257 139754714375142950873311 := by
  unfold tailWord_408257
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890356081962088589639025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926904054641392393092683 14890356081962088589639025)
  ·
    refine ⟨11167767061471566442229269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14890356081962088589639025 11167767061471566442229269)
    ·
      refine ⟨523489081006479676979497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11167767061471566442229269 523489081006479676979497)
      ·
        refine ⟨392616810754859757734623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523489081006479676979497 392616810754859757734623)
        ·
          refine ⟨588925216132289636601935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392616810754859757734623 588925216132289636601935)
          ·
            refine ⟨883387824198434454902903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588925216132289636601935 883387824198434454902903)
            ·
              refine ⟨1325081736297651682354355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883387824198434454902903 1325081736297651682354355)
              ·
                refine ⟨1987622604446477523531533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325081736297651682354355 1987622604446477523531533)
                ·
                  refine ⟨745358476667429071324325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1987622604446477523531533 745358476667429071324325)
                  ·
                    refine ⟨139754714375142950873311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745358476667429071324325 139754714375142950873311)
                    ·
                      rfl

theorem cell22_408257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_408257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408257 prefixEnd_408257 := by exact prefixLift 408257
  have htrace : WordTrace (prefixWord ++ tailWord_408257) baseStart_408257 baseEnd_408257 := by
    simpa [prefixWord, tailWord_408257, baseEnd_408257] using wordTrace_append hprefix tailTrace_408257
  have hstable : (prefixWord ++ tailWord_408257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408257).length < 2 ^ (prefixWord ++ tailWord_408257).sum := by decide
  have hdescent : baseEnd_408257 < baseStart_408257 := by decide
  rcases family_descends (prefixWord ++ tailWord_408257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408311 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 9]
def baseStart_408311 : Nat := 118140960795 + 408311 * 2 ^ 59
def prefixEnd_408311 : Nat := 4983230072969 + 3 ^ 40 * 408311 * 2
def baseEnd_408311 : Nat := 46591066559568270007715

theorem tailTrace_408311 : CollatzResearch.WordTrace tailWord_408311 prefixEnd_408311 46591066559568270007715 := by
  unfold tailWord_408311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892325623766455812104787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9928217082510970541403191 14892325623766455812104787)
  ·
    refine ⟨22338488435649683718157181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14892325623766455812104787 22338488435649683718157181)
    ·
      refine ⟨8376933163368631394308943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22338488435649683718157181 8376933163368631394308943)
      ·
        refine ⟨12565399745052947091463415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8376933163368631394308943 12565399745052947091463415)
        ·
          refine ⟨18848099617579420637195123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12565399745052947091463415 18848099617579420637195123)
          ·
            refine ⟨28272149426369130955792685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18848099617579420637195123 28272149426369130955792685)
            ·
              refine ⟨10602056034888424108422257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28272149426369130955792685 10602056034888424108422257)
              ·
                refine ⟨7951542026166318081316693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10602056034888424108422257 7951542026166318081316693)
                ·
                  refine ⟨46591066559568270007715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7951542026166318081316693 46591066559568270007715)
                  ·
                    rfl

theorem cell22_408311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_408311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408311 prefixEnd_408311 := by exact prefixLift 408311
  have htrace : WordTrace (prefixWord ++ tailWord_408311) baseStart_408311 baseEnd_408311 := by
    simpa [prefixWord, tailWord_408311, baseEnd_408311] using wordTrace_append hprefix tailTrace_408311
  have hstable : (prefixWord ++ tailWord_408311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408311).length < 2 ^ (prefixWord ++ tailWord_408311).sum := by decide
  have hdescent : baseEnd_408311 < baseStart_408311 := by decide
  rcases family_descends (prefixWord ++ tailWord_408311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408349 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_408349 : Nat := 118140960795 + 408349 * 2 ^ 59
def prefixEnd_408349 : Nat := 4983230072969 + 3 ^ 40 * 408349 * 2
def baseEnd_408349 : Nat := 139786207855285377573029

theorem tailTrace_408349 : CollatzResearch.WordTrace tailWord_408349 prefixEnd_408349 139786207855285377573029 := by
  unfold tailWord_408349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893711597628788301988101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9929141065085858867992067 14893711597628788301988101)
  ·
    refine ⟨2792570924555397806622769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14893711597628788301988101 2792570924555397806622769)
    ·
      refine ⟨2094428193416548354967077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2792570924555397806622769 2094428193416548354967077)
      ·
        refine ⟨392705286265602816556327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2094428193416548354967077 392705286265602816556327)
        ·
          refine ⟨589057929398404224834491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392705286265602816556327 589057929398404224834491)
          ·
            refine ⟨883586894097606337251737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589057929398404224834491 883586894097606337251737)
            ·
              refine ⟨662690170573204752938803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883586894097606337251737 662690170573204752938803)
              ·
                refine ⟨994035255859807129408205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662690170573204752938803 994035255859807129408205)
                ·
                  refine ⟨372763220947427673528077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994035255859807129408205 372763220947427673528077)
                  ·
                    refine ⟨139786207855285377573029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372763220947427673528077 139786207855285377573029)
                    ·
                      rfl

theorem cell22_408349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_408349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408349 prefixEnd_408349 := by exact prefixLift 408349
  have htrace : WordTrace (prefixWord ++ tailWord_408349) baseStart_408349 baseEnd_408349 := by
    simpa [prefixWord, tailWord_408349, baseEnd_408349] using wordTrace_append hprefix tailTrace_408349
  have hstable : (prefixWord ++ tailWord_408349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408349).length < 2 ^ (prefixWord ++ tailWord_408349).sum := by decide
  have hdescent : baseEnd_408349 < baseStart_408349 := by decide
  rcases family_descends (prefixWord ++ tailWord_408349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408375 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 1, 4]
def baseStart_408375 : Nat := 118140960795 + 408375 * 2 ^ 59
def prefixEnd_408375 : Nat := 4983230072969 + 3 ^ 40 * 408375 * 2
def baseEnd_408375 : Nat := 139795108186629976422949

theorem tailTrace_408375 : CollatzResearch.WordTrace tailWord_408375 prefixEnd_408375 139795108186629976422949 := by
  unfold tailWord_408375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14894659895534594742434579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9929773263689729828289719 14894659895534594742434579)
  ·
    refine ⟨22341989843301892113651869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14894659895534594742434579 22341989843301892113651869)
    ·
      refine ⟨8378246191238209542619451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22341989843301892113651869 8378246191238209542619451)
      ·
        refine ⟨12567369286857314313929177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378246191238209542619451 12567369286857314313929177)
        ·
          refine ⟨9425526965142985735446883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567369286857314313929177 9425526965142985735446883)
          ·
            refine ⟨14138290447714478603170325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425526965142985735446883 14138290447714478603170325)
            ·
              refine ⟨662732364736616184523609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14138290447714478603170325 662732364736616184523609)
              ·
                refine ⟨497049273552462138392707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662732364736616184523609 497049273552462138392707)
                ·
                  refine ⟨745573910328693207589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497049273552462138392707 745573910328693207589061)
                  ·
                    refine ⟨139795108186629976422949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745573910328693207589061 139795108186629976422949)
                    ·
                      rfl

theorem cell22_408375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_408375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408375 prefixEnd_408375 := by exact prefixLift 408375
  have htrace : WordTrace (prefixWord ++ tailWord_408375) baseStart_408375 baseEnd_408375 := by
    simpa [prefixWord, tailWord_408375, baseEnd_408375] using wordTrace_append hprefix tailTrace_408375
  have hstable : (prefixWord ++ tailWord_408375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408375).length < 2 ^ (prefixWord ++ tailWord_408375).sum := by decide
  have hdescent : baseEnd_408375 < baseStart_408375 := by decide
  rcases family_descends (prefixWord ++ tailWord_408375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408405 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_408405 : Nat := 118140960795 + 408405 * 2 ^ 59
def prefixEnd_408405 : Nat := 4983230072969 + 3 ^ 40 * 408405 * 2
def baseEnd_408405 : Nat := 139805377799719898172857

theorem tailTrace_408405 : CollatzResearch.WordTrace tailWord_408405 prefixEnd_408405 139805377799719898172857 := by
  unfold tailWord_408405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14895754085425909866026669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9930502723617273244017779 14895754085425909866026669)
  ·
    refine ⟨5585907782034716199760001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14895754085425909866026669 5585907782034716199760001)
    ·
      refine ⟨4189430836526037149820001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5585907782034716199760001 4189430836526037149820001)
      ·
        refine ⟨3142073127394527862365001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4189430836526037149820001 3142073127394527862365001)
        ·
          refine ⟨2356554845545895896773751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142073127394527862365001 2356554845545895896773751)
          ·
            refine ⟨3534832268318843845160627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356554845545895896773751 3534832268318843845160627)
            ·
              refine ⟨5302248402478265767740941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534832268318843845160627 5302248402478265767740941)
              ·
                refine ⟨1988343150929349662902853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5302248402478265767740941 1988343150929349662902853)
                ·
                  refine ⟨372814340799253061794285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988343150929349662902853 372814340799253061794285)
                  ·
                    refine ⟨139805377799719898172857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372814340799253061794285 139805377799719898172857)
                    ·
                      rfl

theorem cell22_408405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_408405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408405 prefixEnd_408405 := by exact prefixLift 408405
  have htrace : WordTrace (prefixWord ++ tailWord_408405) baseStart_408405 baseEnd_408405 := by
    simpa [prefixWord, tailWord_408405, baseEnd_408405] using wordTrace_append hprefix tailTrace_408405
  have hstable : (prefixWord ++ tailWord_408405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408405).length < 2 ^ (prefixWord ++ tailWord_408405).sum := by decide
  have hdescent : baseEnd_408405 < baseStart_408405 := by decide
  rcases family_descends (prefixWord ++ tailWord_408405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408437 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_408437 : Nat := 118140960795 + 408437 * 2 ^ 59
def prefixEnd_408437 : Nat := 4983230072969 + 3 ^ 40 * 408437 * 2
def baseEnd_408437 : Nat := 139816332053682481372759

theorem tailTrace_408437 : CollatzResearch.WordTrace tailWord_408437 prefixEnd_408437 139816332053682481372759 := by
  unfold tailWord_408437
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896921221309979331191565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9931280814206652887461043 14896921221309979331191565)
  ·
    refine ⟨5586345457991242249196837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14896921221309979331191565 5586345457991242249196837)
    ·
      refine ⟨1047439773373357921724407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5586345457991242249196837 1047439773373357921724407)
      ·
        refine ⟨1571159660060036882586611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047439773373357921724407 1571159660060036882586611)
        ·
          refine ⟨2356739490090055323879917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571159660060036882586611 2356739490090055323879917)
          ·
            refine ⟨883777308783770746454969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2356739490090055323879917 883777308783770746454969)
            ·
              refine ⟨662832981587828059841227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883777308783770746454969 662832981587828059841227)
              ·
                refine ⟨994249472381742089761841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662832981587828059841227 994249472381742089761841)
                ·
                  refine ⟨745687104286306567321381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994249472381742089761841 745687104286306567321381)
                  ·
                    refine ⟨139816332053682481372759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745687104286306567321381 139816332053682481372759)
                    ·
                      rfl

theorem cell22_408437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_408437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408437 prefixEnd_408437 := by exact prefixLift 408437
  have htrace : WordTrace (prefixWord ++ tailWord_408437) baseStart_408437 baseEnd_408437 := by
    simpa [prefixWord, tailWord_408437, baseEnd_408437] using wordTrace_append hprefix tailTrace_408437
  have hstable : (prefixWord ++ tailWord_408437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408437).length < 2 ^ (prefixWord ++ tailWord_408437).sum := by decide
  have hdescent : baseEnd_408437 < baseStart_408437 := by decide
  rcases family_descends (prefixWord ++ tailWord_408437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408480 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_408480 : Nat := 118140960795 + 408480 * 2 ^ 59
def prefixEnd_408480 : Nat := 4983230072969 + 3 ^ 40 * 408480 * 2
def baseEnd_408480 : Nat := 46610350610814900849209

theorem tailTrace_408480 : CollatzResearch.WordTrace tailWord_408480 prefixEnd_408480 46610350610814900849209 := by
  unfold tailWord_408480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7449244780077098837503447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9932326373436131783337929 7449244780077098837503447)
  ·
    refine ⟨11173867170115648256255171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7449244780077098837503447 11173867170115648256255171)
    ·
      refine ⟨16760800755173472384382757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173867170115648256255171 16760800755173472384382757)
      ·
        refine ⟨3142650141595026072071767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16760800755173472384382757 3142650141595026072071767)
        ·
          refine ⟨4713975212392539108107651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142650141595026072071767 4713975212392539108107651)
          ·
            refine ⟨7070962818588808662161477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713975212392539108107651 7070962818588808662161477)
            ·
              refine ⟨1325805528485401624155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7070962818588808662161477 1325805528485401624155277)
              ·
                refine ⟨497177073182025609058229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325805528485401624155277 497177073182025609058229)
                ·
                  refine ⟨46610350610814900849209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497177073182025609058229 46610350610814900849209)
                  ·
                    rfl

theorem cell22_408480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_408480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408480 prefixEnd_408480 := by exact prefixLift 408480
  have htrace : WordTrace (prefixWord ++ tailWord_408480) baseStart_408480 baseEnd_408480 := by
    simpa [prefixWord, tailWord_408480, baseEnd_408480] using wordTrace_append hprefix tailTrace_408480
  have hstable : (prefixWord ++ tailWord_408480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408480).length < 2 ^ (prefixWord ++ tailWord_408480).sum := by decide
  have hdescent : baseEnd_408480 < baseStart_408480 := by decide
  rcases family_descends (prefixWord ++ tailWord_408480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408559 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 4]
def baseStart_408559 : Nat := 118140960795 + 408559 * 2 ^ 59
def prefixEnd_408559 : Nat := 4983230072969 + 3 ^ 40 * 408559 * 2
def baseEnd_408559 : Nat := 46619365048971609940795

theorem tailTrace_408559 : CollatzResearch.WordTrace tailWord_408559 prefixEnd_408559 46619365048971609940795 := by
  unfold tailWord_408559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901370926867994167132731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9934247284578662778088487 14901370926867994167132731)
  ·
    refine ⟨22352056390301991250699097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14901370926867994167132731 22352056390301991250699097)
    ·
      refine ⟨16764042292726493438024323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22352056390301991250699097 16764042292726493438024323)
      ·
        refine ⟨25146063439089740157036485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16764042292726493438024323 25146063439089740157036485)
        ·
          refine ⟨4714886894829326279444341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25146063439089740157036485 4714886894829326279444341)
          ·
            refine ⟨442020646390249338697907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4714886894829326279444341 442020646390249338697907)
            ·
              refine ⟨663030969585374008046861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442020646390249338697907 663030969585374008046861)
              ·
                refine ⟨248636613594515253017573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663030969585374008046861 248636613594515253017573)
                ·
                  refine ⟨46619365048971609940795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248636613594515253017573 46619365048971609940795)
                  ·
                    rfl

theorem cell22_408559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 4].length) (baseStart_408559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408559 prefixEnd_408559 := by exact prefixLift 408559
  have htrace : WordTrace (prefixWord ++ tailWord_408559) baseStart_408559 baseEnd_408559 := by
    simpa [prefixWord, tailWord_408559, baseEnd_408559] using wordTrace_append hprefix tailTrace_408559
  have hstable : (prefixWord ++ tailWord_408559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408559).length < 2 ^ (prefixWord ++ tailWord_408559).sum := by decide
  have hdescent : baseEnd_408559 < baseStart_408559 := by decide
  rcases family_descends (prefixWord ++ tailWord_408559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408572 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_408572 : Nat := 118140960795 + 408572 * 2 ^ 59
def prefixEnd_408572 : Nat := 4983230072969 + 3 ^ 40 * 408572 * 2
def baseEnd_408572 : Nat := 139862545312587129247345

theorem tailTrace_408572 : CollatzResearch.WordTrace tailWord_408572 prefixEnd_408572 139862545312587129247345 := by
  unfold tailWord_408572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450922537910448693677985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9934563383880598258237313 7450922537910448693677985)
  ·
    refine ⟨5588191903432836520258489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7450922537910448693677985 5588191903432836520258489)
    ·
      refine ⟨4191143927574627390193867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5588191903432836520258489 4191143927574627390193867)
      ·
        refine ⟨6286715891361941085290801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191143927574627390193867 6286715891361941085290801)
        ·
          refine ⟨4715036918521455813968101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6286715891361941085290801 4715036918521455813968101)
          ·
            refine ⟨884069422222772965119019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4715036918521455813968101 884069422222772965119019)
            ·
              refine ⟨1326104133334159447678529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884069422222772965119019 1326104133334159447678529)
              ·
                refine ⟨994578100000619585758897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326104133334159447678529 994578100000619585758897)
                ·
                  refine ⟨745933575000464689319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994578100000619585758897 745933575000464689319173)
                  ·
                    refine ⟨139862545312587129247345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745933575000464689319173 139862545312587129247345)
                    ·
                      rfl

theorem cell22_408572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_408572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408572 prefixEnd_408572 := by exact prefixLift 408572
  have htrace : WordTrace (prefixWord ++ tailWord_408572) baseStart_408572 baseEnd_408572 := by
    simpa [prefixWord, tailWord_408572, baseEnd_408572] using wordTrace_append hprefix tailTrace_408572
  have hstable : (prefixWord ++ tailWord_408572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408572).length < 2 ^ (prefixWord ++ tailWord_408572).sum := by decide
  have hdescent : baseEnd_408572 < baseStart_408572 := by decide
  rcases family_descends (prefixWord ++ tailWord_408572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408602 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_408602 : Nat := 118140960795 + 408602 * 2 ^ 59
def prefixEnd_408602 : Nat := 4983230072969 + 3 ^ 40 * 408602 * 2
def baseEnd_408602 : Nat := 139872814925677050997253

theorem tailTrace_408602 : CollatzResearch.WordTrace tailWord_408602 prefixEnd_408602 139872814925677050997253 := by
  unfold tailWord_408602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725734816428053127737015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9935292843808141673965373 3725734816428053127737015)
  ·
    refine ⟨5588602224642079691605523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3725734816428053127737015 5588602224642079691605523)
    ·
      refine ⟨8382903336963119537408285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588602224642079691605523 8382903336963119537408285)
      ·
        refine ⟨3143588751361169826528107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8382903336963119537408285 3143588751361169826528107)
        ·
          refine ⟨4715383127041754739792161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143588751361169826528107 4715383127041754739792161)
          ·
            refine ⟨3536537345281316054844121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715383127041754739792161 3536537345281316054844121)
            ·
              refine ⟨2652403008960987041133091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536537345281316054844121 2652403008960987041133091)
              ·
                refine ⟨3978604513441480561699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652403008960987041133091 3978604513441480561699637)
                ·
                  refine ⟨372994173135138802659341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978604513441480561699637 372994173135138802659341)
                  ·
                    refine ⟨139872814925677050997253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 372994173135138802659341 139872814925677050997253)
                    ·
                      rfl

theorem cell22_408602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_408602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408602 prefixEnd_408602 := by exact prefixLift 408602
  have htrace : WordTrace (prefixWord ++ tailWord_408602) baseStart_408602 baseEnd_408602 := by
    simpa [prefixWord, tailWord_408602, baseEnd_408602] using wordTrace_append hprefix tailTrace_408602
  have hstable : (prefixWord ++ tailWord_408602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408602).length < 2 ^ (prefixWord ++ tailWord_408602).sum := by decide
  have hdescent : baseEnd_408602 < baseStart_408602 := by decide
  rcases family_descends (prefixWord ++ tailWord_408602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408619 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 1, 3]
def baseStart_408619 : Nat := 118140960795 + 408619 * 2 ^ 59
def prefixEnd_408619 : Nat := 4983230072969 + 3 ^ 40 * 408619 * 2
def baseEnd_408619 : Nat := 139878634373094673322201

theorem tailTrace_408619 : CollatzResearch.WordTrace tailWord_408619 prefixEnd_408619 139878634373094673322201 := by
  unfold tailWord_408619
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903559306650624414316911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9935706204433749609544607 14903559306650624414316911)
  ·
    refine ⟨22355338959975936621475367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903559306650624414316911 22355338959975936621475367)
    ·
      refine ⟨33533008439963904932213051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355338959975936621475367 33533008439963904932213051)
      ·
        refine ⟨50299512659945857398319577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33533008439963904932213051 50299512659945857398319577)
        ·
          refine ⟨37724634494959393048739683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50299512659945857398319577 37724634494959393048739683)
          ·
            refine ⟨56586951742439089573109525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37724634494959393048739683 56586951742439089573109525)
            ·
              refine ⟨2652513362926832323739509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56586951742439089573109525 2652513362926832323739509)
              ·
                refine ⟨248673127774390530350579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2652513362926832323739509 248673127774390530350579)
                ·
                  refine ⟨373009691661585795525869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248673127774390530350579 373009691661585795525869)
                  ·
                    refine ⟨139878634373094673322201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373009691661585795525869 139878634373094673322201)
                    ·
                      rfl

theorem cell22_408619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 3].length) (baseStart_408619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408619 prefixEnd_408619 := by exact prefixLift 408619
  have htrace : WordTrace (prefixWord ++ tailWord_408619) baseStart_408619 baseEnd_408619 := by
    simpa [prefixWord, tailWord_408619, baseEnd_408619] using wordTrace_append hprefix tailTrace_408619
  have hstable : (prefixWord ++ tailWord_408619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408619).length < 2 ^ (prefixWord ++ tailWord_408619).sum := by decide
  have hdescent : baseEnd_408619 < baseStart_408619 := by decide
  rcases family_descends (prefixWord ++ tailWord_408619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408632 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_408632 : Nat := 118140960795 + 408632 * 2 ^ 59
def prefixEnd_408632 : Nat := 4983230072969 + 3 ^ 40 * 408632 * 2
def baseEnd_408632 : Nat := 46627694846255657582387

theorem tailTrace_408632 : CollatzResearch.WordTrace tailWord_408632 prefixEnd_408632 46627694846255657582387 := by
  unfold tailWord_408632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452016727801763817270075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9936022303735685089693433 7452016727801763817270075)
  ·
    refine ⟨11178025091702645725905113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452016727801763817270075 11178025091702645725905113)
    ·
      refine ⟨8383518818776984294428835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11178025091702645725905113 8383518818776984294428835)
      ·
        refine ⟨12575278228165476441643253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383518818776984294428835 12575278228165476441643253)
        ·
          refine ⟨1178932333890513416404055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12575278228165476441643253 1178932333890513416404055)
          ·
            refine ⟨1768398500835770124606083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178932333890513416404055 1768398500835770124606083)
            ·
              refine ⟨2652597751253655186909125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768398500835770124606083 2652597751253655186909125)
              ·
                refine ⟨497362078360060347545461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2652597751253655186909125 497362078360060347545461)
                ·
                  refine ⟨46627694846255657582387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497362078360060347545461 46627694846255657582387)
                  ·
                    rfl

theorem cell22_408632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_408632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408632 prefixEnd_408632 := by exact prefixLift 408632
  have htrace : WordTrace (prefixWord ++ tailWord_408632) baseStart_408632 baseEnd_408632 := by
    simpa [prefixWord, tailWord_408632, baseEnd_408632] using wordTrace_append hprefix tailTrace_408632
  have hstable : (prefixWord ++ tailWord_408632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408632).length < 2 ^ (prefixWord ++ tailWord_408632).sum := by decide
  have hdescent : baseEnd_408632 < baseStart_408632 := by decide
  rcases family_descends (prefixWord ++ tailWord_408632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408636 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_408636 : Nat := 118140960795 + 408636 * 2 ^ 59
def prefixEnd_408636 : Nat := 4983230072969 + 3 ^ 40 * 408636 * 2
def baseEnd_408636 : Nat := 139884453820512295647149

theorem tailTrace_408636 : CollatzResearch.WordTrace tailWord_408636 prefixEnd_408636 139884453820512295647149 := by
  unfold tailWord_408636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452089673794518158842881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9936119565059357545123841 7452089673794518158842881)
  ·
    refine ⟨5589067255345888619132161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7452089673794518158842881 5589067255345888619132161)
    ·
      refine ⟨4191800441509416464349121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589067255345888619132161 4191800441509416464349121)
      ·
        refine ⟨3143850331132062348261841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191800441509416464349121 3143850331132062348261841)
        ·
          refine ⟨2357887748349046761196381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143850331132062348261841 2357887748349046761196381)
          ·
            refine ⟨884207905630892535448643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2357887748349046761196381 884207905630892535448643)
            ·
              refine ⟨1326311858446338803172965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884207905630892535448643 1326311858446338803172965)
              ·
                refine ⟨248683473458688525594931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1326311858446338803172965 248683473458688525594931)
                ·
                  refine ⟨373025210188032788392397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248683473458688525594931 373025210188032788392397)
                  ·
                    refine ⟨139884453820512295647149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373025210188032788392397 139884453820512295647149)
                    ·
                      rfl

theorem cell22_408636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_408636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408636 prefixEnd_408636 := by exact prefixLift 408636
  have htrace : WordTrace (prefixWord ++ tailWord_408636) baseStart_408636 baseEnd_408636 := by
    simpa [prefixWord, tailWord_408636, baseEnd_408636] using wordTrace_append hprefix tailTrace_408636
  have hstable : (prefixWord ++ tailWord_408636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408636).length < 2 ^ (prefixWord ++ tailWord_408636).sum := by decide
  have hdescent : baseEnd_408636 < baseStart_408636 := by decide
  rcases family_descends (prefixWord ++ tailWord_408636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408647 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_408647 : Nat := 118140960795 + 408647 * 2 ^ 59
def prefixEnd_408647 : Nat := 4983230072969 + 3 ^ 40 * 408647 * 2
def baseEnd_408647 : Nat := 139888219345311933622115

theorem tailTrace_408647 : CollatzResearch.WordTrace tailWord_408647 prefixEnd_408647 139888219345311933622115 := by
  unfold tailWord_408647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904580550549185196336195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9936387033699456797557463 14904580550549185196336195)
  ·
    refine ⟨22356870825823777794504293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904580550549185196336195 22356870825823777794504293)
    ·
      refine ⟨4191913279841958336469555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22356870825823777794504293 4191913279841958336469555)
      ·
        refine ⟨6287869919762937504704333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191913279841958336469555 6287869919762937504704333)
        ·
          refine ⟨2357951219911101564264125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6287869919762937504704333 2357951219911101564264125)
          ·
            refine ⟨884231707466663086599047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2357951219911101564264125 884231707466663086599047)
            ·
              refine ⟨1326347561199994629898571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884231707466663086599047 1326347561199994629898571)
              ·
                refine ⟨1989521341799991944847857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326347561199994629898571 1989521341799991944847857)
                ·
                  refine ⟨1492141006349993958635893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989521341799991944847857 1492141006349993958635893)
                  ·
                    refine ⟨139888219345311933622115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1492141006349993958635893 139888219345311933622115)
                    ·
                      rfl

theorem cell22_408647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_408647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408647 prefixEnd_408647 := by exact prefixLift 408647
  have htrace : WordTrace (prefixWord ++ tailWord_408647) baseStart_408647 baseEnd_408647 := by
    simpa [prefixWord, tailWord_408647, baseEnd_408647] using wordTrace_append hprefix tailTrace_408647
  have hstable : (prefixWord ++ tailWord_408647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408647).length < 2 ^ (prefixWord ++ tailWord_408647).sum := by decide
  have hdescent : baseEnd_408647 < baseStart_408647 := by decide
  rcases family_descends (prefixWord ++ tailWord_408647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408670 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_408670 : Nat := 118140960795 + 408670 * 2 ^ 59
def prefixEnd_408670 : Nat := 4983230072969 + 3 ^ 40 * 408670 * 2
def baseEnd_408670 : Nat := 139896092715347540297045

theorem tailTrace_408670 : CollatzResearch.WordTrace tailWord_408670 prefixEnd_408670 139896092715347540297045 := by
  unfold tailWord_408670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863177428683232515552933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9936946286310573416282309 1863177428683232515552933)
  ·
    refine ⟨349345767878106096666175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1863177428683232515552933 349345767878106096666175)
    ·
      refine ⟨524018651817159144999263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349345767878106096666175 524018651817159144999263)
      ·
        refine ⟨786027977725738717498895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524018651817159144999263 786027977725738717498895)
        ·
          refine ⟨1179041966588608076248343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786027977725738717498895 1179041966588608076248343)
          ·
            refine ⟨1768562949882912114372515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179041966588608076248343 1768562949882912114372515)
            ·
              refine ⟨2652844424824368171558773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768562949882912114372515 2652844424824368171558773)
              ·
                refine ⟨248704164827284516083635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2652844424824368171558773 248704164827284516083635)
                ·
                  refine ⟨373056247240926774125453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248704164827284516083635 373056247240926774125453)
                  ·
                    refine ⟨139896092715347540297045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373056247240926774125453 139896092715347540297045)
                    ·
                      rfl

theorem cell22_408670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_408670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408670 prefixEnd_408670 := by exact prefixLift 408670
  have htrace : WordTrace (prefixWord ++ tailWord_408670) baseStart_408670 baseEnd_408670 := by
    simpa [prefixWord, tailWord_408670, baseEnd_408670] using wordTrace_append hprefix tailTrace_408670
  have hstable : (prefixWord ++ tailWord_408670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408670).length < 2 ^ (prefixWord ++ tailWord_408670).sum := by decide
  have hdescent : baseEnd_408670 < baseStart_408670 := by decide
  rcases family_descends (prefixWord ++ tailWord_408670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408679 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 1, 4]
def baseStart_408679 : Nat := 118140960795 + 408679 * 2 ^ 59
def prefixEnd_408679 : Nat := 4983230072969 + 3 ^ 40 * 408679 * 2
def baseEnd_408679 : Nat := 139899173599274516822017

theorem tailTrace_408679 : CollatzResearch.WordTrace tailWord_408679 prefixEnd_408679 139899173599274516822017 := by
  unfold tailWord_408679
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905747686433254661501091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9937165124288836441000727 14905747686433254661501091)
  ·
    refine ⟨22358621529649881992251637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14905747686433254661501091 22358621529649881992251637)
    ·
      refine ⟨2096120768404676436773591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22358621529649881992251637 2096120768404676436773591)
      ·
        refine ⟨3144181152607014655160387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096120768404676436773591 3144181152607014655160387)
        ·
          refine ⟨4716271728910521982740581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144181152607014655160387 4716271728910521982740581)
          ·
            refine ⟨884300949170722871763859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4716271728910521982740581 884300949170722871763859)
            ·
              refine ⟨1326451423756084307645789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884300949170722871763859 1326451423756084307645789)
              ·
                refine ⟨497419283908531615367171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326451423756084307645789 497419283908531615367171)
                ·
                  refine ⟨746128925862797423050757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497419283908531615367171 746128925862797423050757)
                  ·
                    refine ⟨139899173599274516822017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746128925862797423050757 139899173599274516822017)
                    ·
                      rfl

theorem cell22_408679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_408679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408679 prefixEnd_408679 := by exact prefixLift 408679
  have htrace : WordTrace (prefixWord ++ tailWord_408679) baseStart_408679 baseEnd_408679 := by
    simpa [prefixWord, tailWord_408679, baseEnd_408679] using wordTrace_append hprefix tailTrace_408679
  have hstable : (prefixWord ++ tailWord_408679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408679).length < 2 ^ (prefixWord ++ tailWord_408679).sum := by decide
  have hdescent : baseEnd_408679 < baseStart_408679 := by decide
  rcases family_descends (prefixWord ++ tailWord_408679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408694 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_408694 : Nat := 118140960795 + 408694 * 2 ^ 59
def prefixEnd_408694 : Nat := 4983230072969 + 3 ^ 40 * 408694 * 2
def baseEnd_408694 : Nat := 46634769468606492565657

theorem tailTrace_408694 : CollatzResearch.WordTrace tailWord_408694 prefixEnd_408694 46634769468606492565657 := by
  unfold tailWord_408694
  simp only [CollatzResearch.WordTrace]
  refine ⟨931643423836182013956071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9937529854252608148864757 931643423836182013956071)
  ·
    refine ⟨1397465135754273020934107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931643423836182013956071 1397465135754273020934107)
    ·
      refine ⟨2096197703631409531401161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397465135754273020934107 2096197703631409531401161)
      ·
        refine ⟨1572148277723557148550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2096197703631409531401161 1572148277723557148550871)
        ·
          refine ⟨2358222416585335722826307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572148277723557148550871 2358222416585335722826307)
          ·
            refine ⟨3537333624878003584239461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358222416585335722826307 3537333624878003584239461)
            ·
              refine ⟨663250054664625672044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3537333624878003584239461 663250054664625672044899)
              ·
                refine ⟨994875081996938508067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663250054664625672044899 994875081996938508067349)
                ·
                  refine ⟨46634769468606492565657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 994875081996938508067349 46634769468606492565657)
                  ·
                    rfl

theorem cell22_408694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_408694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408694 prefixEnd_408694 := by exact prefixLift 408694
  have htrace : WordTrace (prefixWord ++ tailWord_408694) baseStart_408694 baseEnd_408694 := by
    simpa [prefixWord, tailWord_408694, baseEnd_408694] using wordTrace_append hprefix tailTrace_408694
  have hstable : (prefixWord ++ tailWord_408694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408694).length < 2 ^ (prefixWord ++ tailWord_408694).sum := by decide
  have hdescent : baseEnd_408694 < baseStart_408694 := by decide
  rcases family_descends (prefixWord ++ tailWord_408694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408814 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_408814 : Nat := 118140960795 + 408814 * 2 ^ 59
def prefixEnd_408814 : Nat := 4983230072969 + 3 ^ 40 * 408814 * 2
def baseEnd_408814 : Nat := 139945386858179164696603

theorem tailTrace_408814 : CollatzResearch.WordTrace tailWord_408814 prefixEnd_408814 139945386858179164696603 := by
  unfold tailWord_408814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863833942618021589708187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9940447693962781811776997 1863833942618021589708187)
  ·
    refine ⟨2795750913927032384562281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863833942618021589708187 2795750913927032384562281)
    ·
      refine ⟨2096813185445274288421711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2795750913927032384562281 2096813185445274288421711)
      ·
        refine ⟨3145219778167911432632567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096813185445274288421711 3145219778167911432632567)
        ·
          refine ⟨4717829667251867148948851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145219778167911432632567 4717829667251867148948851)
          ·
            refine ⟨7076744500877800723423277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717829667251867148948851 7076744500877800723423277)
            ·
              refine ⟨2653779187829175271283729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7076744500877800723423277 2653779187829175271283729)
              ·
                refine ⟨1990334390871881453462797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653779187829175271283729 1990334390871881453462797)
                ·
                  refine ⟨746375396576955545048549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1990334390871881453462797 746375396576955545048549)
                  ·
                    refine ⟨139945386858179164696603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746375396576955545048549 139945386858179164696603)
                    ·
                      rfl

theorem cell22_408814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_408814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408814 prefixEnd_408814 := by exact prefixLift 408814
  have htrace : WordTrace (prefixWord ++ tailWord_408814) baseStart_408814 baseEnd_408814 := by
    simpa [prefixWord, tailWord_408814, baseEnd_408814] using wordTrace_append hprefix tailTrace_408814
  have hstable : (prefixWord ++ tailWord_408814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408814).length < 2 ^ (prefixWord ++ tailWord_408814).sum := by decide
  have hdescent : baseEnd_408814 < baseStart_408814 := by decide
  rcases family_descends (prefixWord ++ tailWord_408814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408844 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_408844 : Nat := 118140960795 + 408844 * 2 ^ 59
def prefixEnd_408844 : Nat := 4983230072969 + 3 ^ 40 * 408844 * 2
def baseEnd_408844 : Nat := 139955656471269086446511

theorem tailTrace_408844 : CollatzResearch.WordTrace tailWord_408844 prefixEnd_408844 139955656471269086446511 := by
  unfold tailWord_408844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455882865417743920628793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9941177153890325227505057 7455882865417743920628793)
  ·
    refine ⟨5591912149063307940471595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7455882865417743920628793 5591912149063307940471595)
    ·
      refine ⟨8387868223594961910707393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5591912149063307940471595 8387868223594961910707393)
      ·
        refine ⟨6290901167696221433030545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8387868223594961910707393 6290901167696221433030545)
        ·
          refine ⟨4718175875772166074772909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290901167696221433030545 4718175875772166074772909)
          ·
            refine ⟨1769315953414562278039841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4718175875772166074772909 1769315953414562278039841)
            ·
              refine ⟨1326986965060921708529881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769315953414562278039841 1326986965060921708529881)
              ·
                refine ⟨995240223795691281397411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326986965060921708529881 995240223795691281397411)
                ·
                  refine ⟨1492860335693536922096117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995240223795691281397411 1492860335693536922096117)
                  ·
                    refine ⟨139955656471269086446511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1492860335693536922096117 139955656471269086446511)
                    ·
                      rfl

theorem cell22_408844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_408844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408844 prefixEnd_408844 := by exact prefixLift 408844
  have htrace : WordTrace (prefixWord ++ tailWord_408844) baseStart_408844 baseEnd_408844 := by
    simpa [prefixWord, tailWord_408844, baseEnd_408844] using wordTrace_append hprefix tailTrace_408844
  have hstable : (prefixWord ++ tailWord_408844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408844).length < 2 ^ (prefixWord ++ tailWord_408844).sum := by decide
  have hdescent : baseEnd_408844 < baseStart_408844 := by decide
  rcases family_descends (prefixWord ++ tailWord_408844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408846 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_408846 : Nat := 118140960795 + 408846 * 2 ^ 59
def prefixEnd_408846 : Nat := 4983230072969 + 3 ^ 40 * 408846 * 2
def baseEnd_408846 : Nat := 46652113704047249298835

theorem tailTrace_408846 : CollatzResearch.WordTrace tailWord_408846 prefixEnd_408846 46652113704047249298835 := by
  unfold tailWord_408846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863979834603530272853799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9941225784552161455220261 1863979834603530272853799)
  ·
    refine ⟨2795969751905295409280699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863979834603530272853799 2795969751905295409280699)
    ·
      refine ⟨4193954627857943113921049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795969751905295409280699 4193954627857943113921049)
      ·
        refine ⟨3145465970893457335440787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4193954627857943113921049 3145465970893457335440787)
        ·
          refine ⟨4718198956340186003161181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145465970893457335440787 4718198956340186003161181)
          ·
            refine ⟨1769324608627569751185443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4718198956340186003161181 1769324608627569751185443)
            ·
              refine ⟨2653986912941354626778165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769324608627569751185443 2653986912941354626778165)
              ·
                refine ⟨248811273088251996260453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2653986912941354626778165 248811273088251996260453)
                ·
                  refine ⟨46652113704047249298835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248811273088251996260453 46652113704047249298835)
                  ·
                    rfl

theorem cell22_408846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_408846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408846 prefixEnd_408846 := by exact prefixLift 408846
  have htrace : WordTrace (prefixWord ++ tailWord_408846) baseStart_408846 baseEnd_408846 := by
    simpa [prefixWord, tailWord_408846, baseEnd_408846] using wordTrace_append hprefix tailTrace_408846
  have hstable : (prefixWord ++ tailWord_408846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408846).length < 2 ^ (prefixWord ++ tailWord_408846).sum := by decide
  have hdescent : baseEnd_408846 < baseStart_408846 := by decide
  rcases family_descends (prefixWord ++ tailWord_408846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408919 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 7]
def baseStart_408919 : Nat := 118140960795 + 408919 * 2 ^ 59
def prefixEnd_408919 : Nat := 4983230072969 + 3 ^ 40 * 408919 * 2
def baseEnd_408919 : Nat := 46660443501331296940427

theorem tailTrace_408919 : CollatzResearch.WordTrace tailWord_408919 prefixEnd_408919 46660443501331296940427 := by
  unfold tailWord_408919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14914501205563775650237811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9943000803709183766825207 14914501205563775650237811)
  ·
    refine ⟨22371751808345663475356717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14914501205563775650237811 22371751808345663475356717)
    ·
      refine ⟨8389406928129623803258769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22371751808345663475356717 8389406928129623803258769)
      ·
        refine ⟨6292055196097217852444077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8389406928129623803258769 6292055196097217852444077)
        ·
          refine ⟨2359520698536456694666529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6292055196097217852444077 2359520698536456694666529)
          ·
            refine ⟨1769640523902342520999897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359520698536456694666529 1769640523902342520999897)
            ·
              refine ⟨1327230392926756890749923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769640523902342520999897 1327230392926756890749923)
              ·
                refine ⟨1990845589390135336124885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327230392926756890749923 1990845589390135336124885)
                ·
                  refine ⟨46660443501331296940427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1990845589390135336124885 46660443501331296940427)
                  ·
                    rfl

theorem cell22_408919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_408919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408919 prefixEnd_408919 := by exact prefixLift 408919
  have htrace : WordTrace (prefixWord ++ tailWord_408919) baseStart_408919 baseEnd_408919 := by
    simpa [prefixWord, tailWord_408919, baseEnd_408919] using wordTrace_append hprefix tailTrace_408919
  have hstable : (prefixWord ++ tailWord_408919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408919).length < 2 ^ (prefixWord ++ tailWord_408919).sum := by decide
  have hdescent : baseEnd_408919 < baseStart_408919 := by decide
  rcases family_descends (prefixWord ++ tailWord_408919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408925 : List Nat := [1, 4, 5, 1, 1, 1, 2, 7]
def baseStart_408925 : Nat := 118140960795 + 408925 * 2 ^ 59
def prefixEnd_408925 : Nat := 4983230072969 + 3 ^ 40 * 408925 * 2
def baseEnd_408925 : Nat := 15553709380734652796807

theorem tailTrace_408925 : CollatzResearch.WordTrace tailWord_408925 prefixEnd_408925 15553709380734652796807 := by
  unfold tailWord_408925
  simp only [CollatzResearch.WordTrace]
  refine ⟨14914720043542038674956229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9943146695694692449970819 14914720043542038674956229)
  ·
    refine ⟨2796510008164132251554293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14914720043542038674956229 2796510008164132251554293)
    ·
      refine ⟨262172813265387398583215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2796510008164132251554293 262172813265387398583215)
      ·
        refine ⟨393259219898081097874823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262172813265387398583215 393259219898081097874823)
        ·
          refine ⟨589888829847121646812235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393259219898081097874823 589888829847121646812235)
          ·
            refine ⟨884833244770682470218353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589888829847121646812235 884833244770682470218353)
            ·
              refine ⟨663624933578011852663765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884833244770682470218353 663624933578011852663765)
              ·
                refine ⟨15553709380734652796807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 663624933578011852663765 15553709380734652796807)
                ·
                  rfl

theorem cell22_408925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 7].length) (baseStart_408925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408925 prefixEnd_408925 := by exact prefixLift 408925
  have htrace : WordTrace (prefixWord ++ tailWord_408925) baseStart_408925 baseEnd_408925 := by
    simpa [prefixWord, tailWord_408925, baseEnd_408925] using wordTrace_append hprefix tailTrace_408925
  have hstable : (prefixWord ++ tailWord_408925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408925).length < 2 ^ (prefixWord ++ tailWord_408925).sum := by decide
  have hdescent : baseEnd_408925 < baseStart_408925 := by decide
  rcases family_descends (prefixWord ++ tailWord_408925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408974 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_408974 : Nat := 118140960795 + 408974 * 2 ^ 59
def prefixEnd_408974 : Nat := 4983230072969 + 3 ^ 40 * 408974 * 2
def baseEnd_408974 : Nat := 140000158127992080696113

theorem tailTrace_408974 : CollatzResearch.WordTrace tailWord_408974 prefixEnd_408974 140000158127992080696113 := by
  unfold tailWord_408974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864563402545565005436247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9944338146909680028993317 1864563402545565005436247)
  ·
    refine ⟨2796845103818347508154371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864563402545565005436247 2796845103818347508154371)
    ·
      refine ⟨4195267655727521262231557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796845103818347508154371 4195267655727521262231557)
      ·
        refine ⟨786612685448910236668417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4195267655727521262231557 786612685448910236668417)
        ·
          refine ⟨589959514086682677501313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786612685448910236668417 589959514086682677501313)
          ·
            refine ⟨442469635565012008125985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589959514086682677501313 442469635565012008125985)
            ·
              refine ⟨331852226673759006094489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442469635565012008125985 331852226673759006094489)
              ·
                refine ⟨248889170005319254570867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331852226673759006094489 248889170005319254570867)
                ·
                  refine ⟨373333755007978881856301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248889170005319254570867 373333755007978881856301)
                  ·
                    refine ⟨140000158127992080696113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373333755007978881856301 140000158127992080696113)
                    ·
                      rfl

theorem cell22_408974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_408974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408974 prefixEnd_408974 := by exact prefixLift 408974
  have htrace : WordTrace (prefixWord ++ tailWord_408974) baseStart_408974 baseEnd_408974 := by
    simpa [prefixWord, tailWord_408974, baseEnd_408974] using wordTrace_append hprefix tailTrace_408974
  have hstable : (prefixWord ++ tailWord_408974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408974).length < 2 ^ (prefixWord ++ tailWord_408974).sum := by decide
  have hdescent : baseEnd_408974 < baseStart_408974 := by decide
  rcases family_descends (prefixWord ++ tailWord_408974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408996 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_408996 : Nat := 118140960795 + 408996 * 2 ^ 59
def prefixEnd_408996 : Nat := 4983230072969 + 3 ^ 40 * 408996 * 2
def baseEnd_408996 : Nat := 140007689177591356646045

theorem tailTrace_408996 : CollatzResearch.WordTrace tailWord_408996 prefixEnd_408996 140007689177591356646045 := by
  unfold tailWord_408996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458654813142408900395421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9944873084189878533860561 7458654813142408900395421)
  ·
    refine ⟨2796995554928403337648283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7458654813142408900395421 2796995554928403337648283)
    ·
      refine ⟨4195493332392605006472425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796995554928403337648283 4195493332392605006472425)
      ·
        refine ⟨3146619999294453754854319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4195493332392605006472425 3146619999294453754854319)
        ·
          refine ⟨4719929998941680632281479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146619999294453754854319 4719929998941680632281479)
          ·
            refine ⟨7079894998412520948422219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719929998941680632281479 7079894998412520948422219)
            ·
              refine ⟨10619842497618781422633329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079894998412520948422219 10619842497618781422633329)
              ·
                refine ⟨7964881873214086066974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10619842497618781422633329 7964881873214086066974997)
                ·
                  refine ⟨373353837806910284389453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7964881873214086066974997 373353837806910284389453)
                  ·
                    refine ⟨140007689177591356646045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373353837806910284389453 140007689177591356646045)
                    ·
                      rfl

theorem cell22_408996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_408996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_408996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_408996 prefixEnd_408996 := by exact prefixLift 408996
  have htrace : WordTrace (prefixWord ++ tailWord_408996) baseStart_408996 baseEnd_408996 := by
    simpa [prefixWord, tailWord_408996, baseEnd_408996] using wordTrace_append hprefix tailTrace_408996
  have hstable : (prefixWord ++ tailWord_408996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408996).length < 2 ^ (prefixWord ++ tailWord_408996).sum := by decide
  have hdescent : baseEnd_408996 < baseStart_408996 := by decide
  rcases family_descends (prefixWord ++ tailWord_408996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409017 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_409017 : Nat := 118140960795 + 409017 * 2 ^ 59
def prefixEnd_409017 : Nat := 4983230072969 + 3 ^ 40 * 409017 * 2
def baseEnd_409017 : Nat := 140014877906754301870981

theorem tailTrace_409017 : CollatzResearch.WordTrace tailWord_409017 prefixEnd_409017 140014877906754301870981 := by
  unfold tailWord_409017
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918075559208738387305305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9945383706139158924870203 14918075559208738387305305)
  ·
    refine ⟨11188556669406553790478979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14918075559208738387305305 11188556669406553790478979)
    ·
      refine ⟨16782835004109830685718469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11188556669406553790478979 16782835004109830685718469)
      ·
        refine ⟨3146781563270593253572213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16782835004109830685718469 3146781563270593253572213)
        ·
          refine ⟨295010771556618117522395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3146781563270593253572213 295010771556618117522395)
          ·
            refine ⟨442516157334927176283593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295010771556618117522395 442516157334927176283593)
            ·
              refine ⟨331887118001195382212695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442516157334927176283593 331887118001195382212695)
              ·
                refine ⟨497830677001793073319043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331887118001195382212695 497830677001793073319043)
                ·
                  refine ⟨746746015502689609978565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497830677001793073319043 746746015502689609978565)
                  ·
                    refine ⟨140014877906754301870981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746746015502689609978565 140014877906754301870981)
                    ·
                      rfl

theorem cell22_409017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_409017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409017 prefixEnd_409017 := by exact prefixLift 409017
  have htrace : WordTrace (prefixWord ++ tailWord_409017) baseStart_409017 baseEnd_409017 := by
    simpa [prefixWord, tailWord_409017, baseEnd_409017] using wordTrace_append hprefix tailTrace_409017
  have hstable : (prefixWord ++ tailWord_409017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409017).length < 2 ^ (prefixWord ++ tailWord_409017).sum := by decide
  have hdescent : baseEnd_409017 < baseStart_409017 := by decide
  rcases family_descends (prefixWord ++ tailWord_409017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409039 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_409039 : Nat := 118140960795 + 409039 * 2 ^ 59
def prefixEnd_409039 : Nat := 4983230072969 + 3 ^ 40 * 409039 * 2
def baseEnd_409039 : Nat := 140022408956353577820913

theorem tailTrace_409039 : CollatzResearch.WordTrace tailWord_409039 prefixEnd_409039 140022408956353577820913 := by
  unfold tailWord_409039
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918877965129036144606171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9945918643419357429737447 14918877965129036144606171)
  ·
    refine ⟨22378316947693554216909257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918877965129036144606171 22378316947693554216909257)
    ·
      refine ⟨16783737710770165662681943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22378316947693554216909257 16783737710770165662681943)
      ·
        refine ⟨25175606566155248494022915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783737710770165662681943 25175606566155248494022915)
        ·
          refine ⟨37763409849232872741034373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25175606566155248494022915 37763409849232872741034373)
          ·
            refine ⟨7080639346731163638943945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37763409849232872741034373 7080639346731163638943945)
            ·
              refine ⟨5310479510048372729207959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7080639346731163638943945 5310479510048372729207959)
              ·
                refine ⟨7965719265072559093811939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310479510048372729207959 7965719265072559093811939)
                ·
                  refine ⟨11948578897608838640717909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7965719265072559093811939 11948578897608838640717909)
                  ·
                    refine ⟨140022408956353577820913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11948578897608838640717909 140022408956353577820913)
                    ·
                      rfl

theorem cell22_409039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_409039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409039 prefixEnd_409039 := by exact prefixLift 409039
  have htrace : WordTrace (prefixWord ++ tailWord_409039) baseStart_409039 baseEnd_409039 := by
    simpa [prefixWord, tailWord_409039, baseEnd_409039] using wordTrace_append hprefix tailTrace_409039
  have hstable : (prefixWord ++ tailWord_409039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409039).length < 2 ^ (prefixWord ++ tailWord_409039).sum := by decide
  have hdescent : baseEnd_409039 < baseStart_409039 := by decide
  rcases family_descends (prefixWord ++ tailWord_409039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409092 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_409092 : Nat := 118140960795 + 409092 * 2 ^ 59
def prefixEnd_409092 : Nat := 4983230072969 + 3 ^ 40 * 409092 * 2
def baseEnd_409092 : Nat := 140040551939479106245751

theorem tailTrace_409092 : CollatzResearch.WordTrace tailWord_409092 prefixEnd_409092 140040551939479106245751 := by
  unfold tailWord_409092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460405516968513098142765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9947207355958017464190353 7460405516968513098142765)
  ·
    refine ⟨2797652068863192411803537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7460405516968513098142765 2797652068863192411803537)
    ·
      refine ⟨2098239051647394308852653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797652068863192411803537 2098239051647394308852653)
      ·
        refine ⟨786839644367772865819745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2098239051647394308852653 786839644367772865819745)
        ·
          refine ⟨590129733275829649364809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786839644367772865819745 590129733275829649364809)
          ·
            refine ⟨442597299956872237023607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590129733275829649364809 442597299956872237023607)
            ·
              refine ⟨663895949935308355535411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442597299956872237023607 663895949935308355535411)
              ·
                refine ⟨995843924902962533303117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663895949935308355535411 995843924902962533303117)
                ·
                  refine ⟨373441471838610949988669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995843924902962533303117 373441471838610949988669)
                  ·
                    refine ⟨140040551939479106245751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373441471838610949988669 140040551939479106245751)
                    ·
                      rfl

theorem cell22_409092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_409092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409092 prefixEnd_409092 := by exact prefixLift 409092
  have htrace : WordTrace (prefixWord ++ tailWord_409092) baseStart_409092 baseEnd_409092 := by
    simpa [prefixWord, tailWord_409092, baseEnd_409092] using wordTrace_append hprefix tailTrace_409092
  have hstable : (prefixWord ++ tailWord_409092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409092).length < 2 ^ (prefixWord ++ tailWord_409092).sum := by decide
  have hdescent : baseEnd_409092 < baseStart_409092 := by decide
  rcases family_descends (prefixWord ++ tailWord_409092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409116 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_409116 : Nat := 118140960795 + 409116 * 2 ^ 59
def prefixEnd_409116 : Nat := 4983230072969 + 3 ^ 40 * 409116 * 2
def baseEnd_409116 : Nat := 46682922543317014548559

theorem tailTrace_409116 : CollatzResearch.WordTrace tailWord_409116 prefixEnd_409116 46682922543317014548559 := by
  unfold tailWord_409116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460843192925039147579601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9947790923900052196772801 7460843192925039147579601)
  ·
    refine ⟨5595632394693779360684701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460843192925039147579601 5595632394693779360684701)
    ·
      refine ⟨2098362148010167260256763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5595632394693779360684701 2098362148010167260256763)
      ·
        refine ⟨3147543222015250890385145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098362148010167260256763 3147543222015250890385145)
        ·
          refine ⟨2360657416511438167788859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147543222015250890385145 2360657416511438167788859)
          ·
            refine ⟨3540986124767157251683289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360657416511438167788859 3540986124767157251683289)
            ·
              refine ⟨2655739593575367938762467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540986124767157251683289 2655739593575367938762467)
              ·
                refine ⟨3983609390363051908143701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655739593575367938762467 3983609390363051908143701)
                ·
                  refine ⟨46682922543317014548559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3983609390363051908143701 46682922543317014548559)
                  ·
                    rfl

theorem cell22_409116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_409116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409116 prefixEnd_409116 := by exact prefixLift 409116
  have htrace : WordTrace (prefixWord ++ tailWord_409116) baseStart_409116 baseEnd_409116 := by
    simpa [prefixWord, tailWord_409116, baseEnd_409116] using wordTrace_append hprefix tailTrace_409116
  have hstable : (prefixWord ++ tailWord_409116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409116).length < 2 ^ (prefixWord ++ tailWord_409116).sum := by decide
  have hdescent : baseEnd_409116 < baseStart_409116 := by decide
  rcases family_descends (prefixWord ++ tailWord_409116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409180 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_409180 : Nat := 118140960795 + 409180 * 2 ^ 59
def prefixEnd_409180 : Nat := 4983230072969 + 3 ^ 40 * 409180 * 2
def baseEnd_409180 : Nat := 140070676137876210045481

theorem tailTrace_409180 : CollatzResearch.WordTrace tailWord_409180 prefixEnd_409180 140070676137876210045481 := by
  unfold tailWord_409180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462010328809108612744497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9949347105078811483659329 7462010328809108612744497)
  ·
    refine ⟨5596507746606831459558373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7462010328809108612744497 5596507746606831459558373)
    ·
      refine ⟨1049345202488780898667195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5596507746606831459558373 1049345202488780898667195)
      ·
        refine ⟨1574017803733171348000793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049345202488780898667195 1574017803733171348000793)
        ·
          refine ⟨1180513352799878511000595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574017803733171348000793 1180513352799878511000595)
          ·
            refine ⟨1770770029199817766500893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180513352799878511000595 1770770029199817766500893)
            ·
              refine ⟨664038760949931662437835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1770770029199817766500893 664038760949931662437835)
              ·
                refine ⟨996058141424897493656753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664038760949931662437835 996058141424897493656753)
                ·
                  refine ⟨747043606068673120242565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996058141424897493656753 747043606068673120242565)
                  ·
                    refine ⟨140070676137876210045481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 747043606068673120242565 140070676137876210045481)
                    ·
                      rfl

theorem cell22_409180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_409180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409180 prefixEnd_409180 := by exact prefixLift 409180
  have htrace : WordTrace (prefixWord ++ tailWord_409180) baseStart_409180 baseEnd_409180 := by
    simpa [prefixWord, tailWord_409180, baseEnd_409180] using wordTrace_append hprefix tailTrace_409180
  have hstable : (prefixWord ++ tailWord_409180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409180).length < 2 ^ (prefixWord ++ tailWord_409180).sum := by decide
  have hdescent : baseEnd_409180 < baseStart_409180 := by decide
  rcases family_descends (prefixWord ++ tailWord_409180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409300 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_409300 : Nat := 118140960795 + 409300 * 2 ^ 59
def prefixEnd_409300 : Nat := 4983230072969 + 3 ^ 40 * 409300 * 2
def baseEnd_409300 : Nat := 140111754590235897045113

theorem tailTrace_409300 : CollatzResearch.WordTrace tailWord_409300 prefixEnd_409300 140111754590235897045113 := by
  unfold tailWord_409300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464198708591738859928677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9952264944788985146571569 7464198708591738859928677)
  ·
    refine ⟨1399537257860951036236627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7464198708591738859928677 1399537257860951036236627)
    ·
      refine ⟨2099305886791426554354941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399537257860951036236627 2099305886791426554354941)
      ·
        refine ⟨787239707546784957883103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2099305886791426554354941 787239707546784957883103)
        ·
          refine ⟨1180859561320177436824655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787239707546784957883103 1180859561320177436824655)
          ·
            refine ⟨1771289341980266155236983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180859561320177436824655 1771289341980266155236983)
            ·
              refine ⟨2656934012970399232855475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771289341980266155236983 2656934012970399232855475)
              ·
                refine ⟨3985401019455598849283213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656934012970399232855475 3985401019455598849283213)
                ·
                  refine ⟨1494525382295849568481205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3985401019455598849283213 1494525382295849568481205)
                  ·
                    refine ⟨140111754590235897045113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1494525382295849568481205 140111754590235897045113)
                    ·
                      rfl

theorem cell22_409300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_409300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409300 prefixEnd_409300 := by exact prefixLift 409300
  have htrace : WordTrace (prefixWord ++ tailWord_409300) baseStart_409300 baseEnd_409300 := by
    simpa [prefixWord, tailWord_409300, baseEnd_409300] using wordTrace_append hprefix tailTrace_409300
  have hstable : (prefixWord ++ tailWord_409300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409300).length < 2 ^ (prefixWord ++ tailWord_409300).sum := by decide
  have hdescent : baseEnd_409300 < baseStart_409300 := by decide
  rcases family_descends (prefixWord ++ tailWord_409300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409313 : List Nat := [1, 2, 3, 1, 5, 10]
def baseStart_409313 : Nat := 118140960795 + 409313 * 2 ^ 59
def prefixEnd_409313 : Nat := 4983230072969 + 3 ^ 40 * 409313 * 2
def baseEnd_409313 : Nat := 1729829688344545635433

theorem tailTrace_409313 : CollatzResearch.WordTrace tailWord_409313 prefixEnd_409313 1729829688344545635433 := by
  unfold tailWord_409313
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928871566136380940080593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9952581044090920626720395 14928871566136380940080593)
  ·
    refine ⟨11196653674602285705060445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14928871566136380940080593 11196653674602285705060445)
    ·
      refine ⟨4198745127975857139397667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11196653674602285705060445 4198745127975857139397667)
      ·
        refine ⟨6298117691963785709096501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198745127975857139397667 6298117691963785709096501)
        ·
          refine ⟨590448533621604910227797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6298117691963785709096501 590448533621604910227797)
          ·
            refine ⟨1729829688344545635433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 590448533621604910227797 1729829688344545635433)
            ·
              rfl

theorem cell22_409313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 10].length) (baseStart_409313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409313 prefixEnd_409313 := by exact prefixLift 409313
  have htrace : WordTrace (prefixWord ++ tailWord_409313) baseStart_409313 baseEnd_409313 := by
    simpa [prefixWord, tailWord_409313, baseEnd_409313] using wordTrace_append hprefix tailTrace_409313
  have hstable : (prefixWord ++ tailWord_409313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409313).length < 2 ^ (prefixWord ++ tailWord_409313).sum := by decide
  have hdescent : baseEnd_409313 < baseStart_409313 := by decide
  rcases family_descends (prefixWord ++ tailWord_409313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409317 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_409317 : Nat := 118140960795 + 409317 * 2 ^ 59
def prefixEnd_409317 : Nat := 4983230072969 + 3 ^ 40 * 409317 * 2
def baseEnd_409317 : Nat := 140117574037653519370061

theorem tailTrace_409317 : CollatzResearch.WordTrace tailWord_409317 prefixEnd_409317 140117574037653519370061 := by
  unfold tailWord_409317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929017458121889623226205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9952678305414593082150803 14929017458121889623226205)
  ·
    refine ⟨5598381546795708608709827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14929017458121889623226205 5598381546795708608709827)
    ·
      refine ⟨8397572320193562913064741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598381546795708608709827 8397572320193562913064741)
      ·
        refine ⟨1574544810036293046199639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8397572320193562913064741 1574544810036293046199639)
        ·
          refine ⟨2361817215054439569299459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574544810036293046199639 2361817215054439569299459)
          ·
            refine ⟨3542725822581659353949189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361817215054439569299459 3542725822581659353949189)
            ·
              refine ⟨664261091734061128865473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3542725822581659353949189 664261091734061128865473)
              ·
                refine ⟨498195818800545846649105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664261091734061128865473 498195818800545846649105)
                ·
                  refine ⟨373646864100409384986829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498195818800545846649105 373646864100409384986829)
                  ·
                    refine ⟨140117574037653519370061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373646864100409384986829 140117574037653519370061)
                    ·
                      rfl

theorem cell22_409317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_409317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409317 prefixEnd_409317 := by exact prefixLift 409317
  have htrace : WordTrace (prefixWord ++ tailWord_409317) baseStart_409317 baseEnd_409317 := by
    simpa [prefixWord, tailWord_409317, baseEnd_409317] using wordTrace_append hprefix tailTrace_409317
  have hstable : (prefixWord ++ tailWord_409317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409317).length < 2 ^ (prefixWord ++ tailWord_409317).sum := by decide
  have hdescent : baseEnd_409317 < baseStart_409317 := by decide
  rcases family_descends (prefixWord ++ tailWord_409317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409319 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 4]
def baseStart_409319 : Nat := 118140960795 + 409319 * 2 ^ 59
def prefixEnd_409319 : Nat := 4983230072969 + 3 ^ 40 * 409319 * 2
def baseEnd_409319 : Nat := 46706086226175393606685

theorem tailTrace_409319 : CollatzResearch.WordTrace tailWord_409319 prefixEnd_409319 46706086226175393606685 := by
  unfold tailWord_409319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929090404114643964799011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9952726936076429309866007 14929090404114643964799011)
  ·
    refine ⟨22393635606171965947198517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14929090404114643964799011 22393635606171965947198517)
    ·
      refine ⟨2099403338078621807549861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22393635606171965947198517 2099403338078621807549861)
      ·
        refine ⟨393638125889741588915599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2099403338078621807549861 393638125889741588915599)
        ·
          refine ⟨590457188834612383373399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393638125889741588915599 590457188834612383373399)
          ·
            refine ⟨885685783251918575060099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590457188834612383373399 885685783251918575060099)
            ·
              refine ⟨1328528674877877862590149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885685783251918575060099 1328528674877877862590149)
              ·
                refine ⟨249099126539602099235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1328528674877877862590149 249099126539602099235653)
                ·
                  refine ⟨46706086226175393606685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249099126539602099235653 46706086226175393606685)
                  ·
                    rfl

theorem cell22_409319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 4].length) (baseStart_409319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409319 prefixEnd_409319 := by exact prefixLift 409319
  have htrace : WordTrace (prefixWord ++ tailWord_409319) baseStart_409319 baseEnd_409319 := by
    simpa [prefixWord, tailWord_409319, baseEnd_409319] using wordTrace_append hprefix tailTrace_409319
  have hstable : (prefixWord ++ tailWord_409319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409319).length < 2 ^ (prefixWord ++ tailWord_409319).sum := by decide
  have hdescent : baseEnd_409319 < baseStart_409319 := by decide
  rcases family_descends (prefixWord ++ tailWord_409319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409345 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_409345 : Nat := 118140960795 + 409345 * 2 ^ 59
def prefixEnd_409345 : Nat := 4983230072969 + 3 ^ 40 * 409345 * 2
def baseEnd_409345 : Nat := 140127159009870779669975

theorem tailTrace_409345 : CollatzResearch.WordTrace tailWord_409345 prefixEnd_409345 140127159009870779669975 := by
  unfold tailWord_409345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930038702020450405245489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9953359134680300270163659 14930038702020450405245489)
  ·
    refine ⟨11197529026515337803934117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14930038702020450405245489 11197529026515337803934117)
    ·
      refine ⟨2099536692471625838237647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11197529026515337803934117 2099536692471625838237647)
      ·
        refine ⟨3149305038707438757356471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099536692471625838237647 3149305038707438757356471)
        ·
          refine ⟨4723957558061158136034707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149305038707438757356471 4723957558061158136034707)
          ·
            refine ⟨7085936337091737204052061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723957558061158136034707 7085936337091737204052061)
            ·
              refine ⟨2657226126409401451519523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085936337091737204052061 2657226126409401451519523)
              ·
                refine ⟨3985839189614102177279285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657226126409401451519523 3985839189614102177279285)
                ·
                  refine ⟨373672424026322079119933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3985839189614102177279285 373672424026322079119933)
                  ·
                    refine ⟨140127159009870779669975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373672424026322079119933 140127159009870779669975)
                    ·
                      rfl

theorem cell22_409345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_409345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409345 prefixEnd_409345 := by exact prefixLift 409345
  have htrace : WordTrace (prefixWord ++ tailWord_409345) baseStart_409345 baseEnd_409345 := by
    simpa [prefixWord, tailWord_409345, baseEnd_409345] using wordTrace_append hprefix tailTrace_409345
  have hstable : (prefixWord ++ tailWord_409345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409345).length < 2 ^ (prefixWord ++ tailWord_409345).sum := by decide
  have hdescent : baseEnd_409345 < baseStart_409345 := by decide
  rcases family_descends (prefixWord ++ tailWord_409345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409364 : List Nat := [2, 4, 4, 1, 1, 1, 9]
def baseStart_409364 : Nat := 118140960795 + 409364 * 2 ^ 59
def prefixEnd_409364 : Nat := 4983230072969 + 3 ^ 40 * 409364 * 2
def baseEnd_409364 : Nat := 5190135670302261609071

theorem tailTrace_409364 : CollatzResearch.WordTrace tailWord_409364 prefixEnd_409364 5190135670302261609071 := by
  unfold tailWord_409364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465365844475808325093573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9953821125967744433458097 7465365844475808325093573)
  ·
    refine ⟨1399756095839214060955045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7465365844475808325093573 1399756095839214060955045)
    ·
      refine ⟨262454267969852636429071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1399756095839214060955045 262454267969852636429071)
      ·
        refine ⟨393681401954778954643607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262454267969852636429071 393681401954778954643607)
        ·
          refine ⟨590522102932168431965411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393681401954778954643607 590522102932168431965411)
          ·
            refine ⟨885783154398252647948117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590522102932168431965411 885783154398252647948117)
            ·
              refine ⟨5190135670302261609071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 885783154398252647948117 5190135670302261609071)
              ·
                rfl

theorem cell22_409364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 9].length) (baseStart_409364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409364 prefixEnd_409364 := by exact prefixLift 409364
  have htrace : WordTrace (prefixWord ++ tailWord_409364) baseStart_409364 baseEnd_409364 := by
    simpa [prefixWord, tailWord_409364, baseEnd_409364] using wordTrace_append hprefix tailTrace_409364
  have hstable : (prefixWord ++ tailWord_409364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409364).length < 2 ^ (prefixWord ++ tailWord_409364).sum := by decide
  have hdescent : baseEnd_409364 < baseStart_409364 := by decide
  rcases family_descends (prefixWord ++ tailWord_409364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409482 : List Nat := [3, 1, 2, 4, 3, 9]
def baseStart_409482 : Nat := 118140960795 + 409482 * 2 ^ 59
def prefixEnd_409482 : Nat := 4983230072969 + 3 ^ 40 * 409482 * 2
def baseEnd_409482 : Nat := 1730543912464791222155

theorem tailTrace_409482 : CollatzResearch.WordTrace tailWord_409482 prefixEnd_409482 1730543912464791222155 := by
  unfold tailWord_409482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733758875631030700745675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9956690335016081868655133 3733758875631030700745675)
  ·
    refine ⟨5600638313446546051118513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733758875631030700745675 5600638313446546051118513)
    ·
      refine ⟨4200478735084909538338885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5600638313446546051118513 4200478735084909538338885)
      ·
        refine ⟨787589762828420538438541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4200478735084909538338885 787589762828420538438541)
        ·
          refine ⟨295346161060657701914453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787589762828420538438541 295346161060657701914453)
          ·
            refine ⟨1730543912464791222155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 295346161060657701914453 1730543912464791222155)
            ·
              rfl

theorem cell22_409482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 9].length) (baseStart_409482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409482 prefixEnd_409482 := by exact prefixLift 409482
  have htrace : WordTrace (prefixWord ++ tailWord_409482) baseStart_409482 baseEnd_409482 := by
    simpa [prefixWord, tailWord_409482, baseEnd_409482] using wordTrace_append hprefix tailTrace_409482
  have hstable : (prefixWord ++ tailWord_409482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409482).length < 2 ^ (prefixWord ++ tailWord_409482).sum := by decide
  have hdescent : baseEnd_409482 < baseStart_409482 := by decide
  rcases family_descends (prefixWord ++ tailWord_409482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409495 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_409495 : Nat := 118140960795 + 409495 * 2 ^ 59
def prefixEnd_409495 : Nat := 4983230072969 + 3 ^ 40 * 409495 * 2
def baseEnd_409495 : Nat := 140178507075320388419515

theorem tailTrace_409495 : CollatzResearch.WordTrace tailWord_409495 prefixEnd_409495 140178507075320388419515 := by
  unfold tailWord_409495
  simp only [CollatzResearch.WordTrace]
  refine ⟨14935509651477026023205939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9957006434318017348803959 14935509651477026023205939)
  ·
    refine ⟨22403264477215539034808909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14935509651477026023205939 22403264477215539034808909)
    ·
      refine ⟨8401224178955827138053341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22403264477215539034808909 8401224178955827138053341)
      ·
        refine ⟨3150459067108435176770003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8401224178955827138053341 3150459067108435176770003)
        ·
          refine ⟨4725688600662652765155005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150459067108435176770003 4725688600662652765155005)
          ·
            refine ⟨1772133225248494786933127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4725688600662652765155005 1772133225248494786933127)
            ·
              refine ⟨2658199837872742180399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772133225248494786933127 2658199837872742180399691)
              ·
                refine ⟨3987299756809113270599537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658199837872742180399691 3987299756809113270599537)
                ·
                  refine ⟨2990474817606834952949653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987299756809113270599537 2990474817606834952949653)
                  ·
                    refine ⟨140178507075320388419515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2990474817606834952949653 140178507075320388419515)
                    ·
                      rfl

theorem cell22_409495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_409495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409495 prefixEnd_409495 := by exact prefixLift 409495
  have htrace : WordTrace (prefixWord ++ tailWord_409495) baseStart_409495 baseEnd_409495 := by
    simpa [prefixWord, tailWord_409495, baseEnd_409495] using wordTrace_append hprefix tailTrace_409495
  have hstable : (prefixWord ++ tailWord_409495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409495).length < 2 ^ (prefixWord ++ tailWord_409495).sum := by decide
  have hdescent : baseEnd_409495 < baseStart_409495 := by decide
  rcases family_descends (prefixWord ++ tailWord_409495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409544 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_409544 : Nat := 118140960795 + 409544 * 2 ^ 59
def prefixEnd_409544 : Nat := 4983230072969 + 3 ^ 40 * 409544 * 2
def baseEnd_409544 : Nat := 46731760258900197981455

theorem tailTrace_409544 : CollatzResearch.WordTrace tailWord_409544 prefixEnd_409544 46731760258900197981455 := by
  unfold tailWord_409544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468648414149753695869843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9958197885533004927826457 7468648414149753695869843)
  ·
    refine ⟨11202972621224630543804765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468648414149753695869843 11202972621224630543804765)
    ·
      refine ⟨4201114732959236453926787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11202972621224630543804765 4201114732959236453926787)
      ·
        refine ⟨6301672099438854680890181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201114732959236453926787 6301672099438854680890181)
        ·
          refine ⟨1181563518644785252666909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6301672099438854680890181 1181563518644785252666909)
          ·
            refine ⟨443086319491794469750091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1181563518644785252666909 443086319491794469750091)
            ·
              refine ⟨664629479237691704625137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443086319491794469750091 664629479237691704625137)
              ·
                refine ⟨498472109428268778468853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664629479237691704625137 498472109428268778468853)
                ·
                  refine ⟨46731760258900197981455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498472109428268778468853 46731760258900197981455)
                  ·
                    rfl

theorem cell22_409544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_409544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409544 prefixEnd_409544 := by exact prefixLift 409544
  have htrace : WordTrace (prefixWord ++ tailWord_409544) baseStart_409544 baseEnd_409544 := by
    simpa [prefixWord, tailWord_409544, baseEnd_409544] using wordTrace_append hprefix tailTrace_409544
  have hstable : (prefixWord ++ tailWord_409544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409544).length < 2 ^ (prefixWord ++ tailWord_409544).sum := by decide
  have hdescent : baseEnd_409544 < baseStart_409544 := by decide
  rcases family_descends (prefixWord ++ tailWord_409544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409621 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_409621 : Nat := 118140960795 + 409621 * 2 ^ 59
def prefixEnd_409621 : Nat := 4983230072969 + 3 ^ 40 * 409621 * 2
def baseEnd_409621 : Nat := 140221639450298059769129

theorem tailTrace_409621 : CollatzResearch.WordTrace tailWord_409621 prefixEnd_409621 140221639450298059769129 := by
  unfold tailWord_409621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940105249020549542292717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960070166013699694861811 14940105249020549542292717)
  ·
    refine ⟨5602539468382706078359769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14940105249020549542292717 5602539468382706078359769)
    ·
      refine ⟨4201904601287029558769827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5602539468382706078359769 4201904601287029558769827)
      ·
        refine ⟨6302856901930544338154741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201904601287029558769827 6302856901930544338154741)
        ·
          refine ⟨590892834555988531702007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6302856901930544338154741 590892834555988531702007)
          ·
            refine ⟨886339251833982797553011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590892834555988531702007 886339251833982797553011)
            ·
              refine ⟨1329508877750974196329517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886339251833982797553011 1329508877750974196329517)
              ·
                refine ⟨498565829156615323623569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329508877750974196329517 498565829156615323623569)
                ·
                  refine ⟨373924371867461492717677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498565829156615323623569 373924371867461492717677)
                  ·
                    refine ⟨140221639450298059769129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373924371867461492717677 140221639450298059769129)
                    ·
                      rfl

theorem cell22_409621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_409621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409621 prefixEnd_409621 := by exact prefixLift 409621
  have htrace : WordTrace (prefixWord ++ tailWord_409621) baseStart_409621 baseEnd_409621 := by
    simpa [prefixWord, tailWord_409621, baseEnd_409621] using wordTrace_append hprefix tailTrace_409621
  have hstable : (prefixWord ++ tailWord_409621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409621).length < 2 ^ (prefixWord ++ tailWord_409621).sum := by decide
  have hdescent : baseEnd_409621 < baseStart_409621 := by decide
  rcases family_descends (prefixWord ++ tailWord_409621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409636 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_409636 : Nat := 118140960795 + 409636 * 2 ^ 59
def prefixEnd_409636 : Nat := 4983230072969 + 3 ^ 40 * 409636 * 2
def baseEnd_409636 : Nat := 140226774256843020644083

theorem tailTrace_409636 : CollatzResearch.WordTrace tailWord_409636 prefixEnd_409636 140226774256843020644083 := by
  unfold tailWord_409636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470326171983103552044381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9960434895977471402725841 7470326171983103552044381)
  ·
    refine ⟨2801372314493663832016643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7470326171983103552044381 2801372314493663832016643)
    ·
      refine ⟨4202058471740495748024965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801372314493663832016643 4202058471740495748024965)
      ·
        refine ⟨787885963451342952754681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4202058471740495748024965 787885963451342952754681)
        ·
          refine ⟨590914472588507214566011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787885963451342952754681 590914472588507214566011)
          ·
            refine ⟨886371708882760821849017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590914472588507214566011 886371708882760821849017)
            ·
              refine ⟨664778781662070616386763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886371708882760821849017 664778781662070616386763)
              ·
                refine ⟨997168172493105924580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664778781662070616386763 997168172493105924580145)
                ·
                  refine ⟨747876129369829443435109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 997168172493105924580145 747876129369829443435109)
                  ·
                    refine ⟨140226774256843020644083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 747876129369829443435109 140226774256843020644083)
                    ·
                      rfl

theorem cell22_409636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_409636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409636 prefixEnd_409636 := by exact prefixLift 409636
  have htrace : WordTrace (prefixWord ++ tailWord_409636) baseStart_409636 baseEnd_409636 := by
    simpa [prefixWord, tailWord_409636, baseEnd_409636] using wordTrace_append hprefix tailTrace_409636
  have hstable : (prefixWord ++ tailWord_409636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409636).length < 2 ^ (prefixWord ++ tailWord_409636).sum := by decide
  have hdescent : baseEnd_409636 < baseStart_409636 := by decide
  rcases family_descends (prefixWord ++ tailWord_409636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409724 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_409724 : Nat := 118140960795 + 409724 * 2 ^ 59
def prefixEnd_409724 : Nat := 4983230072969 + 3 ^ 40 * 409724 * 2
def baseEnd_409724 : Nat := 46752299485080041481271

theorem tailTrace_409724 : CollatzResearch.WordTrace tailWord_409724 prefixEnd_409724 46752299485080041481271 := by
  unfold tailWord_409724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471930983823699066646113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9962574645098265422194817 7471930983823699066646113)
  ·
    refine ⟨5603948237867774299984585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7471930983823699066646113 5603948237867774299984585)
    ·
      refine ⟨4202961178400830724988439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5603948237867774299984585 4202961178400830724988439)
      ·
        refine ⟨6304441767601246087482659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202961178400830724988439 6304441767601246087482659)
        ·
          refine ⟨9456662651401869131223989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304441767601246087482659 9456662651401869131223989)
          ·
            refine ⟨886562123568925231052249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9456662651401869131223989 886562123568925231052249)
            ·
              refine ⟨664921592676693923289187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886562123568925231052249 664921592676693923289187)
              ·
                refine ⟨997382389015040884933781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664921592676693923289187 997382389015040884933781)
                ·
                  refine ⟨46752299485080041481271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997382389015040884933781 46752299485080041481271)
                  ·
                    rfl

theorem cell22_409724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_409724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409724 prefixEnd_409724 := by exact prefixLift 409724
  have htrace : WordTrace (prefixWord ++ tailWord_409724) baseStart_409724 baseEnd_409724 := by
    simpa [prefixWord, tailWord_409724, baseEnd_409724] using wordTrace_append hprefix tailTrace_409724
  have hstable : (prefixWord ++ tailWord_409724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409724).length < 2 ^ (prefixWord ++ tailWord_409724).sum := by decide
  have hdescent : baseEnd_409724 < baseStart_409724 := by decide
  rcases family_descends (prefixWord ++ tailWord_409724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409737 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_409737 : Nat := 118140960795 + 409737 * 2 ^ 59
def prefixEnd_409737 : Nat := 4983230072969 + 3 ^ 40 * 409737 * 2
def baseEnd_409737 : Nat := 140261348620912423868773

theorem tailTrace_409737 : CollatzResearch.WordTrace tailWord_409737 prefixEnd_409737 140261348620912423868773 := by
  unfold tailWord_409737
  simp only [CollatzResearch.WordTrace]
  refine ⟨14944336116600301353515465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9962890744400200902343643 14944336116600301353515465)
  ·
    refine ⟨11208252087450226015136599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14944336116600301353515465 11208252087450226015136599)
    ·
      refine ⟨16812378131175339022704899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208252087450226015136599 16812378131175339022704899)
      ·
        refine ⟨25218567196763008534057349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16812378131175339022704899 25218567196763008534057349)
        ·
          refine ⟨4728481349393064100135753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25218567196763008534057349 4728481349393064100135753)
          ·
            refine ⟨3546361012044798075101815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4728481349393064100135753 3546361012044798075101815)
            ·
              refine ⟨5319541518067197112652723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546361012044798075101815 5319541518067197112652723)
              ·
                refine ⟨7979312277100795668979085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319541518067197112652723 7979312277100795668979085)
                ·
                  refine ⟨2992242103912798375867157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979312277100795668979085 2992242103912798375867157)
                  ·
                    refine ⟨140261348620912423868773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2992242103912798375867157 140261348620912423868773)
                    ·
                      rfl

theorem cell22_409737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_409737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409737 prefixEnd_409737 := by exact prefixLift 409737
  have htrace : WordTrace (prefixWord ++ tailWord_409737) baseStart_409737 baseEnd_409737 := by
    simpa [prefixWord, tailWord_409737, baseEnd_409737] using wordTrace_append hprefix tailTrace_409737
  have hstable : (prefixWord ++ tailWord_409737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409737).length < 2 ^ (prefixWord ++ tailWord_409737).sum := by decide
  have hdescent : baseEnd_409737 < baseStart_409737 := by decide
  rcases family_descends (prefixWord ++ tailWord_409737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409826 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_409826 : Nat := 118140960795 + 409826 * 2 ^ 59
def prefixEnd_409826 : Nat := 4983230072969 + 3 ^ 40 * 409826 * 2
def baseEnd_409826 : Nat := 46763938379915286131167

theorem tailTrace_409826 : CollatzResearch.WordTrace tailWord_409826 prefixEnd_409826 46763938379915286131167 := by
  unfold tailWord_409826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736895553319467388376333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9965054808851913035670221 3736895553319467388376333)
  ·
    refine ⟨1401335832494800270641125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3736895553319467388376333 1401335832494800270641125)
    ·
      refine ⟨262750468592775050745211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1401335832494800270641125 262750468592775050745211)
      ·
        refine ⟨394125702889162576117817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262750468592775050745211 394125702889162576117817)
        ·
          refine ⟨295594277166871932088363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394125702889162576117817 295594277166871932088363)
          ·
            refine ⟨443391415750307898132545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295594277166871932088363 443391415750307898132545)
            ·
              refine ⟨332543561812730923599409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443391415750307898132545 332543561812730923599409)
              ·
                refine ⟨249407671359548192699557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332543561812730923599409 249407671359548192699557)
                ·
                  refine ⟨46763938379915286131167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249407671359548192699557 46763938379915286131167)
                  ·
                    rfl

theorem cell22_409826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_409826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409826 prefixEnd_409826 := by exact prefixLift 409826
  have htrace : WordTrace (prefixWord ++ tailWord_409826) baseStart_409826 baseEnd_409826 := by
    simpa [prefixWord, tailWord_409826, baseEnd_409826] using wordTrace_append hprefix tailTrace_409826
  have hstable : (prefixWord ++ tailWord_409826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409826).length < 2 ^ (prefixWord ++ tailWord_409826).sum := by decide
  have hdescent : baseEnd_409826 < baseStart_409826 := by decide
  rcases family_descends (prefixWord ++ tailWord_409826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409831 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 5]
def baseStart_409831 : Nat := 118140960795 + 409831 * 2 ^ 59
def prefixEnd_409831 : Nat := 4983230072969 + 3 ^ 40 * 409831 * 2
def baseEnd_409831 : Nat := 46764508913975837339495

theorem tailTrace_409831 : CollatzResearch.WordTrace tailWord_409831 prefixEnd_409831 46764508913975837339495 := by
  unfold tailWord_409831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947764578259755407437347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9965176385506503604958231 14947764578259755407437347)
  ·
    refine ⟨22421646867389633111156021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947764578259755407437347 22421646867389633111156021)
    ·
      refine ⟨2102029393817778104170877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22421646867389633111156021 2102029393817778104170877)
      ·
        refine ⟨788261022681666789064079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2102029393817778104170877 788261022681666789064079)
        ·
          refine ⟨1182391534022500183596119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788261022681666789064079 1182391534022500183596119)
          ·
            refine ⟨1773587301033750275394179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182391534022500183596119 1773587301033750275394179)
            ·
              refine ⟨2660380951550625413091269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773587301033750275394179 2660380951550625413091269)
              ·
                refine ⟨498821428415742264954613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2660380951550625413091269 498821428415742264954613)
                ·
                  refine ⟨46764508913975837339495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498821428415742264954613 46764508913975837339495)
                  ·
                    rfl

theorem cell22_409831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].length) (baseStart_409831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409831 prefixEnd_409831 := by exact prefixLift 409831
  have htrace : WordTrace (prefixWord ++ tailWord_409831) baseStart_409831 baseEnd_409831 := by
    simpa [prefixWord, tailWord_409831, baseEnd_409831] using wordTrace_append hprefix tailTrace_409831
  have hstable : (prefixWord ++ tailWord_409831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409831).length < 2 ^ (prefixWord ++ tailWord_409831).sum := by decide
  have hdescent : baseEnd_409831 < baseStart_409831 := by decide
  rcases family_descends (prefixWord ++ tailWord_409831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409859 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 6]
def baseStart_409859 : Nat := 118140960795 + 409859 * 2 ^ 59
def prefixEnd_409859 : Nat := 4983230072969 + 3 ^ 40 * 409859 * 2
def baseEnd_409859 : Nat := 46767703904714924106133

theorem tailTrace_409859 : CollatzResearch.WordTrace tailWord_409859 prefixEnd_409859 46767703904714924106133 := by
  unfold tailWord_409859
  simp only [CollatzResearch.WordTrace]
  refine ⟨14948785822158316189456631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9965857214772210792971087 14948785822158316189456631)
  ·
    refine ⟨22423178733237474284184947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14948785822158316189456631 22423178733237474284184947)
    ·
      refine ⟨33634768099856211426277421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22423178733237474284184947 33634768099856211426277421)
      ·
        refine ⟨12613038037446079284854033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33634768099856211426277421 12613038037446079284854033)
        ·
          refine ⟨9459778528084559463640525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12613038037446079284854033 9459778528084559463640525)
          ·
            refine ⟨3547416948031709798865197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9459778528084559463640525 3547416948031709798865197)
            ·
              refine ⟨1330281355511891174574449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547416948031709798865197 1330281355511891174574449)
              ·
                refine ⟨997711016633918380930837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330281355511891174574449 997711016633918380930837)
                ·
                  refine ⟨46767703904714924106133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997711016633918380930837 46767703904714924106133)
                  ·
                    rfl

theorem cell22_409859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_409859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409859 prefixEnd_409859 := by exact prefixLift 409859
  have htrace : WordTrace (prefixWord ++ tailWord_409859) baseStart_409859 baseEnd_409859 := by
    simpa [prefixWord, tailWord_409859, baseEnd_409859] using wordTrace_append hprefix tailTrace_409859
  have hstable : (prefixWord ++ tailWord_409859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409859).length < 2 ^ (prefixWord ++ tailWord_409859).sum := by decide
  have hdescent : baseEnd_409859 < baseStart_409859 := by decide
  rcases family_descends (prefixWord ++ tailWord_409859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409891 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 4, 3]
def baseStart_409891 : Nat := 118140960795 + 409891 * 2 ^ 59
def prefixEnd_409891 : Nat := 4983230072969 + 3 ^ 40 * 409891 * 2
def baseEnd_409891 : Nat := 140314065968107355518301

theorem tailTrace_409891 : CollatzResearch.WordTrace tailWord_409891 prefixEnd_409891 140314065968107355518301 := by
  unfold tailWord_409891
  simp only [CollatzResearch.WordTrace]
  refine ⟨14949952958042385654621527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9966635305361590436414351 14949952958042385654621527)
  ·
    refine ⟨22424929437063578481932291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14949952958042385654621527 22424929437063578481932291)
    ·
      refine ⟨33637394155595367722898437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22424929437063578481932291 33637394155595367722898437)
      ·
        refine ⟨6307011404174131448043457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33637394155595367722898437 6307011404174131448043457)
        ·
          refine ⟨4730258553130598586032593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307011404174131448043457 4730258553130598586032593)
          ·
            refine ⟨3547693914847948939524445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730258553130598586032593 3547693914847948939524445)
            ·
              refine ⟨1330385218067980852321667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547693914847948939524445 1330385218067980852321667)
              ·
                refine ⟨1995577827101971278482501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330385218067980852321667 1995577827101971278482501)
                ·
                  refine ⟨374170842581619614715469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995577827101971278482501 374170842581619614715469)
                  ·
                    refine ⟨140314065968107355518301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374170842581619614715469 140314065968107355518301)
                    ·
                      rfl

theorem cell22_409891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].length) (baseStart_409891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409891 prefixEnd_409891 := by exact prefixLift 409891
  have htrace : WordTrace (prefixWord ++ tailWord_409891) baseStart_409891 baseEnd_409891 := by
    simpa [prefixWord, tailWord_409891, baseEnd_409891] using wordTrace_append hprefix tailTrace_409891
  have hstable : (prefixWord ++ tailWord_409891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409891).length < 2 ^ (prefixWord ++ tailWord_409891).sum := by decide
  have hdescent : baseEnd_409891 < baseStart_409891 := by decide
  rcases family_descends (prefixWord ++ tailWord_409891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409908 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_409908 : Nat := 118140960795 + 409908 * 2 ^ 59
def prefixEnd_409908 : Nat := 4983230072969 + 3 ^ 40 * 409908 * 2
def baseEnd_409908 : Nat := 140319885415524977843249

theorem tailTrace_409908 : CollatzResearch.WordTrace tailWord_409908 prefixEnd_409908 140319885415524977843249 := by
  unfold tailWord_409908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475286499490398778995189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9967048665987198371993585 7475286499490398778995189)
  ·
    refine ⟨700808109327224885530799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7475286499490398778995189 700808109327224885530799)
    ·
      refine ⟨1051212163990837328296199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700808109327224885530799 1051212163990837328296199)
      ·
        refine ⟨1576818245986255992444299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051212163990837328296199 1576818245986255992444299)
        ·
          refine ⟨2365227368979383988666449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576818245986255992444299 2365227368979383988666449)
          ·
            refine ⟨1773920526734537991499837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365227368979383988666449 1773920526734537991499837)
            ·
              refine ⟨665220197525451746812439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773920526734537991499837 665220197525451746812439)
              ·
                refine ⟨997830296288177620218659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665220197525451746812439 997830296288177620218659)
                ·
                  refine ⟨1496745444432266430327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997830296288177620218659 1496745444432266430327989)
                  ·
                    refine ⟨140319885415524977843249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1496745444432266430327989 140319885415524977843249)
                    ·
                      rfl

theorem cell22_409908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_409908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409908 prefixEnd_409908 := by exact prefixLift 409908
  have htrace : WordTrace (prefixWord ++ tailWord_409908) baseStart_409908 baseEnd_409908 := by
    simpa [prefixWord, tailWord_409908, baseEnd_409908] using wordTrace_append hprefix tailTrace_409908
  have hstable : (prefixWord ++ tailWord_409908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409908).length < 2 ^ (prefixWord ++ tailWord_409908).sum := by decide
  have hdescent : baseEnd_409908 < baseStart_409908 := by decide
  rcases family_descends (prefixWord ++ tailWord_409908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409919 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_409919 : Nat := 118140960795 + 409919 * 2 ^ 59
def prefixEnd_409919 : Nat := 4983230072969 + 3 ^ 40 * 409919 * 2
def baseEnd_409919 : Nat := 140323650940324615818215

theorem tailTrace_409919 : CollatzResearch.WordTrace tailWord_409919 prefixEnd_409919 140323650940324615818215 := by
  unfold tailWord_409919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14950974201940946436640811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9967316134627297624427207 14950974201940946436640811)
  ·
    refine ⟨22426461302911419654961217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14950974201940946436640811 22426461302911419654961217)
    ·
      refine ⟨16819845977183564741220913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22426461302911419654961217 16819845977183564741220913)
      ·
        refine ⟨12614884482887673555915685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16819845977183564741220913 12614884482887673555915685)
        ·
          refine ⟨2365290840541438791734191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12614884482887673555915685 2365290840541438791734191)
          ·
            refine ⟨3547936260812158187601287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365290840541438791734191 3547936260812158187601287)
            ·
              refine ⟨5321904391218237281401931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547936260812158187601287 5321904391218237281401931)
              ·
                refine ⟨7982856586827355922102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321904391218237281401931 7982856586827355922102897)
                ·
                  refine ⟨5987142440120516941577173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982856586827355922102897 5987142440120516941577173)
                  ·
                    refine ⟨140323650940324615818215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5987142440120516941577173 140323650940324615818215)
                    ·
                      rfl

theorem cell22_409919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_409919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_409919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_409919 prefixEnd_409919 := by exact prefixLift 409919
  have htrace : WordTrace (prefixWord ++ tailWord_409919) baseStart_409919 baseEnd_409919 := by
    simpa [prefixWord, tailWord_409919, baseEnd_409919] using wordTrace_append hprefix tailTrace_409919
  have hstable : (prefixWord ++ tailWord_409919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409919).length < 2 ^ (prefixWord ++ tailWord_409919).sum := by decide
  have hdescent : baseEnd_409919 < baseStart_409919 := by decide
  rcases family_descends (prefixWord ++ tailWord_409919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410045 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 4]
def baseStart_410045 : Nat := 118140960795 + 410045 * 2 ^ 59
def prefixEnd_410045 : Nat := 4983230072969 + 3 ^ 40 * 410045 * 2
def baseEnd_410045 : Nat := 46788927771767429055943

theorem tailTrace_410045 : CollatzResearch.WordTrace tailWord_410045 prefixEnd_410045 46788927771767429055943 := by
  unfold tailWord_410045
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955569799484469955727589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9970379866322979970485059 14955569799484469955727589)
  ·
    refine ⟨2804169337403338116698923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14955569799484469955727589 2804169337403338116698923)
    ·
      refine ⟨4206254006105007175048385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804169337403338116698923 4206254006105007175048385)
      ·
        refine ⟨3154690504578755381286289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4206254006105007175048385 3154690504578755381286289)
        ·
          refine ⟨2366017878434066535964717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3154690504578755381286289 2366017878434066535964717)
          ·
            refine ⟨887256704412774950986769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2366017878434066535964717 887256704412774950986769)
            ·
              refine ⟨665442528309581213240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887256704412774950986769 665442528309581213240077)
              ·
                refine ⟨249540948116092954965029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665442528309581213240077 249540948116092954965029)
                ·
                  refine ⟨46788927771767429055943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249540948116092954965029 46788927771767429055943)
                  ·
                    rfl

theorem cell22_410045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_410045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410045 prefixEnd_410045 := by exact prefixLift 410045
  have htrace : WordTrace (prefixWord ++ tailWord_410045) baseStart_410045 baseEnd_410045 := by
    simpa [prefixWord, tailWord_410045, baseEnd_410045] using wordTrace_append hprefix tailTrace_410045
  have hstable : (prefixWord ++ tailWord_410045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410045).length < 2 ^ (prefixWord ++ tailWord_410045).sum := by decide
  have hdescent : baseEnd_410045 < baseStart_410045 := by decide
  rcases family_descends (prefixWord ++ tailWord_410045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410056 : List Nat := [2, 1, 3, 1, 3, 3, 9]
def baseStart_410056 : Nat := 118140960795 + 410056 * 2 ^ 59
def prefixEnd_410056 : Nat := 4983230072969 + 3 ^ 40 * 410056 * 2
def baseEnd_410056 : Nat := 5198909216300071301585

theorem tailTrace_410056 : CollatzResearch.WordTrace tailWord_410056 prefixEnd_410056 5198909216300071301585 := by
  unfold tailWord_410056
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477985501222309417189011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9970647334963079222918681 7477985501222309417189011)
  ·
    refine ⟨11216978251833464125783517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477985501222309417189011 11216978251833464125783517)
    ·
      refine ⟨4206366844437549047168819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11216978251833464125783517 4206366844437549047168819)
      ·
        refine ⟨6309550266656323570753229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206366844437549047168819 6309550266656323570753229)
        ·
          refine ⟨2366081349996121339032461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309550266656323570753229 2366081349996121339032461)
          ·
            refine ⟨887280506248545502137173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2366081349996121339032461 887280506248545502137173)
            ·
              refine ⟨5198909216300071301585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 887280506248545502137173 5198909216300071301585)
              ·
                rfl

theorem cell22_410056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 9].length) (baseStart_410056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410056 prefixEnd_410056 := by exact prefixLift 410056
  have htrace : WordTrace (prefixWord ++ tailWord_410056) baseStart_410056 baseEnd_410056 := by
    simpa [prefixWord, tailWord_410056, baseEnd_410056] using wordTrace_append hprefix tailTrace_410056
  have hstable : (prefixWord ++ tailWord_410056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410056).length < 2 ^ (prefixWord ++ tailWord_410056).sum := by decide
  have hdescent : baseEnd_410056 < baseStart_410056 := by decide
  rcases family_descends (prefixWord ++ tailWord_410056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410060 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_410060 : Nat := 118140960795 + 410060 * 2 ^ 59
def prefixEnd_410060 : Nat := 4983230072969 + 3 ^ 40 * 410060 * 2
def baseEnd_410060 : Nat := 140371918121847248042783

theorem tailTrace_410060 : CollatzResearch.WordTrace tailWord_410060 prefixEnd_410060 140371918121847248042783 := by
  unfold tailWord_410060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478058447215063758761817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9970744596286751678349089 7478058447215063758761817)
  ·
    refine ⟨5608543835411297819071363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7478058447215063758761817 5608543835411297819071363)
    ·
      refine ⟨8412815753116946728607045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5608543835411297819071363 8412815753116946728607045)
      ·
        refine ⟨1577402953709427511613821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8412815753116946728607045 1577402953709427511613821)
        ·
          refine ⟨591526107641035316855183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577402953709427511613821 591526107641035316855183)
          ·
            refine ⟨887289161461552975282775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591526107641035316855183 887289161461552975282775)
            ·
              refine ⟨1330933742192329462924163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887289161461552975282775 1330933742192329462924163)
              ·
                refine ⟨1996400613288494194386245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330933742192329462924163 1996400613288494194386245)
                ·
                  refine ⟨374325114991592661447421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996400613288494194386245 374325114991592661447421)
                  ·
                    refine ⟨140371918121847248042783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374325114991592661447421 140371918121847248042783)
                    ·
                      rfl

theorem cell22_410060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_410060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410060 prefixEnd_410060 := by exact prefixLift 410060
  have htrace : WordTrace (prefixWord ++ tailWord_410060) baseStart_410060 baseEnd_410060 := by
    simpa [prefixWord, tailWord_410060, baseEnd_410060] using wordTrace_append hprefix tailTrace_410060
  have hstable : (prefixWord ++ tailWord_410060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410060).length < 2 ^ (prefixWord ++ tailWord_410060).sum := by decide
  have hdescent : baseEnd_410060 < baseStart_410060 := by decide
  rcases family_descends (prefixWord ++ tailWord_410060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410077 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_410077 : Nat := 118140960795 + 410077 * 2 ^ 59
def prefixEnd_410077 : Nat := 4983230072969 + 3 ^ 40 * 410077 * 2
def baseEnd_410077 : Nat := 140377737569264870367731

theorem tailTrace_410077 : CollatzResearch.WordTrace tailWord_410077 prefixEnd_410077 140377737569264870367731 := by
  unfold tailWord_410077
  simp only [CollatzResearch.WordTrace]
  refine ⟨14956736935368539420892485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9971157956912359613928323 14956736935368539420892485)
  ·
    refine ⟨2804388175381601141417341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14956736935368539420892485 2804388175381601141417341)
    ·
      refine ⟨1051645565768100428031503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2804388175381601141417341 1051645565768100428031503)
      ·
        refine ⟨1577468348652150642047255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051645565768100428031503 1577468348652150642047255)
        ·
          refine ⟨2366202522978225963070883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577468348652150642047255 2366202522978225963070883)
          ·
            refine ⟨3549303784467338944606325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366202522978225963070883 3549303784467338944606325)
            ·
              refine ⟨332747229793813026056843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3549303784467338944606325 332747229793813026056843)
              ·
                refine ⟨499120844690719539085265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332747229793813026056843 499120844690719539085265)
                ·
                  refine ⟨374340633518039654313949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499120844690719539085265 374340633518039654313949)
                  ·
                    refine ⟨140377737569264870367731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374340633518039654313949 140377737569264870367731)
                    ·
                      rfl

theorem cell22_410077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_410077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410077 prefixEnd_410077 := by exact prefixLift 410077
  have htrace : WordTrace (prefixWord ++ tailWord_410077) baseStart_410077 baseEnd_410077 := by
    simpa [prefixWord, tailWord_410077, baseEnd_410077] using wordTrace_append hprefix tailTrace_410077
  have hstable : (prefixWord ++ tailWord_410077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410077).length < 2 ^ (prefixWord ++ tailWord_410077).sum := by decide
  have hdescent : baseEnd_410077 < baseStart_410077 := by decide
  rcases family_descends (prefixWord ++ tailWord_410077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410090 : List Nat := [3, 1, 3, 1, 3, 3, 2, 6]
def baseStart_410090 : Nat := 118140960795 + 410090 * 2 ^ 59
def prefixEnd_410090 : Nat := 4983230072969 + 3 ^ 40 * 410090 * 2
def baseEnd_410090 : Nat := 15598020859437463310299

theorem tailTrace_410090 : CollatzResearch.WordTrace tailWord_410090 prefixEnd_410090 15598020859437463310299 := by
  unfold tailWord_410090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739302771080360660278931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9971474056214295094077149 3739302771080360660278931)
  ·
    refine ⟨5608954156620540990418397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3739302771080360660278931 5608954156620540990418397)
    ·
      refine ⟨2103357808732702871406899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5608954156620540990418397 2103357808732702871406899)
      ·
        refine ⟨3155036713099054307110349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103357808732702871406899 3155036713099054307110349)
        ·
          refine ⟨1183138767412145365166381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155036713099054307110349 1183138767412145365166381)
          ·
            refine ⟨443677037779554511937393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183138767412145365166381 443677037779554511937393)
            ·
              refine ⟨332757778334665883953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443677037779554511937393 332757778334665883953045)
              ·
                refine ⟨15598020859437463310299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 332757778334665883953045 15598020859437463310299)
                ·
                  rfl

theorem cell22_410090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_410090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410090 prefixEnd_410090 := by exact prefixLift 410090
  have htrace : WordTrace (prefixWord ++ tailWord_410090) baseStart_410090 baseEnd_410090 := by
    simpa [prefixWord, tailWord_410090, baseEnd_410090] using wordTrace_append hprefix tailTrace_410090
  have hstable : (prefixWord ++ tailWord_410090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410090).length < 2 ^ (prefixWord ++ tailWord_410090).sum := by decide
  have hdescent : baseEnd_410090 < baseStart_410090 := by decide
  rcases family_descends (prefixWord ++ tailWord_410090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410182 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_410182 : Nat := 118140960795 + 410182 * 2 ^ 59
def prefixEnd_410182 : Nat := 4983230072969 + 3 ^ 40 * 410182 * 2
def baseEnd_410182 : Nat := 140413681215079596492409

theorem tailTrace_410182 : CollatzResearch.WordTrace tailWord_410182 prefixEnd_410182 140413681215079596492409 := by
  unfold tailWord_410182
  simp only [CollatzResearch.WordTrace]
  refine ⟨467517706249629448545775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9973711066658761568976533 467517706249629448545775)
  ·
    refine ⟨701276559374444172818663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467517706249629448545775 701276559374444172818663)
    ·
      refine ⟨1051914839061666259227995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701276559374444172818663 1051914839061666259227995)
      ·
        refine ⟨1577872258592499388841993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051914839061666259227995 1577872258592499388841993)
        ·
          refine ⟨1183404193944374541631495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577872258592499388841993 1183404193944374541631495)
          ·
            refine ⟨1775106290916561812447243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183404193944374541631495 1775106290916561812447243)
            ·
              refine ⟨2662659436374842718670865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775106290916561812447243 2662659436374842718670865)
              ·
                refine ⟨1996994577281132039003149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662659436374842718670865 1996994577281132039003149)
                ·
                  refine ⟨748872966480424514626181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1996994577281132039003149 748872966480424514626181)
                  ·
                    refine ⟨140413681215079596492409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 748872966480424514626181 140413681215079596492409)
                    ·
                      rfl

theorem cell22_410182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_410182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410182 prefixEnd_410182 := by exact prefixLift 410182
  have htrace : WordTrace (prefixWord ++ tailWord_410182) baseStart_410182 baseEnd_410182 := by
    simpa [prefixWord, tailWord_410182, baseEnd_410182] using wordTrace_append hprefix tailTrace_410182
  have hstable : (prefixWord ++ tailWord_410182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410182).length < 2 ^ (prefixWord ++ tailWord_410182).sum := by decide
  have hdescent : baseEnd_410182 < baseStart_410182 := by decide
  rcases family_descends (prefixWord ++ tailWord_410182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410216 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_410216 : Nat := 118140960795 + 410216 * 2 ^ 59
def prefixEnd_410216 : Nat := 4983230072969 + 3 ^ 40 * 410216 * 2
def baseEnd_410216 : Nat := 140425320109914841142305

theorem tailTrace_410216 : CollatzResearch.WordTrace tailWord_410216 prefixEnd_410216 140425320109914841142305 := by
  unfold tailWord_410216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480903340932483080101251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9974537787909977440135001 7480903340932483080101251)
  ·
    refine ⟨11221355011398724620151877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480903340932483080101251 11221355011398724620151877)
    ·
      refine ⟨2104004064637260866278477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11221355011398724620151877 2104004064637260866278477)
      ·
        refine ⟨789001524238972824854429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2104004064637260866278477 789001524238972824854429)
        ·
          refine ⟨295875571589614809320411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789001524238972824854429 295875571589614809320411)
          ·
            refine ⟨443813357384422213980617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295875571589614809320411 443813357384422213980617)
            ·
              refine ⟨332860018038316660485463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443813357384422213980617 332860018038316660485463)
              ·
                refine ⟨499290027057474990728195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332860018038316660485463 499290027057474990728195)
                ·
                  refine ⟨748935040586212486092293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499290027057474990728195 748935040586212486092293)
                  ·
                    refine ⟨140425320109914841142305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 748935040586212486092293 140425320109914841142305)
                    ·
                      rfl

theorem cell22_410216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_410216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410216 prefixEnd_410216 := by exact prefixLift 410216
  have htrace : WordTrace (prefixWord ++ tailWord_410216) baseStart_410216 baseEnd_410216 := by
    simpa [prefixWord, tailWord_410216, baseEnd_410216] using wordTrace_append hprefix tailTrace_410216
  have hstable : (prefixWord ++ tailWord_410216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410216).length < 2 ^ (prefixWord ++ tailWord_410216).sum := by decide
  have hdescent : baseEnd_410216 < baseStart_410216 := by decide
  rcases family_descends (prefixWord ++ tailWord_410216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410240 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_410240 : Nat := 118140960795 + 410240 * 2 ^ 59
def prefixEnd_410240 : Nat := 4983230072969 + 3 ^ 40 * 410240 * 2
def baseEnd_410240 : Nat := 140433535800386778542231

theorem tailTrace_410240 : CollatzResearch.WordTrace tailWord_410240 prefixEnd_410240 140433535800386778542231 := by
  unfold tailWord_410240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481341016889009129538087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9975121355852012172717449 7481341016889009129538087)
  ·
    refine ⟨11222011525333513694307131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7481341016889009129538087 11222011525333513694307131)
    ·
      refine ⟨16833017288000270541460697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11222011525333513694307131 16833017288000270541460697)
      ·
        refine ⟨12624762966000202906095523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16833017288000270541460697 12624762966000202906095523)
        ·
          refine ⟨18937144449000304359143285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12624762966000202906095523 18937144449000304359143285)
          ·
            refine ⟨1775357292093778533669683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18937144449000304359143285 1775357292093778533669683)
            ·
              refine ⟨2663035938140667800504525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775357292093778533669683 2663035938140667800504525)
              ·
                refine ⟨998638476802750425189197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2663035938140667800504525 998638476802750425189197)
                ·
                  refine ⟨374489428801031409445949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998638476802750425189197 374489428801031409445949)
                  ·
                    refine ⟨140433535800386778542231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374489428801031409445949 140433535800386778542231)
                    ·
                      rfl

theorem cell22_410240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_410240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410240 prefixEnd_410240 := by exact prefixLift 410240
  have htrace : WordTrace (prefixWord ++ tailWord_410240) baseStart_410240 baseEnd_410240 := by
    simpa [prefixWord, tailWord_410240, baseEnd_410240] using wordTrace_append hprefix tailTrace_410240
  have hstable : (prefixWord ++ tailWord_410240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410240).length < 2 ^ (prefixWord ++ tailWord_410240).sum := by decide
  have hdescent : baseEnd_410240 < baseStart_410240 := by decide
  rcases family_descends (prefixWord ++ tailWord_410240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410270 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_410270 : Nat := 118140960795 + 410270 * 2 ^ 59
def prefixEnd_410270 : Nat := 4983230072969 + 3 ^ 40 * 410270 * 2
def baseEnd_410270 : Nat := 46814601804492233430713

theorem tailTrace_410270 : CollatzResearch.WordTrace tailWord_410270 prefixEnd_410270 46814601804492233430713 := by
  unfold tailWord_410270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870472027958666672833533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9975850815779555588445509 1870472027958666672833533)
  ·
    refine ⟨701427010484500002312575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1870472027958666672833533 701427010484500002312575)
    ·
      refine ⟨1052140515726750003468863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701427010484500002312575 1052140515726750003468863)
      ·
        refine ⟨1578210773590125005203295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052140515726750003468863 1578210773590125005203295)
        ·
          refine ⟨2367316160385187507804943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578210773590125005203295 2367316160385187507804943)
          ·
            refine ⟨3550974240577781261707415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367316160385187507804943 3550974240577781261707415)
            ·
              refine ⟨5326461360866671892561123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550974240577781261707415 5326461360866671892561123)
              ·
                refine ⟨7989692041300007838841685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326461360866671892561123 7989692041300007838841685)
                ·
                  refine ⟨46814601804492233430713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7989692041300007838841685 46814601804492233430713)
                  ·
                    rfl

theorem cell22_410270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_410270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410270 prefixEnd_410270 := by exact prefixLift 410270
  have htrace : WordTrace (prefixWord ++ tailWord_410270) baseStart_410270 baseEnd_410270 := by
    simpa [prefixWord, tailWord_410270, baseEnd_410270] using wordTrace_append hprefix tailTrace_410270
  have hstable : (prefixWord ++ tailWord_410270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410270).length < 2 ^ (prefixWord ++ tailWord_410270).sum := by decide
  have hdescent : baseEnd_410270 < baseStart_410270 := by decide
  rcases family_descends (prefixWord ++ tailWord_410270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410300 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_410300 : Nat := 118140960795 + 410300 * 2 ^ 59
def prefixEnd_410300 : Nat := 4983230072969 + 3 ^ 40 * 410300 * 2
def baseEnd_410300 : Nat := 140454075026566622042047

theorem tailTrace_410300 : CollatzResearch.WordTrace tailWord_410300 prefixEnd_410300 140454075026566622042047 := by
  unfold tailWord_410300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482435206780324253130177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9976580275707099004173569 7482435206780324253130177)
  ·
    refine ⟨5611826405085243189847633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7482435206780324253130177 5611826405085243189847633)
    ·
      refine ⟨4208869803813932392385725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5611826405085243189847633 4208869803813932392385725)
      ·
        refine ⟨1578326176430224647144647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4208869803813932392385725 1578326176430224647144647)
        ·
          refine ⟨2367489264645336970716971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578326176430224647144647 2367489264645336970716971)
          ·
            refine ⟨3551233896968005456075457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367489264645336970716971 3551233896968005456075457)
            ·
              refine ⟨2663425422726004092056593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551233896968005456075457 2663425422726004092056593)
              ·
                refine ⟨1997569067044503069042445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663425422726004092056593 1997569067044503069042445)
                ·
                  refine ⟨749088400141688650890917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1997569067044503069042445 749088400141688650890917)
                  ·
                    refine ⟨140454075026566622042047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749088400141688650890917 140454075026566622042047)
                    ·
                      rfl

theorem cell22_410300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_410300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410300 prefixEnd_410300 := by exact prefixLift 410300
  have htrace : WordTrace (prefixWord ++ tailWord_410300) baseStart_410300 baseEnd_410300 := by
    simpa [prefixWord, tailWord_410300, baseEnd_410300] using wordTrace_append hprefix tailTrace_410300
  have hstable : (prefixWord ++ tailWord_410300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410300).length < 2 ^ (prefixWord ++ tailWord_410300).sum := by decide
  have hdescent : baseEnd_410300 < baseStart_410300 := by decide
  rcases family_descends (prefixWord ++ tailWord_410300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410313 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_410313 : Nat := 118140960795 + 410313 * 2 ^ 59
def prefixEnd_410313 : Nat := 4983230072969 + 3 ^ 40 * 410313 * 2
def baseEnd_410313 : Nat := 140458525192238921467007

theorem tailTrace_410313 : CollatzResearch.WordTrace tailWord_410313 prefixEnd_410313 140458525192238921467007 := by
  unfold tailWord_410313
  simp only [CollatzResearch.WordTrace]
  refine ⟨14965344562513551726483593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9976896375009034484322395 14965344562513551726483593)
  ·
    refine ⟨11224008421885163794862695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14965344562513551726483593 11224008421885163794862695)
    ·
      refine ⟨16836012632827745692294043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11224008421885163794862695 16836012632827745692294043)
      ·
        refine ⟨25254018949241618538441065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836012632827745692294043 25254018949241618538441065)
        ·
          refine ⟨18940514211931213903830799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25254018949241618538441065 18940514211931213903830799)
          ·
            refine ⟨28410771317896820855746199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940514211931213903830799 28410771317896820855746199)
            ·
              refine ⟨42616156976845231283619299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28410771317896820855746199 42616156976845231283619299)
              ·
                refine ⟨63924235465267846925428949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42616156976845231283619299 63924235465267846925428949)
                ·
                  refine ⟨1498224268717215162314741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63924235465267846925428949 1498224268717215162314741)
                  ·
                    refine ⟨140458525192238921467007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1498224268717215162314741 140458525192238921467007)
                    ·
                      rfl

theorem cell22_410313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_410313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410313 prefixEnd_410313 := by exact prefixLift 410313
  have htrace : WordTrace (prefixWord ++ tailWord_410313) baseStart_410313 baseEnd_410313 := by
    simpa [prefixWord, tailWord_410313, baseEnd_410313] using wordTrace_append hprefix tailTrace_410313
  have hstable : (prefixWord ++ tailWord_410313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410313).length < 2 ^ (prefixWord ++ tailWord_410313).sum := by decide
  have hdescent : baseEnd_410313 < baseStart_410313 := by decide
  rcases family_descends (prefixWord ++ tailWord_410313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410330 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_410330 : Nat := 118140960795 + 410330 * 2 ^ 59
def prefixEnd_410330 : Nat := 4983230072969 + 3 ^ 40 * 410330 * 2
def baseEnd_410330 : Nat := 140464344639656543791955

theorem tailTrace_410330 : CollatzResearch.WordTrace tailWord_410330 prefixEnd_410330 140464344639656543791955 := by
  unfold tailWord_410330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741491150862990907463111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9977309735634642419901629 3741491150862990907463111)
  ·
    refine ⟨5612236726294486361194667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741491150862990907463111 5612236726294486361194667)
    ·
      refine ⟨8418355089441729541792001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5612236726294486361194667 8418355089441729541792001)
      ·
        refine ⟨6313766317081297156344001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8418355089441729541792001 6313766317081297156344001)
        ·
          refine ⟨4735324737810972867258001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6313766317081297156344001 4735324737810972867258001)
          ·
            refine ⟨3551493553358229650443501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735324737810972867258001 3551493553358229650443501)
            ·
              refine ⟨1331810082509336118916313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551493553358229650443501 1331810082509336118916313)
              ·
                refine ⟨998857561882002089187235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331810082509336118916313 998857561882002089187235)
                ·
                  refine ⟨1498286342823003133780853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998857561882002089187235 1498286342823003133780853)
                  ·
                    refine ⟨140464344639656543791955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1498286342823003133780853 140464344639656543791955)
                    ·
                      rfl

theorem cell22_410330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_410330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410330 prefixEnd_410330 := by exact prefixLift 410330
  have htrace : WordTrace (prefixWord ++ tailWord_410330) baseStart_410330 baseEnd_410330 := by
    simpa [prefixWord, tailWord_410330, baseEnd_410330] using wordTrace_append hprefix tailTrace_410330
  have hstable : (prefixWord ++ tailWord_410330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410330).length < 2 ^ (prefixWord ++ tailWord_410330).sum := by decide
  have hdescent : baseEnd_410330 < baseStart_410330 := by decide
  rcases family_descends (prefixWord ++ tailWord_410330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410343 : List Nat := [1, 1, 5, 15]
def baseStart_410343 : Nat := 118140960795 + 410343 * 2 ^ 59
def prefixEnd_410343 : Nat := 4983230072969 + 3 ^ 40 * 410343 * 2
def baseEnd_410343 : Nat := 192686961324182226635

theorem tailTrace_410343 : CollatzResearch.WordTrace tailWord_410343 prefixEnd_410343 192686961324182226635 := by
  unfold tailWord_410343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966438752404866850075683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9977625834936577900050455 14966438752404866850075683)
  ·
    refine ⟨22449658128607300275113525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14966438752404866850075683 22449658128607300275113525)
    ·
      refine ⟨2104655449556934400791893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22449658128607300275113525 2104655449556934400791893)
      ·
        refine ⟨192686961324182226635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 2104655449556934400791893 192686961324182226635)
        ·
          rfl

theorem cell22_410343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 15].length) (baseStart_410343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410343 prefixEnd_410343 := by exact prefixLift 410343
  have htrace : WordTrace (prefixWord ++ tailWord_410343) baseStart_410343 baseEnd_410343 := by
    simpa [prefixWord, tailWord_410343, baseEnd_410343] using wordTrace_append hprefix tailTrace_410343
  have hstable : (prefixWord ++ tailWord_410343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410343).length < 2 ^ (prefixWord ++ tailWord_410343).sum := by decide
  have hdescent : baseEnd_410343 < baseStart_410343 := by decide
  rcases family_descends (prefixWord ++ tailWord_410343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410345 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_410345 : Nat := 118140960795 + 410345 * 2 ^ 59
def prefixEnd_410345 : Nat := 4983230072969 + 3 ^ 40 * 410345 * 2
def baseEnd_410345 : Nat := 140469479446201504666909

theorem tailTrace_410345 : CollatzResearch.WordTrace tailWord_410345 prefixEnd_410345 140469479446201504666909 := by
  unfold tailWord_410345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966511698397621191648489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9977674465598414127765659 14966511698397621191648489)
  ·
    refine ⟨11224883773798215893736367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14966511698397621191648489 11224883773798215893736367)
    ·
      refine ⟨16837325660697323840604551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11224883773798215893736367 16837325660697323840604551)
      ·
        refine ⟨25255988491045985760906827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16837325660697323840604551 25255988491045985760906827)
        ·
          refine ⟨37883982736568978641360241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25255988491045985760906827 37883982736568978641360241)
          ·
            refine ⟨28412987052426733981020181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37883982736568978641360241 28412987052426733981020181)
            ·
              refine ⟨1331858768082503155360321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28412987052426733981020181 1331858768082503155360321)
              ·
                refine ⟨998894076061877366520241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331858768082503155360321 998894076061877366520241)
                ·
                  refine ⟨749170557046408024890181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998894076061877366520241 749170557046408024890181)
                  ·
                    refine ⟨140469479446201504666909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749170557046408024890181 140469479446201504666909)
                    ·
                      rfl

theorem cell22_410345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_410345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410345 prefixEnd_410345 := by exact prefixLift 410345
  have htrace : WordTrace (prefixWord ++ tailWord_410345) baseStart_410345 baseEnd_410345 := by
    simpa [prefixWord, tailWord_410345, baseEnd_410345] using wordTrace_append hprefix tailTrace_410345
  have hstable : (prefixWord ++ tailWord_410345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410345).length < 2 ^ (prefixWord ++ tailWord_410345).sum := by decide
  have hdescent : baseEnd_410345 < baseStart_410345 := by decide
  rcases family_descends (prefixWord ++ tailWord_410345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410405 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 7]
def baseStart_410405 : Nat := 118140960795 + 410405 * 2 ^ 59
def prefixEnd_410405 : Nat := 4983230072969 + 3 ^ 40 * 410405 * 2
def baseEnd_410405 : Nat := 46830006224127116055575

theorem tailTrace_410405 : CollatzResearch.WordTrace tailWord_410405 prefixEnd_410405 46830006224127116055575 := by
  unfold tailWord_410405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968700078180251438832669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9979133385453500959221779 14968700078180251438832669)
  ·
    refine ⟨5613262529317594289562251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14968700078180251438832669 5613262529317594289562251)
    ·
      refine ⟨8419893793976391434343377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613262529317594289562251 8419893793976391434343377)
      ·
        refine ⟨6314920345482293575757533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8419893793976391434343377 6314920345482293575757533)
        ·
          refine ⟨2368095129555860090909075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6314920345482293575757533 2368095129555860090909075)
          ·
            refine ⟨3552142694333790136363613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368095129555860090909075 3552142694333790136363613)
            ·
              refine ⟨1332053510375171301136355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3552142694333790136363613 1332053510375171301136355)
              ·
                refine ⟨1998080265562756951704533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332053510375171301136355 1998080265562756951704533)
                ·
                  refine ⟨46830006224127116055575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1998080265562756951704533 46830006224127116055575)
                  ·
                    rfl

theorem cell22_410405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_410405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410405 prefixEnd_410405 := by exact prefixLift 410405
  have htrace : WordTrace (prefixWord ++ tailWord_410405) baseStart_410405 baseEnd_410405 := by
    simpa [prefixWord, tailWord_410405, baseEnd_410405] using wordTrace_append hprefix tailTrace_410405
  have hstable : (prefixWord ++ tailWord_410405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410405).length < 2 ^ (prefixWord ++ tailWord_410405).sum := by decide
  have hdescent : baseEnd_410405 < baseStart_410405 := by decide
  rcases family_descends (prefixWord ++ tailWord_410405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410465 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_410465 : Nat := 118140960795 + 410465 * 2 ^ 59
def prefixEnd_410465 : Nat := 4983230072969 + 3 ^ 40 * 410465 * 2
def baseEnd_410465 : Nat := 140510557898561191666541

theorem tailTrace_410465 : CollatzResearch.WordTrace tailWord_410465 prefixEnd_410465 140510557898561191666541 := by
  unfold tailWord_410465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970888457962881686016849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9980592305308587790677899 14970888457962881686016849)
  ·
    refine ⟨11228166343472161264512637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14970888457962881686016849 11228166343472161264512637)
    ·
      refine ⟨4210562378802060474192239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11228166343472161264512637 4210562378802060474192239)
      ·
        refine ⟨6315843568203090711288359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210562378802060474192239 6315843568203090711288359)
        ·
          refine ⟨9473765352304636066932539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315843568203090711288359 9473765352304636066932539)
          ·
            refine ⟨14210648028456954100398809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9473765352304636066932539 14210648028456954100398809)
            ·
              refine ⟨10657986021342715575299107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14210648028456954100398809 10657986021342715575299107)
              ·
                refine ⟨15986979032014073362948661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657986021342715575299107 15986979032014073362948661)
                ·
                  refine ⟨1498779284251319377776437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15986979032014073362948661 1498779284251319377776437)
                  ·
                    refine ⟨140510557898561191666541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1498779284251319377776437 140510557898561191666541)
                    ·
                      rfl

theorem cell22_410465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_410465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410465 prefixEnd_410465 := by exact prefixLift 410465
  have htrace : WordTrace (prefixWord ++ tailWord_410465) baseStart_410465 baseEnd_410465 := by
    simpa [prefixWord, tailWord_410465, baseEnd_410465] using wordTrace_append hprefix tailTrace_410465
  have hstable : (prefixWord ++ tailWord_410465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410465).length < 2 ^ (prefixWord ++ tailWord_410465).sum := by decide
  have hdescent : baseEnd_410465 < baseStart_410465 := by decide
  rcases family_descends (prefixWord ++ tailWord_410465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410467 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 6]
def baseStart_410467 : Nat := 118140960795 + 410467 * 2 ^ 59
def prefixEnd_410467 : Nat := 4983230072969 + 3 ^ 40 * 410467 * 2
def baseEnd_410467 : Nat := 46837080846477951038845

theorem tailTrace_410467 : CollatzResearch.WordTrace tailWord_410467 prefixEnd_410467 46837080846477951038845 := by
  unfold tailWord_410467
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970961403955636027589655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9980640935970424018393103 14970961403955636027589655)
  ·
    refine ⟨22456442105933454041384483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14970961403955636027589655 22456442105933454041384483)
    ·
      refine ⟨33684663158900181062076725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22456442105933454041384483 33684663158900181062076725)
      ·
        refine ⟨3157937171146891974569693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33684663158900181062076725 3157937171146891974569693)
        ·
          refine ⟨1184226439180084490463635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3157937171146891974569693 1184226439180084490463635)
          ·
            refine ⟨1776339658770126735695453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184226439180084490463635 1776339658770126735695453)
            ·
              refine ⟨666127372038797525885795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776339658770126735695453 666127372038797525885795)
              ·
                refine ⟨999191058058196288828693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666127372038797525885795 999191058058196288828693)
                ·
                  refine ⟨46837080846477951038845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 999191058058196288828693 46837080846477951038845)
                  ·
                    rfl

theorem cell22_410467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_410467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410467 prefixEnd_410467 := by exact prefixLift 410467
  have htrace : WordTrace (prefixWord ++ tailWord_410467) baseStart_410467 baseEnd_410467 := by
    simpa [prefixWord, tailWord_410467, baseEnd_410467] using wordTrace_append hprefix tailTrace_410467
  have hstable : (prefixWord ++ tailWord_410467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410467).length < 2 ^ (prefixWord ++ tailWord_410467).sum := by decide
  have hdescent : baseEnd_410467 < baseStart_410467 := by decide
  rcases family_descends (prefixWord ++ tailWord_410467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410480 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_410480 : Nat := 118140960795 + 410480 * 2 ^ 59
def prefixEnd_410480 : Nat := 4983230072969 + 3 ^ 40 * 410480 * 2
def baseEnd_410480 : Nat := 140515692705106152541495

theorem tailTrace_410480 : CollatzResearch.WordTrace tailWord_410480 prefixEnd_410480 140515692705106152541495 := by
  unfold tailWord_410480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485717776454269623906447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9980957035272359498541929 7485717776454269623906447)
  ·
    refine ⟨11228576664681404435859671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485717776454269623906447 11228576664681404435859671)
    ·
      refine ⟨16842864997022106653789507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228576664681404435859671 16842864997022106653789507)
      ·
        refine ⟨25264297495533159980684261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842864997022106653789507 25264297495533159980684261)
        ·
          refine ⟨4737055780412467496378299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25264297495533159980684261 4737055780412467496378299)
          ·
            refine ⟨7105583670618701244567449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737055780412467496378299 7105583670618701244567449)
            ·
              refine ⟨5329187752964025933425587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105583670618701244567449 5329187752964025933425587)
              ·
                refine ⟨7993781629446038900138381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329187752964025933425587 7993781629446038900138381)
                ·
                  refine ⟨2997668111042264587551893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7993781629446038900138381 2997668111042264587551893)
                  ·
                    refine ⟨140515692705106152541495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2997668111042264587551893 140515692705106152541495)
                    ·
                      rfl

theorem cell22_410480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_410480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410480 prefixEnd_410480 := by exact prefixLift 410480
  have htrace : WordTrace (prefixWord ++ tailWord_410480) baseStart_410480 baseEnd_410480 := by
    simpa [prefixWord, tailWord_410480, baseEnd_410480] using wordTrace_append hprefix tailTrace_410480
  have hstable : (prefixWord ++ tailWord_410480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410480).length < 2 ^ (prefixWord ++ tailWord_410480).sum := by decide
  have hdescent : baseEnd_410480 < baseStart_410480 := by decide
  rcases family_descends (prefixWord ++ tailWord_410480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410486 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_410486 : Nat := 118140960795 + 410486 * 2 ^ 59
def prefixEnd_410486 : Nat := 4983230072969 + 3 ^ 40 * 410486 * 2
def baseEnd_410486 : Nat := 140517746627724136891477

theorem tailTrace_410486 : CollatzResearch.WordTrace tailWord_410486 prefixEnd_410486 140517746627724136891477 := by
  unfold tailWord_410486
  simp only [CollatzResearch.WordTrace]
  refine ⟨935728399430425142033207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9981102927257868181687541 935728399430425142033207)
  ·
    refine ⟨1403592599145637713049811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 935728399430425142033207 1403592599145637713049811)
    ·
      refine ⟨2105388898718456569574717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403592599145637713049811 2105388898718456569574717)
      ·
        refine ⟨789520837019421213590519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2105388898718456569574717 789520837019421213590519)
        ·
          refine ⟨1184281255529131820385779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789520837019421213590519 1184281255529131820385779)
          ·
            refine ⟨1776421883293697730578669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184281255529131820385779 1776421883293697730578669)
            ·
              refine ⟨666158206235136648967001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776421883293697730578669 666158206235136648967001)
              ·
                refine ⟨499618654676352486725251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666158206235136648967001 499618654676352486725251)
                ·
                  refine ⟨749427982014528730087877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499618654676352486725251 749427982014528730087877)
                  ·
                    refine ⟨140517746627724136891477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749427982014528730087877 140517746627724136891477)
                    ·
                      rfl

theorem cell22_410486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_410486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410486 prefixEnd_410486 := by exact prefixLift 410486
  have htrace : WordTrace (prefixWord ++ tailWord_410486) baseStart_410486 baseEnd_410486 := by
    simpa [prefixWord, tailWord_410486, baseEnd_410486] using wordTrace_append hprefix tailTrace_410486
  have hstable : (prefixWord ++ tailWord_410486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410486).length < 2 ^ (prefixWord ++ tailWord_410486).sum := by decide
  have hdescent : baseEnd_410486 < baseStart_410486 := by decide
  rcases family_descends (prefixWord ++ tailWord_410486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410495 : List Nat := [1, 1, 2, 2, 1, 1, 6, 8]
def baseStart_410495 : Nat := 118140960795 + 410495 * 2 ^ 59
def prefixEnd_410495 : Nat := 4983230072969 + 3 ^ 40 * 410495 * 2
def baseEnd_410495 : Nat := 15613425279072345935161

theorem tailTrace_410495 : CollatzResearch.WordTrace tailWord_410495 prefixEnd_410495 15613425279072345935161 := by
  unfold tailWord_410495
  simp only [CollatzResearch.WordTrace]
  refine ⟨14971982647854196809608939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9981321765236131206405959 14971982647854196809608939)
  ·
    refine ⟨22457973971781295214413409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14971982647854196809608939 22457973971781295214413409)
    ·
      refine ⟨16843480478835971410810057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22457973971781295214413409 16843480478835971410810057)
      ·
        refine ⟨12632610359126978558107543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16843480478835971410810057 12632610359126978558107543)
        ·
          refine ⟨18948915538690467837161315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632610359126978558107543 18948915538690467837161315)
          ·
            refine ⟨28423373308035701755741973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948915538690467837161315 28423373308035701755741973)
            ·
              refine ⟨1332345623814173519800405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28423373308035701755741973 1332345623814173519800405)
              ·
                refine ⟨15613425279072345935161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1332345623814173519800405 15613425279072345935161)
                ·
                  rfl

theorem cell22_410495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 8].length) (baseStart_410495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410495 prefixEnd_410495 := by exact prefixLift 410495
  have htrace : WordTrace (prefixWord ++ tailWord_410495) baseStart_410495 baseEnd_410495 := by
    simpa [prefixWord, tailWord_410495, baseEnd_410495] using wordTrace_append hprefix tailTrace_410495
  have hstable : (prefixWord ++ tailWord_410495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410495).length < 2 ^ (prefixWord ++ tailWord_410495).sum := by decide
  have hdescent : baseEnd_410495 < baseStart_410495 := by decide
  rcases family_descends (prefixWord ++ tailWord_410495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410516 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_410516 : Nat := 118140960795 + 410516 * 2 ^ 59
def prefixEnd_410516 : Nat := 4983230072969 + 3 ^ 40 * 410516 * 2
def baseEnd_410516 : Nat := 140528016240814058641385

theorem tailTrace_410516 : CollatzResearch.WordTrace tailWord_410516 prefixEnd_410516 140528016240814058641385 := by
  unfold tailWord_410516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486374290389058698061701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9981832387185411597415601 7486374290389058698061701)
  ·
    refine ⟨1403695179447948505886569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7486374290389058698061701 1403695179447948505886569)
    ·
      refine ⟨1052771384585961379414927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1403695179447948505886569 1052771384585961379414927)
      ·
        refine ⟨1579157076878942069122391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052771384585961379414927 1579157076878942069122391)
        ·
          refine ⟨2368735615318413103683587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579157076878942069122391 2368735615318413103683587)
          ·
            refine ⟨3553103422977619655525381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368735615318413103683587 3553103422977619655525381)
            ·
              refine ⟨666206891808303685411009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3553103422977619655525381 666206891808303685411009)
              ·
                refine ⟨499655168856227764058257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666206891808303685411009 499655168856227764058257)
                ·
                  refine ⟨374741376642170823043693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499655168856227764058257 374741376642170823043693)
                  ·
                    refine ⟨140528016240814058641385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374741376642170823043693 140528016240814058641385)
                    ·
                      rfl

theorem cell22_410516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_410516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410516 prefixEnd_410516 := by exact prefixLift 410516
  have htrace : WordTrace (prefixWord ++ tailWord_410516) baseStart_410516 baseEnd_410516 := by
    simpa [prefixWord, tailWord_410516, baseEnd_410516] using wordTrace_append hprefix tailTrace_410516
  have hstable : (prefixWord ++ tailWord_410516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410516).length < 2 ^ (prefixWord ++ tailWord_410516).sum := by decide
  have hdescent : baseEnd_410516 < baseStart_410516 := by decide
  rcases family_descends (prefixWord ++ tailWord_410516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410529 : List Nat := [1, 2, 3, 4, 1, 3, 1, 7]
def baseStart_410529 : Nat := 118140960795 + 410529 * 2 ^ 59
def prefixEnd_410529 : Nat := 4983230072969 + 3 ^ 40 * 410529 * 2
def baseEnd_410529 : Nat := 15614718489609595340705

theorem tailTrace_410529 : CollatzResearch.WordTrace tailWord_410529 prefixEnd_410529 15614718489609595340705 := by
  unfold tailWord_410529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14973222729731020616346641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9982148486487347077564427 14973222729731020616346641)
  ·
    refine ⟨11229917047298265462259981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14973222729731020616346641 11229917047298265462259981)
    ·
      refine ⟨4211218892736849548347493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11229917047298265462259981 4211218892736849548347493)
      ·
        refine ⟨789603542388159290315155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4211218892736849548347493 789603542388159290315155)
        ·
          refine ⟨1184405313582238935472733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789603542388159290315155 1184405313582238935472733)
          ·
            refine ⟨444151992593339600802275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184405313582238935472733 444151992593339600802275)
            ·
              refine ⟨666227988890009401203413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444151992593339600802275 666227988890009401203413)
              ·
                refine ⟨15614718489609595340705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 666227988890009401203413 15614718489609595340705)
                ·
                  rfl

theorem cell22_410529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 7].length) (baseStart_410529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410529 prefixEnd_410529 := by exact prefixLift 410529
  have htrace : WordTrace (prefixWord ++ tailWord_410529) baseStart_410529 baseEnd_410529 := by
    simpa [prefixWord, tailWord_410529, baseEnd_410529] using wordTrace_append hprefix tailTrace_410529
  have hstable : (prefixWord ++ tailWord_410529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410529).length < 2 ^ (prefixWord ++ tailWord_410529).sum := by decide
  have hdescent : baseEnd_410529 < baseStart_410529 := by decide
  rcases family_descends (prefixWord ++ tailWord_410529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410548 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_410548 : Nat := 118140960795 + 410548 * 2 ^ 59
def prefixEnd_410548 : Nat := 4983230072969 + 3 ^ 40 * 410548 * 2
def baseEnd_410548 : Nat := 140538970494776641841287

theorem tailTrace_410548 : CollatzResearch.WordTrace tailWord_410548 prefixEnd_410548 140538970494776641841287 := by
  unfold tailWord_410548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486957858331093430644149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9982610477774791240858865 7486957858331093430644149)
  ·
    refine ⟨701902299218540009122889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7486957858331093430644149 701902299218540009122889)
    ·
      refine ⟨526426724413905006842167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701902299218540009122889 526426724413905006842167)
      ·
        refine ⟨789640086620857510263251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526426724413905006842167 789640086620857510263251)
        ·
          refine ⟨1184460129931286265394877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789640086620857510263251 1184460129931286265394877)
          ·
            refine ⟨444172548724232349523079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184460129931286265394877 444172548724232349523079)
            ·
              refine ⟨666258823086348524284619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444172548724232349523079 666258823086348524284619)
              ·
                refine ⟨999388234629522786426929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666258823086348524284619 999388234629522786426929)
                ·
                  refine ⟨749541175972142089820197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999388234629522786426929 749541175972142089820197)
                  ·
                    refine ⟨140538970494776641841287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 749541175972142089820197 140538970494776641841287)
                    ·
                      rfl

theorem cell22_410548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_410548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410548 prefixEnd_410548 := by exact prefixLift 410548
  have htrace : WordTrace (prefixWord ++ tailWord_410548) baseStart_410548 baseEnd_410548 := by
    simpa [prefixWord, tailWord_410548, baseEnd_410548] using wordTrace_append hprefix tailTrace_410548
  have hstable : (prefixWord ++ tailWord_410548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410548).length < 2 ^ (prefixWord ++ tailWord_410548).sum := by decide
  have hdescent : baseEnd_410548 < baseStart_410548 := by decide
  rcases family_descends (prefixWord ++ tailWord_410548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410572 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_410572 : Nat := 118140960795 + 410572 * 2 ^ 59
def prefixEnd_410572 : Nat := 4983230072969 + 3 ^ 40 * 410572 * 2
def baseEnd_410572 : Nat := 140547186185248579241213

theorem tailTrace_410572 : CollatzResearch.WordTrace tailWord_410572 prefixEnd_410572 140547186185248579241213 := by
  unfold tailWord_410572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487395534287619480080985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9983194045716825973441313 7487395534287619480080985)
  ·
    refine ⟨5615546650715714610060739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7487395534287619480080985 5615546650715714610060739)
    ·
      refine ⟨8423319976073571915091109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615546650715714610060739 8423319976073571915091109)
      ·
        refine ⟨1579372495513794734079583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8423319976073571915091109 1579372495513794734079583)
        ·
          refine ⟨2369058743270692101119375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579372495513794734079583 2369058743270692101119375)
          ·
            refine ⟨3553588114906038151679063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369058743270692101119375 3553588114906038151679063)
            ·
              refine ⟨5330382172359057227518595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553588114906038151679063 5330382172359057227518595)
              ·
                refine ⟨7995573258538585841277893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330382172359057227518595 7995573258538585841277893)
                ·
                  refine ⟨1499169985975984845239605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7995573258538585841277893 1499169985975984845239605)
                  ·
                    refine ⟨140547186185248579241213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1499169985975984845239605 140547186185248579241213)
                    ·
                      rfl

theorem cell22_410572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_410572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410572 prefixEnd_410572 := by exact prefixLift 410572
  have htrace : WordTrace (prefixWord ++ tailWord_410572) baseStart_410572 baseEnd_410572 := by
    simpa [prefixWord, tailWord_410572, baseEnd_410572] using wordTrace_append hprefix tailTrace_410572
  have hstable : (prefixWord ++ tailWord_410572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410572).length < 2 ^ (prefixWord ++ tailWord_410572).sum := by decide
  have hdescent : baseEnd_410572 < baseStart_410572 := by decide
  rcases family_descends (prefixWord ++ tailWord_410572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410574 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_410574 : Nat := 118140960795 + 410574 * 2 ^ 59
def prefixEnd_410574 : Nat := 4983230072969 + 3 ^ 40 * 410574 * 2
def baseEnd_410574 : Nat := 46849290275373746897069

theorem tailTrace_410574 : CollatzResearch.WordTrace tailWord_410574 prefixEnd_410574 46849290275373746897069 := by
  unfold tailWord_410574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871858001820999162716847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9983242676378662201156517 1871858001820999162716847)
  ·
    refine ⟨2807787002731498744075271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871858001820999162716847 2807787002731498744075271)
    ·
      refine ⟨4211680504097248116112907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2807787002731498744075271 4211680504097248116112907)
      ·
        refine ⟨6317520756145872174169361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211680504097248116112907 6317520756145872174169361)
        ·
          refine ⟨4738140567109404130627021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6317520756145872174169361 4738140567109404130627021)
          ·
            refine ⟨1776802712666026548985133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4738140567109404130627021 1776802712666026548985133)
            ·
              refine ⟨666301017249759955869425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776802712666026548985133 666301017249759955869425)
              ·
                refine ⟨499725762937319966902069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666301017249759955869425 499725762937319966902069)
                ·
                  refine ⟨46849290275373746897069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499725762937319966902069 46849290275373746897069)
                  ·
                    rfl

theorem cell22_410574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_410574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410574 prefixEnd_410574 := by exact prefixLift 410574
  have htrace : WordTrace (prefixWord ++ tailWord_410574) baseStart_410574 baseEnd_410574 := by
    simpa [prefixWord, tailWord_410574, baseEnd_410574] using wordTrace_append hprefix tailTrace_410574
  have hstable : (prefixWord ++ tailWord_410574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410574).length < 2 ^ (prefixWord ++ tailWord_410574).sum := by decide
  have hdescent : baseEnd_410574 < baseStart_410574 := by decide
  rcases family_descends (prefixWord ++ tailWord_410574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410578 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_410578 : Nat := 118140960795 + 410578 * 2 ^ 59
def prefixEnd_410578 : Nat := 4983230072969 + 3 ^ 40 * 410578 * 2
def baseEnd_410578 : Nat := 140549240107866563591195

theorem tailTrace_410578 : CollatzResearch.WordTrace tailWord_410578 prefixEnd_410578 140549240107866563591195 := by
  unfold tailWord_410578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743752476638375496220097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9983339937702334656586925 3743752476638375496220097)
  ·
    refine ⟨2807814357478781622165073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3743752476638375496220097 2807814357478781622165073)
    ·
      refine ⟨2105860768109086216623805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2807814357478781622165073 2105860768109086216623805)
      ·
        refine ⟨789697788040907331233927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2105860768109086216623805 789697788040907331233927)
        ·
          refine ⟨1184546682061360996850891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789697788040907331233927 1184546682061360996850891)
          ·
            refine ⟨1776820023092041495276337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184546682061360996850891 1776820023092041495276337)
            ·
              refine ⟨1332615017319031121457253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776820023092041495276337 1332615017319031121457253)
              ·
                refine ⟨249865315747318335273235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1332615017319031121457253 249865315747318335273235)
                ·
                  refine ⟨374797973620977502909853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249865315747318335273235 374797973620977502909853)
                  ·
                    refine ⟨140549240107866563591195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374797973620977502909853 140549240107866563591195)
                    ·
                      rfl

theorem cell22_410578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_410578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410578 prefixEnd_410578 := by exact prefixLift 410578
  have htrace : WordTrace (prefixWord ++ tailWord_410578) baseStart_410578 baseEnd_410578 := by
    simpa [prefixWord, tailWord_410578, baseEnd_410578] using wordTrace_append hprefix tailTrace_410578
  have hstable : (prefixWord ++ tailWord_410578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410578).length < 2 ^ (prefixWord ++ tailWord_410578).sum := by decide
  have hdescent : baseEnd_410578 < baseStart_410578 := by decide
  rcases family_descends (prefixWord ++ tailWord_410578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410589 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_410589 : Nat := 118140960795 + 410589 * 2 ^ 59
def prefixEnd_410589 : Nat := 4983230072969 + 3 ^ 40 * 410589 * 2
def baseEnd_410589 : Nat := 140553005632666201566161

theorem tailTrace_410589 : CollatzResearch.WordTrace tailWord_410589 prefixEnd_410589 140553005632666201566161 := by
  unfold tailWord_410589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14975411109513650863530821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9983607406342433909020547 14975411109513650863530821)
  ·
    refine ⟨2807889583033809536912029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14975411109513650863530821 2807889583033809536912029)
    ·
      refine ⟨1052958593637678576342011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2807889583033809536912029 1052958593637678576342011)
      ·
        refine ⟨1579437890456517864513017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052958593637678576342011 1579437890456517864513017)
        ·
          refine ⟨1184578417842388398384763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579437890456517864513017 1184578417842388398384763)
          ·
            refine ⟨1776867626763582597577145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184578417842388398384763 1776867626763582597577145)
            ·
              refine ⟨1332650720072686948182859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776867626763582597577145 1332650720072686948182859)
              ·
                refine ⟨1998976080109030422274289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332650720072686948182859 1998976080109030422274289)
                ·
                  refine ⟨1499232060081772816705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998976080109030422274289 1499232060081772816705717)
                  ·
                    refine ⟨140553005632666201566161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1499232060081772816705717 140553005632666201566161)
                    ·
                      rfl

theorem cell22_410589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_410589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410589 prefixEnd_410589 := by exact prefixLift 410589
  have htrace : WordTrace (prefixWord ++ tailWord_410589) baseStart_410589 baseEnd_410589 := by
    simpa [prefixWord, tailWord_410589, baseEnd_410589] using wordTrace_append hprefix tailTrace_410589
  have hstable : (prefixWord ++ tailWord_410589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410589).length < 2 ^ (prefixWord ++ tailWord_410589).sum := by decide
  have hdescent : baseEnd_410589 < baseStart_410589 := by decide
  rcases family_descends (prefixWord ++ tailWord_410589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410591 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 5]
def baseStart_410591 : Nat := 118140960795 + 410591 * 2 ^ 59
def prefixEnd_410591 : Nat := 4983230072969 + 3 ^ 40 * 410591 * 2
def baseEnd_410591 : Nat := 46851230091179621005385

theorem tailTrace_410591 : CollatzResearch.WordTrace tailWord_410591 prefixEnd_410591 46851230091179621005385 := by
  unfold tailWord_410591
  simp only [CollatzResearch.WordTrace]
  refine ⟨14975484055506405205103627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9983656037004270136735751 14975484055506405205103627)
  ·
    refine ⟨22463226083259607807655441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14975484055506405205103627 22463226083259607807655441)
    ·
      refine ⟨16847419562444705855741581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22463226083259607807655441 16847419562444705855741581)
      ·
        refine ⟨6317782335916764695903093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16847419562444705855741581 6317782335916764695903093)
        ·
          refine ⟨592292093992196690240915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6317782335916764695903093 592292093992196690240915)
          ·
            refine ⟨888438140988295035361373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592292093992196690240915 888438140988295035361373)
            ·
              refine ⟨333164302870610638260515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888438140988295035361373 333164302870610638260515)
              ·
                refine ⟨499746454305915957390773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333164302870610638260515 499746454305915957390773)
                ·
                  refine ⟨46851230091179621005385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499746454305915957390773 46851230091179621005385)
                  ·
                    rfl

theorem cell22_410591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 5].length) (baseStart_410591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410591 prefixEnd_410591 := by exact prefixLift 410591
  have htrace : WordTrace (prefixWord ++ tailWord_410591) baseStart_410591 baseEnd_410591 := by
    simpa [prefixWord, tailWord_410591, baseEnd_410591] using wordTrace_append hprefix tailTrace_410591
  have hstable : (prefixWord ++ tailWord_410591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410591).length < 2 ^ (prefixWord ++ tailWord_410591).sum := by decide
  have hdescent : baseEnd_410591 < baseStart_410591 := by decide
  rcases family_descends (prefixWord ++ tailWord_410591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410617 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_410617 : Nat := 118140960795 + 410617 * 2 ^ 59
def prefixEnd_410617 : Nat := 4983230072969 + 3 ^ 40 * 410617 * 2
def baseEnd_410617 : Nat := 140562590604883461866075

theorem tailTrace_410617 : CollatzResearch.WordTrace tailWord_410617 prefixEnd_410617 140562590604883461866075 := by
  unfold tailWord_410617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976432353412211645550105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9984288235608141097033403 14976432353412211645550105)
  ·
    refine ⟨11232324265059158734162579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14976432353412211645550105 11232324265059158734162579)
    ·
      refine ⟨16848486397588738101243869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11232324265059158734162579 16848486397588738101243869)
      ·
        refine ⟨6318182399095776787966451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16848486397588738101243869 6318182399095776787966451)
        ·
          refine ⟨9477273598643665181949677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318182399095776787966451 9477273598643665181949677)
          ·
            refine ⟨3553977599491374443231129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9477273598643665181949677 3553977599491374443231129)
            ·
              refine ⟨2665483199618530832423347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553977599491374443231129 2665483199618530832423347)
              ·
                refine ⟨3998224799427796248635021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665483199618530832423347 3998224799427796248635021)
                ·
                  refine ⟨1499334299785423593238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3998224799427796248635021 1499334299785423593238133)
                  ·
                    refine ⟨140562590604883461866075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1499334299785423593238133 140562590604883461866075)
                    ·
                      rfl

theorem cell22_410617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_410617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410617 prefixEnd_410617 := by exact prefixLift 410617
  have htrace : WordTrace (prefixWord ++ tailWord_410617) baseStart_410617 baseEnd_410617 := by
    simpa [prefixWord, tailWord_410617, baseEnd_410617] using wordTrace_append hprefix tailTrace_410617
  have hstable : (prefixWord ++ tailWord_410617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410617).length < 2 ^ (prefixWord ++ tailWord_410617).sum := by decide
  have hdescent : baseEnd_410617 < baseStart_410617 := by decide
  rcases family_descends (prefixWord ++ tailWord_410617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410642 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_410642 : Nat := 118140960795 + 410642 * 2 ^ 59
def prefixEnd_410642 : Nat := 4983230072969 + 3 ^ 40 * 410642 * 2
def baseEnd_410642 : Nat := 46857049538597243330333

theorem tailTrace_410642 : CollatzResearch.WordTrace tailWord_410642 prefixEnd_410642 46857049538597243330333 := by
  unfold tailWord_410642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744336044580410228802545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9984896118881093943473453 3744336044580410228802545)
  ·
    refine ⟨2808252033435307671601909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3744336044580410228802545 2808252033435307671601909)
    ·
      refine ⟨263273628134560094212679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2808252033435307671601909 263273628134560094212679)
      ·
        refine ⟨394910442201840141319019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263273628134560094212679 394910442201840141319019)
        ·
          refine ⟨592365663302760211978529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394910442201840141319019 592365663302760211978529)
          ·
            refine ⟨444274247477070158983897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592365663302760211978529 444274247477070158983897)
            ·
              refine ⟨333205685607802619237923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444274247477070158983897 333205685607802619237923)
              ·
                refine ⟨499808528411703928856885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333205685607802619237923 499808528411703928856885)
                ·
                  refine ⟨46857049538597243330333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499808528411703928856885 46857049538597243330333)
                  ·
                    rfl

theorem cell22_410642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_410642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410642 prefixEnd_410642 := by exact prefixLift 410642
  have htrace : WordTrace (prefixWord ++ tailWord_410642) baseStart_410642 baseEnd_410642 := by
    simpa [prefixWord, tailWord_410642, baseEnd_410642] using wordTrace_append hprefix tailTrace_410642
  have hstable : (prefixWord ++ tailWord_410642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410642).length < 2 ^ (prefixWord ++ tailWord_410642).sum := by decide
  have hdescent : baseEnd_410642 < baseStart_410642 := by decide
  rcases family_descends (prefixWord ++ tailWord_410642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410707 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_410707 : Nat := 118140960795 + 410707 * 2 ^ 59
def prefixEnd_410707 : Nat := 4983230072969 + 3 ^ 40 * 410707 * 2
def baseEnd_410707 : Nat := 140593399444153227115799

theorem tailTrace_410707 : CollatzResearch.WordTrace tailWord_410707 prefixEnd_410707 140593399444153227115799 := by
  unfold tailWord_410707
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979714923086157016326375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986476615390771344217583 14979714923086157016326375)
  ·
    refine ⟨22469572384629235524489563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14979714923086157016326375 22469572384629235524489563)
    ·
      refine ⟨33704358576943853286734345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22469572384629235524489563 33704358576943853286734345)
      ·
        refine ⟨25278268932707889965050759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33704358576943853286734345 25278268932707889965050759)
        ·
          refine ⟨37917403399061834947576139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25278268932707889965050759 37917403399061834947576139)
          ·
            refine ⟨56876105098592752421364209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37917403399061834947576139 56876105098592752421364209)
            ·
              refine ⟨42657078823944564316023157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56876105098592752421364209 42657078823944564316023157)
              ·
                refine ⟨3999101139744802904627171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42657078823944564316023157 3999101139744802904627171)
                ·
                  refine ⟨5998651709617204356940757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999101139744802904627171 5998651709617204356940757)
                  ·
                    refine ⟨140593399444153227115799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5998651709617204356940757 140593399444153227115799)
                    ·
                      rfl

theorem cell22_410707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_410707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410707 prefixEnd_410707 := by exact prefixLift 410707
  have htrace : WordTrace (prefixWord ++ tailWord_410707) baseStart_410707 baseEnd_410707 := by
    simpa [prefixWord, tailWord_410707, baseEnd_410707] using wordTrace_append hprefix tailTrace_410707
  have hstable : (prefixWord ++ tailWord_410707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410707).length < 2 ^ (prefixWord ++ tailWord_410707).sum := by decide
  have hdescent : baseEnd_410707 < baseStart_410707 := by decide
  rcases family_descends (prefixWord ++ tailWord_410707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410709 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 5]
def baseStart_410709 : Nat := 118140960795 + 410709 * 2 ^ 59
def prefixEnd_410709 : Nat := 4983230072969 + 3 ^ 40 * 410709 * 2
def baseEnd_410709 : Nat := 46864694695008629521931

theorem tailTrace_410709 : CollatzResearch.WordTrace tailWord_410709 prefixEnd_410709 46864694695008629521931 := by
  unfold tailWord_410709
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979787869078911357899181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986525246052607571932787 14979787869078911357899181)
  ·
    refine ⟨5617420450904591759212193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14979787869078911357899181 5617420450904591759212193)
    ·
      refine ⟨4213065338178443819409145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5617420450904591759212193 4213065338178443819409145)
      ·
        refine ⟨3159799003633832864556859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4213065338178443819409145 3159799003633832864556859)
        ·
          refine ⟨4739698505450749296835289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159799003633832864556859 4739698505450749296835289)
          ·
            refine ⟨3554773879088061972626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739698505450749296835289 3554773879088061972626467)
            ·
              refine ⟨5332160818632092958939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554773879088061972626467 5332160818632092958939701)
              ·
                refine ⟨499890076746758714900597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5332160818632092958939701 499890076746758714900597)
                ·
                  refine ⟨46864694695008629521931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499890076746758714900597 46864694695008629521931)
                  ·
                    rfl

theorem cell22_410709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_410709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410709 prefixEnd_410709 := by exact prefixLift 410709
  have htrace : WordTrace (prefixWord ++ tailWord_410709) baseStart_410709 baseEnd_410709 := by
    simpa [prefixWord, tailWord_410709, baseEnd_410709] using wordTrace_append hprefix tailTrace_410709
  have hstable : (prefixWord ++ tailWord_410709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410709).length < 2 ^ (prefixWord ++ tailWord_410709).sum := by decide
  have hdescent : baseEnd_410709 < baseStart_410709 := by decide
  rcases family_descends (prefixWord ++ tailWord_410709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410730 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_410730 : Nat := 118140960795 + 410730 * 2 ^ 59
def prefixEnd_410730 : Nat := 4983230072969 + 3 ^ 40 * 410730 * 2
def baseEnd_410730 : Nat := 140601272814188833790729

theorem tailTrace_410730 : CollatzResearch.WordTrace tailWord_410730 prefixEnd_410730 140601272814188833790729 := by
  unfold tailWord_410730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745138450500707986103411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9987035868001887962942429 3745138450500707986103411)
  ·
    refine ⟨5617707675751061979155117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745138450500707986103411 5617707675751061979155117)
    ·
      refine ⟨2106640378406648242183169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5617707675751061979155117 2106640378406648242183169)
      ·
        refine ⟨1579980283804986181637377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2106640378406648242183169 1579980283804986181637377)
        ·
          refine ⟨1184985212853739636228033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579980283804986181637377 1184985212853739636228033)
          ·
            refine ⟨888738909640304727171025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184985212853739636228033 888738909640304727171025)
            ·
              refine ⟨666554182230228545378269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888738909640304727171025 666554182230228545378269)
              ·
                refine ⟨249957818336335704516851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666554182230228545378269 249957818336335704516851)
                ·
                  refine ⟨374936727504503556775277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249957818336335704516851 374936727504503556775277)
                  ·
                    refine ⟨140601272814188833790729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374936727504503556775277 140601272814188833790729)
                    ·
                      rfl

theorem cell22_410730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_410730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410730 prefixEnd_410730 := by exact prefixLift 410730
  have htrace : WordTrace (prefixWord ++ tailWord_410730) baseStart_410730 baseEnd_410730 := by
    simpa [prefixWord, tailWord_410730, baseEnd_410730] using wordTrace_append hprefix tailTrace_410730
  have hstable : (prefixWord ++ tailWord_410730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410730).length < 2 ^ (prefixWord ++ tailWord_410730).sum := by decide
  have hdescent : baseEnd_410730 < baseStart_410730 := by decide
  rcases family_descends (prefixWord ++ tailWord_410730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410784 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_410784 : Nat := 118140960795 + 410784 * 2 ^ 59
def prefixEnd_410784 : Nat := 4983230072969 + 3 ^ 40 * 410784 * 2
def baseEnd_410784 : Nat := 140619758117750692940563

theorem tailTrace_410784 : CollatzResearch.WordTrace tailWord_410784 prefixEnd_410784 140619758117750692940563 := by
  unfold tailWord_410784
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491261671903599583439703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9988348895871466111252937 7491261671903599583439703)
  ·
    refine ⟨11236892507855399375159555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7491261671903599583439703 11236892507855399375159555)
    ·
      refine ⟨16855338761783099062739333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236892507855399375159555 16855338761783099062739333)
      ·
        refine ⟨3160376017834331074263625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16855338761783099062739333 3160376017834331074263625)
        ·
          refine ⟨2370282013375748305697719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160376017834331074263625 2370282013375748305697719)
          ·
            refine ⟨3555423020063622458546579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370282013375748305697719 3555423020063622458546579)
            ·
              refine ⟨5333134530095433687819869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555423020063622458546579 5333134530095433687819869)
              ·
                refine ⟨1999925448785787632932451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5333134530095433687819869 1999925448785787632932451)
                ·
                  refine ⟨2999888173178681449398677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999925448785787632932451 2999888173178681449398677)
                  ·
                    refine ⟨140619758117750692940563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2999888173178681449398677 140619758117750692940563)
                    ·
                      rfl

theorem cell22_410784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_410784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410784 prefixEnd_410784 := by exact prefixLift 410784
  have htrace : WordTrace (prefixWord ++ tailWord_410784) baseStart_410784 baseEnd_410784 := by
    simpa [prefixWord, tailWord_410784, baseEnd_410784] using wordTrace_append hprefix tailTrace_410784
  have hstable : (prefixWord ++ tailWord_410784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410784).length < 2 ^ (prefixWord ++ tailWord_410784).sum := by decide
  have hdescent : baseEnd_410784 < baseStart_410784 := by decide
  rcases family_descends (prefixWord ++ tailWord_410784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410788 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_410788 : Nat := 118140960795 + 410788 * 2 ^ 59
def prefixEnd_410788 : Nat := 4983230072969 + 3 ^ 40 * 410788 * 2
def baseEnd_410788 : Nat := 46873709133165338613517

theorem tailTrace_410788 : CollatzResearch.WordTrace tailWord_410788 prefixEnd_410788 46873709133165338613517 := by
  unfold tailWord_410788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491334617896353925012509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9988446157195138566683345 7491334617896353925012509)
  ·
    refine ⟨2809250481711132721879691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7491334617896353925012509 2809250481711132721879691)
    ·
      refine ⟨4213875722566699082819537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809250481711132721879691 4213875722566699082819537)
      ·
        refine ⟨3160406791925024312114653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4213875722566699082819537 3160406791925024312114653)
        ·
          refine ⟨1185152546971884117042995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3160406791925024312114653 1185152546971884117042995)
          ·
            refine ⟨1777728820457826175564493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185152546971884117042995 1777728820457826175564493)
            ·
              refine ⟨666648307671684815836685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777728820457826175564493 666648307671684815836685)
              ·
                refine ⟨249993115376881805938757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666648307671684815836685 249993115376881805938757)
                ·
                  refine ⟨46873709133165338613517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249993115376881805938757 46873709133165338613517)
                  ·
                    rfl

theorem cell22_410788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_410788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410788 prefixEnd_410788 := by exact prefixLift 410788
  have htrace : WordTrace (prefixWord ++ tailWord_410788) baseStart_410788 baseEnd_410788 := by
    simpa [prefixWord, tailWord_410788, baseEnd_410788] using wordTrace_append hprefix tailTrace_410788
  have hstable : (prefixWord ++ tailWord_410788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410788).length < 2 ^ (prefixWord ++ tailWord_410788).sum := by decide
  have hdescent : baseEnd_410788 < baseStart_410788 := by decide
  rcases family_descends (prefixWord ++ tailWord_410788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410801 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_410801 : Nat := 118140960795 + 410801 * 2 ^ 59
def prefixEnd_410801 : Nat := 4983230072969 + 3 ^ 40 * 410801 * 2
def baseEnd_410801 : Nat := 140625577565168315265511

theorem tailTrace_410801 : CollatzResearch.WordTrace tailWord_410801 prefixEnd_410801 140625577565168315265511 := by
  unfold tailWord_410801
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983143384745611070248257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9988762256497074046832171 14983143384745611070248257)
  ·
    refine ⟨11237357538559208302686193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14983143384745611070248257 11237357538559208302686193)
    ·
      refine ⟨8428018153919406227014645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11237357538559208302686193 8428018153919406227014645)
      ·
        refine ⟨790126701929944333782623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8428018153919406227014645 790126701929944333782623)
        ·
          refine ⟨1185190052894916500673935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790126701929944333782623 1185190052894916500673935)
          ·
            refine ⟨1777785079342374751010903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185190052894916500673935 1777785079342374751010903)
            ·
              refine ⟨2666677619013562126516355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777785079342374751010903 2666677619013562126516355)
              ·
                refine ⟨4000016428520343189774533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666677619013562126516355 4000016428520343189774533)
                ·
                  refine ⟨750003080347564348082725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4000016428520343189774533 750003080347564348082725)
                  ·
                    refine ⟨140625577565168315265511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750003080347564348082725 140625577565168315265511)
                    ·
                      rfl

theorem cell22_410801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_410801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410801 prefixEnd_410801 := by exact prefixLift 410801
  have htrace : WordTrace (prefixWord ++ tailWord_410801) baseStart_410801 baseEnd_410801 := by
    simpa [prefixWord, tailWord_410801, baseEnd_410801] using wordTrace_append hprefix tailTrace_410801
  have hstable : (prefixWord ++ tailWord_410801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410801).length < 2 ^ (prefixWord ++ tailWord_410801).sum := by decide
  have hdescent : baseEnd_410801 < baseStart_410801 := by decide
  rcases family_descends (prefixWord ++ tailWord_410801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410816 : List Nat := [2, 1, 1, 2, 6, 1, 2, 7]
def baseStart_410816 : Nat := 118140960795 + 410816 * 2 ^ 59
def prefixEnd_410816 : Nat := 4983230072969 + 3 ^ 40 * 410816 * 2
def baseEnd_410816 : Nat := 15625634707968141793385

theorem tailTrace_410816 : CollatzResearch.WordTrace tailWord_410816 prefixEnd_410816 15625634707968141793385 := by
  unfold tailWord_410816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491845239845634316022151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9989126986460845754696201 7491845239845634316022151)
  ·
    refine ⟨11237767859768451474033227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7491845239845634316022151 11237767859768451474033227)
    ·
      refine ⟨16856651789652677211049841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237767859768451474033227 16856651789652677211049841)
      ·
        refine ⟨12642488842239507908287381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16856651789652677211049841 12642488842239507908287381)
        ·
          refine ⟨592616664479976933200971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12642488842239507908287381 592616664479976933200971)
          ·
            refine ⟨888924996719965399801457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592616664479976933200971 888924996719965399801457)
            ·
              refine ⟨666693747539974049851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888924996719965399801457 666693747539974049851093)
              ·
                refine ⟨15625634707968141793385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 666693747539974049851093 15625634707968141793385)
                ·
                  rfl

theorem cell22_410816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_410816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410816 prefixEnd_410816 := by exact prefixLift 410816
  have htrace : WordTrace (prefixWord ++ tailWord_410816) baseStart_410816 baseEnd_410816 := by
    simpa [prefixWord, tailWord_410816, baseEnd_410816] using wordTrace_append hprefix tailTrace_410816
  have hstable : (prefixWord ++ tailWord_410816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410816).length < 2 ^ (prefixWord ++ tailWord_410816).sum := by decide
  have hdescent : baseEnd_410816 < baseStart_410816 := by decide
  rcases family_descends (prefixWord ++ tailWord_410816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410820 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_410820 : Nat := 118140960795 + 410820 * 2 ^ 59
def prefixEnd_410820 : Nat := 4983230072969 + 3 ^ 40 * 410820 * 2
def baseEnd_410820 : Nat := 140632081653458599040453

theorem tailTrace_410820 : CollatzResearch.WordTrace tailWord_410820 prefixEnd_410820 140632081653458599040453 := by
  unfold tailWord_410820
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491918185838388657594957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9989224247784518210126609 7491918185838388657594957)
  ·
    refine ⟨2809469319689395746598109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7491918185838388657594957 2809469319689395746598109)
    ·
      refine ⟨1053550994883523404974291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2809469319689395746598109 1053550994883523404974291)
      ·
        refine ⟨1580326492325285107461437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053550994883523404974291 1580326492325285107461437)
        ·
          refine ⟨592622434621981915298039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1580326492325285107461437 592622434621981915298039)
          ·
            refine ⟨888933651932972872947059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592622434621981915298039 888933651932972872947059)
            ·
              refine ⟨1333400477899459309420589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888933651932972872947059 1333400477899459309420589)
              ·
                refine ⟨500025179212297241032721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333400477899459309420589 500025179212297241032721)
                ·
                  refine ⟨375018884409222930774541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500025179212297241032721 375018884409222930774541)
                  ·
                    refine ⟨140632081653458599040453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375018884409222930774541 140632081653458599040453)
                    ·
                      rfl

theorem cell22_410820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_410820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410820 prefixEnd_410820 := by exact prefixLift 410820
  have htrace : WordTrace (prefixWord ++ tailWord_410820) baseStart_410820 baseEnd_410820 := by
    simpa [prefixWord, tailWord_410820, baseEnd_410820] using wordTrace_append hprefix tailTrace_410820
  have hstable : (prefixWord ++ tailWord_410820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410820).length < 2 ^ (prefixWord ++ tailWord_410820).sum := by decide
  have hdescent : baseEnd_410820 < baseStart_410820 := by decide
  rcases family_descends (prefixWord ++ tailWord_410820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410878 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_410878 : Nat := 118140960795 + 410878 * 2 ^ 59
def prefixEnd_410878 : Nat := 4983230072969 + 3 ^ 40 * 410878 * 2
def baseEnd_410878 : Nat := 46883978746255260363425

theorem tailTrace_410878 : CollatzResearch.WordTrace tailWord_410878 prefixEnd_410878 46883978746255260363425 := by
  unfold tailWord_410878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873243975683331652600161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9990634536977768813867525 1873243975683331652600161)
  ·
    refine ⟨1404932981762498739450121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1873243975683331652600161 1404932981762498739450121)
    ·
      refine ⟨1053699736321874054587591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1404932981762498739450121 1053699736321874054587591)
      ·
        refine ⟨1580549604482811081881387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053699736321874054587591 1580549604482811081881387)
        ·
          refine ⟨2370824406724216622822081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580549604482811081881387 2370824406724216622822081)
          ·
            refine ⟨1778118305043162467116561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370824406724216622822081 1778118305043162467116561)
            ·
              refine ⟨1333588728782371850337421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778118305043162467116561 1333588728782371850337421)
              ·
                refine ⟨500095773293389443876533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333588728782371850337421 500095773293389443876533)
                ·
                  refine ⟨46883978746255260363425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500095773293389443876533 46883978746255260363425)
                  ·
                    rfl

theorem cell22_410878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_410878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410878 prefixEnd_410878 := by exact prefixLift 410878
  have htrace : WordTrace (prefixWord ++ tailWord_410878) baseStart_410878 baseEnd_410878 := by
    simpa [prefixWord, tailWord_410878, baseEnd_410878] using wordTrace_append hprefix tailTrace_410878
  have hstable : (prefixWord ++ tailWord_410878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410878).length < 2 ^ (prefixWord ++ tailWord_410878).sum := by decide
  have hdescent : baseEnd_410878 < baseStart_410878 := by decide
  rcases family_descends (prefixWord ++ tailWord_410878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410891 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_410891 : Nat := 118140960795 + 410891 * 2 ^ 59
def prefixEnd_410891 : Nat := 4983230072969 + 3 ^ 40 * 410891 * 2
def baseEnd_410891 : Nat := 140656386404438080515235

theorem tailTrace_410891 : CollatzResearch.WordTrace tailWord_410891 prefixEnd_410891 140656386404438080515235 := by
  unfold tailWord_410891
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986425954419556441024527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9990950636279704294016351 14986425954419556441024527)
  ·
    refine ⟨22479638931629334661536791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14986425954419556441024527 22479638931629334661536791)
    ·
      refine ⟨33719458397444001992305187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22479638931629334661536791 33719458397444001992305187)
      ·
        refine ⟨50579187596166002988457781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33719458397444001992305187 50579187596166002988457781)
        ·
          refine ⟨4741798837140562780167917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50579187596166002988457781 4741798837140562780167917)
          ·
            refine ⟨1778174563927711042562969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4741798837140562780167917 1778174563927711042562969)
            ·
              refine ⟨1333630922945783281922227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778174563927711042562969 1333630922945783281922227)
              ·
                refine ⟨2000446384418674922883341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333630922945783281922227 2000446384418674922883341)
                ·
                  refine ⟨750167394157003096081253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2000446384418674922883341 750167394157003096081253)
                  ·
                    refine ⟨140656386404438080515235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750167394157003096081253 140656386404438080515235)
                    ·
                      rfl

theorem cell22_410891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_410891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410891 prefixEnd_410891 := by exact prefixLift 410891
  have htrace : WordTrace (prefixWord ++ tailWord_410891) baseStart_410891 baseEnd_410891 := by
    simpa [prefixWord, tailWord_410891, baseEnd_410891] using wordTrace_append hprefix tailTrace_410891
  have hstable : (prefixWord ++ tailWord_410891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410891).length < 2 ^ (prefixWord ++ tailWord_410891).sum := by decide
  have hdescent : baseEnd_410891 < baseStart_410891 := by decide
  rcases family_descends (prefixWord ++ tailWord_410891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410951 : List Nat := [1, 1, 4, 1, 2, 4, 1, 8]
def baseStart_410951 : Nat := 118140960795 + 410951 * 2 ^ 59
def prefixEnd_410951 : Nat := 4983230072969 + 3 ^ 40 * 410951 * 2
def baseEnd_410951 : Nat := 15630769514513102668339

theorem tailTrace_410951 : CollatzResearch.WordTrace tailWord_410951 prefixEnd_410951 15630769514513102668339 := by
  unfold tailWord_410951
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988614334202186688208707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9992409556134791125472471 14988614334202186688208707)
  ·
    refine ⟨22482921501303280032313061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14988614334202186688208707 22482921501303280032313061)
    ·
      refine ⟨4215547781494365006058699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22482921501303280032313061 4215547781494365006058699)
      ·
        refine ⟨6323321672241547509088049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215547781494365006058699 6323321672241547509088049)
        ·
          refine ⟨4742491254181160631816037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6323321672241547509088049 4742491254181160631816037)
          ·
            refine ⟨889217110158967618465507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4742491254181160631816037 889217110158967618465507)
            ·
              refine ⟨1333825665238451427698261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889217110158967618465507 1333825665238451427698261)
              ·
                refine ⟨15630769514513102668339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1333825665238451427698261 15630769514513102668339)
                ·
                  rfl

theorem cell22_410951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 8].length) (baseStart_410951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410951 prefixEnd_410951 := by exact prefixLift 410951
  have htrace : WordTrace (prefixWord ++ tailWord_410951) baseStart_410951 baseEnd_410951 := by
    simpa [prefixWord, tailWord_410951, baseEnd_410951] using wordTrace_append hprefix tailTrace_410951
  have hstable : (prefixWord ++ tailWord_410951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410951).length < 2 ^ (prefixWord ++ tailWord_410951).sum := by decide
  have hdescent : baseEnd_410951 < baseStart_410951 := by decide
  rcases family_descends (prefixWord ++ tailWord_410951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410981 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_410981 : Nat := 118140960795 + 410981 * 2 ^ 59
def prefixEnd_410981 : Nat := 4983230072969 + 3 ^ 40 * 410981 * 2
def baseEnd_410981 : Nat := 140687195243707845764959

theorem tailTrace_410981 : CollatzResearch.WordTrace tailWord_410981 prefixEnd_410981 140687195243707845764959 := by
  unfold tailWord_410981
  simp only [CollatzResearch.WordTrace]
  refine ⟨14989708524093501811800797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9993139016062334541200531 14989708524093501811800797)
  ·
    refine ⟨5621140696535063179425299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14989708524093501811800797 5621140696535063179425299)
    ·
      refine ⟨8431711044802594769137949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621140696535063179425299 8431711044802594769137949)
      ·
        refine ⟨3161891641800973038426731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8431711044802594769137949 3161891641800973038426731)
        ·
          refine ⟨4742837462701459557640097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161891641800973038426731 4742837462701459557640097)
          ·
            refine ⟨3557128097026094668230073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4742837462701459557640097 3557128097026094668230073)
            ·
              refine ⟨2667846072769571001172555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557128097026094668230073 2667846072769571001172555)
              ·
                refine ⟨4001769109154356501758833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667846072769571001172555 4001769109154356501758833)
                ·
                  refine ⟨3001326831865767376319125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001769109154356501758833 3001326831865767376319125)
                  ·
                    refine ⟨140687195243707845764959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3001326831865767376319125 140687195243707845764959)
                    ·
                      rfl

theorem cell22_410981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_410981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_410981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_410981 prefixEnd_410981 := by exact prefixLift 410981
  have htrace : WordTrace (prefixWord ++ tailWord_410981) baseStart_410981 baseEnd_410981 := by
    simpa [prefixWord, tailWord_410981, baseEnd_410981] using wordTrace_append hprefix tailTrace_410981
  have hstable : (prefixWord ++ tailWord_410981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410981).length < 2 ^ (prefixWord ++ tailWord_410981).sum := by decide
  have hdescent : baseEnd_410981 < baseStart_410981 := by decide
  rcases family_descends (prefixWord ++ tailWord_410981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411118 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_411118 : Nat := 118140960795 + 411118 * 2 ^ 59
def prefixEnd_411118 : Nat := 4983230072969 + 3 ^ 40 * 411118 * 2
def baseEnd_411118 : Nat := 140734093143485155089539

theorem tailTrace_411118 : CollatzResearch.WordTrace tailWord_411118 prefixEnd_411118 140734093143485155089539 := by
  unfold tailWord_411118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874338165574646776192251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9996470216398116139692005 1874338165574646776192251)
  ·
    refine ⟨2811507248361970164288377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874338165574646776192251 2811507248361970164288377)
    ·
      refine ⟨2108630436271477623216283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2811507248361970164288377 2108630436271477623216283)
      ·
        refine ⟨3162945654407216434824425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108630436271477623216283 3162945654407216434824425)
        ·
          refine ⟨2372209240805412326118319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162945654407216434824425 2372209240805412326118319)
          ·
            refine ⟨3558313861208118489177479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372209240805412326118319 3558313861208118489177479)
            ·
              refine ⟨5337470791812177733766219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558313861208118489177479 5337470791812177733766219)
              ·
                refine ⟨8006206187718266600649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337470791812177733766219 8006206187718266600649329)
                ·
                  refine ⟨6004654640788699950486997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8006206187718266600649329 6004654640788699950486997)
                  ·
                    refine ⟨140734093143485155089539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6004654640788699950486997 140734093143485155089539)
                    ·
                      rfl

theorem cell22_411118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_411118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411118 prefixEnd_411118 := by exact prefixLift 411118
  have htrace : WordTrace (prefixWord ++ tailWord_411118) baseStart_411118 baseEnd_411118 := by
    simpa [prefixWord, tailWord_411118, baseEnd_411118] using wordTrace_append hprefix tailTrace_411118
  have hstable : (prefixWord ++ tailWord_411118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411118).length < 2 ^ (prefixWord ++ tailWord_411118).sum := by decide
  have hdescent : baseEnd_411118 < baseStart_411118 := by decide
  rcases family_descends (prefixWord ++ tailWord_411118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411120 : List Nat := [2, 1, 1, 1, 3, 6, 2, 6]
def baseStart_411120 : Nat := 118140960795 + 411120 * 2 ^ 59
def prefixEnd_411120 : Nat := 4983230072969 + 3 ^ 40 * 411120 * 2
def baseEnd_411120 : Nat := 15637197531595312948837

theorem tailTrace_411120 : CollatzResearch.WordTrace tailWord_411120 prefixEnd_411120 15637197531595312948837 := by
  unfold tailWord_411120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497389135294964275555407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9996518847059952367407209 7497389135294964275555407)
  ·
    refine ⟨11246083702942446413333111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497389135294964275555407 11246083702942446413333111)
    ·
      refine ⟨16869125554413669619999667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246083702942446413333111 16869125554413669619999667)
      ·
        refine ⟨25303688331620504429999501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16869125554413669619999667 25303688331620504429999501)
        ·
          refine ⟨9488883124357689161249813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25303688331620504429999501 9488883124357689161249813)
          ·
            refine ⟨444791396454266679433585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9488883124357689161249813 444791396454266679433585)
            ·
              refine ⟨333593547340700009575189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444791396454266679433585 333593547340700009575189)
              ·
                refine ⟨15637197531595312948837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333593547340700009575189 15637197531595312948837)
                ·
                  rfl

theorem cell22_411120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_411120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411120 prefixEnd_411120 := by exact prefixLift 411120
  have htrace : WordTrace (prefixWord ++ tailWord_411120) baseStart_411120 baseEnd_411120 := by
    simpa [prefixWord, tailWord_411120, baseEnd_411120] using wordTrace_append hprefix tailTrace_411120
  have hstable : (prefixWord ++ tailWord_411120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411120).length < 2 ^ (prefixWord ++ tailWord_411120).sum := by decide
  have hdescent : baseEnd_411120 < baseStart_411120 := by decide
  rcases family_descends (prefixWord ++ tailWord_411120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411165 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 5]
def baseStart_411165 : Nat := 118140960795 + 411165 * 2 ^ 59
def prefixEnd_411165 : Nat := 4983230072969 + 3 ^ 40 * 411165 * 2
def baseEnd_411165 : Nat := 46916727401330899721465

theorem tailTrace_411165 : CollatzResearch.WordTrace tailWord_411165 prefixEnd_411165 46916727401330899721465 := by
  unfold tailWord_411165
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996419555426901236498949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9997613036951267490999299 14996419555426901236498949)
  ·
    refine ⟨2811828666642543981843553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14996419555426901236498949 2811828666642543981843553)
    ·
      refine ⟨2108871499981907986382665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2811828666642543981843553 2108871499981907986382665)
      ·
        refine ⟨1581653624986430989786999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108871499981907986382665 1581653624986430989786999)
        ·
          refine ⟨2372480437479646484680499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581653624986430989786999 2372480437479646484680499)
          ·
            refine ⟨3558720656219469727020749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372480437479646484680499 3558720656219469727020749)
            ·
              refine ⟨1334520246082301147632781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558720656219469727020749 1334520246082301147632781)
              ·
                refine ⟨500445092280862930362293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334520246082301147632781 500445092280862930362293)
                ·
                  refine ⟨46916727401330899721465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500445092280862930362293 46916727401330899721465)
                  ·
                    rfl

theorem cell22_411165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_411165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411165 prefixEnd_411165 := by exact prefixLift 411165
  have htrace : WordTrace (prefixWord ++ tailWord_411165) baseStart_411165 baseEnd_411165 := by
    simpa [prefixWord, tailWord_411165, baseEnd_411165] using wordTrace_append hprefix tailTrace_411165
  have hstable : (prefixWord ++ tailWord_411165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411165).length < 2 ^ (prefixWord ++ tailWord_411165).sum := by decide
  have hdescent : baseEnd_411165 < baseStart_411165 := by decide
  rcases family_descends (prefixWord ++ tailWord_411165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411246 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_411246 : Nat := 118140960795 + 411246 * 2 ^ 59
def prefixEnd_411246 : Nat := 4983230072969 + 3 ^ 40 * 411246 * 2
def baseEnd_411246 : Nat := 140777910159335487889147

theorem tailTrace_411246 : CollatzResearch.WordTrace tailWord_411246 prefixEnd_411246 140777910159335487889147 := by
  unfold tailWord_411246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874921733516681508774699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9999582578755634713465061 1874921733516681508774699)
  ·
    refine ⟨2812382600275022263162049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874921733516681508774699 2812382600275022263162049)
    ·
      refine ⟨2109286950206266697371537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2812382600275022263162049 2109286950206266697371537)
      ·
        refine ⟨1581965212654700023028653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109286950206266697371537 1581965212654700023028653)
        ·
          refine ⟨593236954745512508635745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1581965212654700023028653 593236954745512508635745)
          ·
            refine ⟨444927716059134381476809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593236954745512508635745 444927716059134381476809)
            ·
              refine ⟨333695787044350786107607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444927716059134381476809 333695787044350786107607)
              ·
                refine ⟨500543680566526179161411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333695787044350786107607 500543680566526179161411)
                ·
                  refine ⟨750815520849789268742117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500543680566526179161411 750815520849789268742117)
                  ·
                    refine ⟨140777910159335487889147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 750815520849789268742117 140777910159335487889147)
                    ·
                      rfl

theorem cell22_411246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_411246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411246 prefixEnd_411246 := by exact prefixLift 411246
  have htrace : WordTrace (prefixWord ++ tailWord_411246) baseStart_411246 baseEnd_411246 := by
    simpa [prefixWord, tailWord_411246, baseEnd_411246] using wordTrace_append hprefix tailTrace_411246
  have hstable : (prefixWord ++ tailWord_411246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411246).length < 2 ^ (prefixWord ++ tailWord_411246).sum := by decide
  have hdescent : baseEnd_411246 < baseStart_411246 := by decide
  rcases family_descends (prefixWord ++ tailWord_411246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411283 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 11]
def baseStart_411283 : Nat := 118140960795 + 411283 * 2 ^ 59
def prefixEnd_411283 : Nat := 4983230072969 + 3 ^ 40 * 411283 * 2
def baseEnd_411283 : Nat := 46930192005159908238011

theorem tailTrace_411283 : CollatzResearch.WordTrace tailWord_411283 prefixEnd_411283 46930192005159908238011 := by
  unfold tailWord_411283
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000723368999407389294503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10000482245999604926196335 15000723368999407389294503)
  ·
    refine ⟨22501085053499111083941755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000723368999407389294503 22501085053499111083941755)
    ·
      refine ⟨33751627580248666625912633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22501085053499111083941755 33751627580248666625912633)
      ·
        refine ⟨25313720685186499969434475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33751627580248666625912633 25313720685186499969434475)
        ·
          refine ⟨37970581027779749954151713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25313720685186499969434475 37970581027779749954151713)
          ·
            refine ⟨28477935770834812465613785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37970581027779749954151713 28477935770834812465613785)
            ·
              refine ⟨21358451828126109349210339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28477935770834812465613785 21358451828126109349210339)
              ·
                refine ⟨32037677742189164023815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21358451828126109349210339 32037677742189164023815509)
                ·
                  refine ⟨46930192005159908238011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 32037677742189164023815509 46930192005159908238011)
                  ·
                    rfl

theorem cell22_411283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_411283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411283 prefixEnd_411283 := by exact prefixLift 411283
  have htrace : WordTrace (prefixWord ++ tailWord_411283) baseStart_411283 baseEnd_411283 := by
    simpa [prefixWord, tailWord_411283, baseEnd_411283] using wordTrace_append hprefix tailTrace_411283
  have hstable : (prefixWord ++ tailWord_411283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411283).length < 2 ^ (prefixWord ++ tailWord_411283).sum := by decide
  have hdescent : baseEnd_411283 < baseStart_411283 := by decide
  rcases family_descends (prefixWord ++ tailWord_411283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411287 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 3, 3]
def baseStart_411287 : Nat := 118140960795 + 411287 * 2 ^ 59
def prefixEnd_411287 : Nat := 4983230072969 + 3 ^ 40 * 411287 * 2
def baseEnd_411287 : Nat := 140791945297225047614021

theorem tailTrace_411287 : CollatzResearch.WordTrace tailWord_411287 prefixEnd_411287 140791945297225047614021 := by
  unfold tailWord_411287
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000869260984916072440115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10000579507323277381626743 15000869260984916072440115)
  ·
    refine ⟨22501303891477374108660173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000869260984916072440115 22501303891477374108660173)
    ·
      refine ⟨8437988959304015290747565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22501303891477374108660173 8437988959304015290747565)
      ·
        refine ⟨3164245859739005734030337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8437988959304015290747565 3164245859739005734030337)
        ·
          refine ⟨2373184394804254300522753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164245859739005734030337 2373184394804254300522753)
          ·
            refine ⟨1779888296103190725392065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373184394804254300522753 1779888296103190725392065)
            ·
              refine ⟨1334916222077393044044049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779888296103190725392065 1334916222077393044044049)
              ·
                refine ⟨1001187166558044783033037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334916222077393044044049 1001187166558044783033037)
                ·
                  refine ⟨375445187459266793637389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001187166558044783033037 375445187459266793637389)
                  ·
                    refine ⟨140791945297225047614021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375445187459266793637389 140791945297225047614021)
                    ·
                      rfl

theorem cell22_411287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_411287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411287 prefixEnd_411287 := by exact prefixLift 411287
  have htrace : WordTrace (prefixWord ++ tailWord_411287) baseStart_411287 baseEnd_411287 := by
    simpa [prefixWord, tailWord_411287, baseEnd_411287] using wordTrace_append hprefix tailTrace_411287
  have hstable : (prefixWord ++ tailWord_411287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411287).length < 2 ^ (prefixWord ++ tailWord_411287).sum := by decide
  have hdescent : baseEnd_411287 < baseStart_411287 := by decide
  rcases family_descends (prefixWord ++ tailWord_411287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411300 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_411300 : Nat := 118140960795 + 411300 * 2 ^ 59
def prefixEnd_411300 : Nat := 4983230072969 + 3 ^ 40 * 411300 * 2
def baseEnd_411300 : Nat := 46932131820965782346327

theorem tailTrace_411300 : CollatzResearch.WordTrace tailWord_411300 prefixEnd_411300 46932131820965782346327 := by
  unfold tailWord_411300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500671704968909646331677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10000895606625212861775569 7500671704968909646331677)
  ·
    refine ⟨2812751889363341117374379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7500671704968909646331677 2812751889363341117374379)
    ·
      refine ⟨4219127834045011676061569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812751889363341117374379 4219127834045011676061569)
      ·
        refine ⟨3164345875533758757046177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219127834045011676061569 3164345875533758757046177)
        ·
          refine ⟨2373259406650319067784633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164345875533758757046177 2373259406650319067784633)
          ·
            refine ⟨1779944554987739300838475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373259406650319067784633 1779944554987739300838475)
            ·
              refine ⟨2669916832481608951257713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779944554987739300838475 2669916832481608951257713)
              ·
                refine ⟨2002437624361206713443285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669916832481608951257713 2002437624361206713443285)
                ·
                  refine ⟨46932131820965782346327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2002437624361206713443285 46932131820965782346327)
                  ·
                    rfl

theorem cell22_411300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_411300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411300 prefixEnd_411300 := by exact prefixLift 411300
  have htrace : WordTrace (prefixWord ++ tailWord_411300) baseStart_411300 baseEnd_411300 := by
    simpa [prefixWord, tailWord_411300, baseEnd_411300] using wordTrace_append hprefix tailTrace_411300
  have hstable : (prefixWord ++ tailWord_411300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411300).length < 2 ^ (prefixWord ++ tailWord_411300).sum := by decide
  have hdescent : baseEnd_411300 < baseStart_411300 := by decide
  rcases family_descends (prefixWord ++ tailWord_411300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411360 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_411360 : Nat := 118140960795 + 411360 * 2 ^ 59
def prefixEnd_411360 : Nat := 4983230072969 + 3 ^ 40 * 411360 * 2
def baseEnd_411360 : Nat := 140816934689077190538797

theorem tailTrace_411360 : CollatzResearch.WordTrace tailWord_411360 prefixEnd_411360 140816934689077190538797 := by
  unfold tailWord_411360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501765894860224769923767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10002354526480299693231689 7501765894860224769923767)
  ·
    refine ⟨11252648842290337154885651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501765894860224769923767 11252648842290337154885651)
    ·
      refine ⟨16878973263435505732328477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252648842290337154885651 16878973263435505732328477)
      ·
        refine ⟨6329614973788314649623179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16878973263435505732328477 6329614973788314649623179)
        ·
          refine ⟨9494422460682471974434769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329614973788314649623179 9494422460682471974434769)
          ·
            refine ⟨7120816845511853980826077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9494422460682471974434769 7120816845511853980826077)
            ·
              refine ⟨2670306317066945242809779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7120816845511853980826077 2670306317066945242809779)
              ·
                refine ⟨4005459475600417864214669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670306317066945242809779 4005459475600417864214669)
                ·
                  refine ⟨1502047303350156699080501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4005459475600417864214669 1502047303350156699080501)
                  ·
                    refine ⟨140816934689077190538797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1502047303350156699080501 140816934689077190538797)
                    ·
                      rfl

theorem cell22_411360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_411360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411360 prefixEnd_411360 := by exact prefixLift 411360
  have htrace : WordTrace (prefixWord ++ tailWord_411360) baseStart_411360 baseEnd_411360 := by
    simpa [prefixWord, tailWord_411360, baseEnd_411360] using wordTrace_append hprefix tailTrace_411360
  have hstable : (prefixWord ++ tailWord_411360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411360).length < 2 ^ (prefixWord ++ tailWord_411360).sum := by decide
  have hdescent : baseEnd_411360 < baseStart_411360 := by decide
  rcases family_descends (prefixWord ++ tailWord_411360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411364 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_411364 : Nat := 118140960795 + 411364 * 2 ^ 59
def prefixEnd_411364 : Nat := 4983230072969 + 3 ^ 40 * 411364 * 2
def baseEnd_411364 : Nat := 140818303970822513438785

theorem tailTrace_411364 : CollatzResearch.WordTrace tailWord_411364 prefixEnd_411364 140818303970822513438785 := by
  unfold tailWord_411364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501838840852979111496573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10002451787803972148662097 7501838840852979111496573)
  ·
    refine ⟨2813189565319867166811215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7501838840852979111496573 2813189565319867166811215)
    ·
      refine ⟨4219784347979800750216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813189565319867166811215 4219784347979800750216823)
      ·
        refine ⟨6329676521969701125325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219784347979800750216823 6329676521969701125325235)
        ·
          refine ⟨9494514782954551687987853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329676521969701125325235 9494514782954551687987853)
          ·
            refine ⟨3560443043607956882995445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9494514782954551687987853 3560443043607956882995445)
            ·
              refine ⟨333791535338245957780823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3560443043607956882995445 333791535338245957780823)
              ·
                refine ⟨500687303007368936671235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333791535338245957780823 500687303007368936671235)
                ·
                  refine ⟨751030954511053405006853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500687303007368936671235 751030954511053405006853)
                  ·
                    refine ⟨140818303970822513438785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751030954511053405006853 140818303970822513438785)
                    ·
                      rfl

theorem cell22_411364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_411364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411364 prefixEnd_411364 := by exact prefixLift 411364
  have htrace : WordTrace (prefixWord ++ tailWord_411364) baseStart_411364 baseEnd_411364 := by
    simpa [prefixWord, tailWord_411364, baseEnd_411364] using wordTrace_append hprefix tailTrace_411364
  have hstable : (prefixWord ++ tailWord_411364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411364).length < 2 ^ (prefixWord ++ tailWord_411364).sum := by decide
  have hdescent : baseEnd_411364 < baseStart_411364 := by decide
  rcases family_descends (prefixWord ++ tailWord_411364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411379 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 4]
def baseStart_411379 : Nat := 118140960795 + 411379 * 2 ^ 59
def prefixEnd_411379 : Nat := 4983230072969 + 3 ^ 40 * 411379 * 2
def baseEnd_411379 : Nat := 46941146259122491437913

theorem tailTrace_411379 : CollatzResearch.WordTrace tailWord_411379 prefixEnd_411379 46941146259122491437913 := by
  unfold tailWord_411379
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004224776651615784789191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10002816517767743856526127 15004224776651615784789191)
  ·
    refine ⟨22506337164977423677183787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004224776651615784789191 22506337164977423677183787)
    ·
      refine ⟨33759505747466135515775681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22506337164977423677183787 33759505747466135515775681)
      ·
        refine ⟨25319629310599601636831761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33759505747466135515775681 25319629310599601636831761)
        ·
          refine ⟨18989721982949701227623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25319629310599601636831761 18989721982949701227623821)
          ·
            refine ⟨7121145743606137960358933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18989721982949701227623821 7121145743606137960358933)
            ·
              refine ⟨333803706731537716891825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7121145743606137960358933 333803706731537716891825)
              ·
                refine ⟨250352780048653287668869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333803706731537716891825 250352780048653287668869)
                ·
                  refine ⟨46941146259122491437913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250352780048653287668869 46941146259122491437913)
                  ·
                    rfl

theorem cell22_411379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 4].length) (baseStart_411379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411379 prefixEnd_411379 := by exact prefixLift 411379
  have htrace : WordTrace (prefixWord ++ tailWord_411379) baseStart_411379 baseEnd_411379 := by
    simpa [prefixWord, tailWord_411379, baseEnd_411379] using wordTrace_append hprefix tailTrace_411379
  have hstable : (prefixWord ++ tailWord_411379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411379).length < 2 ^ (prefixWord ++ tailWord_411379).sum := by decide
  have hdescent : baseEnd_411379 < baseStart_411379 := by decide
  rcases family_descends (prefixWord ++ tailWord_411379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411394 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_411394 : Nat := 118140960795 + 411394 * 2 ^ 59
def prefixEnd_411394 : Nat := 4983230072969 + 3 ^ 40 * 411394 * 2
def baseEnd_411394 : Nat := 140828573583912435188693

theorem tailTrace_411394 : CollatzResearch.WordTrace tailWord_411394 prefixEnd_411394 140828573583912435188693 := by
  unfold tailWord_411394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751192967899318336646309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10003181247731515564390157 3751192967899318336646309)
  ·
    refine ⟨703348681481122188121183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3751192967899318336646309 703348681481122188121183)
    ·
      refine ⟨1055023022221683282181775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703348681481122188121183 1055023022221683282181775)
      ·
        refine ⟨1582534533332524923272663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055023022221683282181775 1582534533332524923272663)
        ·
          refine ⟨2373801799998787384908995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582534533332524923272663 2373801799998787384908995)
          ·
            refine ⟨3560702699998181077363493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373801799998787384908995 3560702699998181077363493)
            ·
              refine ⟨667631756249658952005655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3560702699998181077363493 667631756249658952005655)
              ·
                refine ⟨1001447634374488428008483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667631756249658952005655 1001447634374488428008483)
                ·
                  refine ⟨1502171451561732642012725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001447634374488428008483 1502171451561732642012725)
                  ·
                    refine ⟨140828573583912435188693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1502171451561732642012725 140828573583912435188693)
                    ·
                      rfl

theorem cell22_411394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_411394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411394 prefixEnd_411394 := by exact prefixLift 411394
  have htrace : WordTrace (prefixWord ++ tailWord_411394) baseStart_411394 baseEnd_411394 := by
    simpa [prefixWord, tailWord_411394, baseEnd_411394] using wordTrace_append hprefix tailTrace_411394
  have hstable : (prefixWord ++ tailWord_411394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411394).length < 2 ^ (prefixWord ++ tailWord_411394).sum := by decide
  have hdescent : baseEnd_411394 < baseStart_411394 := by decide
  rcases family_descends (prefixWord ++ tailWord_411394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411452 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_411452 : Nat := 118140960795 + 411452 * 2 ^ 59
def prefixEnd_411452 : Nat := 4983230072969 + 3 ^ 40 * 411452 * 2
def baseEnd_411452 : Nat := 46949476056406539079505

theorem tailTrace_411452 : CollatzResearch.WordTrace tailWord_411452 prefixEnd_411452 46949476056406539079505 := by
  unfold tailWord_411452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503443652693574626098305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10004591536924766168131073 7503443652693574626098305)
  ·
    refine ⟨5627582739520180969573729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7503443652693574626098305 5627582739520180969573729)
    ·
      refine ⟨4220687054640135727180297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5627582739520180969573729 4220687054640135727180297)
      ·
        refine ⟨3165515290980101795385223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4220687054640135727180297 3165515290980101795385223)
        ·
          refine ⟨4748272936470152693077835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165515290980101795385223 4748272936470152693077835)
          ·
            refine ⟨7122409404705229039616753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748272936470152693077835 7122409404705229039616753)
            ·
              refine ⟨5341807053528921779712565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122409404705229039616753 5341807053528921779712565)
              ·
                refine ⟨500794411268336416848053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5341807053528921779712565 500794411268336416848053)
                ·
                  refine ⟨46949476056406539079505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 500794411268336416848053 46949476056406539079505)
                  ·
                    rfl

theorem cell22_411452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_411452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411452 prefixEnd_411452 := by exact prefixLift 411452
  have htrace : WordTrace (prefixWord ++ tailWord_411452) baseStart_411452 baseEnd_411452 := by
    simpa [prefixWord, tailWord_411452, baseEnd_411452] using wordTrace_append hprefix tailTrace_411452
  have hstable : (prefixWord ++ tailWord_411452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411452).length < 2 ^ (prefixWord ++ tailWord_411452).sum := by decide
  have hdescent : baseEnd_411452 < baseStart_411452 := by decide
  rcases family_descends (prefixWord ++ tailWord_411452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411469 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 7]
def baseStart_411469 : Nat := 118140960795 + 411469 * 2 ^ 59
def prefixEnd_411469 : Nat := 4983230072969 + 3 ^ 40 * 411469 * 2
def baseEnd_411469 : Nat := 46951415872212413187821

theorem tailTrace_411469 : CollatzResearch.WordTrace tailWord_411469 prefixEnd_411469 46951415872212413187821 := by
  unfold tailWord_411469
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007507346325561155565461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10005004897550374103710307 15007507346325561155565461)
  ·
    refine ⟨703476906859010679167131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15007507346325561155565461 703476906859010679167131)
    ·
      refine ⟨1055215360288516018750697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703476906859010679167131 1055215360288516018750697)
      ·
        refine ⟨791411520216387014063023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055215360288516018750697 791411520216387014063023)
        ·
          refine ⟨1187117280324580521094535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791411520216387014063023 1187117280324580521094535)
          ·
            refine ⟨1780675920486870781641803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187117280324580521094535 1780675920486870781641803)
            ·
              refine ⟨2671013880730306172462705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780675920486870781641803 2671013880730306172462705)
              ·
                refine ⟨2003260410547729629347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671013880730306172462705 2003260410547729629347029)
                ·
                  refine ⟨46951415872212413187821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2003260410547729629347029 46951415872212413187821)
                  ·
                    rfl

theorem cell22_411469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_411469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411469 prefixEnd_411469 := by exact prefixLift 411469
  have htrace : WordTrace (prefixWord ++ tailWord_411469) baseStart_411469 baseEnd_411469 := by
    simpa [prefixWord, tailWord_411469, baseEnd_411469] using wordTrace_append hprefix tailTrace_411469
  have hstable : (prefixWord ++ tailWord_411469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411469).length < 2 ^ (prefixWord ++ tailWord_411469).sum := by decide
  have hdescent : baseEnd_411469 < baseStart_411469 := by decide
  rcases family_descends (prefixWord ++ tailWord_411469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411473 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_411473 : Nat := 118140960795 + 411473 * 2 ^ 59
def prefixEnd_411473 : Nat := 4983230072969 + 3 ^ 40 * 411473 * 2
def baseEnd_411473 : Nat := 140855616898382562463451

theorem tailTrace_411473 : CollatzResearch.WordTrace tailWord_411473 prefixEnd_411473 140855616898382562463451 := by
  unfold tailWord_411473
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007653238311069838711073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10005102158874046559140715 15007653238311069838711073)
  ·
    refine ⟨11255739928733302379033305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15007653238311069838711073 11255739928733302379033305)
    ·
      refine ⟨8441804946549976784274979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11255739928733302379033305 8441804946549976784274979)
      ·
        refine ⟨12662707419824965176412469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441804946549976784274979 12662707419824965176412469)
        ·
          refine ⟨1187128820608590485288669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12662707419824965176412469 1187128820608590485288669)
          ·
            refine ⟨445173307728221431983251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1187128820608590485288669 445173307728221431983251)
            ·
              refine ⟨667759961592332147974877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445173307728221431983251 667759961592332147974877)
              ·
                refine ⟨250409985597124555490579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667759961592332147974877 250409985597124555490579)
                ·
                  refine ⟨375614978395686833235869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250409985597124555490579 375614978395686833235869)
                  ·
                    refine ⟨140855616898382562463451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375614978395686833235869 140855616898382562463451)
                    ·
                      rfl

theorem cell22_411473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_411473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411473 prefixEnd_411473 := by exact prefixLift 411473
  have htrace : WordTrace (prefixWord ++ tailWord_411473) baseStart_411473 baseEnd_411473 := by
    simpa [prefixWord, tailWord_411473, baseEnd_411473] using wordTrace_append hprefix tailTrace_411473
  have hstable : (prefixWord ++ tailWord_411473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411473).length < 2 ^ (prefixWord ++ tailWord_411473).sum := by decide
  have hdescent : baseEnd_411473 < baseStart_411473 := by decide
  rcases family_descends (prefixWord ++ tailWord_411473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411490 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_411490 : Nat := 118140960795 + 411490 * 2 ^ 59
def prefixEnd_411490 : Nat := 4983230072969 + 3 ^ 40 * 411490 * 2
def baseEnd_411490 : Nat := 140861436345800184788399

theorem tailTrace_411490 : CollatzResearch.WordTrace tailWord_411490 prefixEnd_411490 140861436345800184788399 := by
  unfold tailWord_411490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752068319812370435519981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10005515519499654494719949 3752068319812370435519981)
  ·
    refine ⟨1407025619929638913319993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3752068319812370435519981 1407025619929638913319993)
    ·
      refine ⟨1055269214947229184989995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1407025619929638913319993 1055269214947229184989995)
      ·
        refine ⟨1582903822420843777484993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055269214947229184989995 1582903822420843777484993)
        ·
          refine ⟨1187177866815632833113745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582903822420843777484993 1187177866815632833113745)
          ·
            refine ⟨890383400111724624835309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187177866815632833113745 890383400111724624835309)
            ·
              refine ⟨333893775041896734313241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890383400111724624835309 333893775041896734313241)
              ·
                refine ⟨250420331281422550734931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333893775041896734313241 250420331281422550734931)
                ·
                  refine ⟨375630496922133826102397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250420331281422550734931 375630496922133826102397)
                  ·
                    refine ⟨140861436345800184788399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375630496922133826102397 140861436345800184788399)
                    ·
                      rfl

theorem cell22_411490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_411490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411490 prefixEnd_411490 := by exact prefixLift 411490
  have htrace : WordTrace (prefixWord ++ tailWord_411490) baseStart_411490 baseEnd_411490 := by
    simpa [prefixWord, tailWord_411490, baseEnd_411490] using wordTrace_append hprefix tailTrace_411490
  have hstable : (prefixWord ++ tailWord_411490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411490).length < 2 ^ (prefixWord ++ tailWord_411490).sum := by decide
  have hdescent : baseEnd_411490 < baseStart_411490 := by decide
  rcases family_descends (prefixWord ++ tailWord_411490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411546 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_411546 : Nat := 118140960795 + 411546 * 2 ^ 59
def prefixEnd_411546 : Nat := 4983230072969 + 3 ^ 40 * 411546 * 2
def baseEnd_411546 : Nat := 140880606290234705388227

theorem tailTrace_411546 : CollatzResearch.WordTrace tailWord_411546 prefixEnd_411546 140880606290234705388227 := by
  unfold tailWord_411546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752578941761650826529623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10006877178031068870745661 3752578941761650826529623)
  ·
    refine ⟨5628868412642476239794435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3752578941761650826529623 5628868412642476239794435)
    ·
      refine ⟨8443302618963714359691653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628868412642476239794435 8443302618963714359691653)
      ·
        refine ⟨1583119241055696442442185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8443302618963714359691653 1583119241055696442442185)
        ·
          refine ⟨1187339430791772331831639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583119241055696442442185 1187339430791772331831639)
          ·
            refine ⟨1781009146187658497747459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187339430791772331831639 1781009146187658497747459)
            ·
              refine ⟨2671513719281487746621189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781009146187658497747459 2671513719281487746621189)
              ·
                refine ⟨500908822365278952491473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2671513719281487746621189 500908822365278952491473)
                ·
                  refine ⟨375681616773959214368605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500908822365278952491473 375681616773959214368605)
                  ·
                    refine ⟨140880606290234705388227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375681616773959214368605 140880606290234705388227)
                    ·
                      rfl

theorem cell22_411546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_411546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411546 prefixEnd_411546 := by exact prefixLift 411546
  have htrace : WordTrace (prefixWord ++ tailWord_411546) baseStart_411546 baseEnd_411546 := by
    simpa [prefixWord, tailWord_411546, baseEnd_411546] using wordTrace_append hprefix tailTrace_411546
  have hstable : (prefixWord ++ tailWord_411546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411546).length < 2 ^ (prefixWord ++ tailWord_411546).sum := by decide
  have hdescent : baseEnd_411546 < baseStart_411546 := by decide
  rcases family_descends (prefixWord ++ tailWord_411546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411548 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_411548 : Nat := 118140960795 + 411548 * 2 ^ 59
def prefixEnd_411548 : Nat := 4983230072969 + 3 ^ 40 * 411548 * 2
def baseEnd_411548 : Nat := 46960430310369122279407

theorem tailTrace_411548 : CollatzResearch.WordTrace tailWord_411548 prefixEnd_411548 46960430310369122279407 := by
  unfold tailWord_411548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505194356519678823845649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10006925808692905098460865 7505194356519678823845649)
  ·
    refine ⟨5628895767389759117884237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7505194356519678823845649 5628895767389759117884237)
    ·
      refine ⟨2110835912771159669206589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5628895767389759117884237 2110835912771159669206589)
      ·
        refine ⟨791563467289184875952471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2110835912771159669206589 791563467289184875952471)
        ·
          refine ⟨1187345200933777313928707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791563467289184875952471 1187345200933777313928707)
          ·
            refine ⟨1781017801400665970893061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187345200933777313928707 1781017801400665970893061)
            ·
              refine ⟨333940837762624869542449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1781017801400665970893061 333940837762624869542449)
              ·
                refine ⟨250455628321968652156837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333940837762624869542449 250455628321968652156837)
                ·
                  refine ⟨46960430310369122279407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250455628321968652156837 46960430310369122279407)
                  ·
                    rfl

theorem cell22_411548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_411548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411548 prefixEnd_411548 := by exact prefixLift 411548
  have htrace : WordTrace (prefixWord ++ tailWord_411548) baseStart_411548 baseEnd_411548 := by
    simpa [prefixWord, tailWord_411548, baseEnd_411548] using wordTrace_append hprefix tailTrace_411548
  have hstable : (prefixWord ++ tailWord_411548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411548).length < 2 ^ (prefixWord ++ tailWord_411548).sum := by decide
  have hdescent : baseEnd_411548 < baseStart_411548 := by decide
  rcases family_descends (prefixWord ++ tailWord_411548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411559 : List Nat := [1, 1, 6, 1, 2, 1, 3, 7]
def baseStart_411559 : Nat := 118140960795 + 411559 * 2 ^ 59
def prefixEnd_411559 : Nat := 4983230072969 + 3 ^ 40 * 411559 * 2
def baseEnd_411559 : Nat := 15653895161767444979243

theorem tailTrace_411559 : CollatzResearch.WordTrace tailWord_411559 prefixEnd_411559 15653895161767444979243 := by
  unfold tailWord_411559
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010789915999506526341731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10007193277333004350894487 15010789915999506526341731)
  ·
    refine ⟨22516184873999259789512597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15010789915999506526341731 22516184873999259789512597)
    ·
      refine ⟨1055446165968715302633403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22516184873999259789512597 1055446165968715302633403)
      ·
        refine ⟨1583169248953072953950105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055446165968715302633403 1583169248953072953950105)
        ·
          refine ⟨1187376936714804715462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583169248953072953950105 1187376936714804715462579)
          ·
            refine ⟨1781065405072207073193869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187376936714804715462579 1781065405072207073193869)
            ·
              refine ⟨667899526902077652447701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1781065405072207073193869 667899526902077652447701)
              ·
                refine ⟨15653895161767444979243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 667899526902077652447701 15653895161767444979243)
                ·
                  rfl

theorem cell22_411559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 7].length) (baseStart_411559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411559 prefixEnd_411559 := by exact prefixLift 411559
  have htrace : WordTrace (prefixWord ++ tailWord_411559) baseStart_411559 baseEnd_411559 := by
    simpa [prefixWord, tailWord_411559, baseEnd_411559] using wordTrace_append hprefix tailTrace_411559
  have hstable : (prefixWord ++ tailWord_411559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411559).length < 2 ^ (prefixWord ++ tailWord_411559).sum := by decide
  have hdescent : baseEnd_411559 < baseStart_411559 := by decide
  rcases family_descends (prefixWord ++ tailWord_411559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411604 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_411604 : Nat := 118140960795 + 411604 * 2 ^ 59
def prefixEnd_411604 : Nat := 4983230072969 + 3 ^ 40 * 411604 * 2
def baseEnd_411604 : Nat := 46966820291847295812683

theorem tailTrace_411604 : CollatzResearch.WordTrace tailWord_411604 prefixEnd_411604 46966820291847295812683 := by
  unfold tailWord_411604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506215600418239605864933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10008287467224319474486577 7506215600418239605864933)
  ·
    refine ⟨1407415425078419926099675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7506215600418239605864933 1407415425078419926099675)
    ·
      refine ⟨2111123137617629889149513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407415425078419926099675 2111123137617629889149513)
      ·
        refine ⟨1583342353213222416862135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111123137617629889149513 1583342353213222416862135)
        ·
          refine ⟨2375013529819833625293203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583342353213222416862135 2375013529819833625293203)
          ·
            refine ⟨3562520294729750437939805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375013529819833625293203 3562520294729750437939805)
            ·
              refine ⟨1335945110523656414227427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3562520294729750437939805 1335945110523656414227427)
              ·
                refine ⟨2003917665785484621341141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335945110523656414227427 2003917665785484621341141)
                ·
                  refine ⟨46966820291847295812683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2003917665785484621341141 46966820291847295812683)
                  ·
                    rfl

theorem cell22_411604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_411604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411604 prefixEnd_411604 := by exact prefixLift 411604
  have htrace : WordTrace (prefixWord ++ tailWord_411604) baseStart_411604 baseEnd_411604 := by
    simpa [prefixWord, tailWord_411604, baseEnd_411604] using wordTrace_append hprefix tailTrace_411604
  have hstable : (prefixWord ++ tailWord_411604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411604).length < 2 ^ (prefixWord ++ tailWord_411604).sum := by decide
  have hdescent : baseEnd_411604 < baseStart_411604 := by decide
  rcases family_descends (prefixWord ++ tailWord_411604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411619 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_411619 : Nat := 118140960795 + 411619 * 2 ^ 59
def prefixEnd_411619 : Nat := 4983230072969 + 3 ^ 40 * 411619 * 2
def baseEnd_411619 : Nat := 140905595682086848313003

theorem tailTrace_411619 : CollatzResearch.WordTrace tailWord_411619 prefixEnd_411619 140905595682086848313003 := by
  unfold tailWord_411619
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012978295782136773525911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008652197188091182350607 15012978295782136773525911)
  ·
    refine ⟨22519467443673205160288867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15012978295782136773525911 22519467443673205160288867)
    ·
      refine ⟨33779201165509807740433301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22519467443673205160288867 33779201165509807740433301)
      ·
        refine ⟨1583400054633272237832811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33779201165509807740433301 1583400054633272237832811)
        ·
          refine ⟨2375100081949908356749217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583400054633272237832811 2375100081949908356749217)
          ·
            refine ⟨1781325061462431267561913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375100081949908356749217 1781325061462431267561913)
            ·
              refine ⟨1335993796096823450671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781325061462431267561913 1335993796096823450671435)
              ·
                refine ⟨2003990694145235176007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335993796096823450671435 2003990694145235176007153)
                ·
                  refine ⟨1502993020608926382005365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003990694145235176007153 1502993020608926382005365)
                  ·
                    refine ⟨140905595682086848313003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1502993020608926382005365 140905595682086848313003)
                    ·
                      rfl

theorem cell22_411619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_411619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411619 prefixEnd_411619 := by exact prefixLift 411619
  have htrace : WordTrace (prefixWord ++ tailWord_411619) baseStart_411619 baseEnd_411619 := by
    simpa [prefixWord, tailWord_411619, baseEnd_411619] using wordTrace_append hprefix tailTrace_411619
  have hstable : (prefixWord ++ tailWord_411619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411619).length < 2 ^ (prefixWord ++ tailWord_411619).sum := by decide
  have hdescent : baseEnd_411619 < baseStart_411619 := by decide
  rcases family_descends (prefixWord ++ tailWord_411619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411679 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_411679 : Nat := 118140960795 + 411679 * 2 ^ 59
def prefixEnd_411679 : Nat := 4983230072969 + 3 ^ 40 * 411679 * 2
def baseEnd_411679 : Nat := 140926134908266691812819

theorem tailTrace_411679 : CollatzResearch.WordTrace tailWord_411679 prefixEnd_411679 140926134908266691812819 := by
  unfold tailWord_411679
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015166675564767020710091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10010111117043178013806727 15015166675564767020710091)
  ·
    refine ⟨22522750013347150531065137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15015166675564767020710091 22522750013347150531065137)
    ·
      refine ⟨16892062510010362898298853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22522750013347150531065137 16892062510010362898298853)
      ·
        refine ⟨3167261720626943043431035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16892062510010362898298853 3167261720626943043431035)
        ·
          refine ⟨4750892580940414565146553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167261720626943043431035 4750892580940414565146553)
          ·
            refine ⟨3563169435705310923859915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750892580940414565146553 3563169435705310923859915)
            ·
              refine ⟨5344754153557966385789873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563169435705310923859915 5344754153557966385789873)
              ·
                refine ⟨4008565615168474789342405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344754153557966385789873 4008565615168474789342405)
                ·
                  refine ⟨751606052844089023001701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4008565615168474789342405 751606052844089023001701)
                  ·
                    refine ⟨140926134908266691812819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751606052844089023001701 140926134908266691812819)
                    ·
                      rfl

theorem cell22_411679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_411679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411679 prefixEnd_411679 := by exact prefixLift 411679
  have htrace : WordTrace (prefixWord ++ tailWord_411679) baseStart_411679 baseEnd_411679 := by
    simpa [prefixWord, tailWord_411679, baseEnd_411679] using wordTrace_append hprefix tailTrace_411679
  have hstable : (prefixWord ++ tailWord_411679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411679).length < 2 ^ (prefixWord ++ tailWord_411679).sum := by decide
  have hdescent : baseEnd_411679 < baseStart_411679 := by decide
  rcases family_descends (prefixWord ++ tailWord_411679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411696 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_411696 : Nat := 118140960795 + 411696 * 2 ^ 59
def prefixEnd_411696 : Nat := 4983230072969 + 3 ^ 40 * 411696 * 2
def baseEnd_411696 : Nat := 140931954355684314137767

theorem tailTrace_411696 : CollatzResearch.WordTrace tailWord_411696 prefixEnd_411696 140931954355684314137767 := by
  unfold tailWord_411696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507893358251589462039471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10010524477668785949385961 7507893358251589462039471)
  ·
    refine ⟨11261840037377384193059207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7507893358251589462039471 11261840037377384193059207)
    ·
      refine ⟨16892760056066076289588811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11261840037377384193059207 16892760056066076289588811)
      ·
        refine ⟨25339140084099114434383217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16892760056066076289588811 25339140084099114434383217)
        ·
          refine ⟨19004355063074335825787413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25339140084099114434383217 19004355063074335825787413)
          ·
            refine ⟨890829143581609491833785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19004355063074335825787413 890829143581609491833785)
            ·
              refine ⟨668121857686207118875339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890829143581609491833785 668121857686207118875339)
              ·
                refine ⟨1002182786529310678313009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668121857686207118875339 1002182786529310678313009)
                ·
                  refine ⟨751637089896983008734757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002182786529310678313009 751637089896983008734757)
                  ·
                    refine ⟨140931954355684314137767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751637089896983008734757 140931954355684314137767)
                    ·
                      rfl

theorem cell22_411696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_411696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411696 prefixEnd_411696 := by exact prefixLift 411696
  have htrace : WordTrace (prefixWord ++ tailWord_411696) baseStart_411696 baseEnd_411696 := by
    simpa [prefixWord, tailWord_411696, baseEnd_411696] using wordTrace_append hprefix tailTrace_411696
  have hstable : (prefixWord ++ tailWord_411696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411696).length < 2 ^ (prefixWord ++ tailWord_411696).sum := by decide
  have hdescent : baseEnd_411696 < baseStart_411696 := by decide
  rcases family_descends (prefixWord ++ tailWord_411696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411724 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_411724 : Nat := 118140960795 + 411724 * 2 ^ 59
def prefixEnd_411724 : Nat := 4983230072969 + 3 ^ 40 * 411724 * 2
def baseEnd_411724 : Nat := 140941539327901574437681

theorem tailTrace_411724 : CollatzResearch.WordTrace tailWord_411724 prefixEnd_411724 140941539327901574437681 := by
  unfold tailWord_411724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508403980200869853049113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10011205306934493137398817 7508403980200869853049113)
  ·
    refine ⟨5631302985150652389786835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508403980200869853049113 5631302985150652389786835)
    ·
      refine ⟨8446954477725978584680253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631302985150652389786835 8446954477725978584680253)
      ·
        refine ⟨3167607929147241969255095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8446954477725978584680253 3167607929147241969255095)
        ·
          refine ⟨4751411893720862953882643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167607929147241969255095 4751411893720862953882643)
          ·
            refine ⟨7127117840581294430823965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751411893720862953882643 7127117840581294430823965)
            ·
              refine ⟨2672669190217985411558987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7127117840581294430823965 2672669190217985411558987)
              ·
                refine ⟨4009003785326978117338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672669190217985411558987 4009003785326978117338481)
                ·
                  refine ⟨3006752838995233588003861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009003785326978117338481 3006752838995233588003861)
                  ·
                    refine ⟨140941539327901574437681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3006752838995233588003861 140941539327901574437681)
                    ·
                      rfl

theorem cell22_411724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_411724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411724 prefixEnd_411724 := by exact prefixLift 411724
  have htrace : WordTrace (prefixWord ++ tailWord_411724) baseStart_411724 baseEnd_411724 := by
    simpa [prefixWord, tailWord_411724, baseEnd_411724] using wordTrace_append hprefix tailTrace_411724
  have hstable : (prefixWord ++ tailWord_411724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411724).length < 2 ^ (prefixWord ++ tailWord_411724).sum := by decide
  have hdescent : baseEnd_411724 < baseStart_411724 := by decide
  rcases family_descends (prefixWord ++ tailWord_411724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411760 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_411760 : Nat := 118140960795 + 411760 * 2 ^ 59
def prefixEnd_411760 : Nat := 4983230072969 + 3 ^ 40 * 411760 * 2
def baseEnd_411760 : Nat := 140953862863609480537571

theorem tailTrace_411760 : CollatzResearch.WordTrace tailWord_411760 prefixEnd_411760 140953862863609480537571 := by
  unfold tailWord_411760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509060494135658927204367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10012080658847545236272489 7509060494135658927204367)
  ·
    refine ⟨11263590741203488390806551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509060494135658927204367 11263590741203488390806551)
    ·
      refine ⟨16895386111805232586209827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263590741203488390806551 16895386111805232586209827)
      ·
        refine ⟨25343079167707848879314741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16895386111805232586209827 25343079167707848879314741)
        ·
          refine ⟨2375913671972610832435757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25343079167707848879314741 2375913671972610832435757)
          ·
            refine ⟨890967626989729062163409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2375913671972610832435757 890967626989729062163409)
            ·
              refine ⟨668225720242296796622557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890967626989729062163409 668225720242296796622557)
              ·
                refine ⟨250584645090861298733459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668225720242296796622557 250584645090861298733459)
                ·
                  refine ⟨375876967636291948100189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250584645090861298733459 375876967636291948100189)
                  ·
                    refine ⟨140953862863609480537571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375876967636291948100189 140953862863609480537571)
                    ·
                      rfl

theorem cell22_411760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_411760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411760 prefixEnd_411760 := by exact prefixLift 411760
  have htrace : WordTrace (prefixWord ++ tailWord_411760) baseStart_411760 baseEnd_411760 := by
    simpa [prefixWord, tailWord_411760, baseEnd_411760] using wordTrace_append hprefix tailTrace_411760
  have hstable : (prefixWord ++ tailWord_411760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411760).length < 2 ^ (prefixWord ++ tailWord_411760).sum := by decide
  have hdescent : baseEnd_411760 < baseStart_411760 := by decide
  rcases family_descends (prefixWord ++ tailWord_411760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411773 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 5]
def baseStart_411773 : Nat := 118140960795 + 411773 * 2 ^ 59
def prefixEnd_411773 : Nat := 4983230072969 + 3 ^ 40 * 411773 * 2
def baseEnd_411773 : Nat := 46986104343093926654177

theorem tailTrace_411773 : CollatzResearch.WordTrace tailWord_411773 prefixEnd_411773 46986104343093926654177 := by
  unfold tailWord_411773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15018595137224221074631973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10012396758149480716421315 15018595137224221074631973)
  ·
    refine ⟨2815986588229541451493495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15018595137224221074631973 2815986588229541451493495)
    ·
      refine ⟨4223979882344312177240243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815986588229541451493495 4223979882344312177240243)
      ·
        refine ⟨6335969823516468265860365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223979882344312177240243 6335969823516468265860365)
        ·
          refine ⟨2375988683818675599697637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6335969823516468265860365 2375988683818675599697637)
          ·
            refine ⟨445497878216001674943307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2375988683818675599697637 445497878216001674943307)
            ·
              refine ⟨668246817324002512414961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445497878216001674943307 668246817324002512414961)
              ·
                refine ⟨501185112993001884311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668246817324002512414961 501185112993001884311221)
                ·
                  refine ⟨46986104343093926654177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501185112993001884311221 46986104343093926654177)
                  ·
                    rfl

theorem cell22_411773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_411773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411773 prefixEnd_411773 := by exact prefixLift 411773
  have htrace : WordTrace (prefixWord ++ tailWord_411773) baseStart_411773 baseEnd_411773 := by
    simpa [prefixWord, tailWord_411773, baseEnd_411773] using wordTrace_append hprefix tailTrace_411773
  have hstable : (prefixWord ++ tailWord_411773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411773).length < 2 ^ (prefixWord ++ tailWord_411773).sum := by decide
  have hdescent : baseEnd_411773 < baseStart_411773 := by decide
  rcases family_descends (prefixWord ++ tailWord_411773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411790 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_411790 : Nat := 118140960795 + 411790 * 2 ^ 59
def prefixEnd_411790 : Nat := 4983230072969 + 3 ^ 40 * 411790 * 2
def baseEnd_411790 : Nat := 46988044158899800762493

theorem tailTrace_411790 : CollatzResearch.WordTrace tailWord_411790 prefixEnd_411790 46988044158899800762493 := by
  unfold tailWord_411790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877401897270329122250103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10012810118775088652000549 1877401897270329122250103)
  ·
    refine ⟨2816102845905493683375155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877401897270329122250103 2816102845905493683375155)
    ·
      refine ⟨4224154268858240525062733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816102845905493683375155 4224154268858240525062733)
      ·
        refine ⟨1584057850821840196898525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4224154268858240525062733 1584057850821840196898525)
        ·
          refine ⟨594021694058190073836947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1584057850821840196898525 594021694058190073836947)
          ·
            refine ⟨891032541087285110755421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594021694058190073836947 891032541087285110755421)
            ·
              refine ⟨334137202907731916533283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891032541087285110755421 334137202907731916533283)
              ·
                refine ⟨501205804361597874799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334137202907731916533283 501205804361597874799925)
                ·
                  refine ⟨46988044158899800762493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501205804361597874799925 46988044158899800762493)
                  ·
                    rfl

theorem cell22_411790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_411790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411790 prefixEnd_411790 := by exact prefixLift 411790
  have htrace : WordTrace (prefixWord ++ tailWord_411790) baseStart_411790 baseEnd_411790 := by
    simpa [prefixWord, tailWord_411790, baseEnd_411790] using wordTrace_append hprefix tailTrace_411790
  have hstable : (prefixWord ++ tailWord_411790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411790).length < 2 ^ (prefixWord ++ tailWord_411790).sum := by decide
  have hdescent : baseEnd_411790 < baseStart_411790 := by decide
  rcases family_descends (prefixWord ++ tailWord_411790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411828 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_411828 : Nat := 118140960795 + 411828 * 2 ^ 59
def prefixEnd_411828 : Nat := 4983230072969 + 3 ^ 40 * 411828 * 2
def baseEnd_411828 : Nat := 140977140653279969837363

theorem tailTrace_411828 : CollatzResearch.WordTrace tailWord_411828 prefixEnd_411828 140977140653279969837363 := by
  unfold tailWord_411828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510300576012482733942069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10013734101349976978589425 7510300576012482733942069)
  ·
    refine ⟨704090679001170256307069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7510300576012482733942069 704090679001170256307069)
    ·
      refine ⟨264034004625438846115151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 704090679001170256307069 264034004625438846115151)
      ·
        refine ⟨396051006938158269172727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264034004625438846115151 396051006938158269172727)
        ·
          refine ⟨594076510407237403759091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396051006938158269172727 594076510407237403759091)
          ·
            refine ⟨891114765610856105638637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594076510407237403759091 891114765610856105638637)
            ·
              refine ⟨334168037104071039614489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891114765610856105638637 334168037104071039614489)
              ·
                refine ⟨250626027828053279710867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334168037104071039614489 250626027828053279710867)
                ·
                  refine ⟨375939041742079919566301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250626027828053279710867 375939041742079919566301)
                  ·
                    refine ⟨140977140653279969837363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375939041742079919566301 140977140653279969837363)
                    ·
                      rfl

theorem cell22_411828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_411828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411828 prefixEnd_411828 := by exact prefixLift 411828
  have htrace : WordTrace (prefixWord ++ tailWord_411828) baseStart_411828 baseEnd_411828 := by
    simpa [prefixWord, tailWord_411828, baseEnd_411828] using wordTrace_append hprefix tailTrace_411828
  have hstable : (prefixWord ++ tailWord_411828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411828).length < 2 ^ (prefixWord ++ tailWord_411828).sum := by decide
  have hdescent : baseEnd_411828 < baseStart_411828 := by decide
  rcases family_descends (prefixWord ++ tailWord_411828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411831 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_411831 : Nat := 118140960795 + 411831 * 2 ^ 59
def prefixEnd_411831 : Nat := 4983230072969 + 3 ^ 40 * 411831 * 2
def baseEnd_411831 : Nat := 140978167614588962012353

theorem tailTrace_411831 : CollatzResearch.WordTrace tailWord_411831 prefixEnd_411831 140978167614588962012353 := by
  unfold tailWord_411831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020710571014096980243347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013807047342731320162231 15020710571014096980243347)
  ·
    refine ⟨22531065856521145470365021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15020710571014096980243347 22531065856521145470365021)
    ·
      refine ⟨8449149696195429551386883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22531065856521145470365021 8449149696195429551386883)
      ·
        refine ⟨12673724544293144327080325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449149696195429551386883 12673724544293144327080325)
        ·
          refine ⟨2376323352054964561327561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12673724544293144327080325 2376323352054964561327561)
          ·
            refine ⟨1782242514041223420995671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376323352054964561327561 1782242514041223420995671)
            ·
              refine ⟨2673363771061835131493507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782242514041223420995671 2673363771061835131493507)
              ·
                refine ⟨4010045656592752697240261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673363771061835131493507 4010045656592752697240261)
                ·
                  refine ⟨751883560611141130732549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4010045656592752697240261 751883560611141130732549)
                  ·
                    refine ⟨140978167614588962012353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751883560611141130732549 140978167614588962012353)
                    ·
                      rfl

theorem cell22_411831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_411831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411831 prefixEnd_411831 := by exact prefixLift 411831
  have htrace : WordTrace (prefixWord ++ tailWord_411831) baseStart_411831 baseEnd_411831 := by
    simpa [prefixWord, tailWord_411831, baseEnd_411831] using wordTrace_append hprefix tailTrace_411831
  have hstable : (prefixWord ++ tailWord_411831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411831).length < 2 ^ (prefixWord ++ tailWord_411831).sum := by decide
  have hdescent : baseEnd_411831 < baseStart_411831 := by decide
  rcases family_descends (prefixWord ++ tailWord_411831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411833 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_411833 : Nat := 118140960795 + 411833 * 2 ^ 59
def prefixEnd_411833 : Nat := 4983230072969 + 3 ^ 40 * 411833 * 2
def baseEnd_411833 : Nat := 140978852255461623462347

theorem tailTrace_411833 : CollatzResearch.WordTrace tailWord_411833 prefixEnd_411833 140978852255461623462347 := by
  unfold tailWord_411833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020783517006851321816153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013855678004567547877435 15020783517006851321816153)
  ·
    refine ⟨11265587637755138491362115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15020783517006851321816153 11265587637755138491362115)
    ·
      refine ⟨16898381456632707737043173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265587637755138491362115 16898381456632707737043173)
      ·
        refine ⟨3168446523118632700695595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16898381456632707737043173 3168446523118632700695595)
        ·
          refine ⟨4752669784677949051043393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168446523118632700695595 4752669784677949051043393)
          ·
            refine ⟨3564502338508461788282545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752669784677949051043393 3564502338508461788282545)
            ·
              refine ⟨2673376753881346341211909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3564502338508461788282545 2673376753881346341211909)
              ·
                refine ⟨501258141352752438977233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2673376753881346341211909 501258141352752438977233)
                ·
                  refine ⟨375943606014564329232925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501258141352752438977233 375943606014564329232925)
                  ·
                    refine ⟨140978852255461623462347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 375943606014564329232925 140978852255461623462347)
                    ·
                      rfl

theorem cell22_411833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_411833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411833 prefixEnd_411833 := by exact prefixLift 411833
  have htrace : WordTrace (prefixWord ++ tailWord_411833) baseStart_411833 baseEnd_411833 := by
    simpa [prefixWord, tailWord_411833, baseEnd_411833] using wordTrace_append hprefix tailTrace_411833
  have hstable : (prefixWord ++ tailWord_411833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411833).length < 2 ^ (prefixWord ++ tailWord_411833).sum := by decide
  have hdescent : baseEnd_411833 < baseStart_411833 := by decide
  rcases family_descends (prefixWord ++ tailWord_411833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411951 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_411951 : Nat := 118140960795 + 411951 * 2 ^ 59
def prefixEnd_411951 : Nat := 4983230072969 + 3 ^ 40 * 411951 * 2
def baseEnd_411951 : Nat := 141019246066948649011985

theorem tailTrace_411951 : CollatzResearch.WordTrace tailWord_411951 prefixEnd_411951 141019246066948649011985 := by
  unfold tailWord_411951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025087330579357474611707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10016724887052904983074471 15025087330579357474611707)
  ·
    refine ⟨22537630995869036211917561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15025087330579357474611707 22537630995869036211917561)
    ·
      refine ⟨16903223246901777158938171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22537630995869036211917561 16903223246901777158938171)
      ·
        refine ⟨25354834870352665738407257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16903223246901777158938171 25354834870352665738407257)
        ·
          refine ⟨19016126152764499303805443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25354834870352665738407257 19016126152764499303805443)
          ·
            refine ⟨28524189229146748955708165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19016126152764499303805443 28524189229146748955708165)
            ·
              refine ⟨5348285480465015429195281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28524189229146748955708165 5348285480465015429195281)
              ·
                refine ⟨4011214110348761571896461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348285480465015429195281 4011214110348761571896461)
                ·
                  refine ⟨1504205291380785589461173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4011214110348761571896461 1504205291380785589461173)
                  ·
                    refine ⟨141019246066948649011985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1504205291380785589461173 141019246066948649011985)
                    ·
                      rfl

theorem cell22_411951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_411951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_411951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_411951 prefixEnd_411951 := by exact prefixLift 411951
  have htrace : WordTrace (prefixWord ++ tailWord_411951) baseStart_411951 baseEnd_411951 := by
    simpa [prefixWord, tailWord_411951, baseEnd_411951] using wordTrace_append hprefix tailTrace_411951
  have hstable : (prefixWord ++ tailWord_411951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411951).length < 2 ^ (prefixWord ++ tailWord_411951).sum := by decide
  have hdescent : baseEnd_411951 < baseStart_411951 := by decide
  rcases family_descends (prefixWord ++ tailWord_411951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412000 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_412000 : Nat := 118140960795 + 412000 * 2 ^ 59
def prefixEnd_412000 : Nat := 4983230072969 + 3 ^ 40 * 412000 * 2
def baseEnd_412000 : Nat := 141036019768328854536835

theorem tailTrace_412000 : CollatzResearch.WordTrace tailWord_412000 prefixEnd_412000 141036019768328854536835 := by
  unfold tailWord_412000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513437253700919421572727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10017916338267892562096969 7513437253700919421572727)
  ·
    refine ⟨11270155880551379132359091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513437253700919421572727 11270155880551379132359091)
    ·
      refine ⟨16905233820827068698538637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270155880551379132359091 16905233820827068698538637)
      ·
        refine ⟨6339462682810150761951989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16905233820827068698538637 6339462682810150761951989)
        ·
          refine ⟨594324626513451633932999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6339462682810150761951989 594324626513451633932999)
          ·
            refine ⟨891486939770177450899499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594324626513451633932999 891486939770177450899499)
            ·
              refine ⟨1337230409655266176349249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891486939770177450899499 1337230409655266176349249)
              ·
                refine ⟨1002922807241449632261937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337230409655266176349249 1002922807241449632261937)
                ·
                  refine ⟨752192105431087224196453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002922807241449632261937 752192105431087224196453)
                  ·
                    refine ⟨141036019768328854536835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752192105431087224196453 141036019768328854536835)
                    ·
                      rfl

theorem cell22_412000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_412000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412000 prefixEnd_412000 := by exact prefixLift 412000
  have htrace : WordTrace (prefixWord ++ tailWord_412000) baseStart_412000 baseEnd_412000 := by
    simpa [prefixWord, tailWord_412000, baseEnd_412000] using wordTrace_append hprefix tailTrace_412000
  have hstable : (prefixWord ++ tailWord_412000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412000).length < 2 ^ (prefixWord ++ tailWord_412000).sum := by decide
  have hdescent : baseEnd_412000 < baseStart_412000 := by decide
  rcases family_descends (prefixWord ++ tailWord_412000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412011 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_412011 : Nat := 118140960795 + 412011 * 2 ^ 59
def prefixEnd_412011 : Nat := 4983230072969 + 3 ^ 40 * 412011 * 2
def baseEnd_412011 : Nat := 141039785293128492511801

theorem tailTrace_412011 : CollatzResearch.WordTrace tailWord_412011 prefixEnd_412011 141039785293128492511801 := by
  unfold tailWord_412011
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027275710361987721795887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10018183806907991814530591 15027275710361987721795887)
  ·
    refine ⟨22540913565542981582693831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15027275710361987721795887 22540913565542981582693831)
    ·
      refine ⟨33811370348314472374040747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22540913565542981582693831 33811370348314472374040747)
      ·
        refine ⟨50717055522471708561061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33811370348314472374040747 50717055522471708561061121)
        ·
          refine ⟨38037791641853781420795841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50717055522471708561061121 38037791641853781420795841)
          ·
            refine ⟨28528343731390336065596881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38037791641853781420795841 28528343731390336065596881)
            ·
              refine ⟨21396257798542752049197661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28528343731390336065596881 21396257798542752049197661)
              ·
                refine ⟨8023596674453532018449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21396257798542752049197661 8023596674453532018449123)
                ·
                  refine ⟨12035395011680298027673685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023596674453532018449123 12035395011680298027673685)
                  ·
                    refine ⟨141039785293128492511801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12035395011680298027673685 141039785293128492511801)
                    ·
                      rfl

theorem cell22_412011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_412011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412011 prefixEnd_412011 := by exact prefixLift 412011
  have htrace : WordTrace (prefixWord ++ tailWord_412011) baseStart_412011 baseEnd_412011 := by
    simpa [prefixWord, tailWord_412011, baseEnd_412011] using wordTrace_append hprefix tailTrace_412011
  have hstable : (prefixWord ++ tailWord_412011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412011).length < 2 ^ (prefixWord ++ tailWord_412011).sum := by decide
  have hdescent : baseEnd_412011 < baseStart_412011 := by decide
  rcases family_descends (prefixWord ++ tailWord_412011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412034 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_412034 : Nat := 118140960795 + 412034 * 2 ^ 59
def prefixEnd_412034 : Nat := 4983230072969 + 3 ^ 40 * 412034 * 2
def baseEnd_412034 : Nat := 141047658663164099186731

theorem tailTrace_412034 : CollatzResearch.WordTrace tailWord_412034 prefixEnd_412034 141047658663164099186731 := by
  unfold tailWord_412034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757028647319665662470789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10018743059519108433255437 3757028647319665662470789)
  ·
    refine ⟨704442871372437311713273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3757028647319665662470789 704442871372437311713273)
    ·
      refine ⟨528332153529327983784955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 704442871372437311713273 528332153529327983784955)
      ·
        refine ⟨792498230293991975677433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528332153529327983784955 792498230293991975677433)
        ·
          refine ⟨594373672720493981758075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792498230293991975677433 594373672720493981758075)
          ·
            refine ⟨891560509080740972637113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594373672720493981758075 891560509080740972637113)
            ·
              refine ⟨668670381810555729477835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891560509080740972637113 668670381810555729477835)
              ·
                refine ⟨1003005572715833594216753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668670381810555729477835 1003005572715833594216753)
                ·
                  refine ⟨752254179536875195662565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003005572715833594216753 752254179536875195662565)
                  ·
                    refine ⟨141047658663164099186731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752254179536875195662565 141047658663164099186731)
                    ·
                      rfl

theorem cell22_412034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_412034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412034 prefixEnd_412034 := by exact prefixLift 412034
  have htrace : WordTrace (prefixWord ++ tailWord_412034) baseStart_412034 baseEnd_412034 := by
    simpa [prefixWord, tailWord_412034, baseEnd_412034] using wordTrace_append hprefix tailTrace_412034
  have hstable : (prefixWord ++ tailWord_412034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412034).length < 2 ^ (prefixWord ++ tailWord_412034).sum := by decide
  have hdescent : baseEnd_412034 < baseStart_412034 := by decide
  rcases family_descends (prefixWord ++ tailWord_412034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412064 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_412064 : Nat := 118140960795 + 412064 * 2 ^ 59
def prefixEnd_412064 : Nat := 4983230072969 + 3 ^ 40 * 412064 * 2
def baseEnd_412064 : Nat := 141057928276254020936639

theorem tailTrace_412064 : CollatzResearch.WordTrace tailWord_412064 prefixEnd_412064 141057928276254020936639 := by
  unfold tailWord_412064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514604389584988886737623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10019472519446651848983497 7514604389584988886737623)
  ·
    refine ⟨11271906584377483330106435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7514604389584988886737623 11271906584377483330106435)
    ·
      refine ⟨16907859876566224995159653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11271906584377483330106435 16907859876566224995159653)
      ·
        refine ⟨3170223726856167186592435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16907859876566224995159653 3170223726856167186592435)
        ·
          refine ⟨4755335590284250779888653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170223726856167186592435 4755335590284250779888653)
          ·
            refine ⟨1783250846356594042458245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4755335590284250779888653 1783250846356594042458245)
            ·
              refine ⟨334359533691861382960921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1783250846356594042458245 334359533691861382960921)
              ·
                refine ⟨250769650268896037220691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334359533691861382960921 250769650268896037220691)
                ·
                  refine ⟨376154475403344055831037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250769650268896037220691 376154475403344055831037)
                  ·
                    refine ⟨141057928276254020936639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376154475403344055831037 141057928276254020936639)
                    ·
                      rfl

theorem cell22_412064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_412064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412064 prefixEnd_412064 := by exact prefixLift 412064
  have htrace : WordTrace (prefixWord ++ tailWord_412064) baseStart_412064 baseEnd_412064 := by
    simpa [prefixWord, tailWord_412064, baseEnd_412064] using wordTrace_append hprefix tailTrace_412064
  have hstable : (prefixWord ++ tailWord_412064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412064).length < 2 ^ (prefixWord ++ tailWord_412064).sum := by decide
  have hdescent : baseEnd_412064 < baseStart_412064 := by decide
  rcases family_descends (prefixWord ++ tailWord_412064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412105 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 4]
def baseStart_412105 : Nat := 118140960795 + 412105 * 2 ^ 59
def prefixEnd_412105 : Nat := 4983230072969 + 3 ^ 40 * 412105 * 2
def baseEnd_412105 : Nat := 47023987804714526887171

theorem tailTrace_412105 : CollatzResearch.WordTrace tailWord_412105 prefixEnd_412105 47023987804714526887171 := by
  unfold tailWord_412105
  simp only [CollatzResearch.WordTrace]
  refine ⟨15030704172021441775717769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10020469448014294517145179 15030704172021441775717769)
  ·
    refine ⟨11273028129016081331788327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15030704172021441775717769 11273028129016081331788327)
    ·
      refine ⟨16909542193524121997682491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273028129016081331788327 16909542193524121997682491)
      ·
        refine ⟨25364313290286182996523737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909542193524121997682491 25364313290286182996523737)
        ·
          refine ⟨19023234967714637247392803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25364313290286182996523737 19023234967714637247392803)
          ·
            refine ⟨28534852451571955871089205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19023234967714637247392803 28534852451571955871089205)
            ·
              refine ⟨2675142417334870862914613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28534852451571955871089205 2675142417334870862914613)
              ·
                refine ⟨250794601625144143398245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2675142417334870862914613 250794601625144143398245)
                ·
                  refine ⟨47023987804714526887171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250794601625144143398245 47023987804714526887171)
                  ·
                    rfl

theorem cell22_412105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_412105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412105 prefixEnd_412105 := by exact prefixLift 412105
  have htrace : WordTrace (prefixWord ++ tailWord_412105) baseStart_412105 baseEnd_412105 := by
    simpa [prefixWord, tailWord_412105, baseEnd_412105] using wordTrace_append hprefix tailTrace_412105
  have hstable : (prefixWord ++ tailWord_412105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412105).length < 2 ^ (prefixWord ++ tailWord_412105).sum := by decide
  have hdescent : baseEnd_412105 < baseStart_412105 := by decide
  rcases family_descends (prefixWord ++ tailWord_412105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412150 : List Nat := [5, 1, 1, 1, 2, 1, 3, 8]
def baseStart_412150 : Nat := 118140960795 + 412150 * 2 ^ 59
def prefixEnd_412150 : Nat := 4983230072969 + 3 ^ 40 * 412150 * 2
def baseEnd_412150 : Nat := 15676374203753162587375

theorem tailTrace_412150 : CollatzResearch.WordTrace tailWord_412150 prefixEnd_412150 15676374203753162587375 := by
  unfold tailWord_412150
  simp only [CollatzResearch.WordTrace]
  refine ⟨939521591053650903819119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10021563637905609640737269 939521591053650903819119)
  ·
    refine ⟨1409282386580476355728679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 939521591053650903819119 1409282386580476355728679)
    ·
      refine ⟨2113923579870714533593019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409282386580476355728679 2113923579870714533593019)
      ·
        refine ⟨3170885369806071800389529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113923579870714533593019 3170885369806071800389529)
        ·
          refine ⟨2378164027354553850292147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170885369806071800389529 2378164027354553850292147)
          ·
            refine ⟨3567246041031830775438221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378164027354553850292147 3567246041031830775438221)
            ·
              refine ⟨1337717265386936540789333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567246041031830775438221 1337717265386936540789333)
              ·
                refine ⟨15676374203753162587375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1337717265386936540789333 15676374203753162587375)
                ·
                  rfl

theorem cell22_412150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_412150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412150 prefixEnd_412150 := by exact prefixLift 412150
  have htrace : WordTrace (prefixWord ++ tailWord_412150) baseStart_412150 baseEnd_412150 := by
    simpa [prefixWord, tailWord_412150, baseEnd_412150] using wordTrace_append hprefix tailTrace_412150
  have hstable : (prefixWord ++ tailWord_412150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412150).length < 2 ^ (prefixWord ++ tailWord_412150).sum := by decide
  have hdescent : baseEnd_412150 < baseStart_412150 := by decide
  rcases family_descends (prefixWord ++ tailWord_412150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412165 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_412165 : Nat := 118140960795 + 412165 * 2 ^ 59
def prefixEnd_412165 : Nat := 4983230072969 + 3 ^ 40 * 412165 * 2
def baseEnd_412165 : Nat := 141092502640323424161329

theorem tailTrace_412165 : CollatzResearch.WordTrace tailWord_412165 prefixEnd_412165 141092502640323424161329 := by
  unfold tailWord_412165
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032892551804072022901949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10021928367869381348601299 15032892551804072022901949)
  ·
    refine ⟨5637334706926527008588231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15032892551804072022901949 5637334706926527008588231)
    ·
      refine ⟨8456002060389790512882347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637334706926527008588231 8456002060389790512882347)
      ·
        refine ⟨12684003090584685769323521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456002060389790512882347 12684003090584685769323521)
        ·
          refine ⟨9513002317938514326992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12684003090584685769323521 9513002317938514326992641)
          ·
            refine ⟨7134751738453885745244481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9513002317938514326992641 7134751738453885745244481)
            ·
              refine ⟨5351063803840414308933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134751738453885745244481 5351063803840414308933361)
              ·
                refine ⟨4013297852880310731700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351063803840414308933361 4013297852880310731700021)
                ·
                  refine ⟨376246673707529131096877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013297852880310731700021 376246673707529131096877)
                  ·
                    refine ⟨141092502640323424161329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376246673707529131096877 141092502640323424161329)
                    ·
                      rfl

theorem cell22_412165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_412165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412165 prefixEnd_412165 := by exact prefixLift 412165
  have htrace : WordTrace (prefixWord ++ tailWord_412165) baseStart_412165 baseEnd_412165 := by
    simpa [prefixWord, tailWord_412165, baseEnd_412165] using wordTrace_append hprefix tailTrace_412165
  have hstable : (prefixWord ++ tailWord_412165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412165).length < 2 ^ (prefixWord ++ tailWord_412165).sum := by decide
  have hdescent : baseEnd_412165 < baseStart_412165 := by decide
  rcases family_descends (prefixWord ++ tailWord_412165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412167 : List Nat := [1, 1, 4, 3, 4, 1, 8]
def baseStart_412167 : Nat := 118140960795 + 412167 * 2 ^ 59
def prefixEnd_412167 : Nat := 4983230072969 + 3 ^ 40 * 412167 * 2
def baseEnd_412167 : Nat := 5225673603007262430049

theorem tailTrace_412167 : CollatzResearch.WordTrace tailWord_412167 prefixEnd_412167 5225673603007262430049 := by
  unfold tailWord_412167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032965497796826364474755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10021976998531217576316503 15032965497796826364474755)
  ·
    refine ⟨22549448246695239546712133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15032965497796826364474755 22549448246695239546712133)
    ·
      refine ⟨4228021546255357415008525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22549448246695239546712133 4228021546255357415008525)
      ·
        refine ⟨1585508079845759030628197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4228021546255357415008525 1585508079845759030628197)
        ·
          refine ⟨297282764971079818242787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1585508079845759030628197 297282764971079818242787)
          ·
            refine ⟨445924147456619727364181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297282764971079818242787 445924147456619727364181)
            ·
              refine ⟨5225673603007262430049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 445924147456619727364181 5225673603007262430049)
              ·
                rfl

theorem cell22_412167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 8].length) (baseStart_412167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412167 prefixEnd_412167 := by exact prefixLift 412167
  have htrace : WordTrace (prefixWord ++ tailWord_412167) baseStart_412167 baseEnd_412167 := by
    simpa [prefixWord, tailWord_412167, baseEnd_412167] using wordTrace_append hprefix tailTrace_412167
  have hstable : (prefixWord ++ tailWord_412167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412167).length < 2 ^ (prefixWord ++ tailWord_412167).sum := by decide
  have hdescent : baseEnd_412167 < baseStart_412167 := by decide
  rcases family_descends (prefixWord ++ tailWord_412167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412173 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 4]
def baseStart_412173 : Nat := 118140960795 + 412173 * 2 ^ 59
def prefixEnd_412173 : Nat := 4983230072969 + 3 ^ 40 * 412173 * 2
def baseEnd_412173 : Nat := 47031747067938023320435

theorem tailTrace_412173 : CollatzResearch.WordTrace tailWord_412173 prefixEnd_412173 47031747067938023320435 := by
  unfold tailWord_412173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033184335775089389193173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022122890516726259462115 15033184335775089389193173)
  ·
    refine ⟨352340257869728657559215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15033184335775089389193173 352340257869728657559215)
    ·
      refine ⟨528510386804592986338823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352340257869728657559215 528510386804592986338823)
      ·
        refine ⟨792765580206889479508235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528510386804592986338823 792765580206889479508235)
        ·
          refine ⟨1189148370310334219262353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792765580206889479508235 1189148370310334219262353)
          ·
            refine ⟨891861277732750664446765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189148370310334219262353 891861277732750664446765)
            ·
              refine ⟨334447979149781499167537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891861277732750664446765 334447979149781499167537)
              ·
                refine ⟨250835984362336124375653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334447979149781499167537 250835984362336124375653)
                ·
                  refine ⟨47031747067938023320435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250835984362336124375653 47031747067938023320435)
                  ·
                    rfl

theorem cell22_412173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_412173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412173 prefixEnd_412173 := by exact prefixLift 412173
  have htrace : WordTrace (prefixWord ++ tailWord_412173) baseStart_412173 baseEnd_412173 := by
    simpa [prefixWord, tailWord_412173, baseEnd_412173] using wordTrace_append hprefix tailTrace_412173
  have hstable : (prefixWord ++ tailWord_412173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412173).length < 2 ^ (prefixWord ++ tailWord_412173).sum := by decide
  have hdescent : baseEnd_412173 < baseStart_412173 := by decide
  rcases family_descends (prefixWord ++ tailWord_412173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412364 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_412364 : Nat := 118140960795 + 412364 * 2 ^ 59
def prefixEnd_412364 : Nat := 4983230072969 + 3 ^ 40 * 412364 * 2
def baseEnd_412364 : Nat := 47053541469051079478573

theorem tailTrace_412364 : CollatzResearch.WordTrace tailWord_412364 prefixEnd_412364 47053541469051079478573 := by
  unfold tailWord_412364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520075339041564504698073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10026767118722086006264097 7520075339041564504698073)
  ·
    refine ⟨5640056504281173378523555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7520075339041564504698073 5640056504281173378523555)
    ·
      refine ⟨8460084756421760067785333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640056504281173378523555 8460084756421760067785333)
      ·
        refine ⟨793132945914540006354875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8460084756421760067785333 793132945914540006354875)
        ·
          refine ⟨1189699418871810009532313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793132945914540006354875 1189699418871810009532313)
          ·
            refine ⟨892274564153857507149235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189699418871810009532313 892274564153857507149235)
            ·
              refine ⟨1338411846230786260723853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892274564153857507149235 1338411846230786260723853)
              ·
                refine ⟨501904442336544847771445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338411846230786260723853 501904442336544847771445)
                ·
                  refine ⟨47053541469051079478573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501904442336544847771445 47053541469051079478573)
                  ·
                    rfl

theorem cell22_412364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_412364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412364 prefixEnd_412364 := by exact prefixLift 412364
  have htrace : WordTrace (prefixWord ++ tailWord_412364) baseStart_412364 baseEnd_412364 := by
    simpa [prefixWord, tailWord_412364, baseEnd_412364] using wordTrace_append hprefix tailTrace_412364
  have hstable : (prefixWord ++ tailWord_412364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412364).length < 2 ^ (prefixWord ++ tailWord_412364).sum := by decide
  have hdescent : baseEnd_412364 < baseStart_412364 := by decide
  rcases family_descends (prefixWord ++ tailWord_412364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412377 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_412377 : Nat := 118140960795 + 412377 * 2 ^ 59
def prefixEnd_412377 : Nat := 4983230072969 + 3 ^ 40 * 412377 * 2
def baseEnd_412377 : Nat := 141165074572825537860679

theorem tailTrace_412377 : CollatzResearch.WordTrace tailWord_412377 prefixEnd_412377 141165074572825537860679 := by
  unfold tailWord_412377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040624827036032229619385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10027083218024021486412923 15040624827036032229619385)
  ·
    refine ⟨11280468620277024172214539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15040624827036032229619385 11280468620277024172214539)
    ·
      refine ⟨16920702930415536258321809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280468620277024172214539 16920702930415536258321809)
      ·
        refine ⟨12690527197811652193741357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16920702930415536258321809 12690527197811652193741357)
        ·
          refine ⟨4758947699179369572653009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12690527197811652193741357 4758947699179369572653009)
          ·
            refine ⟨3569210774384527179489757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758947699179369572653009 3569210774384527179489757)
            ·
              refine ⟨1338454040394197692308659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3569210774384527179489757 1338454040394197692308659)
              ·
                refine ⟨2007681060591296538462989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338454040394197692308659 2007681060591296538462989)
                ·
                  refine ⟨752880397721736201923621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2007681060591296538462989 752880397721736201923621)
                  ·
                    refine ⟨141165074572825537860679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752880397721736201923621 141165074572825537860679)
                    ·
                      rfl

theorem cell22_412377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_412377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412377 prefixEnd_412377 := by exact prefixLift 412377
  have htrace : WordTrace (prefixWord ++ tailWord_412377) baseStart_412377 baseEnd_412377 := by
    simpa [prefixWord, tailWord_412377, baseEnd_412377] using wordTrace_append hprefix tailTrace_412377
  have hstable : (prefixWord ++ tailWord_412377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412377).length < 2 ^ (prefixWord ++ tailWord_412377).sum := by decide
  have hdescent : baseEnd_412377 < baseStart_412377 := by decide
  rcases family_descends (prefixWord ++ tailWord_412377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412424 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_412424 : Nat := 118140960795 + 412424 * 2 ^ 59
def prefixEnd_412424 : Nat := 4983230072969 + 3 ^ 40 * 412424 * 2
def baseEnd_412424 : Nat := 141181163633333081935535

theorem tailTrace_412424 : CollatzResearch.WordTrace tailWord_412424 prefixEnd_412424 141181163633333081935535 := by
  unfold tailWord_412424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521169528932879628290163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10028226038577172837720217 7521169528932879628290163)
  ·
    refine ⟨11281754293399319442435245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521169528932879628290163 11281754293399319442435245)
    ·
      refine ⟨4230657860024744790913217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11281754293399319442435245 4230657860024744790913217)
      ·
        refine ⟨3172993395018558593184913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4230657860024744790913217 3172993395018558593184913)
        ·
          refine ⟨2379745046263918944888685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172993395018558593184913 2379745046263918944888685)
          ·
            refine ⟨892404392348969604333257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2379745046263918944888685 892404392348969604333257)
            ·
              refine ⟨669303294261727203249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892404392348969604333257 669303294261727203249943)
              ·
                refine ⟨1003954941392590804874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669303294261727203249943 1003954941392590804874915)
                ·
                  refine ⟨1505932412088886207312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003954941392590804874915 1505932412088886207312373)
                  ·
                    refine ⟨141181163633333081935535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1505932412088886207312373 141181163633333081935535)
                    ·
                      rfl

theorem cell22_412424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_412424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412424 prefixEnd_412424 := by exact prefixLift 412424
  have htrace : WordTrace (prefixWord ++ tailWord_412424) baseStart_412424 baseEnd_412424 := by
    simpa [prefixWord, tailWord_412424, baseEnd_412424] using wordTrace_append hprefix tailTrace_412424
  have hstable : (prefixWord ++ tailWord_412424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412424).length < 2 ^ (prefixWord ++ tailWord_412424).sum := by decide
  have hdescent : baseEnd_412424 < baseStart_412424 := by decide
  rcases family_descends (prefixWord ++ tailWord_412424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412439 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_412439 : Nat := 118140960795 + 412439 * 2 ^ 59
def prefixEnd_412439 : Nat := 4983230072969 + 3 ^ 40 * 412439 * 2
def baseEnd_412439 : Nat := 141186298439878042810489

theorem tailTrace_412439 : CollatzResearch.WordTrace tailWord_412439 prefixEnd_412439 141186298439878042810489 := by
  unfold tailWord_412439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042886152811416818376371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10028590768540944545584247 15042886152811416818376371)
  ·
    refine ⟨22564329229217125227564557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15042886152811416818376371 22564329229217125227564557)
    ·
      refine ⟨8461623460956421960336709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22564329229217125227564557 8461623460956421960336709)
      ·
        refine ⟨1586554398929329117563133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8461623460956421960336709 1586554398929329117563133)
        ·
          refine ⟨594957899598498419086175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1586554398929329117563133 594957899598498419086175)
          ·
            refine ⟨892436849397747628629263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594957899598498419086175 892436849397747628629263)
            ·
              refine ⟨1338655274096621442943895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892436849397747628629263 1338655274096621442943895)
              ·
                refine ⟨2007982911144932164415843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338655274096621442943895 2007982911144932164415843)
                ·
                  refine ⟨3011974366717398246623765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007982911144932164415843 3011974366717398246623765)
                  ·
                    refine ⟨141186298439878042810489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3011974366717398246623765 141186298439878042810489)
                    ·
                      rfl

theorem cell22_412439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_412439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412439 prefixEnd_412439 := by exact prefixLift 412439
  have htrace : WordTrace (prefixWord ++ tailWord_412439) baseStart_412439 baseEnd_412439 := by
    simpa [prefixWord, tailWord_412439, baseEnd_412439] using wordTrace_append hprefix tailTrace_412439
  have hstable : (prefixWord ++ tailWord_412439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412439).length < 2 ^ (prefixWord ++ tailWord_412439).sum := by decide
  have hdescent : baseEnd_412439 < baseStart_412439 := by decide
  rcases family_descends (prefixWord ++ tailWord_412439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412445 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_412445 : Nat := 118140960795 + 412445 * 2 ^ 59
def prefixEnd_412445 : Nat := 4983230072969 + 3 ^ 40 * 412445 * 2
def baseEnd_412445 : Nat := 141188352362496027160471

theorem tailTrace_412445 : CollatzResearch.WordTrace tailWord_412445 prefixEnd_412445 141188352362496027160471 := by
  unfold tailWord_412445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043104990789679843094789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10028736660526453228729859 15043104990789679843094789)
  ·
    refine ⟨2820582185773064970580273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15043104990789679843094789 2820582185773064970580273)
    ·
      refine ⟨2115436639329798727935205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2820582185773064970580273 2115436639329798727935205)
      ·
        refine ⟨396644369874337261487851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2115436639329798727935205 396644369874337261487851)
        ·
          refine ⟨594966554811505892231777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396644369874337261487851 594966554811505892231777)
          ·
            refine ⟨446224916108629419173833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594966554811505892231777 446224916108629419173833)
            ·
              refine ⟨334668687081472064380375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446224916108629419173833 334668687081472064380375)
              ·
                refine ⟨502003030622208096570563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334668687081472064380375 502003030622208096570563)
                ·
                  refine ⟨753004545933312144855845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502003030622208096570563 753004545933312144855845)
                  ·
                    refine ⟨141188352362496027160471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753004545933312144855845 141188352362496027160471)
                    ·
                      rfl

theorem cell22_412445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_412445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412445 prefixEnd_412445 := by exact prefixLift 412445
  have htrace : WordTrace (prefixWord ++ tailWord_412445) baseStart_412445 baseEnd_412445 := by
    simpa [prefixWord, tailWord_412445, baseEnd_412445] using wordTrace_append hprefix tailTrace_412445
  have hstable : (prefixWord ++ tailWord_412445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412445).length < 2 ^ (prefixWord ++ tailWord_412445).sum := by decide
  have hdescent : baseEnd_412445 < baseStart_412445 := by decide
  rcases family_descends (prefixWord ++ tailWord_412445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412458 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_412458 : Nat := 118140960795 + 412458 * 2 ^ 59
def prefixEnd_412458 : Nat := 4983230072969 + 3 ^ 40 * 412458 * 2
def baseEnd_412458 : Nat := 141192802528168326585431

theorem tailTrace_412458 : CollatzResearch.WordTrace tailWord_412458 prefixEnd_412458 141192802528168326585431 := by
  unfold tailWord_412458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760894784935645765829507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10029052759828388708878685 3760894784935645765829507)
  ·
    refine ⟨5641342177403468648744261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760894784935645765829507 5641342177403468648744261)
    ·
      refine ⟨1057751658263150371639549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5641342177403468648744261 1057751658263150371639549)
      ·
        refine ⟨396656871848681389364831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1057751658263150371639549 396656871848681389364831)
        ·
          refine ⟨594985307773022084047247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396656871848681389364831 594985307773022084047247)
          ·
            refine ⟨892477961659533126070871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594985307773022084047247 892477961659533126070871)
            ·
              refine ⟨1338716942489299689106307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892477961659533126070871 1338716942489299689106307)
              ·
                refine ⟨2008075413733949533659461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338716942489299689106307 2008075413733949533659461)
                ·
                  refine ⟨376514140075115537561149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008075413733949533659461 376514140075115537561149)
                  ·
                    refine ⟨141192802528168326585431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376514140075115537561149 141192802528168326585431)
                    ·
                      rfl

theorem cell22_412458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_412458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412458 prefixEnd_412458 := by exact prefixLift 412458
  have htrace : WordTrace (prefixWord ++ tailWord_412458) baseStart_412458 baseEnd_412458 := by
    simpa [prefixWord, tailWord_412458, baseEnd_412458] using wordTrace_append hprefix tailTrace_412458
  have hstable : (prefixWord ++ tailWord_412458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412458).length < 2 ^ (prefixWord ++ tailWord_412458).sum := by decide
  have hdescent : baseEnd_412458 < baseStart_412458 := by decide
  rcases family_descends (prefixWord ++ tailWord_412458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412503 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 1, 3]
def baseStart_412503 : Nat := 118140960795 + 412503 * 2 ^ 59
def prefixEnd_412503 : Nat := 4983230072969 + 3 ^ 40 * 412503 * 2
def baseEnd_412503 : Nat := 141208206947803209210293

theorem tailTrace_412503 : CollatzResearch.WordTrace tailWord_412503 prefixEnd_412503 141208206947803209210293 := by
  unfold tailWord_412503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045220424579555748706163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10030146949719703832470775 15045220424579555748706163)
  ·
    refine ⟨22567830636869333623059245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045220424579555748706163 22567830636869333623059245)
    ·
      refine ⟨8462936488826000108647217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22567830636869333623059245 8462936488826000108647217)
      ·
        refine ⟨6347202366619500081485413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8462936488826000108647217 6347202366619500081485413)
        ·
          refine ⟨1190100443741156265278515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6347202366619500081485413 1190100443741156265278515)
          ·
            refine ⟨1785150665611734397917773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190100443741156265278515 1785150665611734397917773)
            ·
              refine ⟨669431499604400399219165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785150665611734397917773 669431499604400399219165)
              ·
                refine ⟨251036812351650149707187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669431499604400399219165 251036812351650149707187)
                ·
                  refine ⟨376555218527475224560781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251036812351650149707187 376555218527475224560781)
                  ·
                    refine ⟨141208206947803209210293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376555218527475224560781 141208206947803209210293)
                    ·
                      rfl

theorem cell22_412503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_412503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412503 prefixEnd_412503 := by exact prefixLift 412503
  have htrace : WordTrace (prefixWord ++ tailWord_412503) baseStart_412503 baseEnd_412503 := by
    simpa [prefixWord, tailWord_412503, baseEnd_412503] using wordTrace_append hprefix tailTrace_412503
  have hstable : (prefixWord ++ tailWord_412503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412503).length < 2 ^ (prefixWord ++ tailWord_412503).sum := by decide
  have hdescent : baseEnd_412503 < baseStart_412503 := by decide
  rcases family_descends (prefixWord ++ tailWord_412503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412520 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_412520 : Nat := 118140960795 + 412520 * 2 ^ 59
def prefixEnd_412520 : Nat := 4983230072969 + 3 ^ 40 * 412520 * 2
def baseEnd_412520 : Nat := 141214026395220831535241

theorem tailTrace_412520 : CollatzResearch.WordTrace tailWord_412520 prefixEnd_412520 141214026395220831535241 := by
  unfold tailWord_412520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522920232758983826037507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10030560310345311768050009 7522920232758983826037507)
  ·
    refine ⟨11284380349138475739056261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7522920232758983826037507 11284380349138475739056261)
    ·
      refine ⟨2115821315463464201073049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11284380349138475739056261 2115821315463464201073049)
      ·
        refine ⟨1586865986597598150804787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115821315463464201073049 1586865986597598150804787)
        ·
          refine ⟨2380298979896397226207181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586865986597598150804787 2380298979896397226207181)
          ·
            refine ⟨892612117461148959827693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2380298979896397226207181 892612117461148959827693)
            ·
              refine ⟨334729544047930859935385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 892612117461148959827693 334729544047930859935385)
              ·
                refine ⟨251047158035948144951539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334729544047930859935385 251047158035948144951539)
                ·
                  refine ⟨376570737053922217427309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251047158035948144951539 376570737053922217427309)
                  ·
                    refine ⟨141214026395220831535241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376570737053922217427309 141214026395220831535241)
                    ·
                      rfl

theorem cell22_412520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_412520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412520 prefixEnd_412520 := by exact prefixLift 412520
  have htrace : WordTrace (prefixWord ++ tailWord_412520) baseStart_412520 baseEnd_412520 := by
    simpa [prefixWord, tailWord_412520, baseEnd_412520] using wordTrace_append hprefix tailTrace_412520
  have hstable : (prefixWord ++ tailWord_412520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412520).length < 2 ^ (prefixWord ++ tailWord_412520).sum := by decide
  have hdescent : baseEnd_412520 < baseStart_412520 := by decide
  rcases family_descends (prefixWord ++ tailWord_412520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412533 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 5]
def baseStart_412533 : Nat := 118140960795 + 412533 * 2 ^ 59
def prefixEnd_412533 : Nat := 4983230072969 + 3 ^ 40 * 412533 * 2
def baseEnd_412533 : Nat := 47072825520297710320067

theorem tailTrace_412533 : CollatzResearch.WordTrace tailWord_412533 prefixEnd_412533 47072825520297710320067 := by
  unfold tailWord_412533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046314614470870872298253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10030876409647247248198835 15046314614470870872298253)
  ·
    refine ⟨5642367980426576577111845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15046314614470870872298253 5642367980426576577111845)
    ·
      refine ⟨1057943996329983108208471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5642367980426576577111845 1057943996329983108208471)
      ·
        refine ⟨1586915994494974662312707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057943996329983108208471 1586915994494974662312707)
        ·
          refine ⟨2380373991742461993469061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586915994494974662312707 2380373991742461993469061)
          ·
            refine ⟨446320123451711623775449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2380373991742461993469061 446320123451711623775449)
            ·
              refine ⟨334740092588783717831587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446320123451711623775449 334740092588783717831587)
              ·
                refine ⟨502110138883175576747381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334740092588783717831587 502110138883175576747381)
                ·
                  refine ⟨47072825520297710320067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502110138883175576747381 47072825520297710320067)
                  ·
                    rfl

theorem cell22_412533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_412533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412533 prefixEnd_412533 := by exact prefixLift 412533
  have htrace : WordTrace (prefixWord ++ tailWord_412533) baseStart_412533 baseEnd_412533 := by
    simpa [prefixWord, tailWord_412533, baseEnd_412533] using wordTrace_append hprefix tailTrace_412533
  have hstable : (prefixWord ++ tailWord_412533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412533).length < 2 ^ (prefixWord ++ tailWord_412533).sum := by decide
  have hdescent : baseEnd_412533 < baseStart_412533 := by decide
  rcases family_descends (prefixWord ++ tailWord_412533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412576 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_412576 : Nat := 118140960795 + 412576 * 2 ^ 59
def prefixEnd_412576 : Nat := 4983230072969 + 3 ^ 40 * 412576 * 2
def baseEnd_412576 : Nat := 141233196339655352135069

theorem tailTrace_412576 : CollatzResearch.WordTrace tailWord_412576 prefixEnd_412576 141233196339655352135069 := by
  unfold tailWord_412576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523941476657544608056791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10031921968876726144075721 7523941476657544608056791)
  ·
    refine ⟨11285912214986316912085187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7523941476657544608056791 11285912214986316912085187)
    ·
      refine ⟨16928868322479475368127781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11285912214986316912085187 16928868322479475368127781)
      ·
        refine ⟨3174162810464901631523959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16928868322479475368127781 3174162810464901631523959)
        ·
          refine ⟨4761244215697352447285939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174162810464901631523959 4761244215697352447285939)
          ·
            refine ⟨7141866323546028670928909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761244215697352447285939 7141866323546028670928909)
            ·
              refine ⟨2678199871329760751598341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141866323546028670928909 2678199871329760751598341)
              ·
                refine ⟨502162475874330140924689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2678199871329760751598341 502162475874330140924689)
                ·
                  refine ⟨376621856905747605693517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502162475874330140924689 376621856905747605693517)
                  ·
                    refine ⟨141233196339655352135069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376621856905747605693517 141233196339655352135069)
                    ·
                      rfl

theorem cell22_412576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_412576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412576 prefixEnd_412576 := by exact prefixLift 412576
  have htrace : WordTrace (prefixWord ++ tailWord_412576) baseStart_412576 baseEnd_412576 := by
    simpa [prefixWord, tailWord_412576, baseEnd_412576] using wordTrace_append hprefix tailTrace_412576
  have hstable : (prefixWord ++ tailWord_412576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412576).length < 2 ^ (prefixWord ++ tailWord_412576).sum := by decide
  have hdescent : baseEnd_412576 < baseStart_412576 := by decide
  rcases family_descends (prefixWord ++ tailWord_412576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
