import V185TrunkScan23Chunk0466

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2762611 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_2762611 : Nat := 118140960795 + 2762611 * 2 ^ 59
def prefixEnd_2762611 : Nat := 4983230072969 + 3 ^ 40 * 2762611 * 2
def baseEnd_2762611 : Nat := 1418547304398196005457489

theorem tailTrace_2762611 : CollatzResearch.WordTrace tailWord_2762611 prefixEnd_2762611 1418547304398196005457489 := by
  unfold tailWord_2762611
  simp only [CollatzResearch.WordTrace]
  refine ⟨100760700994539638240687687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67173800663026425493791791 100760700994539638240687687)
  ·
    refine ⟨151141051491809457361031531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100760700994539638240687687 151141051491809457361031531)
    ·
      refine ⟨226711577237714186041547297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151141051491809457361031531 226711577237714186041547297)
      ·
        refine ⟨170033682928285639531160473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226711577237714186041547297 170033682928285639531160473)
        ·
          refine ⟨127525262196214229648370355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170033682928285639531160473 127525262196214229648370355)
          ·
            refine ⟨191287893294321344472555533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127525262196214229648370355 191287893294321344472555533)
            ·
              refine ⟨71732959985370504177208325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191287893294321344472555533 71732959985370504177208325)
              ·
                refine ⟨13449929997256969533226561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71732959985370504177208325 13449929997256969533226561)
                ·
                  refine ⟨10087447497942727149919921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13449929997256969533226561 10087447497942727149919921)
                  ·
                    refine ⟨7565585623457045362439941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10087447497942727149919921 7565585623457045362439941)
                    ·
                      refine ⟨1418547304398196005457489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7565585623457045362439941 1418547304398196005457489)
                      ·
                        rfl

theorem cell23_2762611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_2762611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762611 prefixEnd_2762611 := by exact prefixLift 2762611
  have htrace : WordTrace (prefixWord ++ tailWord_2762611) baseStart_2762611 baseEnd_2762611 := by
    simpa [prefixWord, tailWord_2762611, baseEnd_2762611] using wordTrace_append hprefix tailTrace_2762611
  have hstable : (prefixWord ++ tailWord_2762611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762611).length < 2 ^ (prefixWord ++ tailWord_2762611).sum := by decide
  have hdescent : baseEnd_2762611 < baseStart_2762611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762621 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 7]
def baseStart_2762621 : Nat := 118140960795 + 2762621 * 2 ^ 59
def prefixEnd_2762621 : Nat := 4983230072969 + 3 ^ 40 * 2762621 * 2
def baseEnd_2762621 : Nat := 157616937689415662925827

theorem tailTrace_2762621 : CollatzResearch.WordTrace tailWord_2762621 prefixEnd_2762621 157616937689415662925827 := by
  unfold tailWord_2762621
  simp only [CollatzResearch.WordTrace]
  refine ⟨100761065724503409948551717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67174043816335606632367811 100761065724503409948551717)
  ·
    refine ⟨18892699823344389365353447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100761065724503409948551717 18892699823344389365353447)
    ·
      refine ⟨28339049735016584048030171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18892699823344389365353447 28339049735016584048030171)
      ·
        refine ⟨42508574602524876072045257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28339049735016584048030171 42508574602524876072045257)
        ·
          refine ⟨31881430951893657054033943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42508574602524876072045257 31881430951893657054033943)
          ·
            refine ⟨47822146427840485581050915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31881430951893657054033943 47822146427840485581050915)
            ·
              refine ⟨71733219641760728371576373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47822146427840485581050915 71733219641760728371576373)
              ·
                refine ⟨6724989341415068284835285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71733219641760728371576373 6724989341415068284835285)
                ·
                  refine ⟨157616937689415662925827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6724989341415068284835285 157616937689415662925827)
                  ·
                    rfl

theorem cell23_2762621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_2762621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762621 prefixEnd_2762621 := by exact prefixLift 2762621
  have htrace : WordTrace (prefixWord ++ tailWord_2762621) baseStart_2762621 baseEnd_2762621 := by
    simpa [prefixWord, tailWord_2762621, baseEnd_2762621] using wordTrace_append hprefix tailTrace_2762621
  have hstable : (prefixWord ++ tailWord_2762621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762621).length < 2 ^ (prefixWord ++ tailWord_2762621).sum := by decide
  have hdescent : baseEnd_2762621 < baseStart_2762621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762625 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2762625 : Nat := 118140960795 + 2762625 * 2 ^ 59
def prefixEnd_2762625 : Nat := 4983230072969 + 3 ^ 40 * 2762625 * 2
def baseEnd_2762625 : Nat := 472851497709119650227475

theorem tailTrace_2762625 : CollatzResearch.WordTrace tailWord_2762625 prefixEnd_2762625 472851497709119650227475 := by
  unfold tailWord_2762625
  simp only [CollatzResearch.WordTrace]
  refine ⟨100761211616488918631697329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67174141077659279087798219 100761211616488918631697329)
  ·
    refine ⟨75570908712366688973772997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100761211616488918631697329 75570908712366688973772997)
    ·
      refine ⟨14169545383568754182582437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75570908712366688973772997 14169545383568754182582437)
      ·
        refine ⟨2656789759419141409234207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14169545383568754182582437 2656789759419141409234207)
        ·
          refine ⟨3985184639128712113851311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656789759419141409234207 3985184639128712113851311)
          ·
            refine ⟨5977776958693068170776967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985184639128712113851311 5977776958693068170776967)
            ·
              refine ⟨8966665438039602256165451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977776958693068170776967 8966665438039602256165451)
              ·
                refine ⟨13449998157059403384248177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8966665438039602256165451 13449998157059403384248177)
                ·
                  refine ⟨10087498617794552538186133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13449998157059403384248177 10087498617794552538186133)
                  ·
                    refine ⟨472851497709119650227475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10087498617794552538186133 472851497709119650227475)
                    ·
                      rfl

theorem cell23_2762625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2762625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762625 prefixEnd_2762625 := by exact prefixLift 2762625
  have htrace : WordTrace (prefixWord ++ tailWord_2762625) baseStart_2762625 baseEnd_2762625 := by
    simpa [prefixWord, tailWord_2762625, baseEnd_2762625] using wordTrace_append hprefix tailTrace_2762625
  have hstable : (prefixWord ++ tailWord_2762625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762625).length < 2 ^ (prefixWord ++ tailWord_2762625).sum := by decide
  have hdescent : baseEnd_2762625 < baseStart_2762625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762632 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2762632 : Nat := 118140960795 + 2762632 * 2 ^ 59
def prefixEnd_2762632 : Nat := 4983230072969 + 3 ^ 40 * 2762632 * 2
def baseEnd_2762632 : Nat := 1418558087491940423294893

theorem tailTrace_2762632 : CollatzResearch.WordTrace tailWord_2762632 prefixEnd_2762632 1418558087491940423294893 := by
  unfold tailWord_2762632
  simp only [CollatzResearch.WordTrace]
  refine ⟨50380733463731779413601075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67174311284975705884801433 50380733463731779413601075)
  ·
    refine ⟨75571100195597669120401613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50380733463731779413601075 75571100195597669120401613)
    ·
      refine ⟨28339162573349125920150605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75571100195597669120401613 28339162573349125920150605)
      ·
        refine ⟨10627185965005922220056477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28339162573349125920150605 10627185965005922220056477)
        ·
          refine ⟨3985194736877220832521179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10627185965005922220056477 3985194736877220832521179)
          ·
            refine ⟨5977792105315831248781769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985194736877220832521179 5977792105315831248781769)
            ·
              refine ⟨4483344078986873436586327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977792105315831248781769 4483344078986873436586327)
              ·
                refine ⟨6725016118480310154879491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483344078986873436586327 6725016118480310154879491)
                ·
                  refine ⟨10087524177720465232319237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725016118480310154879491 10087524177720465232319237)
                  ·
                    refine ⟨1891410783322587231059857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10087524177720465232319237 1891410783322587231059857)
                    ·
                      refine ⟨1418558087491940423294893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891410783322587231059857 1418558087491940423294893)
                      ·
                        rfl

theorem cell23_2762632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2762632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762632 prefixEnd_2762632 := by exact prefixLift 2762632
  have htrace : WordTrace (prefixWord ++ tailWord_2762632) baseStart_2762632 baseEnd_2762632 := by
    simpa [prefixWord, tailWord_2762632, baseEnd_2762632] using wordTrace_append hprefix tailTrace_2762632
  have hstable : (prefixWord ++ tailWord_2762632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762632).length < 2 ^ (prefixWord ++ tailWord_2762632).sum := by decide
  have hdescent : baseEnd_2762632 < baseStart_2762632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762661 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2762661 : Nat := 118140960795 + 2762661 * 2 ^ 59
def prefixEnd_2762661 : Nat := 4983230072969 + 3 ^ 40 * 2762661 * 2
def baseEnd_2762661 : Nat := 1418572978430920809832259

theorem tailTrace_2762661 : CollatzResearch.WordTrace tailWord_2762661 prefixEnd_2762661 1418572978430920809832259 := by
  unfold tailWord_2762661
  simp only [CollatzResearch.WordTrace]
  refine ⟨100762524644358496780007837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67175016429572331186671891 100762524644358496780007837)
  ·
    refine ⟨37785946741634436292502939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100762524644358496780007837 37785946741634436292502939)
    ·
      refine ⟨56678920112451654438754409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37785946741634436292502939 56678920112451654438754409)
      ·
        refine ⟨42509190084338740829065807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56678920112451654438754409 42509190084338740829065807)
        ·
          refine ⟨63763785126508111243598711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42509190084338740829065807 63763785126508111243598711)
          ·
            refine ⟨95645677689762166865398067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63763785126508111243598711 95645677689762166865398067)
            ·
              refine ⟨143468516534643250298097101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95645677689762166865398067 143468516534643250298097101)
              ·
                refine ⟨53800693700491218861786413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143468516534643250298097101 53800693700491218861786413)
                ·
                  refine ⟨20175260137684207073169905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53800693700491218861786413 20175260137684207073169905)
                  ·
                    refine ⟨15131445103263155304877429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20175260137684207073169905 15131445103263155304877429)
                    ·
                      refine ⟨1418572978430920809832259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15131445103263155304877429 1418572978430920809832259)
                      ·
                        rfl

theorem cell23_2762661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2762661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762661 prefixEnd_2762661 := by exact prefixLift 2762661
  have htrace : WordTrace (prefixWord ++ tailWord_2762661) baseStart_2762661 baseEnd_2762661 := by
    simpa [prefixWord, tailWord_2762661, baseEnd_2762661] using wordTrace_append hprefix tailTrace_2762661
  have hstable : (prefixWord ++ tailWord_2762661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762661).length < 2 ^ (prefixWord ++ tailWord_2762661).sum := by decide
  have hdescent : baseEnd_2762661 < baseStart_2762661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762711 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 10]
def baseStart_2762711 : Nat := 118140960795 + 2762711 * 2 ^ 59
def prefixEnd_2762711 : Nat := 4983230072969 + 3 ^ 40 * 2762711 * 2
def baseEnd_2762711 : Nat := 157622072495960623800781

theorem tailTrace_2762711 : CollatzResearch.WordTrace tailWord_2762711 prefixEnd_2762711 157622072495960623800781 := by
  unfold tailWord_2762711
  simp only [CollatzResearch.WordTrace]
  refine ⟨100764348294177355319327987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67176232196118236879551991 100764348294177355319327987)
  ·
    refine ⟨151146522441266032978991981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100764348294177355319327987 151146522441266032978991981)
    ·
      refine ⟨56679945915474762367121993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151146522441266032978991981 56679945915474762367121993)
      ·
        refine ⟨42509959436606071775341495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56679945915474762367121993 42509959436606071775341495)
        ·
          refine ⟨63764939154909107663012243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42509959436606071775341495 63764939154909107663012243)
          ·
            refine ⟨95647408732363661494518365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63764939154909107663012243 95647408732363661494518365)
            ·
              refine ⟨35867778274636373060444387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95647408732363661494518365 35867778274636373060444387)
              ·
                refine ⟨53801667411954559590666581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35867778274636373060444387 53801667411954559590666581)
                ·
                  refine ⟨157622072495960623800781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53801667411954559590666581 157622072495960623800781)
                  ·
                    rfl

theorem cell23_2762711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 10].length) (baseStart_2762711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762711 prefixEnd_2762711 := by exact prefixLift 2762711
  have htrace : WordTrace (prefixWord ++ tailWord_2762711) baseStart_2762711 baseEnd_2762711 := by
    simpa [prefixWord, tailWord_2762711, baseEnd_2762711] using wordTrace_append hprefix tailTrace_2762711
  have hstable : (prefixWord ++ tailWord_2762711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762711).length < 2 ^ (prefixWord ++ tailWord_2762711).sum := by decide
  have hdescent : baseEnd_2762711 < baseStart_2762711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762728 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 6]
def baseStart_2762728 : Nat := 118140960795 + 2762728 * 2 ^ 59
def prefixEnd_2762728 : Nat := 4983230072969 + 3 ^ 40 * 2762728 * 2
def baseEnd_2762728 : Nat := 157623042403863560854939

theorem tailTrace_2762728 : CollatzResearch.WordTrace tailWord_2762728 prefixEnd_2762728 157623042403863560854939 := by
  unfold tailWord_2762728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50382484167557883611348419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67176645556743844815131225 50382484167557883611348419)
  ·
    refine ⟨75573726251336825417022629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50382484167557883611348419 75573726251336825417022629)
    ·
      refine ⟨14170073672125654765691743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75573726251336825417022629 14170073672125654765691743)
      ·
        refine ⟨21255110508188482148537615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170073672125654765691743 21255110508188482148537615)
        ·
          refine ⟨31882665762282723222806423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21255110508188482148537615 31882665762282723222806423)
          ·
            refine ⟨47823998643424084834209635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31882665762282723222806423 47823998643424084834209635)
            ·
              refine ⟨71735997965136127251314453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47823998643424084834209635 71735997965136127251314453)
              ·
                refine ⟨3362624904615755964905365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71735997965136127251314453 3362624904615755964905365)
                ·
                  refine ⟨157623042403863560854939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3362624904615755964905365 157623042403863560854939)
                  ·
                    rfl

theorem cell23_2762728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_2762728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762728 prefixEnd_2762728 := by exact prefixLift 2762728
  have htrace : WordTrace (prefixWord ++ tailWord_2762728) baseStart_2762728 baseEnd_2762728 := by
    simpa [prefixWord, tailWord_2762728, baseEnd_2762728] using wordTrace_append hprefix tailTrace_2762728
  have hstable : (prefixWord ++ tailWord_2762728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762728).length < 2 ^ (prefixWord ++ tailWord_2762728).sum := by decide
  have hdescent : baseEnd_2762728 < baseStart_2762728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762731 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_2762731 : Nat := 118140960795 + 2762731 * 2 ^ 59
def prefixEnd_2762731 : Nat := 4983230072969 + 3 ^ 40 * 2762731 * 2
def baseEnd_2762731 : Nat := 1418608922076735535956937

theorem tailTrace_2762731 : CollatzResearch.WordTrace tailWord_2762731 prefixEnd_2762731 1418608922076735535956937 := by
  unfold tailWord_2762731
  simp only [CollatzResearch.WordTrace]
  refine ⟨100765077754104898735056047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67176718502736599156704031 100765077754104898735056047)
  ·
    refine ⟨151147616631157348102584071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100765077754104898735056047 151147616631157348102584071)
    ·
      refine ⟨226721424946736022153876107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151147616631157348102584071 226721424946736022153876107)
      ·
        refine ⟨340082137420104033230814161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226721424946736022153876107 340082137420104033230814161)
        ·
          refine ⟨255061603065078024923110621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340082137420104033230814161 255061603065078024923110621)
          ·
            refine ⟨95648101149404259346166483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255061603065078024923110621 95648101149404259346166483)
            ·
              refine ⟨143472151724106389019249725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95648101149404259346166483 143472151724106389019249725)
              ·
                refine ⟨53802056896539895882218647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143472151724106389019249725 53802056896539895882218647)
                ·
                  refine ⟨80703085344809843823327971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53802056896539895882218647 80703085344809843823327971)
                  ·
                    refine ⟨121054628017214765734991957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80703085344809843823327971 121054628017214765734991957)
                    ·
                      refine ⟨1418608922076735535956937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121054628017214765734991957 1418608922076735535956937)
                      ·
                        rfl

theorem cell23_2762731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_2762731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762731 prefixEnd_2762731 := by exact prefixLift 2762731
  have htrace : WordTrace (prefixWord ++ tailWord_2762731) baseStart_2762731 baseEnd_2762731 := by
    simpa [prefixWord, tailWord_2762731, baseEnd_2762731] using wordTrace_append hprefix tailTrace_2762731
  have hstable : (prefixWord ++ tailWord_2762731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762731).length < 2 ^ (prefixWord ++ tailWord_2762731).sum := by decide
  have hdescent : baseEnd_2762731 < baseStart_2762731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762745 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 6]
def baseStart_2762745 : Nat := 118140960795 + 2762745 * 2 ^ 59
def prefixEnd_2762745 : Nat := 4983230072969 + 3 ^ 40 * 2762745 * 2
def baseEnd_2762745 : Nat := 157624012311766497909097

theorem tailTrace_2762745 : CollatzResearch.WordTrace tailWord_2762745 prefixEnd_2762745 157624012311766497909097 := by
  unfold tailWord_2762745
  simp only [CollatzResearch.WordTrace]
  refine ⟨100765588376054179126065689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67177058917369452750710459 100765588376054179126065689)
  ·
    refine ⟨75574191282040634344549267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100765588376054179126065689 75574191282040634344549267)
    ·
      refine ⟨113361286923060951516823901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75574191282040634344549267 113361286923060951516823901)
      ·
        refine ⟨42510482596147856818808963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113361286923060951516823901 42510482596147856818808963)
        ·
          refine ⟨63765723894221785228213445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42510482596147856818808963 63765723894221785228213445)
          ·
            refine ⟨11956073230166584730290021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63765723894221785228213445 11956073230166584730290021)
            ·
              refine ⟨2241763730656234636929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11956073230166584730290021 2241763730656234636929379)
              ·
                refine ⟨3362645595984351955394069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241763730656234636929379 3362645595984351955394069)
                ·
                  refine ⟨157624012311766497909097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3362645595984351955394069 157624012311766497909097)
                  ·
                    rfl

theorem cell23_2762745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_2762745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762745 prefixEnd_2762745 := by exact prefixLift 2762745
  have htrace : WordTrace (prefixWord ++ tailWord_2762745) baseStart_2762745 baseEnd_2762745 := by
    simpa [prefixWord, tailWord_2762745, baseEnd_2762745] using wordTrace_append hprefix tailTrace_2762745
  have hstable : (prefixWord ++ tailWord_2762745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762745).length < 2 ^ (prefixWord ++ tailWord_2762745).sum := by decide
  have hdescent : baseEnd_2762745 < baseStart_2762745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762755 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 3]
def baseStart_2762755 : Nat := 118140960795 + 2762755 * 2 ^ 59
def prefixEnd_2762755 : Nat := 4983230072969 + 3 ^ 40 * 2762755 * 2
def baseEnd_2762755 : Nat := 1418621245612443442056827

theorem tailTrace_2762755 : CollatzResearch.WordTrace tailWord_2762755 prefixEnd_2762755 1418621245612443442056827 := by
  unfold tailWord_2762755
  simp only [CollatzResearch.WordTrace]
  refine ⟨100765953106017950833929719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67177302070678633889286479 100765953106017950833929719)
  ·
    refine ⟨151148929659026926250894579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100765953106017950833929719 151148929659026926250894579)
    ·
      refine ⟨226723394488540389376341869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151148929659026926250894579 226723394488540389376341869)
      ·
        refine ⟨85021272933202646016128201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226723394488540389376341869 85021272933202646016128201)
        ·
          refine ⟨63765954699901984512096151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85021272933202646016128201 63765954699901984512096151)
          ·
            refine ⟨95648932049852976768144227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63765954699901984512096151 95648932049852976768144227)
            ·
              refine ⟨143473398074779465152216341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95648932049852976768144227 143473398074779465152216341)
              ·
                refine ⟨6725315534755287429010141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143473398074779465152216341 6725315534755287429010141)
                ·
                  refine ⟨2521993325533232785878803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6725315534755287429010141 2521993325533232785878803)
                  ·
                    refine ⟨3782989988299849178818205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521993325533232785878803 3782989988299849178818205)
                    ·
                      refine ⟨1418621245612443442056827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3782989988299849178818205 1418621245612443442056827)
                      ·
                        rfl

theorem cell23_2762755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_2762755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762755 prefixEnd_2762755 := by exact prefixLift 2762755
  have htrace : WordTrace (prefixWord ++ tailWord_2762755) baseStart_2762755 baseEnd_2762755 := by
    simpa [prefixWord, tailWord_2762755, baseEnd_2762755] using wordTrace_append hprefix tailTrace_2762755
  have hstable : (prefixWord ++ tailWord_2762755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762755).length < 2 ^ (prefixWord ++ tailWord_2762755).sum := by decide
  have hdescent : baseEnd_2762755 < baseStart_2762755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762789 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_2762789 : Nat := 118140960795 + 2762789 * 2 ^ 59
def prefixEnd_2762789 : Nat := 4983230072969 + 3 ^ 40 * 2762789 * 2
def baseEnd_2762789 : Nat := 1418638703954696309031671

theorem tailTrace_2762789 : CollatzResearch.WordTrace tailWord_2762789 prefixEnd_2762789 1418638703954696309031671 := by
  unfold tailWord_2762789
  simp only [CollatzResearch.WordTrace]
  refine ⟨100767193187894774640667421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67178128791929849760444947 100767193187894774640667421)
  ·
    refine ⟨37787697445460540490250283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100767193187894774640667421 37787697445460540490250283)
    ·
      refine ⟨56681546168190810735375425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37787697445460540490250283 56681546168190810735375425)
      ·
        refine ⟨42511159626143108051531569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56681546168190810735375425 42511159626143108051531569)
        ·
          refine ⟨31883369719607331038648677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42511159626143108051531569 31883369719607331038648677)
          ·
            refine ⟨5978131822426374569746627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31883369719607331038648677 5978131822426374569746627)
            ·
              refine ⟨8967197733639561854619941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978131822426374569746627 8967197733639561854619941)
              ·
                refine ⟨1681349575057417847741239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8967197733639561854619941 1681349575057417847741239)
                ·
                  refine ⟨2522024362586126771611859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681349575057417847741239 2522024362586126771611859)
                  ·
                    refine ⟨3783036543879190157417789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522024362586126771611859 3783036543879190157417789)
                    ·
                      refine ⟨1418638703954696309031671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783036543879190157417789 1418638703954696309031671)
                      ·
                        rfl

theorem cell23_2762789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_2762789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762789 prefixEnd_2762789 := by exact prefixLift 2762789
  have htrace : WordTrace (prefixWord ++ tailWord_2762789) baseStart_2762789 baseEnd_2762789 := by
    simpa [prefixWord, tailWord_2762789, baseEnd_2762789] using wordTrace_append hprefix tailTrace_2762789
  have hstable : (prefixWord ++ tailWord_2762789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762789).length < 2 ^ (prefixWord ++ tailWord_2762789).sum := by decide
  have hdescent : baseEnd_2762789 < baseStart_2762789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762815 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_2762815 : Nat := 118140960795 + 2762815 * 2 ^ 59
def prefixEnd_2762815 : Nat := 4983230072969 + 3 ^ 40 * 2762815 * 2
def baseEnd_2762815 : Nat := 1418652054451713207306551

theorem tailTrace_2762815 : CollatzResearch.WordTrace tailWord_2762815 prefixEnd_2762815 1418652054451713207306551 := by
  unfold tailWord_2762815
  simp only [CollatzResearch.WordTrace]
  refine ⟨100768141485800581081113899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67178760990533720720742599 100768141485800581081113899)
  ·
    refine ⟨151152212228700871621670849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100768141485800581081113899 151152212228700871621670849)
    ·
      refine ⟨113364159171525653716253137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151152212228700871621670849 113364159171525653716253137)
      ·
        refine ⟨85023119378644240287189853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113364159171525653716253137 85023119378644240287189853)
        ·
          refine ⟨31883669766991590107696195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85023119378644240287189853 31883669766991590107696195)
          ·
            refine ⟨47825504650487385161544293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31883669766991590107696195 47825504650487385161544293)
            ·
              refine ⟨8967282121966384717789555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47825504650487385161544293 8967282121966384717789555)
              ·
                refine ⟨13450923182949577076684333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8967282121966384717789555 13450923182949577076684333)
                ·
                  refine ⟨5044096193606091403756625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13450923182949577076684333 5044096193606091403756625)
                  ·
                    refine ⟨3783072145204568552817469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5044096193606091403756625 3783072145204568552817469)
                    ·
                      refine ⟨1418652054451713207306551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783072145204568552817469 1418652054451713207306551)
                      ·
                        rfl

theorem cell23_2762815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_2762815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762815 prefixEnd_2762815 := by exact prefixLift 2762815
  have htrace : WordTrace (prefixWord ++ tailWord_2762815) baseStart_2762815 baseEnd_2762815 := by
    simpa [prefixWord, tailWord_2762815, baseEnd_2762815] using wordTrace_append hprefix tailTrace_2762815
  have hstable : (prefixWord ++ tailWord_2762815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762815).length < 2 ^ (prefixWord ++ tailWord_2762815).sum := by decide
  have hdescent : baseEnd_2762815 < baseStart_2762815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762822 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2762822 : Nat := 118140960795 + 2762822 * 2 ^ 59
def prefixEnd_2762822 : Nat := 4983230072969 + 3 ^ 40 * 2762822 * 2
def baseEnd_2762822 : Nat := 472885216272098226639673

theorem tailTrace_2762822 : CollatzResearch.WordTrace tailWord_2762822 prefixEnd_2762822 472885216272098226639673 := by
  unfold tailWord_2762822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149012399899225664894335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67178931197850147517745813 3149012399899225664894335)
  ·
    refine ⟨4723518599848838497341503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3149012399899225664894335 4723518599848838497341503)
    ·
      refine ⟨7085277899773257746012255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723518599848838497341503 7085277899773257746012255)
      ·
        refine ⟨10627916849659886619018383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085277899773257746012255 10627916849659886619018383)
        ·
          refine ⟨15941875274489829928527575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627916849659886619018383 15941875274489829928527575)
          ·
            refine ⟨23912812911734744892791363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15941875274489829928527575 23912812911734744892791363)
            ·
              refine ⟨35869219367602117339187045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23912812911734744892791363 35869219367602117339187045)
              ·
                refine ⟨6725478631425397001097571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35869219367602117339187045 6725478631425397001097571)
                ·
                  refine ⟨10088217947138095501646357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725478631425397001097571 10088217947138095501646357)
                  ·
                    refine ⟨472885216272098226639673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10088217947138095501646357 472885216272098226639673)
                    ·
                      rfl

theorem cell23_2762822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2762822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762822 prefixEnd_2762822 := by exact prefixLift 2762822
  have htrace : WordTrace (prefixWord ++ tailWord_2762822) baseStart_2762822 baseEnd_2762822 := by
    simpa [prefixWord, tailWord_2762822, baseEnd_2762822] using wordTrace_append hprefix tailTrace_2762822
  have hstable : (prefixWord ++ tailWord_2762822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762822).length < 2 ^ (prefixWord ++ tailWord_2762822).sum := by decide
  have hdescent : baseEnd_2762822 < baseStart_2762822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762829 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_2762829 : Nat := 118140960795 + 2762829 * 2 ^ 59
def prefixEnd_2762829 : Nat := 4983230072969 + 3 ^ 40 * 2762829 * 2
def baseEnd_2762829 : Nat := 1418659243180876152531487

theorem tailTrace_2762829 : CollatzResearch.WordTrace tailWord_2762829 prefixEnd_2762829 1418659243180876152531487 := by
  unfold tailWord_2762829
  simp only [CollatzResearch.WordTrace]
  refine ⟨100768652107749861472123541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67179101405166574314749027 100768652107749861472123541)
  ·
    refine ⟨4723530567550774756505791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100768652107749861472123541 4723530567550774756505791)
    ·
      refine ⟨7085295851326162134758687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723530567550774756505791 7085295851326162134758687)
      ·
        refine ⟨10627943776989243202138031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085295851326162134758687 10627943776989243202138031)
        ·
          refine ⟨15941915665483864803207047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627943776989243202138031 15941915665483864803207047)
          ·
            refine ⟨23912873498225797204810571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15941915665483864803207047 23912873498225797204810571)
            ·
              refine ⟨35869310247338695807215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23912873498225797204810571 35869310247338695807215857)
              ·
                refine ⟨26901982685504021855411893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35869310247338695807215857 26901982685504021855411893)
                ·
                  refine ⟨2522060876766002048944865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26901982685504021855411893 2522060876766002048944865)
                  ·
                    refine ⟨1891545657574501536708649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522060876766002048944865 1891545657574501536708649)
                    ·
                      refine ⟨1418659243180876152531487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891545657574501536708649 1418659243180876152531487)
                      ·
                        rfl

theorem cell23_2762829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_2762829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762829 prefixEnd_2762829 := by exact prefixLift 2762829
  have htrace : WordTrace (prefixWord ++ tailWord_2762829) baseStart_2762829 baseEnd_2762829 := by
    simpa [prefixWord, tailWord_2762829, baseEnd_2762829] using wordTrace_append hprefix tailTrace_2762829
  have hstable : (prefixWord ++ tailWord_2762829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762829).length < 2 ^ (prefixWord ++ tailWord_2762829).sum := by decide
  have hdescent : baseEnd_2762829 < baseStart_2762829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762955 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 2, 5]
def baseStart_2762955 : Nat := 118140960795 + 2762955 * 2 ^ 59
def prefixEnd_2762955 : Nat := 4983230072969 + 3 ^ 40 * 2762955 * 2
def baseEnd_2762955 : Nat := 472907980581114219851969

theorem tailTrace_2762955 : CollatzResearch.WordTrace tailWord_2762955 prefixEnd_2762955 472907980581114219851969 := by
  unfold tailWord_2762955
  simp only [CollatzResearch.WordTrace]
  refine ⟨100773247705293384991210319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67182165136862256660806879 100773247705293384991210319)
  ·
    refine ⟨151159871557940077486815479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100773247705293384991210319 151159871557940077486815479)
    ·
      refine ⟨226739807336910116230223219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151159871557940077486815479 226739807336910116230223219)
      ·
        refine ⟨340109711005365174345334829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226739807336910116230223219 340109711005365174345334829)
        ·
          refine ⟨127541141627011940379500561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340109711005365174345334829 127541141627011940379500561)
          ·
            refine ⟨95655856220258955284625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127541141627011940379500561 95655856220258955284625421)
            ·
              refine ⟨35870946082597108231734533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95655856220258955284625421 35870946082597108231734533)
              ·
                refine ⟨6725802390486957793450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35870946082597108231734533 6725802390486957793450225)
                ·
                  refine ⟨5044351792865218345087669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725802390486957793450225 5044351792865218345087669)
                  ·
                    refine ⟨472907980581114219851969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5044351792865218345087669 472907980581114219851969)
                    ·
                      rfl

theorem cell23_2762955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 5].length) (baseStart_2762955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762955 prefixEnd_2762955 := by exact prefixLift 2762955
  have htrace : WordTrace (prefixWord ++ tailWord_2762955) baseStart_2762955 baseEnd_2762955 := by
    simpa [prefixWord, tailWord_2762955, baseEnd_2762955] using wordTrace_append hprefix tailTrace_2762955
  have hstable : (prefixWord ++ tailWord_2762955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762955).length < 2 ^ (prefixWord ++ tailWord_2762955).sum := by decide
  have hdescent : baseEnd_2762955 < baseStart_2762955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762975 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2762975 : Nat := 118140960795 + 2762975 * 2 ^ 59
def prefixEnd_2762975 : Nat := 4983230072969 + 3 ^ 40 * 2762975 * 2
def baseEnd_2762975 : Nat := 1418734211356432581305815

theorem tailTrace_2762975 : CollatzResearch.WordTrace tailWord_2762975 prefixEnd_2762975 1418734211356432581305815 := by
  unfold tailWord_2762975
  simp only [CollatzResearch.WordTrace]
  refine ⟨100773977165220928406938379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67182651443480618937958919 100773977165220928406938379)
  ·
    refine ⟨151160965747831392610407569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100773977165220928406938379 151160965747831392610407569)
    ·
      refine ⟨113370724310873544457805677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151160965747831392610407569 113370724310873544457805677)
      ·
        refine ⟨42514021616577579171677129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113370724310873544457805677 42514021616577579171677129)
        ·
          refine ⟨31885516212433184378757847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42514021616577579171677129 31885516212433184378757847)
          ·
            refine ⟨47828274318649776568136771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31885516212433184378757847 47828274318649776568136771)
            ·
              refine ⟨71742411477974664852205157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47828274318649776568136771 71742411477974664852205157)
              ·
                refine ⟨13451702152120249659788467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71742411477974664852205157 13451702152120249659788467)
                ·
                  refine ⟨20177553228180374489682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13451702152120249659788467 20177553228180374489682701)
                  ·
                    refine ⟨7566582460567640433631013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20177553228180374489682701 7566582460567640433631013)
                    ·
                      refine ⟨1418734211356432581305815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7566582460567640433631013 1418734211356432581305815)
                      ·
                        rfl

theorem cell23_2762975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2762975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2762975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2762975 prefixEnd_2762975 := by exact prefixLift 2762975
  have htrace : WordTrace (prefixWord ++ tailWord_2762975) baseStart_2762975 baseEnd_2762975 := by
    simpa [prefixWord, tailWord_2762975, baseEnd_2762975] using wordTrace_append hprefix tailTrace_2762975
  have hstable : (prefixWord ++ tailWord_2762975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762975).length < 2 ^ (prefixWord ++ tailWord_2762975).sum := by decide
  have hdescent : baseEnd_2762975 < baseStart_2762975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763005 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2763005 : Nat := 118140960795 + 2763005 * 2 ^ 59
def prefixEnd_2763005 : Nat := 4983230072969 + 3 ^ 40 * 2763005 * 2
def baseEnd_2763005 : Nat := 1418749615776067463930677

theorem tailTrace_2763005 : CollatzResearch.WordTrace tailWord_2763005 prefixEnd_2763005 1418749615776067463930677 := by
  unfold tailWord_2763005
  simp only [CollatzResearch.WordTrace]
  refine ⟨100775071355112243530530469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67183380903408162353686979 100775071355112243530530469)
  ·
    refine ⟨18895325879083545661974463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100775071355112243530530469 18895325879083545661974463)
    ·
      refine ⟨28342988818625318492961695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18895325879083545661974463 28342988818625318492961695)
      ·
        refine ⟨42514483227937977739442543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28342988818625318492961695 42514483227937977739442543)
        ·
          refine ⟨63771724841906966609163815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42514483227937977739442543 63771724841906966609163815)
          ·
            refine ⟨95657587262860449913745723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63771724841906966609163815 95657587262860449913745723)
            ·
              refine ⟨143486380894290674870618585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95657587262860449913745723 143486380894290674870618585)
              ·
                refine ⟨107614785670718006152963939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143486380894290674870618585 107614785670718006152963939)
                ·
                  refine ⟨161422178506077009229445909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107614785670718006152963939 161422178506077009229445909)
                  ·
                    refine ⟨7566664617472359807630277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161422178506077009229445909 7566664617472359807630277)
                    ·
                      refine ⟨1418749615776067463930677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7566664617472359807630277 1418749615776067463930677)
                      ·
                        rfl

theorem cell23_2763005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2763005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763005 prefixEnd_2763005 := by exact prefixLift 2763005
  have htrace : WordTrace (prefixWord ++ tailWord_2763005) baseStart_2763005 baseEnd_2763005 := by
    simpa [prefixWord, tailWord_2763005, baseEnd_2763005] using wordTrace_append hprefix tailTrace_2763005
  have hstable : (prefixWord ++ tailWord_2763005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763005).length < 2 ^ (prefixWord ++ tailWord_2763005).sum := by decide
  have hdescent : baseEnd_2763005 < baseStart_2763005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763019 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 1, 4]
def baseStart_2763019 : Nat := 118140960795 + 2763019 * 2 ^ 59
def prefixEnd_2763019 : Nat := 4983230072969 + 3 ^ 40 * 2763019 * 2
def baseEnd_2763019 : Nat := 472918934835076803051871

theorem tailTrace_2763019 : CollatzResearch.WordTrace tailWord_2763019 prefixEnd_2763019 472918934835076803051871 := by
  unfold tailWord_2763019
  simp only [CollatzResearch.WordTrace]
  refine ⟨100775581977061523921540111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67183721318041015947693407 100775581977061523921540111)
  ·
    refine ⟨151163372965592285882310167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100775581977061523921540111 151163372965592285882310167)
    ·
      refine ⟨226745059448388428823465251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151163372965592285882310167 226745059448388428823465251)
      ·
        refine ⟨340117589172582643235197877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226745059448388428823465251 340117589172582643235197877)
        ·
          refine ⟨31886023984929622803299801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340117589172582643235197877 31886023984929622803299801)
          ·
            refine ⟨23914517988697217102474851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31886023984929622803299801 23914517988697217102474851)
            ·
              refine ⟨35871776983045825653712277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23914517988697217102474851 35871776983045825653712277)
              ·
                refine ⟨1681489546080273077517763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35871776983045825653712277 1681489546080273077517763)
                ·
                  refine ⟨2522234319120409616276645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681489546080273077517763 2522234319120409616276645)
                  ·
                    refine ⟨472918934835076803051871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2522234319120409616276645 472918934835076803051871)
                    ·
                      rfl

theorem cell23_2763019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 4].length) (baseStart_2763019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763019 prefixEnd_2763019 := by exact prefixLift 2763019
  have htrace : WordTrace (prefixWord ++ tailWord_2763019) baseStart_2763019 baseEnd_2763019 := by
    simpa [prefixWord, tailWord_2763019, baseEnd_2763019] using wordTrace_append hprefix tailTrace_2763019
  have hstable : (prefixWord ++ tailWord_2763019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763019).length < 2 ^ (prefixWord ++ tailWord_2763019).sum := by decide
  have hdescent : baseEnd_2763019 < baseStart_2763019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763139 : List Nat := [1, 1, 1, 3, 6, 2, 1, 8]
def baseStart_2763139 : Nat := 118140960795 + 2763139 * 2 ^ 59
def prefixEnd_2763139 : Nat := 4983230072969 + 3 ^ 40 * 2763139 * 2
def baseEnd_2763139 : Nat := 52548830451250738505743

theorem tailTrace_2763139 : CollatzResearch.WordTrace tailWord_2763139 prefixEnd_2763139 52548830451250738505743 := by
  unfold tailWord_2763139
  simp only [CollatzResearch.WordTrace]
  refine ⟨100779958736626784415908471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67186639157751189610605647 100779958736626784415908471)
  ·
    refine ⟨151169938104940176623862707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100779958736626784415908471 151169938104940176623862707)
    ·
      refine ⟨226754907157410264935794061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151169938104940176623862707 226754907157410264935794061)
      ·
        refine ⟨85033090184028849350922773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226754907157410264935794061 85033090184028849350922773)
        ·
          refine ⟨3985926102376352313324505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85033090184028849350922773 3985926102376352313324505)
          ·
            refine ⟨2989444576782264234993379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985926102376352313324505 2989444576782264234993379)
            ·
              refine ⟨4484166865173396352490069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989444576782264234993379 4484166865173396352490069)
              ·
                refine ⟨52548830451250738505743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4484166865173396352490069 52548830451250738505743)
                ·
                  rfl

theorem cell23_2763139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 8].length) (baseStart_2763139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763139 prefixEnd_2763139 := by exact prefixLift 2763139
  have htrace : WordTrace (prefixWord ++ tailWord_2763139) baseStart_2763139 baseEnd_2763139 := by
    simpa [prefixWord, tailWord_2763139, baseEnd_2763139] using wordTrace_append hprefix tailTrace_2763139
  have hstable : (prefixWord ++ tailWord_2763139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763139).length < 2 ^ (prefixWord ++ tailWord_2763139).sum := by decide
  have hdescent : baseEnd_2763139 < baseStart_2763139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763156 : List Nat := [2, 4, 2, 1, 3, 1, 3, 7]
def baseStart_2763156 : Nat := 118140960795 + 2763156 * 2 ^ 59
def prefixEnd_2763156 : Nat := 4983230072969 + 3 ^ 40 * 2763156 * 2
def baseEnd_2763156 : Nat := 52549153753885050857129

theorem tailTrace_2763156 : CollatzResearch.WordTrace tailWord_2763156 prefixEnd_2763156 52549153753885050857129 := by
  unfold tailWord_2763156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50390289388782598159638661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67187052518376797546184881 50390289388782598159638661)
  ·
    refine ⟨9448179260396737154932249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50390289388782598159638661 9448179260396737154932249)
    ·
      refine ⟨7086134445297552866199187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448179260396737154932249 7086134445297552866199187)
      ·
        refine ⟨10629201667946329299298781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086134445297552866199187 10629201667946329299298781)
        ·
          refine ⟨3985950625479873487237043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10629201667946329299298781 3985950625479873487237043)
          ·
            refine ⟨5978925938219810230855565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985950625479873487237043 5978925938219810230855565)
            ·
              refine ⟨2242097226832428836570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5978925938219810230855565 2242097226832428836570837)
              ·
                refine ⟨52549153753885050857129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2242097226832428836570837 52549153753885050857129)
                ·
                  rfl

theorem cell23_2763156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 7].length) (baseStart_2763156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763156 prefixEnd_2763156 := by exact prefixLift 2763156
  have htrace : WordTrace (prefixWord ++ tailWord_2763156) baseStart_2763156 baseEnd_2763156 := by
    simpa [prefixWord, tailWord_2763156, baseEnd_2763156] using wordTrace_append hprefix tailTrace_2763156
  have hstable : (prefixWord ++ tailWord_2763156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763156).length < 2 ^ (prefixWord ++ tailWord_2763156).sum := by decide
  have hdescent : baseEnd_2763156 < baseStart_2763156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_2763192 : Nat := 118140960795 + 2763192 * 2 ^ 59
def prefixEnd_2763192 : Nat := 4983230072969 + 3 ^ 40 * 2763192 * 2
def baseEnd_2763192 : Nat := 1418845636658458232292317

theorem tailTrace_2763192 : CollatzResearch.WordTrace tailWord_2763192 prefixEnd_2763192 1418845636658458232292317 := by
  unfold tailWord_2763192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50390945902717387233793915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67187927870289849645058553 50390945902717387233793915)
  ·
    refine ⟨75586418854076080850690873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50390945902717387233793915 75586418854076080850690873)
    ·
      refine ⟨56689814140557060638018155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75586418854076080850690873 56689814140557060638018155)
      ·
        refine ⟨85034721210835590957027233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56689814140557060638018155 85034721210835590957027233)
        ·
          refine ⟨63776040908126693217770425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85034721210835590957027233 63776040908126693217770425)
          ·
            refine ⟨47832030681095019913327819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63776040908126693217770425 47832030681095019913327819)
            ·
              refine ⟨71748046021642529869991729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47832030681095019913327819 71748046021642529869991729)
              ·
                refine ⟨53811034516231897402493797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71748046021642529869991729 53811034516231897402493797)
                ·
                  refine ⟨10089568971793480762967587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53811034516231897402493797 10089568971793480762967587)
                  ·
                    refine ⟨15134353457690221144451381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10089568971793480762967587 15134353457690221144451381)
                    ·
                      refine ⟨1418845636658458232292317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15134353457690221144451381 1418845636658458232292317)
                      ·
                        rfl

theorem cell23_2763192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_2763192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763192 prefixEnd_2763192 := by exact prefixLift 2763192
  have htrace : WordTrace (prefixWord ++ tailWord_2763192) baseStart_2763192 baseEnd_2763192 := by
    simpa [prefixWord, tailWord_2763192, baseEnd_2763192] using wordTrace_append hprefix tailTrace_2763192
  have hstable : (prefixWord ++ tailWord_2763192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763192).length < 2 ^ (prefixWord ++ tailWord_2763192).sum := by decide
  have hdescent : baseEnd_2763192 < baseStart_2763192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763246 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_2763246 : Nat := 118140960795 + 2763246 * 2 ^ 59
def prefixEnd_2763246 : Nat := 4983230072969 + 3 ^ 40 * 2763246 * 2
def baseEnd_2763246 : Nat := 157652596068200113446341

theorem tailTrace_2763246 : CollatzResearch.WordTrace tailWord_2763246 prefixEnd_2763246 157652596068200113446341 := by
  unfold tailWord_2763246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597982668404892711256699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67189240898159427793369061 12597982668404892711256699)
  ·
    refine ⟨18896974002607339066885049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12597982668404892711256699 18896974002607339066885049)
    ·
      refine ⟨14172730501955504300163787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18896974002607339066885049 14172730501955504300163787)
      ·
        refine ⟨21259095752933256450245681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14172730501955504300163787 21259095752933256450245681)
        ·
          refine ⟨15944321814699942337684261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21259095752933256450245681 15944321814699942337684261)
          ·
            refine ⟨2989560340256239188315799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15944321814699942337684261 2989560340256239188315799)
            ·
              refine ⟨4484340510384358782473699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989560340256239188315799 4484340510384358782473699)
              ·
                refine ⟨6726510765576538173710549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484340510384358782473699 6726510765576538173710549)
                ·
                  refine ⟨157652596068200113446341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6726510765576538173710549 157652596068200113446341)
                  ·
                    rfl

theorem cell23_2763246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_2763246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763246 prefixEnd_2763246 := by exact prefixLift 2763246
  have htrace : WordTrace (prefixWord ++ tailWord_2763246) baseStart_2763246 baseEnd_2763246 := by
    simpa [prefixWord, tailWord_2763246, baseEnd_2763246] using wordTrace_append hprefix tailTrace_2763246
  have hstable : (prefixWord ++ tailWord_2763246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763246).length < 2 ^ (prefixWord ++ tailWord_2763246).sum := by decide
  have hdescent : baseEnd_2763246 < baseStart_2763246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763276 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_2763276 : Nat := 118140960795 + 2763276 * 2 ^ 59
def prefixEnd_2763276 : Nat := 4983230072969 + 3 ^ 40 * 2763276 * 2
def baseEnd_2763276 : Nat := 472962923011145301213977

theorem tailTrace_2763276 : CollatzResearch.WordTrace tailWord_2763276 prefixEnd_2763276 472962923011145301213977 := by
  unfold tailWord_2763276
  simp only [CollatzResearch.WordTrace]
  refine ⟨50392477768565228406822841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67189970358086971209097121 50392477768565228406822841)
  ·
    refine ⟨37794358326423921305117131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50392477768565228406822841 37794358326423921305117131)
    ·
      refine ⟨56691537489635881957675697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37794358326423921305117131 56691537489635881957675697)
      ·
        refine ⟨42518653117226911468256773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56691537489635881957675697 42518653117226911468256773)
        ·
          refine ⟨7972247459480045900298145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42518653117226911468256773 7972247459480045900298145)
          ·
            refine ⟨5979185594610034425223609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972247459480045900298145 5979185594610034425223609)
            ·
              refine ⟨4484389195957525818917707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5979185594610034425223609 4484389195957525818917707)
              ·
                refine ⟨6726583793936288728376561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484389195957525818917707 6726583793936288728376561)
                ·
                  refine ⟨5044937845452216546282421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6726583793936288728376561 5044937845452216546282421)
                  ·
                    refine ⟨472962923011145301213977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5044937845452216546282421 472962923011145301213977)
                    ·
                      rfl

theorem cell23_2763276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_2763276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763276 prefixEnd_2763276 := by exact prefixLift 2763276
  have htrace : WordTrace (prefixWord ++ tailWord_2763276) baseStart_2763276 baseEnd_2763276 := by
    simpa [prefixWord, tailWord_2763276, baseEnd_2763276] using wordTrace_append hprefix tailTrace_2763276
  have hstable : (prefixWord ++ tailWord_2763276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763276).length < 2 ^ (prefixWord ++ tailWord_2763276).sum := by decide
  have hdescent : baseEnd_2763276 < baseStart_2763276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763279 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_2763279 : Nat := 118140960795 + 2763279 * 2 ^ 59
def prefixEnd_2763279 : Nat := 4983230072969 + 3 ^ 40 * 2763279 * 2
def baseEnd_2763279 : Nat := 1418890309475399391904417

theorem tailTrace_2763279 : CollatzResearch.WordTrace tailWord_2763279 prefixEnd_2763279 1418890309475399391904417 := by
  unfold tailWord_2763279
  simp only [CollatzResearch.WordTrace]
  refine ⟨100785064956119588326004891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67190043304079725550669927 100785064956119588326004891)
  ·
    refine ⟨151177597434179382489007337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100785064956119588326004891 151177597434179382489007337)
    ·
      refine ⟨113383198075634536866755503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151177597434179382489007337 113383198075634536866755503)
      ·
        refine ⟨170074797113451805300133255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113383198075634536866755503 170074797113451805300133255)
        ·
          refine ⟨255112195670177707950199883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170074797113451805300133255 255112195670177707950199883)
          ·
            refine ⟨382668293505266561925299825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255112195670177707950199883 382668293505266561925299825)
            ·
              refine ⟨287001220128949921443974869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382668293505266561925299825 287001220128949921443974869)
              ·
                refine ⟨6726591096772263783843161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 287001220128949921443974869 6726591096772263783843161)
                ·
                  refine ⟨5044943322579197837882371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6726591096772263783843161 5044943322579197837882371)
                  ·
                    refine ⟨7567414983868796756823557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044943322579197837882371 7567414983868796756823557)
                    ·
                      refine ⟨1418890309475399391904417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7567414983868796756823557 1418890309475399391904417)
                      ·
                        rfl

theorem cell23_2763279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_2763279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763279 prefixEnd_2763279 := by exact prefixLift 2763279
  have htrace : WordTrace (prefixWord ++ tailWord_2763279) baseStart_2763279 baseEnd_2763279 := by
    simpa [prefixWord, tailWord_2763279, baseEnd_2763279] using wordTrace_append hprefix tailTrace_2763279
  have hstable : (prefixWord ++ tailWord_2763279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763279).length < 2 ^ (prefixWord ++ tailWord_2763279).sum := by decide
  have hdescent : baseEnd_2763279 < baseStart_2763279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763289 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_2763289 : Nat := 118140960795 + 2763289 * 2 ^ 59
def prefixEnd_2763289 : Nat := 4983230072969 + 3 ^ 40 * 2763289 * 2
def baseEnd_2763289 : Nat := 472965148093981450926457

theorem tailTrace_2763289 : CollatzResearch.WordTrace tailWord_2763289 prefixEnd_2763289 472965148093981450926457 := by
  unfold tailWord_2763289
  simp only [CollatzResearch.WordTrace]
  refine ⟨100785429686083360033868921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67190286457388906689245947 100785429686083360033868921)
  ·
    refine ⟨75589072264562520025401691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100785429686083360033868921 75589072264562520025401691)
    ·
      refine ⟨113383608396843780038102537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75589072264562520025401691 113383608396843780038102537)
      ·
        refine ⟨85037706297632835028576903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113383608396843780038102537 85037706297632835028576903)
        ·
          refine ⟨127556559446449252542865355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85037706297632835028576903 127556559446449252542865355)
          ·
            refine ⟨191334839169673878814298033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127556559446449252542865355 191334839169673878814298033)
            ·
              refine ⟨143501129377255409110723525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191334839169673878814298033 143501129377255409110723525)
              ·
                refine ⟨26906461758235389208260661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143501129377255409110723525 26906461758235389208260661)
                ·
                  refine ⟨2522480789834567738274437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26906461758235389208260661 2522480789834567738274437)
                  ·
                    refine ⟨472965148093981450926457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2522480789834567738274437 472965148093981450926457)
                    ·
                      rfl

theorem cell23_2763289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_2763289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763289 prefixEnd_2763289 := by exact prefixLift 2763289
  have htrace : WordTrace (prefixWord ++ tailWord_2763289) baseStart_2763289 baseEnd_2763289 := by
    simpa [prefixWord, tailWord_2763289, baseEnd_2763289] using wordTrace_append hprefix tailTrace_2763289
  have hstable : (prefixWord ++ tailWord_2763289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763289).length < 2 ^ (prefixWord ++ tailWord_2763289).sum := by decide
  have hdescent : baseEnd_2763289 < baseStart_2763289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763319 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 6]
def baseStart_2763319 : Nat := 118140960795 + 2763319 * 2 ^ 59
def prefixEnd_2763319 : Nat := 4983230072969 + 3 ^ 40 * 2763319 * 2
def baseEnd_2763319 : Nat := 157656760966842137267137

theorem tailTrace_2763319 : CollatzResearch.WordTrace tailWord_2763319 prefixEnd_2763319 157656760966842137267137 := by
  unfold tailWord_2763319
  simp only [CollatzResearch.WordTrace]
  refine ⟨100786523875974675157461011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67191015917316450104974007 100786523875974675157461011)
  ·
    refine ⟨151179785813962012736191517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100786523875974675157461011 151179785813962012736191517)
    ·
      refine ⟨56692419680235754776071819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151179785813962012736191517 56692419680235754776071819)
      ·
        refine ⟨85038629520353632164107729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56692419680235754776071819 85038629520353632164107729)
        ·
          refine ⟨63778972140265224123080797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85038629520353632164107729 63778972140265224123080797)
          ·
            refine ⟨23917114552599459046155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63778972140265224123080797 23917114552599459046155299)
            ·
              refine ⟨35875671828899188569232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23917114552599459046155299 35875671828899188569232949)
              ·
                refine ⟨3363344233959298928365589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35875671828899188569232949 3363344233959298928365589)
                ·
                  refine ⟨157656760966842137267137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3363344233959298928365589 157656760966842137267137)
                  ·
                    rfl

theorem cell23_2763319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 6].length) (baseStart_2763319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763319 prefixEnd_2763319 := by exact prefixLift 2763319
  have htrace : WordTrace (prefixWord ++ tailWord_2763319) baseStart_2763319 baseEnd_2763319 := by
    simpa [prefixWord, tailWord_2763319, baseEnd_2763319] using wordTrace_append hprefix tailTrace_2763319
  have hstable : (prefixWord ++ tailWord_2763319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763319).length < 2 ^ (prefixWord ++ tailWord_2763319).sum := by decide
  have hdescent : baseEnd_2763319 < baseStart_2763319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763333 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_2763333 : Nat := 118140960795 + 2763333 * 2 ^ 59
def prefixEnd_2763333 : Nat := 4983230072969 + 3 ^ 40 * 2763333 * 2
def baseEnd_2763333 : Nat := 1418918037430742180629169

theorem tailTrace_2763333 : CollatzResearch.WordTrace tailWord_2763333 prefixEnd_2763333 1418918037430742180629169 := by
  unfold tailWord_2763333
  simp only [CollatzResearch.WordTrace]
  refine ⟨100787034497923955548470653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67191356331949303698980435 100787034497923955548470653)
  ·
    refine ⟨37795137936721483330676495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100787034497923955548470653 37795137936721483330676495)
    ·
      refine ⟨56692706905082224996014743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37795137936721483330676495 56692706905082224996014743)
      ·
        refine ⟨85039060357623337494022115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56692706905082224996014743 85039060357623337494022115)
        ·
          refine ⟨127558590536435006241033173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85039060357623337494022115 127558590536435006241033173)
          ·
            refine ⟨2989654465697695458774215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 127558590536435006241033173 2989654465697695458774215)
            ·
              refine ⟨4484481698546543188161323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989654465697695458774215 4484481698546543188161323)
              ·
                refine ⟨6726722547819814782241985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484481698546543188161323 6726722547819814782241985)
                ·
                  refine ⟨5045041910864861086681489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6726722547819814782241985 5045041910864861086681489)
                  ·
                    refine ⟨3783781433148645815011117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045041910864861086681489 3783781433148645815011117)
                    ·
                      refine ⟨1418918037430742180629169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783781433148645815011117 1418918037430742180629169)
                      ·
                        rfl

theorem cell23_2763333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_2763333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763333 prefixEnd_2763333 := by exact prefixLift 2763333
  have htrace : WordTrace (prefixWord ++ tailWord_2763333) baseStart_2763333 baseEnd_2763333 := by
    simpa [prefixWord, tailWord_2763333, baseEnd_2763333] using wordTrace_append hprefix tailTrace_2763333
  have hstable : (prefixWord ++ tailWord_2763333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763333).length < 2 ^ (prefixWord ++ tailWord_2763333).sum := by decide
  have hdescent : baseEnd_2763333 < baseStart_2763333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763363 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2763363 : Nat := 118140960795 + 2763363 * 2 ^ 59
def prefixEnd_2763363 : Nat := 4983230072969 + 3 ^ 40 * 2763363 * 2
def baseEnd_2763363 : Nat := 1418933441850377063254031

theorem tailTrace_2763363 : CollatzResearch.WordTrace tailWord_2763363 prefixEnd_2763363 1418933441850377063254031 := by
  unfold tailWord_2763363
  simp only [CollatzResearch.WordTrace]
  refine ⟨100788128687815270672062743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67192085791876847114708495 100788128687815270672062743)
  ·
    refine ⟨151182193031722906008094115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100788128687815270672062743 151182193031722906008094115)
    ·
      refine ⟨226773289547584359012141173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151182193031722906008094115 226773289547584359012141173)
      ·
        refine ⟨21259995895086033657388235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226773289547584359012141173 21259995895086033657388235)
        ·
          refine ⟨31889993842629050486082353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21259995895086033657388235 31889993842629050486082353)
          ·
            refine ⟨23917495381971787864561765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31889993842629050486082353 23917495381971787864561765)
            ·
              refine ⟨4484530384119710224605331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23917495381971787864561765 4484530384119710224605331)
              ·
                refine ⟨6726795576179565336907997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484530384119710224605331 6726795576179565336907997)
                ·
                  refine ⟨2522548341067337001340499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6726795576179565336907997 2522548341067337001340499)
                  ·
                    refine ⟨3783822511601005502010749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522548341067337001340499 3783822511601005502010749)
                    ·
                      refine ⟨1418933441850377063254031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783822511601005502010749 1418933441850377063254031)
                      ·
                        rfl

theorem cell23_2763363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2763363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763363 prefixEnd_2763363 := by exact prefixLift 2763363
  have htrace : WordTrace (prefixWord ++ tailWord_2763363) baseStart_2763363 baseEnd_2763363 := by
    simpa [prefixWord, tailWord_2763363, baseEnd_2763363] using wordTrace_append hprefix tailTrace_2763363
  have hstable : (prefixWord ++ tailWord_2763363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763363).length < 2 ^ (prefixWord ++ tailWord_2763363).sum := by decide
  have hdescent : baseEnd_2763363 < baseStart_2763363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763373 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_2763373 : Nat := 118140960795 + 2763373 * 2 ^ 59
def prefixEnd_2763373 : Nat := 4983230072969 + 3 ^ 40 * 2763373 * 2
def baseEnd_2763373 : Nat := 1418938576656922024128985

theorem tailTrace_2763373 : CollatzResearch.WordTrace tailWord_2763373 prefixEnd_2763373 1418938576656922024128985 := by
  unfold tailWord_2763373
  simp only [CollatzResearch.WordTrace]
  refine ⟨100788493417779042379926773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67192328945186028253284515 100788493417779042379926773)
  ·
    refine ⟨9448921257916785223118135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100788493417779042379926773 9448921257916785223118135)
    ·
      refine ⟨14173381886875177834677203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9448921257916785223118135 14173381886875177834677203)
      ·
        refine ⟨21260072830312766752015805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14173381886875177834677203 21260072830312766752015805)
        ·
          refine ⟨7972527311367287532005927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21260072830312766752015805 7972527311367287532005927)
          ·
            refine ⟨11958790967050931298008891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972527311367287532005927 11958790967050931298008891)
            ·
              refine ⟨17938186450576396947013337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11958790967050931298008891 17938186450576396947013337)
              ·
                refine ⟨13453639837932297710260003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17938186450576396947013337 13453639837932297710260003)
                ·
                  refine ⟨20180459756898446565390005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13453639837932297710260003 20180459756898446565390005)
                  ·
                    refine ⟨1891918102209229365505313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20180459756898446565390005 1891918102209229365505313)
                    ·
                      refine ⟨1418938576656922024128985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1891918102209229365505313 1418938576656922024128985)
                      ·
                        rfl

theorem cell23_2763373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_2763373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763373 prefixEnd_2763373 := by exact prefixLift 2763373
  have htrace : WordTrace (prefixWord ++ tailWord_2763373) baseStart_2763373 baseEnd_2763373 := by
    simpa [prefixWord, tailWord_2763373, baseEnd_2763373] using wordTrace_append hprefix tailTrace_2763373
  have hstable : (prefixWord ++ tailWord_2763373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763373).length < 2 ^ (prefixWord ++ tailWord_2763373).sum := by decide
  have hdescent : baseEnd_2763373 < baseStart_2763373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763379 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 6]
def baseStart_2763379 : Nat := 118140960795 + 2763379 * 2 ^ 59
def prefixEnd_2763379 : Nat := 4983230072969 + 3 ^ 40 * 2763379 * 2
def baseEnd_2763379 : Nat := 472980552513616333551319

theorem tailTrace_2763379 : CollatzResearch.WordTrace tailWord_2763379 prefixEnd_2763379 472980552513616333551319 := by
  unfold tailWord_2763379
  simp only [CollatzResearch.WordTrace]
  refine ⟨100788712255757305404645191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67192474837171536936430127 100788712255757305404645191)
  ·
    refine ⟨151183068383635958106967787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100788712255757305404645191 151183068383635958106967787)
    ·
      refine ⟨226774602575453937160451681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151183068383635958106967787 226774602575453937160451681)
      ·
        refine ⟨170080951931590452870338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226774602575453937160451681 170080951931590452870338761)
        ·
          refine ⟨127560713948692839652754071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170080951931590452870338761 127560713948692839652754071)
          ·
            refine ⟨191341070923039259479131107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127560713948692839652754071 191341070923039259479131107)
            ·
              refine ⟨287011606384558889218696661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191341070923039259479131107 287011606384558889218696661)
              ·
                refine ⟨6726834524638098966063203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 287011606384558889218696661 6726834524638098966063203)
                ·
                  refine ⟨10090251786957148449094805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6726834524638098966063203 10090251786957148449094805)
                  ·
                    refine ⟨472980552513616333551319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10090251786957148449094805 472980552513616333551319)
                    ·
                      rfl

theorem cell23_2763379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_2763379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763379 prefixEnd_2763379 := by exact prefixLift 2763379
  have htrace : WordTrace (prefixWord ++ tailWord_2763379) baseStart_2763379 baseEnd_2763379 := by
    simpa [prefixWord, tailWord_2763379, baseEnd_2763379] using wordTrace_append hprefix tailTrace_2763379
  have hstable : (prefixWord ++ tailWord_2763379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763379).length < 2 ^ (prefixWord ++ tailWord_2763379).sum := by decide
  have hdescent : baseEnd_2763379 < baseStart_2763379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763397 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_2763397 : Nat := 118140960795 + 2763397 * 2 ^ 59
def prefixEnd_2763397 : Nat := 4983230072969 + 3 ^ 40 * 2763397 * 2
def baseEnd_2763397 : Nat := 1418950900192629930228875

theorem tailTrace_2763397 : CollatzResearch.WordTrace tailWord_2763397 prefixEnd_2763397 1418950900192629930228875 := by
  unfold tailWord_2763397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100789368769692094478800445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67192912513128062985866963 100789368769692094478800445)
  ·
    refine ⟨37796013288634535429550167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100789368769692094478800445 37796013288634535429550167)
    ·
      refine ⟨56694019932951803144325251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37796013288634535429550167 56694019932951803144325251)
      ·
        refine ⟨85041029899427704716487877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56694019932951803144325251 85041029899427704716487877)
        ·
          refine ⟨15945193106142694634341477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85041029899427704716487877 15945193106142694634341477)
          ·
            refine ⟨2989723707401755243939027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15945193106142694634341477 2989723707401755243939027)
            ·
              refine ⟨4484585561102632865908541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989723707401755243939027 4484585561102632865908541)
              ·
                refine ⟨1681719585413487324715703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4484585561102632865908541 1681719585413487324715703)
                ·
                  refine ⟨2522579378120230987073555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681719585413487324715703 2522579378120230987073555)
                  ·
                    refine ⟨3783869067180346480610333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522579378120230987073555 3783869067180346480610333)
                    ·
                      refine ⟨1418950900192629930228875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783869067180346480610333 1418950900192629930228875)
                      ·
                        rfl

theorem cell23_2763397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_2763397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763397 prefixEnd_2763397 := by exact prefixLift 2763397
  have htrace : WordTrace (prefixWord ++ tailWord_2763397) baseStart_2763397 baseEnd_2763397 := by
    simpa [prefixWord, tailWord_2763397, baseEnd_2763397] using wordTrace_append hprefix tailTrace_2763397
  have hstable : (prefixWord ++ tailWord_2763397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763397).length < 2 ^ (prefixWord ++ tailWord_2763397).sum := by decide
  have hdescent : baseEnd_2763397 < baseStart_2763397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763429 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2763429 : Nat := 118140960795 + 2763429 * 2 ^ 59
def prefixEnd_2763429 : Nat := 4983230072969 + 3 ^ 40 * 2763429 * 2
def baseEnd_2763429 : Nat := 1418967331573573805028727

theorem tailTrace_2763429 : CollatzResearch.WordTrace tailWord_2763429 prefixEnd_2763429 1418967331573573805028727 := by
  unfold tailWord_2763429
  simp only [CollatzResearch.WordTrace]
  refine ⟨100790535905576163943965341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67193690603717442629310227 100790535905576163943965341)
  ·
    refine ⟨37796450964591061478987003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100790535905576163943965341 37796450964591061478987003)
    ·
      refine ⟨56694676446886592218480505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37796450964591061478987003 56694676446886592218480505)
      ·
        refine ⟨42521007335164944163860379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56694676446886592218480505 42521007335164944163860379)
        ·
          refine ⟨63781511002747416245790569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42521007335164944163860379 63781511002747416245790569)
          ·
            refine ⟨47836133252060562184342927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63781511002747416245790569 47836133252060562184342927)
            ·
              refine ⟨71754199878090843276514391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47836133252060562184342927 71754199878090843276514391)
              ·
                refine ⟨107631299817136264914771587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71754199878090843276514391 107631299817136264914771587)
                ·
                  refine ⟨161446949725704397372157381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107631299817136264914771587 161446949725704397372157381)
                  ·
                    refine ⟨30271303073569574507279509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161446949725704397372157381 30271303073569574507279509)
                    ·
                      refine ⟨1418967331573573805028727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30271303073569574507279509 1418967331573573805028727)
                      ·
                        rfl

theorem cell23_2763429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2763429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763429 prefixEnd_2763429 := by exact prefixLift 2763429
  have htrace : WordTrace (prefixWord ++ tailWord_2763429) baseStart_2763429 baseEnd_2763429 := by
    simpa [prefixWord, tailWord_2763429, baseEnd_2763429] using wordTrace_append hprefix tailTrace_2763429
  have hstable : (prefixWord ++ tailWord_2763429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763429).length < 2 ^ (prefixWord ++ tailWord_2763429).sum := by decide
  have hdescent : baseEnd_2763429 < baseStart_2763429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763434 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2763434 : Nat := 118140960795 + 2763434 * 2 ^ 59
def prefixEnd_2763434 : Nat := 4983230072969 + 3 ^ 40 * 2763434 * 2
def baseEnd_2763434 : Nat := 472989966325615428488735

theorem tailTrace_2763434 : CollatzResearch.WordTrace tailWord_2763434 prefixEnd_2763434 472989966325615428488735 := by
  unfold tailWord_2763434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25197679567639512449474339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67193812180372033198598237 25197679567639512449474339)
  ·
    refine ⟨37796519351459268674211509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25197679567639512449474339 37796519351459268674211509)
    ·
      refine ⟨3543423689199306438207329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37796519351459268674211509 3543423689199306438207329)
      ·
        refine ⟨2657567766899479828655497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543423689199306438207329 2657567766899479828655497)
        ·
          refine ⟨1993175825174609871491623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657567766899479828655497 1993175825174609871491623)
          ·
            refine ⟨2989763737761914807237435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993175825174609871491623 2989763737761914807237435)
            ·
              refine ⟨4484645606642872210856153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989763737761914807237435 4484645606642872210856153)
              ·
                refine ⟨3363484204982154158142115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4484645606642872210856153 3363484204982154158142115)
                ·
                  refine ⟨5045226307473231237213173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363484204982154158142115 5045226307473231237213173)
                  ·
                    refine ⟨472989966325615428488735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5045226307473231237213173 472989966325615428488735)
                    ·
                      rfl

theorem cell23_2763434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2763434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763434 prefixEnd_2763434 := by exact prefixLift 2763434
  have htrace : WordTrace (prefixWord ++ tailWord_2763434) baseStart_2763434 baseEnd_2763434 := by
    simpa [prefixWord, tailWord_2763434, baseEnd_2763434] using wordTrace_append hprefix tailTrace_2763434
  have hstable : (prefixWord ++ tailWord_2763434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763434).length < 2 ^ (prefixWord ++ tailWord_2763434).sum := by decide
  have hdescent : baseEnd_2763434 < baseStart_2763434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763453 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2763453 : Nat := 118140960795 + 2763453 * 2 ^ 59
def prefixEnd_2763453 : Nat := 4983230072969 + 3 ^ 40 * 2763453 * 2
def baseEnd_2763453 : Nat := 1418979655109281711128617

theorem tailTrace_2763453 : CollatzResearch.WordTrace tailWord_2763453 prefixEnd_2763453 1418979655109281711128617 := by
  unfold tailWord_2763453
  simp only [CollatzResearch.WordTrace]
  refine ⟨100791411257489216042839013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67194274171659477361892675 100791411257489216042839013)
  ·
    refine ⟨18898389610779228008032315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100791411257489216042839013 18898389610779228008032315)
    ·
      refine ⟨28347584416168842012048473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18898389610779228008032315 28347584416168842012048473)
      ·
        refine ⟨21260688312126631509036355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28347584416168842012048473 21260688312126631509036355)
        ·
          refine ⟨31891032468189947263554533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21260688312126631509036355 31891032468189947263554533)
          ·
            refine ⟨5979568587785615111916475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31891032468189947263554533 5979568587785615111916475)
            ·
              refine ⟨8969352881678422667874713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979568587785615111916475 8969352881678422667874713)
              ·
                refine ⟨6727014661258817000906035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969352881678422667874713 6727014661258817000906035)
                ·
                  refine ⟨10090521991888225501359053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727014661258817000906035 10090521991888225501359053)
                  ·
                    refine ⟨3783945746958084563009645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10090521991888225501359053 3783945746958084563009645)
                    ·
                      refine ⟨1418979655109281711128617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783945746958084563009645 1418979655109281711128617)
                      ·
                        rfl

theorem cell23_2763453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2763453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763453 prefixEnd_2763453 := by exact prefixLift 2763453
  have htrace : WordTrace (prefixWord ++ tailWord_2763453) baseStart_2763453 baseEnd_2763453 := by
    simpa [prefixWord, tailWord_2763453, baseEnd_2763453] using wordTrace_append hprefix tailTrace_2763453
  have hstable : (prefixWord ++ tailWord_2763453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763453).length < 2 ^ (prefixWord ++ tailWord_2763453).sum := by decide
  have hdescent : baseEnd_2763453 < baseStart_2763453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763457 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2763457 : Nat := 118140960795 + 2763457 * 2 ^ 59
def prefixEnd_2763457 : Nat := 4983230072969 + 3 ^ 40 * 2763457 * 2
def baseEnd_2763457 : Nat := 1418981709031899695478599

theorem tailTrace_2763457 : CollatzResearch.WordTrace tailWord_2763457 prefixEnd_2763457 1418981709031899695478599 := by
  unfold tailWord_2763457
  simp only [CollatzResearch.WordTrace]
  refine ⟨100791557149474724725984625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67194371432983149817323083 100791557149474724725984625)
  ·
    refine ⟨75593667862106043544488469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100791557149474724725984625 75593667862106043544488469)
    ·
      refine ⟨3543453181036220791147897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75593667862106043544488469 3543453181036220791147897)
      ·
        refine ⟨2657589885777165593360923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543453181036220791147897 2657589885777165593360923)
        ·
          refine ⟨3986384828665748390041385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657589885777165593360923 3986384828665748390041385)
          ·
            refine ⟨2989788621499311292531039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986384828665748390041385 2989788621499311292531039)
            ·
              refine ⟨4484682932248966938796559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989788621499311292531039 4484682932248966938796559)
              ·
                refine ⟨6727024398373450408194839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484682932248966938796559 6727024398373450408194839)
                ·
                  refine ⟨10090536597560175612292259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727024398373450408194839 10090536597560175612292259)
                  ·
                    refine ⟨15135804896340263418438389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10090536597560175612292259 15135804896340263418438389)
                    ·
                      refine ⟨1418981709031899695478599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15135804896340263418438389 1418981709031899695478599)
                      ·
                        rfl

theorem cell23_2763457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2763457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763457 prefixEnd_2763457 := by exact prefixLift 2763457
  have htrace : WordTrace (prefixWord ++ tailWord_2763457) baseStart_2763457 baseEnd_2763457 := by
    simpa [prefixWord, tailWord_2763457, baseEnd_2763457] using wordTrace_append hprefix tailTrace_2763457
  have hstable : (prefixWord ++ tailWord_2763457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763457).length < 2 ^ (prefixWord ++ tailWord_2763457).sum := by decide
  have hdescent : baseEnd_2763457 < baseStart_2763457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763470 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2763470 : Nat := 118140960795 + 2763470 * 2 ^ 59
def prefixEnd_2763470 : Nat := 4983230072969 + 3 ^ 40 * 2763470 * 2
def baseEnd_2763470 : Nat := 1418988384280408144616039

theorem tailTrace_2763470 : CollatzResearch.WordTrace tailWord_2763470 prefixEnd_2763470 1418988384280408144616039 := by
  unfold tailWord_2763470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599003912303453493275983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67194687532285085297471909 12599003912303453493275983)
  ·
    refine ⟨18898505868455180239913975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599003912303453493275983 18898505868455180239913975)
    ·
      refine ⟨28347758802682770359870963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18898505868455180239913975 28347758802682770359870963)
      ·
        refine ⟨42521638204024155539806445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28347758802682770359870963 42521638204024155539806445)
        ·
          refine ⟨15945614326509058327427417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42521638204024155539806445 15945614326509058327427417)
          ·
            refine ⟨11959210744881793745570563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15945614326509058327427417 11959210744881793745570563)
            ·
              refine ⟨17938816117322690618355845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959210744881793745570563 17938816117322690618355845)
              ·
                refine ⟨3363528021998004490941721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17938816117322690618355845 3363528021998004490941721)
                ·
                  refine ⟨2522646016498503368206291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363528021998004490941721 2522646016498503368206291)
                  ·
                    refine ⟨3783969024747755052309437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522646016498503368206291 3783969024747755052309437)
                    ·
                      refine ⟨1418988384280408144616039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3783969024747755052309437 1418988384280408144616039)
                      ·
                        rfl

theorem cell23_2763470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2763470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763470 prefixEnd_2763470 := by exact prefixLift 2763470
  have htrace : WordTrace (prefixWord ++ tailWord_2763470) baseStart_2763470 baseEnd_2763470 := by
    simpa [prefixWord, tailWord_2763470, baseEnd_2763470] using wordTrace_append hprefix tailTrace_2763470
  have hstable : (prefixWord ++ tailWord_2763470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763470).length < 2 ^ (prefixWord ++ tailWord_2763470).sum := by decide
  have hdescent : baseEnd_2763470 < baseStart_2763470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763508 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2763508 : Nat := 118140960795 + 2763508 * 2 ^ 59
def prefixEnd_2763508 : Nat := 4983230072969 + 3 ^ 40 * 2763508 * 2
def baseEnd_2763508 : Nat := 1419007896545278995940865

theorem tailTrace_2763508 : CollatzResearch.WordTrace tailWord_2763508 prefixEnd_2763508 1419007896545278995940865 := by
  unfold tailWord_2763508
  simp only [CollatzResearch.WordTrace]
  refine ⟨50396708636144980218045589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67195611514859973624060785 50396708636144980218045589)
  ·
    refine ⟨2362345717319295947720887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50396708636144980218045589 2362345717319295947720887)
    ·
      refine ⟨3543518575978943921581331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362345717319295947720887 3543518575978943921581331)
      ·
        refine ⟨5315277863968415882371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543518575978943921581331 5315277863968415882371997)
        ·
          refine ⟨1993229198988155955889499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5315277863968415882371997 1993229198988155955889499)
          ·
            refine ⟨2989843798482233933834249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993229198988155955889499 2989843798482233933834249)
            ·
              refine ⟨2242382848861675450375687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989843798482233933834249 2242382848861675450375687)
              ·
                refine ⟨3363574273292513175563531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242382848861675450375687 3363574273292513175563531)
                ·
                  refine ⟨5045361409938769763345297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363574273292513175563531 5045361409938769763345297)
                  ·
                    refine ⟨3784021057454077322508973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045361409938769763345297 3784021057454077322508973)
                    ·
                      refine ⟨1419007896545278995940865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784021057454077322508973 1419007896545278995940865)
                      ·
                        rfl

theorem cell23_2763508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2763508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763508 prefixEnd_2763508 := by exact prefixLift 2763508
  have htrace : WordTrace (prefixWord ++ tailWord_2763508) baseStart_2763508 baseEnd_2763508 := by
    simpa [prefixWord, tailWord_2763508, baseEnd_2763508] using wordTrace_append hprefix tailTrace_2763508
  have hstable : (prefixWord ++ tailWord_2763508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763508).length < 2 ^ (prefixWord ++ tailWord_2763508).sum := by decide
  have hdescent : baseEnd_2763508 < baseStart_2763508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763510 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2763510 : Nat := 118140960795 + 2763510 * 2 ^ 59
def prefixEnd_2763510 : Nat := 4983230072969 + 3 ^ 40 * 2763510 * 2
def baseEnd_2763510 : Nat := 1419008923506587988115855

theorem tailTrace_2763510 : CollatzResearch.WordTrace tailWord_2763510 prefixEnd_2763510 1419008923506587988115855 := by
  unfold tailWord_2763510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299593138642669673603999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67195660145521809851775989 6299593138642669673603999)
  ·
    refine ⟨9449389707964004510405999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6299593138642669673603999 9449389707964004510405999)
    ·
      refine ⟨14174084561946006765608999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9449389707964004510405999 14174084561946006765608999)
      ·
        refine ⟨21261126842919010148413499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14174084561946006765608999 21261126842919010148413499)
        ·
          refine ⟨31891690264378515222620249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261126842919010148413499 31891690264378515222620249)
          ·
            refine ⟨23918767698283886416965187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31891690264378515222620249 23918767698283886416965187)
            ·
              refine ⟨35878151547425829625447781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23918767698283886416965187 35878151547425829625447781)
              ·
                refine ⟨6727153415142343054771459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35878151547425829625447781 6727153415142343054771459)
                ·
                  refine ⟨10090730122713514582157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727153415142343054771459 10090730122713514582157189)
                  ·
                    refine ⟨1892011898008783984154473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10090730122713514582157189 1892011898008783984154473)
                    ·
                      refine ⟨1419008923506587988115855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892011898008783984154473 1419008923506587988115855)
                      ·
                        rfl

theorem cell23_2763510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2763510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763510 prefixEnd_2763510 := by exact prefixLift 2763510
  have htrace : WordTrace (prefixWord ++ tailWord_2763510) baseStart_2763510 baseEnd_2763510 := by
    simpa [prefixWord, tailWord_2763510, baseEnd_2763510] using wordTrace_append hprefix tailTrace_2763510
  have hstable : (prefixWord ++ tailWord_2763510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763510).length < 2 ^ (prefixWord ++ tailWord_2763510).sum := by decide
  have hdescent : baseEnd_2763510 < baseStart_2763510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763527 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2763527 : Nat := 118140960795 + 2763527 * 2 ^ 59
def prefixEnd_2763527 : Nat := 4983230072969 + 3 ^ 40 * 2763527 * 2
def baseEnd_2763527 : Nat := 1419017652677714421603277

theorem tailTrace_2763527 : CollatzResearch.WordTrace tailWord_2763527 prefixEnd_2763527 1419017652677714421603277 := by
  unfold tailWord_2763527
  simp only [CollatzResearch.WordTrace]
  refine ⟨100794110259221126681032835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67196073506147417787355223 100794110259221126681032835)
  ·
    refine ⟨151191165388831690021549253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100794110259221126681032835 151191165388831690021549253)
    ·
      refine ⟨28348343510405941879040485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151191165388831690021549253 28348343510405941879040485)
      ·
        refine ⟨5315314408201114102320091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28348343510405941879040485 5315314408201114102320091)
        ·
          refine ⟨7972971612301671153480137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315314408201114102320091 7972971612301671153480137)
          ·
            refine ⟨5979728709226253365110103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972971612301671153480137 5979728709226253365110103)
            ·
              refine ⟨8969593063839380047665155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979728709226253365110103 8969593063839380047665155)
              ·
                refine ⟨13454389595759070071497733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8969593063839380047665155 13454389595759070071497733)
                ·
                  refine ⟨2522698049204825638405825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13454389595759070071497733 2522698049204825638405825)
                  ·
                    refine ⟨1892023536903619228804369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522698049204825638405825 1892023536903619228804369)
                    ·
                      refine ⟨1419017652677714421603277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892023536903619228804369 1419017652677714421603277)
                      ·
                        rfl

theorem cell23_2763527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2763527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763527 prefixEnd_2763527 := by exact prefixLift 2763527
  have htrace : WordTrace (prefixWord ++ tailWord_2763527) baseStart_2763527 baseEnd_2763527 := by
    simpa [prefixWord, tailWord_2763527, baseEnd_2763527] using wordTrace_append hprefix tailTrace_2763527
  have hstable : (prefixWord ++ tailWord_2763527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763527).length < 2 ^ (prefixWord ++ tailWord_2763527).sum := by decide
  have hdescent : baseEnd_2763527 < baseStart_2763527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763546 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_2763546 : Nat := 118140960795 + 2763546 * 2 ^ 59
def prefixEnd_2763546 : Nat := 4983230072969 + 3 ^ 40 * 2763546 * 2
def baseEnd_2763546 : Nat := 473009136270049949088563

theorem tailTrace_2763546 : CollatzResearch.WordTrace tailWord_2763546 prefixEnd_2763546 473009136270049949088563 := by
  unfold tailWord_2763546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25198700811538073231493623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67196535497434861950649661 25198700811538073231493623)
  ·
    refine ⟨37798051217307109847240435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25198700811538073231493623 37798051217307109847240435)
    ·
      refine ⟨56697076825960664770860653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37798051217307109847240435 56697076825960664770860653)
      ·
        refine ⟨21261403809735249289072745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56697076825960664770860653 21261403809735249289072745)
        ·
          refine ⟨15946052857301436966804559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21261403809735249289072745 15946052857301436966804559)
          ·
            refine ⟨23919079285952155450206839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15946052857301436966804559 23919079285952155450206839)
            ·
              refine ⟨35878618928928233175310259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23919079285952155450206839 35878618928928233175310259)
              ·
                refine ⟨53817928393392349762965389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35878618928928233175310259 53817928393392349762965389)
                ·
                  refine ⟨20181723147522131161112021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53817928393392349762965389 20181723147522131161112021)
                  ·
                    refine ⟨473009136270049949088563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20181723147522131161112021 473009136270049949088563)
                    ·
                      rfl

theorem cell23_2763546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_2763546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763546 prefixEnd_2763546 := by exact prefixLift 2763546
  have htrace : WordTrace (prefixWord ++ tailWord_2763546) baseStart_2763546 baseEnd_2763546 := by
    simpa [prefixWord, tailWord_2763546, baseEnd_2763546] using wordTrace_append hprefix tailTrace_2763546
  have hstable : (prefixWord ++ tailWord_2763546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763546).length < 2 ^ (prefixWord ++ tailWord_2763546).sum := by decide
  have hdescent : baseEnd_2763546 < baseStart_2763546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763583 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_2763583 : Nat := 118140960795 + 2763583 * 2 ^ 59
def prefixEnd_2763583 : Nat := 4983230072969 + 3 ^ 40 * 2763583 * 2
def baseEnd_2763583 : Nat := 1419046407594366202503019

theorem tailTrace_2763583 : CollatzResearch.WordTrace tailWord_2763583 prefixEnd_2763583 1419046407594366202503019 := by
  unfold tailWord_2763583
  simp only [CollatzResearch.WordTrace]
  refine ⟨100796152747018248245071403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67197435164678832163380935 100796152747018248245071403)
  ·
    refine ⟨151194229120527372367607105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100796152747018248245071403 151194229120527372367607105)
    ·
      refine ⟨113395671840395529275705329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151194229120527372367607105 113395671840395529275705329)
      ·
        refine ⟨85046753880296646956778997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113395671840395529275705329 85046753880296646956778997)
        ·
          refine ⟨7973133176277810652198031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85046753880296646956778997 7973133176277810652198031)
          ·
            refine ⟨11959699764416715978297047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973133176277810652198031 11959699764416715978297047)
            ·
              refine ⟨17939549646625073967445571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959699764416715978297047 17939549646625073967445571)
              ·
                refine ⟨26909324469937610951168357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17939549646625073967445571 26909324469937610951168357)
                ·
                  refine ⟨5045498338113302053344067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26909324469937610951168357 5045498338113302053344067)
                  ·
                    refine ⟨7568247507169953080016101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045498338113302053344067 7568247507169953080016101)
                    ·
                      refine ⟨1419046407594366202503019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7568247507169953080016101 1419046407594366202503019)
                      ·
                        rfl

theorem cell23_2763583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_2763583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763583 prefixEnd_2763583 := by exact prefixLift 2763583
  have htrace : WordTrace (prefixWord ++ tailWord_2763583) baseStart_2763583 baseEnd_2763583 := by
    simpa [prefixWord, tailWord_2763583, baseEnd_2763583] using wordTrace_append hprefix tailTrace_2763583
  have hstable : (prefixWord ++ tailWord_2763583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763583).length < 2 ^ (prefixWord ++ tailWord_2763583).sum := by decide
  have hdescent : baseEnd_2763583 < baseStart_2763583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763620 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_2763620 : Nat := 118140960795 + 2763620 * 2 ^ 59
def prefixEnd_2763620 : Nat := 4983230072969 + 3 ^ 40 * 2763620 * 2
def baseEnd_2763620 : Nat := 1419065406378582557740349

theorem tailTrace_2763620 : CollatzResearch.WordTrace tailWord_2763620 prefixEnd_2763620 1419065406378582557740349 := by
  unfold tailWord_2763620
  simp only [CollatzResearch.WordTrace]
  refine ⟨50398751123942101782084157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67198334831922802376112209 50398751123942101782084157)
  ·
    refine ⟨18899531671478288168281559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50398751123942101782084157 18899531671478288168281559)
    ·
      refine ⟨28349297507217432252422339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18899531671478288168281559 28349297507217432252422339)
      ·
        refine ⟨42523946260826148378633509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28349297507217432252422339 42523946260826148378633509)
        ·
          refine ⟨7973239923904902820993783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42523946260826148378633509 7973239923904902820993783)
          ·
            refine ⟨11959859885857354231490675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973239923904902820993783 11959859885857354231490675)
            ·
              refine ⟨17939789828786031347236013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959859885857354231490675 17939789828786031347236013)
              ·
                refine ⟨6727421185794761755213505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17939789828786031347236013 6727421185794761755213505)
                ·
                  refine ⟨5045565889346071316410129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727421185794761755213505 5045565889346071316410129)
                  ·
                    refine ⟨3784174417009553487307597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045565889346071316410129 3784174417009553487307597)
                    ·
                      refine ⟨1419065406378582557740349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784174417009553487307597 1419065406378582557740349)
                      ·
                        rfl

theorem cell23_2763620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_2763620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763620 prefixEnd_2763620 := by exact prefixLift 2763620
  have htrace : WordTrace (prefixWord ++ tailWord_2763620) baseStart_2763620 baseEnd_2763620 := by
    simpa [prefixWord, tailWord_2763620, baseEnd_2763620] using wordTrace_append hprefix tailTrace_2763620
  have hstable : (prefixWord ++ tailWord_2763620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763620).length < 2 ^ (prefixWord ++ tailWord_2763620).sum := by decide
  have hdescent : baseEnd_2763620 < baseStart_2763620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763653 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2763653 : Nat := 118140960795 + 2763653 * 2 ^ 59
def prefixEnd_2763653 : Nat := 4983230072969 + 3 ^ 40 * 2763653 * 2
def baseEnd_2763653 : Nat := 473027450413393642875899

theorem tailTrace_2763653 : CollatzResearch.WordTrace tailWord_2763653 prefixEnd_2763653 473027450413393642875899 := by
  unfold tailWord_2763653
  simp only [CollatzResearch.WordTrace]
  refine ⟨100798705856764650200119613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67199137237843100133413075 100798705856764650200119613)
  ·
    refine ⟨37799514696286743825044855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100798705856764650200119613 37799514696286743825044855)
    ·
      refine ⟨56699272044430115737567283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37799514696286743825044855 56699272044430115737567283)
      ·
        refine ⟨85048908066645173606350925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56699272044430115737567283 85048908066645173606350925)
        ·
          refine ⟨31893340524991940102381597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85048908066645173606350925 31893340524991940102381597)
          ·
            refine ⟨11960002696871977538393099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31893340524991940102381597 11960002696871977538393099)
            ·
              refine ⟨17940004045307966307589649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960002696871977538393099 17940004045307966307589649)
              ·
                refine ⟨13455003033980974730692237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17940004045307966307589649 13455003033980974730692237)
                ·
                  refine ⟨5045626137742865524009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13455003033980974730692237 5045626137742865524009589)
                  ·
                    refine ⟨473027450413393642875899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5045626137742865524009589 473027450413393642875899)
                    ·
                      rfl

theorem cell23_2763653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2763653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763653 prefixEnd_2763653 := by exact prefixLift 2763653
  have htrace : WordTrace (prefixWord ++ tailWord_2763653) baseStart_2763653 baseEnd_2763653 := by
    simpa [prefixWord, tailWord_2763653, baseEnd_2763653] using wordTrace_append hprefix tailTrace_2763653
  have hstable : (prefixWord ++ tailWord_2763653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763653).length < 2 ^ (prefixWord ++ tailWord_2763653).sum := by decide
  have hdescent : baseEnd_2763653 < baseStart_2763653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763660 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_2763660 : Nat := 118140960795 + 2763660 * 2 ^ 59
def prefixEnd_2763660 : Nat := 4983230072969 + 3 ^ 40 * 2763660 * 2
def baseEnd_2763660 : Nat := 1419085945604762401240165

theorem tailTrace_2763660 : CollatzResearch.WordTrace tailWord_2763660 prefixEnd_2763660 1419085945604762401240165 := by
  unfold tailWord_2763660
  simp only [CollatzResearch.WordTrace]
  refine ⟨50399480583869645197812217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67199307445159526930416289 50399480583869645197812217)
  ·
    refine ⟨37799610437902233898359163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50399480583869645197812217 37799610437902233898359163)
    ·
      refine ⟨56699415656853350847538745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37799610437902233898359163 56699415656853350847538745)
      ·
        refine ⟨42524561742640013135654059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56699415656853350847538745 42524561742640013135654059)
        ·
          refine ⟨63786842613960019703481089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42524561742640013135654059 63786842613960019703481089)
          ·
            refine ⟨47840131960470014777610817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63786842613960019703481089 47840131960470014777610817)
            ·
              refine ⟨35880098970352511083208113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47840131960470014777610817 35880098970352511083208113)
              ·
                refine ⟨26910074227764383312406085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35880098970352511083208113 26910074227764383312406085)
                ·
                  refine ⟨5045638917705821871076141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26910074227764383312406085 5045638917705821871076141)
                  ·
                    refine ⟨1892114594139683201653553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5045638917705821871076141 1892114594139683201653553)
                    ·
                      refine ⟨1419085945604762401240165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892114594139683201653553 1419085945604762401240165)
                      ·
                        rfl

theorem cell23_2763660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_2763660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763660 prefixEnd_2763660 := by exact prefixLift 2763660
  have htrace : WordTrace (prefixWord ++ tailWord_2763660) baseStart_2763660 baseEnd_2763660 := by
    simpa [prefixWord, tailWord_2763660, baseEnd_2763660] using wordTrace_append hprefix tailTrace_2763660
  have hstable : (prefixWord ++ tailWord_2763660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763660).length < 2 ^ (prefixWord ++ tailWord_2763660).sum := by decide
  have hdescent : baseEnd_2763660 < baseStart_2763660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763683 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 6]
def baseStart_2763683 : Nat := 118140960795 + 2763683 * 2 ^ 59
def prefixEnd_2763683 : Nat := 4983230072969 + 3 ^ 40 * 2763683 * 2
def baseEnd_2763683 : Nat := 473032585219938603750853

theorem tailTrace_2763683 : CollatzResearch.WordTrace tailWord_2763683 prefixEnd_2763683 473032585219938603750853 := by
  unfold tailWord_2763683
  simp only [CollatzResearch.WordTrace]
  refine ⟨100799800046655965323711703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67199866697770643549141135 100799800046655965323711703)
  ·
    refine ⟨151199700069983947985567555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100799800046655965323711703 151199700069983947985567555)
    ·
      refine ⟨226799550104975921978351333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151199700069983947985567555 226799550104975921978351333)
      ·
        refine ⟨42524915644682985370940875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226799550104975921978351333 42524915644682985370940875)
        ·
          refine ⟨63787373467024478056411313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42524915644682985370940875 63787373467024478056411313)
          ·
            refine ⟨47840530100268358542308485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63787373467024478056411313 47840530100268358542308485)
            ·
              refine ⟨8970099393800317226682841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47840530100268358542308485 8970099393800317226682841)
              ·
                refine ⟨6727574545350237920012131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8970099393800317226682841 6727574545350237920012131)
                ·
                  refine ⟨10091361818025356880018197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727574545350237920012131 10091361818025356880018197)
                  ·
                    refine ⟨473032585219938603750853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10091361818025356880018197 473032585219938603750853)
                    ·
                      rfl

theorem cell23_2763683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_2763683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763683 prefixEnd_2763683 := by exact prefixLift 2763683
  have htrace : WordTrace (prefixWord ++ tailWord_2763683) baseStart_2763683 baseEnd_2763683 := by
    simpa [prefixWord, tailWord_2763683, baseEnd_2763683] using wordTrace_append hprefix tailTrace_2763683
  have hstable : (prefixWord ++ tailWord_2763683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763683).length < 2 ^ (prefixWord ++ tailWord_2763683).sum := by decide
  have hdescent : baseEnd_2763683 < baseStart_2763683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763684 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_2763684 : Nat := 118140960795 + 2763684 * 2 ^ 59
def prefixEnd_2763684 : Nat := 4983230072969 + 3 ^ 40 * 2763684 * 2
def baseEnd_2763684 : Nat := 1419098269140470307340055

theorem tailTrace_2763684 : CollatzResearch.WordTrace tailWord_2763684 prefixEnd_2763684 1419098269140470307340055 := by
  unfold tailWord_2763684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50399918259826171247249053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67199891013101561662998737 50399918259826171247249053)
  ·
    refine ⟨18899969347434814217718395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50399918259826171247249053 18899969347434814217718395)
    ·
      refine ⟨28349954021152221326577593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18899969347434814217718395 28349954021152221326577593)
      ·
        refine ⟨21262465515864165994933195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28349954021152221326577593 21262465515864165994933195)
        ·
          refine ⟨31893698273796248992399793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21262465515864165994933195 31893698273796248992399793)
          ·
            refine ⟨23920273705347186744299845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31893698273796248992399793 23920273705347186744299845)
            ·
              refine ⟨4485051319752597514556221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23920273705347186744299845 4485051319752597514556221)
              ·
                refine ⟨1681894244907224067958583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4485051319752597514556221 1681894244907224067958583)
                ·
                  refine ⟨2522841367360836101937875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681894244907224067958583 2522841367360836101937875)
                  ·
                    refine ⟨3784262051041254152906813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522841367360836101937875 3784262051041254152906813)
                    ·
                      refine ⟨1419098269140470307340055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784262051041254152906813 1419098269140470307340055)
                      ·
                        rfl

theorem cell23_2763684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_2763684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763684 prefixEnd_2763684 := by exact prefixLift 2763684
  have htrace : WordTrace (prefixWord ++ tailWord_2763684) baseStart_2763684 baseEnd_2763684 := by
    simpa [prefixWord, tailWord_2763684, baseEnd_2763684] using wordTrace_append hprefix tailTrace_2763684
  have hstable : (prefixWord ++ tailWord_2763684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763684).length < 2 ^ (prefixWord ++ tailWord_2763684).sum := by decide
  have hdescent : baseEnd_2763684 < baseStart_2763684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763687 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2763687 : Nat := 118140960795 + 2763687 * 2 ^ 59
def prefixEnd_2763687 : Nat := 4983230072969 + 3 ^ 40 * 2763687 * 2
def baseEnd_2763687 : Nat := 473033269860811265200847

theorem tailTrace_2763687 : CollatzResearch.WordTrace tailWord_2763687 prefixEnd_2763687 473033269860811265200847 := by
  unfold tailWord_2763687
  simp only [CollatzResearch.WordTrace]
  refine ⟨100799945938641474006857315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67199963959094316004571543 100799945938641474006857315)
  ·
    refine ⟨151199918907962211010285973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100799945938641474006857315 151199918907962211010285973)
    ·
      refine ⟨7087496198810728641107155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151199918907962211010285973 7087496198810728641107155)
      ·
        refine ⟨10631244298216092961660733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087496198810728641107155 10631244298216092961660733)
        ·
          refine ⟨3986716611831034860622775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10631244298216092961660733 3986716611831034860622775)
          ·
            refine ⟨5980074917746552290934163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986716611831034860622775 5980074917746552290934163)
            ·
              refine ⟨8970112376619828436401245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980074917746552290934163 8970112376619828436401245)
              ·
                refine ⟨3363792141232435663650467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8970112376619828436401245 3363792141232435663650467)
                ·
                  refine ⟨5045688211848653495475701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363792141232435663650467 5045688211848653495475701)
                  ·
                    refine ⟨473033269860811265200847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5045688211848653495475701 473033269860811265200847)
                    ·
                      rfl

theorem cell23_2763687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2763687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763687 prefixEnd_2763687 := by exact prefixLift 2763687
  have htrace : WordTrace (prefixWord ++ tailWord_2763687) baseStart_2763687 baseEnd_2763687 := by
    simpa [prefixWord, tailWord_2763687, baseEnd_2763687] using wordTrace_append hprefix tailTrace_2763687
  have hstable : (prefixWord ++ tailWord_2763687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763687).length < 2 ^ (prefixWord ++ tailWord_2763687).sum := by decide
  have hdescent : baseEnd_2763687 < baseStart_2763687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763703 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_2763703 : Nat := 118140960795 + 2763703 * 2 ^ 59
def prefixEnd_2763703 : Nat := 4983230072969 + 3 ^ 40 * 2763703 * 2
def baseEnd_2763703 : Nat := 1419108025272905733002467

theorem tailTrace_2763703 : CollatzResearch.WordTrace tailWord_2763703 prefixEnd_2763703 1419108025272905733002467 := by
  unfold tailWord_2763703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100800529506583508739439763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67200353004389005826293175 100800529506583508739439763)
  ·
    refine ⟨151200794259875263109159645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100800529506583508739439763 151200794259875263109159645)
    ·
      refine ⟨56700297847453223665934867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151200794259875263109159645 56700297847453223665934867)
      ·
        refine ⟨85050446771179835498902301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56700297847453223665934867 85050446771179835498902301)
        ·
          refine ⟨31893917539192438312088363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85050446771179835498902301 31893917539192438312088363)
          ·
            refine ⟨47840876308788657468132545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31893917539192438312088363 47840876308788657468132545)
            ·
              refine ⟨35880657231591493101099409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47840876308788657468132545 35880657231591493101099409)
              ·
                refine ⟨26910492923693619825824557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35880657231591493101099409 26910492923693619825824557)
                ·
                  refine ⟨10091434846385107434684209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26910492923693619825824557 10091434846385107434684209)
                  ·
                    refine ⟨7568576134788830576013157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10091434846385107434684209 7568576134788830576013157)
                    ·
                      refine ⟨1419108025272905733002467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7568576134788830576013157 1419108025272905733002467)
                      ·
                        rfl

theorem cell23_2763703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_2763703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763703 prefixEnd_2763703 := by exact prefixLift 2763703
  have htrace : WordTrace (prefixWord ++ tailWord_2763703) baseStart_2763703 baseEnd_2763703 := by
    simpa [prefixWord, tailWord_2763703, baseEnd_2763703] using wordTrace_append hprefix tailTrace_2763703
  have hstable : (prefixWord ++ tailWord_2763703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763703).length < 2 ^ (prefixWord ++ tailWord_2763703).sum := by decide
  have hdescent : baseEnd_2763703 < baseStart_2763703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763710 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2763710 : Nat := 118140960795 + 2763710 * 2 ^ 59
def prefixEnd_2763710 : Nat := 4983230072969 + 3 ^ 40 * 2763710 * 2
def baseEnd_2763710 : Nat := 1419111619637487205614935

theorem tailTrace_2763710 : CollatzResearch.WordTrace tailWord_2763710 prefixEnd_2763710 1419111619637487205614935 := by
  unfold tailWord_2763710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600098102194768616868073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67200523211705432623296389 12600098102194768616868073)
  ·
    refine ⟨9450073576646076462651055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600098102194768616868073 9450073576646076462651055)
    ·
      refine ⟨14175110364969114693976583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450073576646076462651055 14175110364969114693976583)
      ·
        refine ⟨21262665547453672040964875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14175110364969114693976583 21262665547453672040964875)
        ·
          refine ⟨31893998321180508061447313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21262665547453672040964875 31893998321180508061447313)
          ·
            refine ⟨23920498740885381046085485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31893998321180508061447313 23920498740885381046085485)
            ·
              refine ⟨8970187027832017892282057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23920498740885381046085485 8970187027832017892282057)
              ·
                refine ⟨6727640270874013419211543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8970187027832017892282057 6727640270874013419211543)
                ·
                  refine ⟨10091460406311020128817315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727640270874013419211543 10091460406311020128817315)
                  ·
                    refine ⟨15137190609466530193225973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10091460406311020128817315 15137190609466530193225973)
                    ·
                      refine ⟨1419111619637487205614935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15137190609466530193225973 1419111619637487205614935)
                      ·
                        rfl

theorem cell23_2763710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2763710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763710 prefixEnd_2763710 := by exact prefixLift 2763710
  have htrace : WordTrace (prefixWord ++ tailWord_2763710) baseStart_2763710 baseEnd_2763710 := by
    simpa [prefixWord, tailWord_2763710, baseEnd_2763710] using wordTrace_append hprefix tailTrace_2763710
  have hstable : (prefixWord ++ tailWord_2763710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763710).length < 2 ^ (prefixWord ++ tailWord_2763710).sum := by decide
  have hdescent : baseEnd_2763710 < baseStart_2763710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763720 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2763720 : Nat := 118140960795 + 2763720 * 2 ^ 59
def prefixEnd_2763720 : Nat := 4983230072969 + 3 ^ 40 * 2763720 * 2
def baseEnd_2763720 : Nat := 1419116754444032166489889

theorem tailTrace_2763720 : CollatzResearch.WordTrace tailWord_2763720 prefixEnd_2763720 1419116754444032166489889 := by
  unfold tailWord_2763720
  simp only [CollatzResearch.WordTrace]
  refine ⟨50400574773760960321404307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67200766365014613761872409 50400574773760960321404307)
  ·
    refine ⟨75600862160641440482106461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50400574773760960321404307 75600862160641440482106461)
    ·
      refine ⟨28350323310240540180789923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75600862160641440482106461 28350323310240540180789923)
      ·
        refine ⟨42525484965360810271184885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28350323310240540180789923 42525484965360810271184885)
        ·
          refine ⟨3986764215502575962923583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42525484965360810271184885 3986764215502575962923583)
          ·
            refine ⟨5980146323253863944385375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986764215502575962923583 5980146323253863944385375)
            ·
              refine ⟨8970219484880795916578063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980146323253863944385375 8970219484880795916578063)
              ·
                refine ⟨13455329227321193874867095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970219484880795916578063 13455329227321193874867095)
                ·
                  refine ⟨20182993840981790812300643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13455329227321193874867095 20182993840981790812300643)
                  ·
                    refine ⟨30274490761472686218450965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20182993840981790812300643 30274490761472686218450965)
                    ·
                      refine ⟨1419116754444032166489889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30274490761472686218450965 1419116754444032166489889)
                      ·
                        rfl

theorem cell23_2763720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2763720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763720 prefixEnd_2763720 := by exact prefixLift 2763720
  have htrace : WordTrace (prefixWord ++ tailWord_2763720) baseStart_2763720 baseEnd_2763720 := by
    simpa [prefixWord, tailWord_2763720, baseEnd_2763720] using wordTrace_append hprefix tailTrace_2763720
  have hstable : (prefixWord ++ tailWord_2763720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763720).length < 2 ^ (prefixWord ++ tailWord_2763720).sum := by decide
  have hdescent : baseEnd_2763720 < baseStart_2763720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763727 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_2763727 : Nat := 118140960795 + 2763727 * 2 ^ 59
def prefixEnd_2763727 : Nat := 4983230072969 + 3 ^ 40 * 2763727 * 2
def baseEnd_2763727 : Nat := 1419120348808613639102357

theorem tailTrace_2763727 : CollatzResearch.WordTrace tailWord_2763727 prefixEnd_2763727 1419120348808613639102357 := by
  unfold tailWord_2763727
  simp only [CollatzResearch.WordTrace]
  refine ⟨100801404858496560838313435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67200936572331040558875623 100801404858496560838313435)
  ·
    refine ⟨151202107287744841257470153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100801404858496560838313435 151202107287744841257470153)
    ·
      refine ⟨113401580465808630943102615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151202107287744841257470153 113401580465808630943102615)
      ·
        refine ⟨170102370698712946414653923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113401580465808630943102615 170102370698712946414653923)
        ·
          refine ⟨255153556048069419621980885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170102370698712946414653923 255153556048069419621980885)
          ·
            refine ⟨5980161469876627022390177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 255153556048069419621980885 5980161469876627022390177)
            ·
              refine ⟨4485121102407470266792633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5980161469876627022390177 4485121102407470266792633)
              ·
                refine ⟨3363840826805602700094475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485121102407470266792633 3363840826805602700094475)
                ·
                  refine ⟨5045761240208404050141713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363840826805602700094475 5045761240208404050141713)
                  ·
                    refine ⟨3784320930156303037606285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045761240208404050141713 3784320930156303037606285)
                    ·
                      refine ⟨1419120348808613639102357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784320930156303037606285 1419120348808613639102357)
                      ·
                        rfl

theorem cell23_2763727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_2763727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763727 prefixEnd_2763727 := by exact prefixLift 2763727
  have htrace : WordTrace (prefixWord ++ tailWord_2763727) baseStart_2763727 baseEnd_2763727 := by
    simpa [prefixWord, tailWord_2763727, baseEnd_2763727] using wordTrace_append hprefix tailTrace_2763727
  have hstable : (prefixWord ++ tailWord_2763727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763727).length < 2 ^ (prefixWord ++ tailWord_2763727).sum := by decide
  have hdescent : baseEnd_2763727 < baseStart_2763727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763730 : List Nat := [3, 2, 2, 3, 1, 2, 1, 9]
def baseStart_2763730 : Nat := 118140960795 + 2763730 * 2 ^ 59
def prefixEnd_2763730 : Nat := 4983230072969 + 3 ^ 40 * 2763730 * 2
def baseEnd_2763730 : Nat := 52560069972243597309809

theorem tailTrace_2763730 : CollatzResearch.WordTrace tailWord_2763730 prefixEnd_2763730 52560069972243597309809 := by
  unfold tailWord_2763730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25200378569371423087668161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67201009518323794900448429 25200378569371423087668161)
  ·
    refine ⟨18900283927028567315751121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25200378569371423087668161 18900283927028567315751121)
    ·
      refine ⟨14175212945271425486813341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18900283927028567315751121 14175212945271425486813341)
      ·
        refine ⟨5315704854476784557555003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14175212945271425486813341 5315704854476784557555003)
        ·
          refine ⟨7973557281715176836332505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315704854476784557555003 7973557281715176836332505)
          ·
            refine ⟨5980167961286382627249379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7973557281715176836332505 5980167961286382627249379)
            ·
              refine ⟨8970251941929573940874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980167961286382627249379 8970251941929573940874069)
              ·
                refine ⟨52560069972243597309809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8970251941929573940874069 52560069972243597309809)
                ·
                  rfl

theorem cell23_2763730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_2763730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763730 prefixEnd_2763730 := by exact prefixLift 2763730
  have htrace : WordTrace (prefixWord ++ tailWord_2763730) baseStart_2763730 baseEnd_2763730 := by
    simpa [prefixWord, tailWord_2763730, baseEnd_2763730] using wordTrace_append hprefix tailTrace_2763730
  have hstable : (prefixWord ++ tailWord_2763730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763730).length < 2 ^ (prefixWord ++ tailWord_2763730).sum := by decide
  have hdescent : baseEnd_2763730 < baseStart_2763730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763758 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_2763758 : Nat := 118140960795 + 2763758 * 2 ^ 59
def prefixEnd_2763758 : Nat := 4983230072969 + 3 ^ 40 * 2763758 * 2
def baseEnd_2763758 : Nat := 1419136266708903017814715

theorem tailTrace_2763758 : CollatzResearch.WordTrace tailWord_2763758 prefixEnd_2763758 1419136266708903017814715 := by
  unfold tailWord_2763758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600316940173031641586491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67201690347589502088461285 12600316940173031641586491)
  ·
    refine ⟨18900475410259547462379737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12600316940173031641586491 18900475410259547462379737)
    ·
      refine ⟨14175356557694660596784803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18900475410259547462379737 14175356557694660596784803)
      ·
        refine ⟨21263034836541990895177205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14175356557694660596784803 21263034836541990895177205)
        ·
          refine ⟨1993409515925811646422863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21263034836541990895177205 1993409515925811646422863)
          ·
            refine ⟨2990114273888717469634295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993409515925811646422863 2990114273888717469634295)
            ·
              refine ⟨4485171410833076204451443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990114273888717469634295 4485171410833076204451443)
              ·
                refine ⟨6727757116249614306677165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485171410833076204451443 6727757116249614306677165)
                ·
                  refine ⟨2522908918593605365003937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6727757116249614306677165 2522908918593605365003937)
                  ·
                    refine ⟨1892181688945204023752953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522908918593605365003937 1892181688945204023752953)
                    ·
                      refine ⟨1419136266708903017814715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892181688945204023752953 1419136266708903017814715)
                      ·
                        rfl

theorem cell23_2763758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_2763758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763758 prefixEnd_2763758 := by exact prefixLift 2763758
  have htrace : WordTrace (prefixWord ++ tailWord_2763758) baseStart_2763758 baseEnd_2763758 := by
    simpa [prefixWord, tailWord_2763758, baseEnd_2763758] using wordTrace_append hprefix tailTrace_2763758
  have hstable : (prefixWord ++ tailWord_2763758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763758).length < 2 ^ (prefixWord ++ tailWord_2763758).sum := by decide
  have hdescent : baseEnd_2763758 < baseStart_2763758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763773 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2763773 : Nat := 118140960795 + 2763773 * 2 ^ 59
def prefixEnd_2763773 : Nat := 4983230072969 + 3 ^ 40 * 2763773 * 2
def baseEnd_2763773 : Nat := 473047989639573486375715

theorem tailTrace_2763773 : CollatzResearch.WordTrace tailWord_2763773 prefixEnd_2763773 473047989639573486375715 := by
  unfold tailWord_2763773
  simp only [CollatzResearch.WordTrace]
  refine ⟨100803082616329910694487973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67202055077553273796325315 100803082616329910694487973)
  ·
    refine ⟨18900577990561858255216495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100803082616329910694487973 18900577990561858255216495)
    ·
      refine ⟨28350866985842787382824743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18900577990561858255216495 28350866985842787382824743)
      ·
        refine ⟨42526300478764181074237115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28350866985842787382824743 42526300478764181074237115)
        ·
          refine ⟨63789450718146271611355673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42526300478764181074237115 63789450718146271611355673)
          ·
            refine ⟨47842088038609703708516755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63789450718146271611355673 47842088038609703708516755)
            ·
              refine ⟨71763132057914555562775133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47842088038609703708516755 71763132057914555562775133)
              ·
                refine ⟨26911174521717958336040675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71763132057914555562775133 26911174521717958336040675)
                ·
                  refine ⟨40366761782576937504061013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26911174521717958336040675 40366761782576937504061013)
                  ·
                    refine ⟨473047989639573486375715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40366761782576937504061013 473047989639573486375715)
                    ·
                      rfl

theorem cell23_2763773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2763773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763773 prefixEnd_2763773 := by exact prefixLift 2763773
  have htrace : WordTrace (prefixWord ++ tailWord_2763773) baseStart_2763773 baseEnd_2763773 := by
    simpa [prefixWord, tailWord_2763773, baseEnd_2763773] using wordTrace_append hprefix tailTrace_2763773
  have hstable : (prefixWord ++ tailWord_2763773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763773).length < 2 ^ (prefixWord ++ tailWord_2763773).sum := by decide
  have hdescent : baseEnd_2763773 < baseStart_2763773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763778 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2763778 : Nat := 118140960795 + 2763778 * 2 ^ 59
def prefixEnd_2763778 : Nat := 4983230072969 + 3 ^ 40 * 2763778 * 2
def baseEnd_2763778 : Nat := 1419146536321992939564623

theorem tailTrace_2763778 : CollatzResearch.WordTrace tailWord_2763778 prefixEnd_2763778 1419146536321992939564623 := by
  unfold tailWord_2763778
  simp only [CollatzResearch.WordTrace]
  refine ⟨25200816245327949137104997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67202176654207864365613325 25200816245327949137104997)
  ·
    refine ⟨4725153045998990463207187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25200816245327949137104997 4725153045998990463207187)
    ·
      refine ⟨7087729568998485694810781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4725153045998990463207187 7087729568998485694810781)
      ·
        refine ⟨2657898588374432135554043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7087729568998485694810781 2657898588374432135554043)
        ·
          refine ⟨3986847882561648203331065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657898588374432135554043 3986847882561648203331065)
          ·
            refine ⟨2990135911921236152498299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986847882561648203331065 2990135911921236152498299)
            ·
              refine ⟨4485203867881854228747449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990135911921236152498299 4485203867881854228747449)
              ·
                refine ⟨3363902900911390671560587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485203867881854228747449 3363902900911390671560587)
                ·
                  refine ⟨5045854351367086007340881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363902900911390671560587 5045854351367086007340881)
                  ·
                    refine ⟨3784390763525314505505661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045854351367086007340881 3784390763525314505505661)
                    ·
                      refine ⟨1419146536321992939564623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784390763525314505505661 1419146536321992939564623)
                      ·
                        rfl

theorem cell23_2763778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2763778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763778 prefixEnd_2763778 := by exact prefixLift 2763778
  have htrace : WordTrace (prefixWord ++ tailWord_2763778) baseStart_2763778 baseEnd_2763778 := by
    simpa [prefixWord, tailWord_2763778, baseEnd_2763778] using wordTrace_append hprefix tailTrace_2763778
  have hstable : (prefixWord ++ tailWord_2763778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763778).length < 2 ^ (prefixWord ++ tailWord_2763778).sum := by decide
  have hdescent : baseEnd_2763778 < baseStart_2763778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763784 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_2763784 : Nat := 118140960795 + 2763784 * 2 ^ 59
def prefixEnd_2763784 : Nat := 4983230072969 + 3 ^ 40 * 2763784 * 2
def baseEnd_2763784 : Nat := 1419149617205919916089595

theorem tailTrace_2763784 : CollatzResearch.WordTrace tailWord_2763784 prefixEnd_2763784 1419149617205919916089595 := by
  unfold tailWord_2763784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50401741909645029786569203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67202322546193373048758937 50401741909645029786569203)
  ·
    refine ⟨75602612864467544679853805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50401741909645029786569203 75602612864467544679853805)
    ·
      refine ⟨28350979824175329254945177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75602612864467544679853805 28350979824175329254945177)
      ·
        refine ⟨21263234868131496941208883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28350979824175329254945177 21263234868131496941208883)
        ·
          refine ⟨31894852302197245411813325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21263234868131496941208883 31894852302197245411813325)
          ·
            refine ⟨11960569613323967029429997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31894852302197245411813325 11960569613323967029429997)
            ·
              refine ⟨4485213604996487636036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11960569613323967029429997 4485213604996487636036249)
              ·
                refine ⟨3363910203747365727027187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485213604996487636036249 3363910203747365727027187)
                ·
                  refine ⟨5045865305621048590540781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363910203747365727027187 5045865305621048590540781)
                  ·
                    refine ⟨1892199489607893221452793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5045865305621048590540781 1892199489607893221452793)
                    ·
                      refine ⟨1419149617205919916089595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892199489607893221452793 1419149617205919916089595)
                      ·
                        rfl

theorem cell23_2763784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_2763784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763784 prefixEnd_2763784 := by exact prefixLift 2763784
  have htrace : WordTrace (prefixWord ++ tailWord_2763784) baseStart_2763784 baseEnd_2763784 := by
    simpa [prefixWord, tailWord_2763784, baseEnd_2763784] using wordTrace_append hprefix tailTrace_2763784
  have hstable : (prefixWord ++ tailWord_2763784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763784).length < 2 ^ (prefixWord ++ tailWord_2763784).sum := by decide
  have hdescent : baseEnd_2763784 < baseStart_2763784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763797 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_2763797 : Nat := 118140960795 + 2763797 * 2 ^ 59
def prefixEnd_2763797 : Nat := 4983230072969 + 3 ^ 40 * 2763797 * 2
def baseEnd_2763797 : Nat := 1419156292454428365227035

theorem tailTrace_2763797 : CollatzResearch.WordTrace tailWord_2763797 prefixEnd_2763797 1419156292454428365227035 := by
  unfold tailWord_2763797
  simp only [CollatzResearch.WordTrace]
  refine ⟨100803957968242962793361645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67202638645495308528907763 100803957968242962793361645)
  ·
    refine ⟨37801484238091111047510617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100803957968242962793361645 37801484238091111047510617)
    ·
      refine ⟨28351113178568333285632963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37801484238091111047510617 28351113178568333285632963)
      ·
        refine ⟨42526669767852499928449445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28351113178568333285632963 42526669767852499928449445)
        ·
          refine ⟨7973750581472343736584271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42526669767852499928449445 7973750581472343736584271)
          ·
            refine ⟨11960625872208515604876407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973750581472343736584271 11960625872208515604876407)
            ·
              refine ⟨17940938808312773407314611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960625872208515604876407 17940938808312773407314611)
              ·
                refine ⟨26911408212469160110971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17940938808312773407314611 26911408212469160110971917)
                ·
                  refine ⟨10091778079675935041614469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26911408212469160110971917 10091778079675935041614469)
                  ·
                    refine ⟨1892208389939237820302713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10091778079675935041614469 1892208389939237820302713)
                    ·
                      refine ⟨1419156292454428365227035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892208389939237820302713 1419156292454428365227035)
                      ·
                        rfl

theorem cell23_2763797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_2763797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763797 prefixEnd_2763797 := by exact prefixLift 2763797
  have htrace : WordTrace (prefixWord ++ tailWord_2763797) baseStart_2763797 baseEnd_2763797 := by
    simpa [prefixWord, tailWord_2763797, baseEnd_2763797] using wordTrace_append hprefix tailTrace_2763797
  have hstable : (prefixWord ++ tailWord_2763797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763797).length < 2 ^ (prefixWord ++ tailWord_2763797).sum := by decide
  have hdescent : baseEnd_2763797 < baseStart_2763797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763800 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2763800 : Nat := 118140960795 + 2763800 * 2 ^ 59
def prefixEnd_2763800 : Nat := 4983230072969 + 3 ^ 40 * 2763800 * 2
def baseEnd_2763800 : Nat := 1419157832896391853489521

theorem tailTrace_2763800 : CollatzResearch.WordTrace tailWord_2763800 prefixEnd_2763800 1419157832896391853489521 := by
  unfold tailWord_2763800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50402033693616047152860427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67202711591488062870480569 50402033693616047152860427)
  ·
    refine ⟨75603050540424070729290641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50402033693616047152860427 75603050540424070729290641)
    ·
      refine ⟨56702287905318053046967981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75603050540424070729290641 56702287905318053046967981)
      ·
        refine ⟨21263357964494269892612993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56702287905318053046967981 21263357964494269892612993)
        ·
          refine ⟨15947518473370702419459745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21263357964494269892612993 15947518473370702419459745)
          ·
            refine ⟨11960638855028026814594809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15947518473370702419459745 11960638855028026814594809)
            ·
              refine ⟨8970479141271020110946107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11960638855028026814594809 8970479141271020110946107)
              ·
                refine ⟨13455718711906530166419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970479141271020110946107 13455718711906530166419161)
                ·
                  refine ⟨10091789033929897624814371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13455718711906530166419161 10091789033929897624814371)
                  ·
                    refine ⟨15137683550894846437221557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10091789033929897624814371 15137683550894846437221557)
                    ·
                      refine ⟨1419157832896391853489521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15137683550894846437221557 1419157832896391853489521)
                      ·
                        rfl

theorem cell23_2763800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2763800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763800 prefixEnd_2763800 := by exact prefixLift 2763800
  have htrace : WordTrace (prefixWord ++ tailWord_2763800) baseStart_2763800 baseEnd_2763800 := by
    simpa [prefixWord, tailWord_2763800, baseEnd_2763800] using wordTrace_append hprefix tailTrace_2763800
  have hstable : (prefixWord ++ tailWord_2763800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763800).length < 2 ^ (prefixWord ++ tailWord_2763800).sum := by decide
  have hdescent : baseEnd_2763800 < baseStart_2763800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763860 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2763860 : Nat := 118140960795 + 2763860 * 2 ^ 59
def prefixEnd_2763860 : Nat := 4983230072969 + 3 ^ 40 * 2763860 * 2
def baseEnd_2763860 : Nat := 1419188641735661618739245

theorem tailTrace_2763860 : CollatzResearch.WordTrace tailWord_2763860 prefixEnd_2763860 1419188641735661618739245 := by
  unfold tailWord_2763860
  simp only [CollatzResearch.WordTrace]
  refine ⟨50403127883507362276452517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67204170511343149701936689 50403127883507362276452517)
  ·
    refine ⟨9450586478157630426834847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50403127883507362276452517 9450586478157630426834847)
    ·
      refine ⟨14175879717236445640252271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450586478157630426834847 14175879717236445640252271)
      ·
        refine ⟨21263819575854668460378407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14175879717236445640252271 21263819575854668460378407)
        ·
          refine ⟨31895729363782002690567611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21263819575854668460378407 31895729363782002690567611)
          ·
            refine ⟨47843594045673004035851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31895729363782002690567611 47843594045673004035851417)
            ·
              refine ⟨35882695534254753026888563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47843594045673004035851417 35882695534254753026888563)
              ·
                refine ⟨53824043301382129540332845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35882695534254753026888563 53824043301382129540332845)
                ·
                  refine ⟨20184016238018298577624817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53824043301382129540332845 20184016238018298577624817)
                  ·
                    refine ⟨15138012178513723933218613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20184016238018298577624817 15138012178513723933218613)
                    ·
                      refine ⟨1419188641735661618739245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15138012178513723933218613 1419188641735661618739245)
                      ·
                        rfl

theorem cell23_2763860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2763860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763860 prefixEnd_2763860 := by exact prefixLift 2763860
  have htrace : WordTrace (prefixWord ++ tailWord_2763860) baseStart_2763860 baseEnd_2763860 := by
    simpa [prefixWord, tailWord_2763860, baseEnd_2763860] using wordTrace_append hprefix tailTrace_2763860
  have hstable : (prefixWord ++ tailWord_2763860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763860).length < 2 ^ (prefixWord ++ tailWord_2763860).sum := by decide
  have hdescent : baseEnd_2763860 < baseStart_2763860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763887 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 4, 2]
def baseStart_2763887 : Nat := 118140960795 + 2763887 * 2 ^ 59
def prefixEnd_2763887 : Nat := 4983230072969 + 3 ^ 40 * 2763887 * 2
def baseEnd_2763887 : Nat := 1419202505713333013101621

theorem tailTrace_2763887 : CollatzResearch.WordTrace tailWord_2763887 prefixEnd_2763887 1419202505713333013101621 := by
  unfold tailWord_2763887
  simp only [CollatzResearch.WordTrace]
  refine ⟨100807240537916908164137915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67204827025277938776091943 100807240537916908164137915)
  ·
    refine ⟨151210860806875362246206873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100807240537916908164137915 151210860806875362246206873)
    ·
      refine ⟨113408145605156521684655155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151210860806875362246206873 113408145605156521684655155)
      ·
        refine ⟨170112218407734782526982733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113408145605156521684655155 170112218407734782526982733)
        ·
          refine ⟨63792081902900543447618525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170112218407734782526982733 63792081902900543447618525)
          ·
            refine ⟨23922030713587703792856947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63792081902900543447618525 23922030713587703792856947)
            ·
              refine ⟨35883046070381555689285421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23922030713587703792856947 35883046070381555689285421)
              ·
                refine ⟨13456142276393083383482033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35883046070381555689285421 13456142276393083383482033)
                ·
                  refine ⟨10092106707294812537611525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13456142276393083383482033 10092106707294812537611525)
                  ·
                    refine ⟨1892270007617777350802161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10092106707294812537611525 1892270007617777350802161)
                    ·
                      refine ⟨1419202505713333013101621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892270007617777350802161 1419202505713333013101621)
                      ·
                        rfl

theorem cell23_2763887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4, 2].length) (baseStart_2763887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763887 prefixEnd_2763887 := by exact prefixLift 2763887
  have htrace : WordTrace (prefixWord ++ tailWord_2763887) baseStart_2763887 baseEnd_2763887 := by
    simpa [prefixWord, tailWord_2763887, baseEnd_2763887] using wordTrace_append hprefix tailTrace_2763887
  have hstable : (prefixWord ++ tailWord_2763887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763887).length < 2 ^ (prefixWord ++ tailWord_2763887).sum := by decide
  have hdescent : baseEnd_2763887 < baseStart_2763887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763900 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2763900 : Nat := 118140960795 + 2763900 * 2 ^ 59
def prefixEnd_2763900 : Nat := 4983230072969 + 3 ^ 40 * 2763900 * 2
def baseEnd_2763900 : Nat := 1419209180961841462239061

theorem tailTrace_2763900 : CollatzResearch.WordTrace tailWord_2763900 prefixEnd_2763900 1419209180961841462239061 := by
  unfold tailWord_2763900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50403857343434905692180577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67205143124579874256240769 50403857343434905692180577)
  ·
    refine ⟨37802893007576179269135433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50403857343434905692180577 37802893007576179269135433)
    ·
      refine ⟨28352169755682134451851575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37802893007576179269135433 28352169755682134451851575)
      ·
        refine ⟨42528254633523201677777363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28352169755682134451851575 42528254633523201677777363)
        ·
          refine ⟨63792381950284802516666045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42528254633523201677777363 63792381950284802516666045)
          ·
            refine ⟨23922143231356800943749767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63792381950284802516666045 23922143231356800943749767)
            ·
              refine ⟨35883214847035201415624651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23922143231356800943749767 35883214847035201415624651)
              ·
                refine ⟨53824822270552802123436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35883214847035201415624651 53824822270552802123436977)
                ·
                  refine ⟨40368616702914601592577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53824822270552802123436977 40368616702914601592577733)
                  ·
                    refine ⟨7569115631796487798608325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40368616702914601592577733 7569115631796487798608325)
                    ·
                      refine ⟨1419209180961841462239061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7569115631796487798608325 1419209180961841462239061)
                      ·
                        rfl

theorem cell23_2763900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2763900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763900 prefixEnd_2763900 := by exact prefixLift 2763900
  have htrace : WordTrace (prefixWord ++ tailWord_2763900) baseStart_2763900 baseEnd_2763900 := by
    simpa [prefixWord, tailWord_2763900, baseEnd_2763900] using wordTrace_append hprefix tailTrace_2763900
  have hstable : (prefixWord ++ tailWord_2763900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763900).length < 2 ^ (prefixWord ++ tailWord_2763900).sum := by decide
  have hdescent : baseEnd_2763900 < baseStart_2763900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763907 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3]
def baseStart_2763907 : Nat := 118140960795 + 2763907 * 2 ^ 59
def prefixEnd_2763907 : Nat := 4983230072969 + 3 ^ 40 * 2763907 * 2
def baseEnd_2763907 : Nat := 1419212775326422934851529

theorem tailTrace_2763907 : CollatzResearch.WordTrace tailWord_2763907 prefixEnd_2763907 1419212775326422934851529 := by
  unfold tailWord_2763907
  simp only [CollatzResearch.WordTrace]
  refine ⟨100807969997844451579865975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67205313331896301053243983 100807969997844451579865975)
  ·
    refine ⟨151211954996766677369798963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100807969997844451579865975 151211954996766677369798963)
    ·
      refine ⟨226817932495150016054698445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151211954996766677369798963 226817932495150016054698445)
      ·
        refine ⟨85056724685681256020511917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226817932495150016054698445 85056724685681256020511917)
        ·
          refine ⟨31896271757130471007691969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85056724685681256020511917 31896271757130471007691969)
          ·
            refine ⟨23922203817847853255768977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31896271757130471007691969 23922203817847853255768977)
            ·
              refine ⟨17941652863385889941826733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23922203817847853255768977 17941652863385889941826733)
              ·
                refine ⟨6728119823769708728185025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17941652863385889941826733 6728119823769708728185025)
                ·
                  refine ⟨5046089867827281546138769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728119823769708728185025 5046089867827281546138769)
                  ·
                    refine ⟨3784567400870461159604077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046089867827281546138769 3784567400870461159604077)
                    ·
                      refine ⟨1419212775326422934851529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784567400870461159604077 1419212775326422934851529)
                      ·
                        rfl

theorem cell23_2763907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_2763907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763907 prefixEnd_2763907 := by exact prefixLift 2763907
  have htrace : WordTrace (prefixWord ++ tailWord_2763907) baseStart_2763907 baseEnd_2763907 := by
    simpa [prefixWord, tailWord_2763907, baseEnd_2763907] using wordTrace_append hprefix tailTrace_2763907
  have hstable : (prefixWord ++ tailWord_2763907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763907).length < 2 ^ (prefixWord ++ tailWord_2763907).sum := by decide
  have hdescent : baseEnd_2763907 < baseStart_2763907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763977 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 6, 2]
def baseStart_2763977 : Nat := 118140960795 + 2763977 * 2 ^ 59
def prefixEnd_2763977 : Nat := 4983230072969 + 3 ^ 40 * 2763977 * 2
def baseEnd_2763977 : Nat := 1419248718972237660976207

theorem tailTrace_2763977 : CollatzResearch.WordTrace tailWord_2763977 prefixEnd_2763977 1419248718972237660976207 := by
  unfold tailWord_2763977
  simp only [CollatzResearch.WordTrace]
  refine ⟨100810523107590853534914185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67207015405060569023276123 100810523107590853534914185)
  ·
    refine ⟨75607892330693140151185639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100810523107590853534914185 75607892330693140151185639)
    ·
      refine ⟨113411838496039710226778459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75607892330693140151185639 113411838496039710226778459)
      ·
        refine ⟨170117757744059565340167689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113411838496039710226778459 170117757744059565340167689)
        ·
          refine ⟨127588318308044674005125767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170117757744059565340167689 127588318308044674005125767)
          ·
            refine ⟨191382477462067011007688651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127588318308044674005125767 191382477462067011007688651)
            ·
              refine ⟨287073716193100516511532977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191382477462067011007688651 287073716193100516511532977)
              ·
                refine ⟨215305287144825387383649733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287073716193100516511532977 215305287144825387383649733)
                ·
                  refine ⟨40369741339654760134434325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215305287144825387383649733 40369741339654760134434325)
                  ·
                    refine ⟨1892331625296316881301609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40369741339654760134434325 1892331625296316881301609)
                    ·
                      refine ⟨1419248718972237660976207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892331625296316881301609 1419248718972237660976207)
                      ·
                        rfl

theorem cell23_2763977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6, 2].length) (baseStart_2763977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2763977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2763977 prefixEnd_2763977 := by exact prefixLift 2763977
  have htrace : WordTrace (prefixWord ++ tailWord_2763977) baseStart_2763977 baseEnd_2763977 := by
    simpa [prefixWord, tailWord_2763977, baseEnd_2763977] using wordTrace_append hprefix tailTrace_2763977
  have hstable : (prefixWord ++ tailWord_2763977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763977).length < 2 ^ (prefixWord ++ tailWord_2763977).sum := by decide
  have hdescent : baseEnd_2763977 < baseStart_2763977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764004 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2764004 : Nat := 118140960795 + 2764004 * 2 ^ 59
def prefixEnd_2764004 : Nat := 4983230072969 + 3 ^ 40 * 2764004 * 2
def baseEnd_2764004 : Nat := 473087527649969685112861

theorem tailTrace_2764004 : CollatzResearch.WordTrace tailWord_2764004 prefixEnd_2764004 473087527649969685112861 := by
  unfold tailWord_2764004
  simp only [CollatzResearch.WordTrace]
  refine ⟨50405753939246518573073533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67207671918995358097431377 50405753939246518573073533)
  ·
    refine ⟨18902157727217444464902575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50405753939246518573073533 18902157727217444464902575)
    ·
      refine ⟨28353236590826166697353863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18902157727217444464902575 28353236590826166697353863)
      ·
        refine ⟨42529854886239250046030795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28353236590826166697353863 42529854886239250046030795)
        ·
          refine ⟨63794782329358875069046193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42529854886239250046030795 63794782329358875069046193)
          ·
            refine ⟨47846086747019156301784645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63794782329358875069046193 47846086747019156301784645)
            ·
              refine ⟨8971141265066091806584621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47846086747019156301784645 8971141265066091806584621)
              ·
                refine ⟨3364177974399784427469233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8971141265066091806584621 3364177974399784427469233)
                ·
                  refine ⟨2523133480799838320601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3364177974399784427469233 2523133480799838320601925)
                  ·
                    refine ⟨473087527649969685112861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2523133480799838320601925 473087527649969685112861)
                    ·
                      rfl

theorem cell23_2764004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2764004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764004 prefixEnd_2764004 := by exact prefixLift 2764004
  have htrace : WordTrace (prefixWord ++ tailWord_2764004) baseStart_2764004 baseEnd_2764004 := by
    simpa [prefixWord, tailWord_2764004, baseEnd_2764004] using wordTrace_append hprefix tailTrace_2764004
  have hstable : (prefixWord ++ tailWord_2764004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764004).length < 2 ^ (prefixWord ++ tailWord_2764004).sum := by decide
  have hdescent : baseEnd_2764004 < baseStart_2764004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764011 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 3, 2, 2]
def baseStart_2764011 : Nat := 118140960795 + 2764011 * 2 ^ 59
def prefixEnd_2764011 : Nat := 4983230072969 + 3 ^ 40 * 2764011 * 2
def baseEnd_2764011 : Nat := 1419266177314490527951051

theorem tailTrace_2764011 : CollatzResearch.WordTrace tailWord_2764011 prefixEnd_2764011 1419266177314490527951051 := by
  unfold tailWord_2764011
  simp only [CollatzResearch.WordTrace]
  refine ⟨100811763189467677341651887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67207842126311784894434591 100811763189467677341651887)
  ·
    refine ⟨151217644784201516012477831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100811763189467677341651887 151217644784201516012477831)
    ·
      refine ⟨226826467176302274018716747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151217644784201516012477831 226826467176302274018716747)
      ·
        refine ⟨340239700764453411028075121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226826467176302274018716747 340239700764453411028075121)
        ·
          refine ⟨255179775573340058271056341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340239700764453411028075121 255179775573340058271056341)
          ·
            refine ⟨5980775990000157615727883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 255179775573340058271056341 5980775990000157615727883)
            ·
              refine ⟨8971163985000236423591825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980775990000157615727883 8971163985000236423591825)
              ·
                refine ⟨6728372988750177317693869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8971163985000236423591825 6728372988750177317693869)
                ·
                  refine ⟨2523139870781316494135201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6728372988750177317693869 2523139870781316494135201)
                  ·
                    refine ⟨1892354903085987370601401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2523139870781316494135201 1892354903085987370601401)
                    ·
                      refine ⟨1419266177314490527951051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892354903085987370601401 1419266177314490527951051)
                      ·
                        rfl

theorem cell23_2764011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2, 2].length) (baseStart_2764011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764011 prefixEnd_2764011 := by exact prefixLift 2764011
  have htrace : WordTrace (prefixWord ++ tailWord_2764011) baseStart_2764011 baseEnd_2764011 := by
    simpa [prefixWord, tailWord_2764011, baseEnd_2764011] using wordTrace_append hprefix tailTrace_2764011
  have hstable : (prefixWord ++ tailWord_2764011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764011).length < 2 ^ (prefixWord ++ tailWord_2764011).sum := by decide
  have hdescent : baseEnd_2764011 < baseStart_2764011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764014 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2764014 : Nat := 118140960795 + 2764014 * 2 ^ 59
def prefixEnd_2764014 : Nat := 4983230072969 + 3 ^ 40 * 2764014 * 2
def baseEnd_2764014 : Nat := 1419267717756454016213537

theorem tailTrace_2764014 : CollatzResearch.WordTrace tailWord_2764014 prefixEnd_2764014 1419267717756454016213537 := by
  unfold tailWord_2764014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12601484076057101106751387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67207915072304539236007397 12601484076057101106751387)
  ·
    refine ⟨18902226114085651660127081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12601484076057101106751387 18902226114085651660127081)
    ·
      refine ⟨14176669585564238745095311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18902226114085651660127081 14176669585564238745095311)
      ·
        refine ⟨21265004378346358117642967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176669585564238745095311 21265004378346358117642967)
        ·
          refine ⟨31897506567519537176464451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21265004378346358117642967 31897506567519537176464451)
          ·
            refine ⟨47846259851279305764696677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31897506567519537176464451 47846259851279305764696677)
            ·
              refine ⟨8971173722114869830880627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47846259851279305764696677 8971173722114869830880627)
              ·
                refine ⟨13456760583172304746320941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971173722114869830880627 13456760583172304746320941)
                ·
                  refine ⟨5046285218689614279870353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13456760583172304746320941 5046285218689614279870353)
                  ·
                    refine ⟨3784713914017210709902765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046285218689614279870353 3784713914017210709902765)
                    ·
                      refine ⟨1419267717756454016213537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784713914017210709902765 1419267717756454016213537)
                      ·
                        rfl

theorem cell23_2764014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2764014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764014 prefixEnd_2764014 := by exact prefixLift 2764014
  have htrace : WordTrace (prefixWord ++ tailWord_2764014) baseStart_2764014 baseEnd_2764014 := by
    simpa [prefixWord, tailWord_2764014, baseEnd_2764014] using wordTrace_append hprefix tailTrace_2764014
  have hstable : (prefixWord ++ tailWord_2764014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764014).length < 2 ^ (prefixWord ++ tailWord_2764014).sum := by decide
  have hdescent : baseEnd_2764014 < baseStart_2764014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764028 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_2764028 : Nat := 118140960795 + 2764028 * 2 ^ 59
def prefixEnd_2764028 : Nat := 4983230072969 + 3 ^ 40 * 2764028 * 2
def baseEnd_2764028 : Nat := 1419274906485616961438473

theorem tailTrace_2764028 : CollatzResearch.WordTrace tailWord_2764028 prefixEnd_2764028 1419274906485616961438473 := by
  unfold tailWord_2764028
  simp only [CollatzResearch.WordTrace]
  refine ⟨50406191615203044622510369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67208255486937392830013825 50406191615203044622510369)
  ·
    refine ⟨37804643711402283466882777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50406191615203044622510369 37804643711402283466882777)
    ·
      refine ⟨28353482783551712600162083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37804643711402283466882777 28353482783551712600162083)
      ·
        refine ⟨42530224175327568900243125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28353482783551712600162083 42530224175327568900243125)
        ·
          refine ⟨3987208516436959584397793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42530224175327568900243125 3987208516436959584397793)
          ·
            refine ⟨2990406387327719688298345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3987208516436959584397793 2990406387327719688298345)
            ·
              refine ⟨2242804790495789766223759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990406387327719688298345 2242804790495789766223759)
              ·
                refine ⟨3364207185743684649335639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242804790495789766223759 3364207185743684649335639)
                ·
                  refine ⟨5046310778615526974003459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364207185743684649335639 5046310778615526974003459)
                  ·
                    refine ⟨7569466167923290461005189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046310778615526974003459 7569466167923290461005189)
                    ·
                      refine ⟨1419274906485616961438473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7569466167923290461005189 1419274906485616961438473)
                      ·
                        rfl

theorem cell23_2764028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_2764028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764028 prefixEnd_2764028 := by exact prefixLift 2764028
  have htrace : WordTrace (prefixWord ++ tailWord_2764028) baseStart_2764028 baseEnd_2764028 := by
    simpa [prefixWord, tailWord_2764028, baseEnd_2764028] using wordTrace_append hprefix tailTrace_2764028
  have hstable : (prefixWord ++ tailWord_2764028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764028).length < 2 ^ (prefixWord ++ tailWord_2764028).sum := by decide
  have hdescent : baseEnd_2764028 < baseStart_2764028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764031 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 1, 2, 3]
def baseStart_2764031 : Nat := 118140960795 + 2764031 * 2 ^ 59
def prefixEnd_2764031 : Nat := 4983230072969 + 3 ^ 40 * 2764031 * 2
def baseEnd_2764031 : Nat := 1419276446927580449700959

theorem tailTrace_2764031 : CollatzResearch.WordTrace tailWord_2764031 prefixEnd_2764031 1419276446927580449700959 := by
  unfold tailWord_2764031
  simp only [CollatzResearch.WordTrace]
  refine ⟨100812492649395220757379947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67208328432930147171586631 100812492649395220757379947)
  ·
    refine ⟨151218738974092831136069921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100812492649395220757379947 151218738974092831136069921)
    ·
      refine ⟨113414054230569623352052441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151218738974092831136069921 113414054230569623352052441)
      ·
        refine ⟨85060540672927217514039331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113414054230569623352052441 85060540672927217514039331)
        ·
          refine ⟨127590811009390826271058997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85060540672927217514039331 127590811009390826271058997)
          ·
            refine ⟨11961638532130389962911781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127590811009390826271058997 11961638532130389962911781)
            ·
              refine ⟨2242807224774448118045959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11961638532130389962911781 2242807224774448118045959)
              ·
                refine ⟨3364210837161672177068939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242807224774448118045959 3364210837161672177068939)
                ·
                  refine ⟨5046316255742508265603409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364210837161672177068939 5046316255742508265603409)
                  ·
                    refine ⟨3784737191806881199202557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046316255742508265603409 3784737191806881199202557)
                    ·
                      refine ⟨1419276446927580449700959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784737191806881199202557 1419276446927580449700959)
                      ·
                        rfl

theorem cell23_2764031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_2764031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764031 prefixEnd_2764031 := by exact prefixLift 2764031
  have htrace : WordTrace (prefixWord ++ tailWord_2764031) baseStart_2764031 baseEnd_2764031 := by
    simpa [prefixWord, tailWord_2764031, baseEnd_2764031] using wordTrace_append hprefix tailTrace_2764031
  have hstable : (prefixWord ++ tailWord_2764031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764031).length < 2 ^ (prefixWord ++ tailWord_2764031).sum := by decide
  have hdescent : baseEnd_2764031 < baseStart_2764031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764034 : List Nat := [3, 4, 1, 1, 3, 1, 10]
def baseStart_2764034 : Nat := 118140960795 + 2764034 * 2 ^ 59
def prefixEnd_2764034 : Nat := 4983230072969 + 3 ^ 40 * 2764034 * 2
def baseEnd_2764034 : Nat := 17521950461352394295845

theorem tailTrace_2764034 : CollatzResearch.WordTrace tailWord_2764034 prefixEnd_2764034 17521950461352394295845 := by
  unfold tailWord_2764034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203150517096088067434789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67208401378922901513159437 25203150517096088067434789)
  ·
    refine ⟨4725590721955516512644023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25203150517096088067434789 4725590721955516512644023)
    ·
      refine ⟨7088386082933274768966035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4725590721955516512644023 7088386082933274768966035)
      ·
        refine ⟨10632579124399912153449053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7088386082933274768966035 10632579124399912153449053)
        ·
          refine ⟨3987217171649967057543395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10632579124399912153449053 3987217171649967057543395)
          ·
            refine ⟨5980825757474950586315093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987217171649967057543395 5980825757474950586315093)
            ·
              refine ⟨17521950461352394295845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5980825757474950586315093 17521950461352394295845)
              ·
                rfl

theorem cell23_2764034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 10].length) (baseStart_2764034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764034 prefixEnd_2764034 := by exact prefixLift 2764034
  have htrace : WordTrace (prefixWord ++ tailWord_2764034) baseStart_2764034 baseEnd_2764034 := by
    simpa [prefixWord, tailWord_2764034, baseEnd_2764034] using wordTrace_append hprefix tailTrace_2764034
  have hstable : (prefixWord ++ tailWord_2764034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764034).length < 2 ^ (prefixWord ++ tailWord_2764034).sum := by decide
  have hdescent : baseEnd_2764034 < baseStart_2764034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764061 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2764061 : Nat := 118140960795 + 2764061 * 2 ^ 59
def prefixEnd_2764061 : Nat := 4983230072969 + 3 ^ 40 * 2764061 * 2
def baseEnd_2764061 : Nat := 1419291851347215332325821

theorem tailTrace_2764061 : CollatzResearch.WordTrace tailWord_2764061 prefixEnd_2764061 1419291851347215332325821 := by
  unfold tailWord_2764061
  simp only [CollatzResearch.WordTrace]
  refine ⟨100813586839286535880972037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67209057892857690587314691 100813586839286535880972037)
  ·
    refine ⟨18902547532366225477682257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100813586839286535880972037 18902547532366225477682257)
    ·
      refine ⟨14176910649274669108261693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18902547532366225477682257 14176910649274669108261693)
      ·
        refine ⟨5316341493478000915598135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14176910649274669108261693 5316341493478000915598135)
        ·
          refine ⟨7974512240217001373397203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316341493478000915598135 7974512240217001373397203)
          ·
            refine ⟨11961768360325502060095805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974512240217001373397203 11961768360325502060095805)
            ·
              refine ⟨4485663135122063272535927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11961768360325502060095805 4485663135122063272535927)
              ·
                refine ⟨6728494702683094908803891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485663135122063272535927 6728494702683094908803891)
                ·
                  refine ⟨10092742054024642363205837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6728494702683094908803891 10092742054024642363205837)
                  ·
                    refine ⟨3784778270259240886202189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10092742054024642363205837 3784778270259240886202189)
                    ·
                      refine ⟨1419291851347215332325821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784778270259240886202189 1419291851347215332325821)
                      ·
                        rfl

theorem cell23_2764061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2764061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764061 prefixEnd_2764061 := by exact prefixLift 2764061
  have htrace : WordTrace (prefixWord ++ tailWord_2764061) baseStart_2764061 baseEnd_2764061 := by
    simpa [prefixWord, tailWord_2764061, baseEnd_2764061] using wordTrace_append hprefix tailTrace_2764061
  have hstable : (prefixWord ++ tailWord_2764061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764061).length < 2 ^ (prefixWord ++ tailWord_2764061).sum := by decide
  have hdescent : baseEnd_2764061 < baseStart_2764061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764074 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2764074 : Nat := 118140960795 + 2764074 * 2 ^ 59
def prefixEnd_2764074 : Nat := 4983230072969 + 3 ^ 40 * 2764074 * 2
def baseEnd_2764074 : Nat := 1419298526595723781463261

theorem tailTrace_2764074 : CollatzResearch.WordTrace tailWord_2764074 prefixEnd_2764074 1419298526595723781463261 := by
  unfold tailWord_2764074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203515247059859775298819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67209373992159626067463517 25203515247059859775298819)
  ·
    refine ⟨37805272870589789662948229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25203515247059859775298819 37805272870589789662948229)
    ·
      refine ⟨7088488663235585561802793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37805272870589789662948229 7088488663235585561802793)
      ·
        refine ⟨5316366497426689171352095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7088488663235585561802793 5316366497426689171352095)
        ·
          refine ⟨7974549746140033757028143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316366497426689171352095 7974549746140033757028143)
          ·
            refine ⟨11961824619210050635542215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974549746140033757028143 11961824619210050635542215)
            ·
              refine ⟨17942736928815075953313323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11961824619210050635542215 17942736928815075953313323)
              ·
                refine ⟨26914105393222613929969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17942736928815075953313323 26914105393222613929969985)
                ·
                  refine ⟨20185579044916960447477489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26914105393222613929969985 20185579044916960447477489)
                  ·
                    refine ⟨15139184283687720335608117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20185579044916960447477489 15139184283687720335608117)
                    ·
                      refine ⟨1419298526595723781463261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15139184283687720335608117 1419298526595723781463261)
                      ·
                        rfl

theorem cell23_2764074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2764074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764074 prefixEnd_2764074 := by exact prefixLift 2764074
  have htrace : WordTrace (prefixWord ++ tailWord_2764074) baseStart_2764074 baseEnd_2764074 := by
    simpa [prefixWord, tailWord_2764074, baseEnd_2764074] using wordTrace_append hprefix tailTrace_2764074
  have hstable : (prefixWord ++ tailWord_2764074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764074).length < 2 ^ (prefixWord ++ tailWord_2764074).sum := by decide
  have hdescent : baseEnd_2764074 < baseStart_2764074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764087 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_2764087 : Nat := 118140960795 + 2764087 * 2 ^ 59
def prefixEnd_2764087 : Nat := 4983230072969 + 3 ^ 40 * 2764087 * 2
def baseEnd_2764087 : Nat := 1419305201844232230600701

theorem tailTrace_2764087 : CollatzResearch.WordTrace tailWord_2764087 prefixEnd_2764087 1419305201844232230600701 := by
  unfold tailWord_2764087
  simp only [CollatzResearch.WordTrace]
  refine ⟨100814535137192342321418515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67209690091461561547612343 100814535137192342321418515)
  ·
    refine ⟨151221802705788513482127773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100814535137192342321418515 151221802705788513482127773)
    ·
      refine ⟨56708176014670692555797915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151221802705788513482127773 56708176014670692555797915)
      ·
        refine ⟨85062264022006038833696873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56708176014670692555797915 85062264022006038833696873)
        ·
          refine ⟨63796698016504529125272655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85062264022006038833696873 63796698016504529125272655)
          ·
            refine ⟨95695047024756793687908983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63796698016504529125272655 95695047024756793687908983)
            ·
              refine ⟨143542570537135190531863475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95695047024756793687908983 143542570537135190531863475)
              ·
                refine ⟨215313855805702785797795213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143542570537135190531863475 215313855805702785797795213)
                ·
                  refine ⟨80742695927138544674173205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215313855805702785797795213 80742695927138544674173205)
                  ·
                    refine ⟨3784813871584619281601869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80742695927138544674173205 3784813871584619281601869)
                    ·
                      refine ⟨1419305201844232230600701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3784813871584619281601869 1419305201844232230600701)
                      ·
                        rfl

theorem cell23_2764087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_2764087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764087 prefixEnd_2764087 := by exact prefixLift 2764087
  have htrace : WordTrace (prefixWord ++ tailWord_2764087) baseStart_2764087 baseEnd_2764087 := by
    simpa [prefixWord, tailWord_2764087, baseEnd_2764087] using wordTrace_append hprefix tailTrace_2764087
  have hstable : (prefixWord ++ tailWord_2764087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764087).length < 2 ^ (prefixWord ++ tailWord_2764087).sum := by decide
  have hdescent : baseEnd_2764087 < baseStart_2764087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764164 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2764164 : Nat := 118140960795 + 2764164 * 2 ^ 59
def prefixEnd_2764164 : Nat := 4983230072969 + 3 ^ 40 * 2764164 * 2
def baseEnd_2764164 : Nat := 1419344739854628429337847

theorem tailTrace_2764164 : CollatzResearch.WordTrace tailWord_2764164 prefixEnd_2764164 1419344739854628429337847 := by
  unfold tailWord_2764164
  simp only [CollatzResearch.WordTrace]
  refine ⟨50408671778956692235985773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67211562371942256314647697 50408671778956692235985773)
  ·
    refine ⟨18903251917108759588494665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50408671778956692235985773 18903251917108759588494665)
    ·
      refine ⟨14177438937831569691370999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18903251917108759588494665 14177438937831569691370999)
      ·
        refine ⟨21266158406747354537056499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14177438937831569691370999 21266158406747354537056499)
        ·
          refine ⟨31899237610121031805584749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21266158406747354537056499 31899237610121031805584749)
          ·
            refine ⟨11962214103795386927094281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31899237610121031805584749 11962214103795386927094281)
            ·
              refine ⟨8971660577846540195320711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11962214103795386927094281 8971660577846540195320711)
              ·
                refine ⟨13457490866769810292981067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971660577846540195320711 13457490866769810292981067)
                ·
                  refine ⟨20186236300154715439471601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13457490866769810292981067 20186236300154715439471601)
                  ·
                    refine ⟨15139677225116036579603701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20186236300154715439471601 15139677225116036579603701)
                    ·
                      refine ⟨1419344739854628429337847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15139677225116036579603701 1419344739854628429337847)
                      ·
                        rfl

theorem cell23_2764164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2764164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764164 prefixEnd_2764164 := by exact prefixLift 2764164
  have htrace : WordTrace (prefixWord ++ tailWord_2764164) baseStart_2764164 baseEnd_2764164 := by
    simpa [prefixWord, tailWord_2764164, baseEnd_2764164] using wordTrace_append hprefix tailTrace_2764164
  have hstable : (prefixWord ++ tailWord_2764164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764164).length < 2 ^ (prefixWord ++ tailWord_2764164).sum := by decide
  have hdescent : baseEnd_2764164 < baseStart_2764164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764177 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2764177 : Nat := 118140960795 + 2764177 * 2 ^ 59
def prefixEnd_2764177 : Nat := 4983230072969 + 3 ^ 40 * 2764177 * 2
def baseEnd_2764177 : Nat := 1419351415103136878475287

theorem tailTrace_2764177 : CollatzResearch.WordTrace tailWord_2764177 prefixEnd_2764177 1419351415103136878475287 := by
  unfold tailWord_2764177
  simp only [CollatzResearch.WordTrace]
  refine ⟨100817817706866287692194785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67211878471244191794796523 100817817706866287692194785)
  ·
    refine ⟨75613363280149715769146089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100817817706866287692194785 75613363280149715769146089)
    ·
      refine ⟨56710022460112286826859567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75613363280149715769146089 56710022460112286826859567)
      ·
        refine ⟨85065033690168430240289351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56710022460112286826859567 85065033690168430240289351)
        ·
          refine ⟨127597550535252645360434027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85065033690168430240289351 127597550535252645360434027)
          ·
            refine ⟨191396325802878968040651041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127597550535252645360434027 191396325802878968040651041)
            ·
              refine ⟨143547244352159226030488281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191396325802878968040651041 143547244352159226030488281)
              ·
                refine ⟨107660433264119419522866211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143547244352159226030488281 107660433264119419522866211)
                ·
                  refine ⟨161490649896179129284299317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107660433264119419522866211 161490649896179129284299317)
                  ·
                    refine ⟨15139748427766793370403061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161490649896179129284299317 15139748427766793370403061)
                    ·
                      refine ⟨1419351415103136878475287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15139748427766793370403061 1419351415103136878475287)
                      ·
                        rfl

theorem cell23_2764177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2764177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764177 prefixEnd_2764177 := by exact prefixLift 2764177
  have htrace : WordTrace (prefixWord ++ tailWord_2764177) baseStart_2764177 baseEnd_2764177 := by
    simpa [prefixWord, tailWord_2764177, baseEnd_2764177] using wordTrace_append hprefix tailTrace_2764177
  have hstable : (prefixWord ++ tailWord_2764177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764177).length < 2 ^ (prefixWord ++ tailWord_2764177).sum := by decide
  have hdescent : baseEnd_2764177 < baseStart_2764177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764191 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2764191 : Nat := 118140960795 + 2764191 * 2 ^ 59
def prefixEnd_2764191 : Nat := 4983230072969 + 3 ^ 40 * 2764191 * 2
def baseEnd_2764191 : Nat := 1419358603832299823700223

theorem tailTrace_2764191 : CollatzResearch.WordTrace tailWord_2764191 prefixEnd_2764191 1419358603832299823700223 := by
  unfold tailWord_2764191
  simp only [CollatzResearch.WordTrace]
  refine ⟨100818328328815568083204427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67212218885877045388802951 100818328328815568083204427)
  ·
    refine ⟨151227492493223352124806641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100818328328815568083204427 151227492493223352124806641)
    ·
      refine ⟨113420619369917514093604981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151227492493223352124806641 113420619369917514093604981)
      ·
        refine ⟨10633183065929766946275467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113420619369917514093604981 10633183065929766946275467)
        ·
          refine ⟨15949774598894650419413201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10633183065929766946275467 15949774598894650419413201)
          ·
            refine ⟨11962330949170987814559901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15949774598894650419413201 11962330949170987814559901)
            ·
              refine ⟨4485874105939120430459963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11962330949170987814559901 4485874105939120430459963)
              ·
                refine ⟨6728811158908680645689945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485874105939120430459963 6728811158908680645689945)
                ·
                  refine ⟨5046608369181510484267459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728811158908680645689945 5046608369181510484267459)
                  ·
                    refine ⟨7569912553772265726401189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046608369181510484267459 7569912553772265726401189)
                    ·
                      refine ⟨1419358603832299823700223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7569912553772265726401189 1419358603832299823700223)
                      ·
                        rfl

theorem cell23_2764191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2764191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764191 prefixEnd_2764191 := by exact prefixLift 2764191
  have htrace : WordTrace (prefixWord ++ tailWord_2764191) baseStart_2764191 baseEnd_2764191 := by
    simpa [prefixWord, tailWord_2764191, baseEnd_2764191] using wordTrace_append hprefix tailTrace_2764191
  have hstable : (prefixWord ++ tailWord_2764191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764191).length < 2 ^ (prefixWord ++ tailWord_2764191).sum := by decide
  have hdescent : baseEnd_2764191 < baseStart_2764191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764231 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 6]
def baseStart_2764231 : Nat := 118140960795 + 2764231 * 2 ^ 59
def prefixEnd_2764231 : Nat := 4983230072969 + 3 ^ 40 * 2764231 * 2
def baseEnd_2764231 : Nat := 157708793673164407466671

theorem tailTrace_2764231 : CollatzResearch.WordTrace tailWord_2764231 prefixEnd_2764231 157708793673164407466671 := by
  unfold tailWord_2764231
  simp only [CollatzResearch.WordTrace]
  refine ⟨100819787248670654914660547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67213191499113769943107031 100819787248670654914660547)
  ·
    refine ⟨151229680873005982371990821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100819787248670654914660547 151229680873005982371990821)
    ·
      refine ⟨28355565163688621694748279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151229680873005982371990821 28355565163688621694748279)
      ·
        refine ⟨42533347745532932542122419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28355565163688621694748279 42533347745532932542122419)
        ·
          refine ⟨63800021618299398813183629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42533347745532932542122419 63800021618299398813183629)
          ·
            refine ⟨23925008106862274554943861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63800021618299398813183629 23925008106862274554943861)
            ·
              refine ⟨2242969510018338239525987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23925008106862274554943861 2242969510018338239525987)
              ·
                refine ⟨3364454265027507359288981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242969510018338239525987 3364454265027507359288981)
                ·
                  refine ⟨157708793673164407466671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3364454265027507359288981 157708793673164407466671)
                  ·
                    rfl

theorem cell23_2764231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 6].length) (baseStart_2764231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764231 prefixEnd_2764231 := by exact prefixLift 2764231
  have htrace : WordTrace (prefixWord ++ tailWord_2764231) baseStart_2764231 baseEnd_2764231 := by
    simpa [prefixWord, tailWord_2764231, baseEnd_2764231] using wordTrace_append hprefix tailTrace_2764231
  have hstable : (prefixWord ++ tailWord_2764231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764231).length < 2 ^ (prefixWord ++ tailWord_2764231).sum := by decide
  have hdescent : baseEnd_2764231 < baseStart_2764231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764298 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2764298 : Nat := 118140960795 + 2764298 * 2 ^ 59
def prefixEnd_2764298 : Nat := 4983230072969 + 3 ^ 40 * 2764298 * 2
def baseEnd_2764298 : Nat := 1419413546262330905062231

theorem tailTrace_2764298 : CollatzResearch.WordTrace tailWord_2764298 prefixEnd_2764298 1419413546262330905062231 := by
  unfold tailWord_2764298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25205557734856981339337387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67214820626285283571566365 25205557734856981339337387)
  ·
    refine ⟨37808336602285472009006081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25205557734856981339337387 37808336602285472009006081)
    ·
      refine ⟨28356252451714104006754561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37808336602285472009006081 28356252451714104006754561)
      ·
        refine ⟨21267189338785578005065921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28356252451714104006754561 21267189338785578005065921)
        ·
          refine ⟨15950392004089183503799441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21267189338785578005065921 15950392004089183503799441)
          ·
            refine ⟨11962794003066887627849581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15950392004089183503799441 11962794003066887627849581)
            ·
              refine ⟨4486047751150082860443593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11962794003066887627849581 4486047751150082860443593)
              ·
                refine ⟨3364535813362562145332695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486047751150082860443593 3364535813362562145332695)
                ·
                  refine ⟨5046803720043843217999043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364535813362562145332695 5046803720043843217999043)
                  ·
                    refine ⟨7570205580065764826998565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046803720043843217999043 7570205580065764826998565)
                    ·
                      refine ⟨1419413546262330905062231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7570205580065764826998565 1419413546262330905062231)
                      ·
                        rfl

theorem cell23_2764298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2764298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764298 prefixEnd_2764298 := by exact prefixLift 2764298
  have htrace : WordTrace (prefixWord ++ tailWord_2764298) baseStart_2764298 baseEnd_2764298 := by
    simpa [prefixWord, tailWord_2764298, baseEnd_2764298] using wordTrace_append hprefix tailTrace_2764298
  have hstable : (prefixWord ++ tailWord_2764298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764298).length < 2 ^ (prefixWord ++ tailWord_2764298).sum := by decide
  have hdescent : baseEnd_2764298 < baseStart_2764298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764375 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_2764375 : Nat := 118140960795 + 2764375 * 2 ^ 59
def prefixEnd_2764375 : Nat := 4983230072969 + 3 ^ 40 * 2764375 * 2
def baseEnd_2764375 : Nat := 1419453084272727103799377

theorem tailTrace_2764375 : CollatzResearch.WordTrace tailWord_2764375 prefixEnd_2764375 1419453084272727103799377 := by
  unfold tailWord_2764375
  simp only [CollatzResearch.WordTrace]
  refine ⟨100825039360148967507902579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67216692906765978338601719 100825039360148967507902579)
  ·
    refine ⟨151237559040223451261853869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100825039360148967507902579 151237559040223451261853869)
    ·
      refine ⟨56714084640083794223195201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151237559040223451261853869 56714084640083794223195201)
      ·
        refine ⟨42535563480062845667396401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56714084640083794223195201 42535563480062845667396401)
        ·
          refine ⟨31901672610047134250547301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42535563480062845667396401 31901672610047134250547301)
          ·
            refine ⟨5981563614383837671977619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31901672610047134250547301 5981563614383837671977619)
            ·
              refine ⟨8972345421575756507966429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981563614383837671977619 8972345421575756507966429)
              ·
                refine ⟨3364629533090908690487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8972345421575756507966429 3364629533090908690487411)
                ·
                  refine ⟨5046944299636363035731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364629533090908690487411 5046944299636363035731117)
                  ·
                    refine ⟨1892604112363636138399169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5046944299636363035731117 1892604112363636138399169)
                    ·
                      refine ⟨1419453084272727103799377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892604112363636138399169 1419453084272727103799377)
                      ·
                        rfl

theorem cell23_2764375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_2764375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764375 prefixEnd_2764375 := by exact prefixLift 2764375
  have htrace : WordTrace (prefixWord ++ tailWord_2764375) baseStart_2764375 baseEnd_2764375 := by
    simpa [prefixWord, tailWord_2764375, baseEnd_2764375] using wordTrace_append hprefix tailTrace_2764375
  have hstable : (prefixWord ++ tailWord_2764375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764375).length < 2 ^ (prefixWord ++ tailWord_2764375).sum := by decide
  have hdescent : baseEnd_2764375 < baseStart_2764375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764391 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2764391 : Nat := 118140960795 + 2764391 * 2 ^ 59
def prefixEnd_2764391 : Nat := 4983230072969 + 3 ^ 40 * 2764391 * 2
def baseEnd_2764391 : Nat := 1419461299963199041199303

theorem tailTrace_2764391 : CollatzResearch.WordTrace tailWord_2764391 prefixEnd_2764391 1419461299963199041199303 := by
  unfold tailWord_2764391
  simp only [CollatzResearch.WordTrace]
  refine ⟨100825622928091002240485027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67217081952060668160323351 100825622928091002240485027)
  ·
    refine ⟨151238434392136503360727541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100825622928091002240485027 151238434392136503360727541)
    ·
      refine ⟨14178603224262797190068207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151238434392136503360727541 14178603224262797190068207)
      ·
        refine ⟨21267904836394195785102311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14178603224262797190068207 21267904836394195785102311)
        ·
          refine ⟨31901857254591293677653467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21267904836394195785102311 31901857254591293677653467)
          ·
            refine ⟨47852785881886940516480201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31901857254591293677653467 47852785881886940516480201)
            ·
              refine ⟨35889589411415205387360151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47852785881886940516480201 35889589411415205387360151)
              ·
                refine ⟨53834384117122808081040227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35889589411415205387360151 53834384117122808081040227)
                ·
                  refine ⟨80751576175684212121560341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53834384117122808081040227 80751576175684212121560341)
                  ·
                    refine ⟨3785230133235197443198141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80751576175684212121560341 3785230133235197443198141)
                    ·
                      refine ⟨1419461299963199041199303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3785230133235197443198141 1419461299963199041199303)
                      ·
                        rfl

theorem cell23_2764391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2764391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764391 prefixEnd_2764391 := by exact prefixLift 2764391
  have htrace : WordTrace (prefixWord ++ tailWord_2764391) baseStart_2764391 baseEnd_2764391 := by
    simpa [prefixWord, tailWord_2764391, baseEnd_2764391] using wordTrace_append hprefix tailTrace_2764391
  have hstable : (prefixWord ++ tailWord_2764391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764391).length < 2 ^ (prefixWord ++ tailWord_2764391).sum := by decide
  have hdescent : baseEnd_2764391 < baseStart_2764391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764451 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2764451 : Nat := 118140960795 + 2764451 * 2 ^ 59
def prefixEnd_2764451 : Nat := 4983230072969 + 3 ^ 40 * 2764451 * 2
def baseEnd_2764451 : Nat := 1419492108802468806449027

theorem tailTrace_2764451 : CollatzResearch.WordTrace tailWord_2764451 prefixEnd_2764451 1419492108802468806449027 := by
  unfold tailWord_2764451
  simp only [CollatzResearch.WordTrace]
  refine ⟨100827811307873632487669207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67218540871915754991779471 100827811307873632487669207)
  ·
    refine ⟨151241716961810448731503811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100827811307873632487669207 151241716961810448731503811)
    ·
      refine ⟨226862575442715673097255717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151241716961810448731503811 226862575442715673097255717)
      ·
        refine ⟨42536732895509188705735447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226862575442715673097255717 42536732895509188705735447)
        ·
          refine ⟨63805099343263783058603171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42536732895509188705735447 63805099343263783058603171)
          ·
            refine ⟨95707649014895674587904757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63805099343263783058603171 95707649014895674587904757)
            ·
              refine ⟨8972592095146469492616071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95707649014895674587904757 8972592095146469492616071)
              ·
                refine ⟨13458888142719704238924107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8972592095146469492616071 13458888142719704238924107)
                ·
                  refine ⟨20188332214079556358386161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13458888142719704238924107 20188332214079556358386161)
                  ·
                    refine ⟨15141249160559667268789621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20188332214079556358386161 15141249160559667268789621)
                    ·
                      refine ⟨1419492108802468806449027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15141249160559667268789621 1419492108802468806449027)
                      ·
                        rfl

theorem cell23_2764451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2764451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764451 prefixEnd_2764451 := by exact prefixLift 2764451
  have htrace : WordTrace (prefixWord ++ tailWord_2764451) baseStart_2764451 baseEnd_2764451 := by
    simpa [prefixWord, tailWord_2764451, baseEnd_2764451] using wordTrace_append hprefix tailTrace_2764451
  have hstable : (prefixWord ++ tailWord_2764451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764451).length < 2 ^ (prefixWord ++ tailWord_2764451).sum := by decide
  have hdescent : baseEnd_2764451 < baseStart_2764451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764555 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 2, 3, 2]
def baseStart_2764555 : Nat := 118140960795 + 2764555 * 2 ^ 59
def prefixEnd_2764555 : Nat := 4983230072969 + 3 ^ 40 * 2764555 * 2
def baseEnd_2764555 : Nat := 1419545510790536399548549

theorem tailTrace_2764555 : CollatzResearch.WordTrace tailWord_2764555 prefixEnd_2764555 1419545510790536399548549 := by
  unfold tailWord_2764555
  simp only [CollatzResearch.WordTrace]
  refine ⟨100831604499496858249455119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67221069666331238832970079 100831604499496858249455119)
  ·
    refine ⟨151247406749245287374182679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100831604499496858249455119 151247406749245287374182679)
    ·
      refine ⟨226871110123867931061274019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151247406749245287374182679 226871110123867931061274019)
      ·
        refine ⟨340306665185801896591911029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226871110123867931061274019 340306665185801896591911029)
        ·
          refine ⟨31903749861168927805491659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340306665185801896591911029 31903749861168927805491659)
          ·
            refine ⟨47855624791753391708237489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31903749861168927805491659 47855624791753391708237489)
            ·
              refine ⟨35891718593815043781178117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47855624791753391708237489 35891718593815043781178117)
              ·
                refine ⟨6729697236340320708970897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35891718593815043781178117 6729697236340320708970897)
                ·
                  refine ⟨5047272927255240531728173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6729697236340320708970897 5047272927255240531728173)
                  ·
                    refine ⟨1892727347720715199398065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5047272927255240531728173 1892727347720715199398065)
                    ·
                      refine ⟨1419545510790536399548549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892727347720715199398065 1419545510790536399548549)
                      ·
                        rfl

theorem cell23_2764555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3, 2].length) (baseStart_2764555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764555 prefixEnd_2764555 := by exact prefixLift 2764555
  have htrace : WordTrace (prefixWord ++ tailWord_2764555) baseStart_2764555 baseEnd_2764555 := by
    simpa [prefixWord, tailWord_2764555, baseEnd_2764555] using wordTrace_append hprefix tailTrace_2764555
  have hstable : (prefixWord ++ tailWord_2764555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764555).length < 2 ^ (prefixWord ++ tailWord_2764555).sum := by decide
  have hdescent : baseEnd_2764555 < baseStart_2764555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764568 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2764568 : Nat := 118140960795 + 2764568 * 2 ^ 59
def prefixEnd_2764568 : Nat := 4983230072969 + 3 ^ 40 * 2764568 * 2
def baseEnd_2764568 : Nat := 1419552186039044848685989

theorem tailTrace_2764568 : CollatzResearch.WordTrace tailWord_2764568 prefixEnd_2764568 1419552186039044848685989 := by
  unfold tailWord_2764568
  simp only [CollatzResearch.WordTrace]
  refine ⟨50416039324224880734839179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67221385765633174313118905 50416039324224880734839179)
  ·
    refine ⟨75624058986337321102258769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50416039324224880734839179 75624058986337321102258769)
    ·
      refine ⟨56718044239752990826694077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75624058986337321102258769 56718044239752990826694077)
      ·
        refine ⟨21269266589907371560010279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56718044239752990826694077 21269266589907371560010279)
        ·
          refine ⟨31903899884861057340015419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21269266589907371560010279 31903899884861057340015419)
          ·
            refine ⟨47855849827291586010023129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31903899884861057340015419 47855849827291586010023129)
            ·
              refine ⟨35891887370468689507517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47855849827291586010023129 35891887370468689507517347)
              ·
                refine ⟨53837831055703034261276021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35891887370468689507517347 53837831055703034261276021)
                ·
                  refine ⟨5047296661472159461994627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53837831055703034261276021 5047296661472159461994627)
                  ·
                    refine ⟨7570944992208239192991941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5047296661472159461994627 7570944992208239192991941)
                    ·
                      refine ⟨1419552186039044848685989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7570944992208239192991941 1419552186039044848685989)
                      ·
                        rfl

theorem cell23_2764568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2764568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764568 prefixEnd_2764568 := by exact prefixLift 2764568
  have htrace : WordTrace (prefixWord ++ tailWord_2764568) baseStart_2764568 baseEnd_2764568 := by
    simpa [prefixWord, tailWord_2764568, baseEnd_2764568] using wordTrace_append hprefix tailTrace_2764568
  have hstable : (prefixWord ++ tailWord_2764568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764568).length < 2 ^ (prefixWord ++ tailWord_2764568).sum := by decide
  have hdescent : baseEnd_2764568 < baseStart_2764568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764591 : List Nat := [1, 1, 2, 1, 2, 1, 2, 13]
def baseStart_2764591 : Nat := 118140960795 + 2764591 * 2 ^ 59
def prefixEnd_2764591 : Nat := 4983230072969 + 3 ^ 40 * 2764591 * 2
def baseEnd_2764591 : Nat := 52576444299781416988829

theorem tailTrace_2764591 : CollatzResearch.WordTrace tailWord_2764591 prefixEnd_2764591 52576444299781416988829 := by
  unfold tailWord_2764591
  simp only [CollatzResearch.WordTrace]
  refine ⟨100832917527366436397765627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67221945018244290931843751 100832917527366436397765627)
  ·
    refine ⟨151249376291049654596648441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100832917527366436397765627 151249376291049654596648441)
    ·
      refine ⟨113437032218287240947486331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151249376291049654596648441 113437032218287240947486331)
      ·
        refine ⟨170155548327430861421229497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113437032218287240947486331 170155548327430861421229497)
        ·
          refine ⟨127616661245573146065922123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170155548327430861421229497 127616661245573146065922123)
          ·
            refine ⟨191424991868359719098883185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127616661245573146065922123 191424991868359719098883185)
            ·
              refine ⟨143568743901269789324162389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191424991868359719098883185 143568743901269789324162389)
              ·
                refine ⟨52576444299781416988829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 143568743901269789324162389 52576444299781416988829)
                ·
                  rfl

theorem cell23_2764591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 13].length) (baseStart_2764591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764591 prefixEnd_2764591 := by exact prefixLift 2764591
  have htrace : WordTrace (prefixWord ++ tailWord_2764591) baseStart_2764591 baseEnd_2764591 := by
    simpa [prefixWord, tailWord_2764591, baseEnd_2764591] using wordTrace_append hprefix tailTrace_2764591
  have hstable : (prefixWord ++ tailWord_2764591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764591).length < 2 ^ (prefixWord ++ tailWord_2764591).sum := by decide
  have hdescent : baseEnd_2764591 < baseStart_2764591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764596 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_2764596 : Nat := 118140960795 + 2764596 * 2 ^ 59
def prefixEnd_2764596 : Nat := 4983230072969 + 3 ^ 40 * 2764596 * 2
def baseEnd_2764596 : Nat := 1419566563497370739135861

theorem tailTrace_2764596 : CollatzResearch.WordTrace tailWord_2764596 prefixEnd_2764596 1419566563497370739135861 := by
  unfold tailWord_2764596
  simp only [CollatzResearch.WordTrace]
  refine ⟨50416549946174161125848821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67222066594898881501131761 50416549946174161125848821)
  ·
    refine ⟨4726551557453827605548327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50416549946174161125848821 4726551557453827605548327)
    ·
      refine ⟨7089827336180741408322491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726551557453827605548327 7089827336180741408322491)
      ·
        refine ⟨10634741004271112112483737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089827336180741408322491 10634741004271112112483737)
        ·
          refine ⟨7976055753203334084362803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10634741004271112112483737 7976055753203334084362803)
          ·
            refine ⟨11964083629805001126544205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976055753203334084362803 11964083629805001126544205)
            ·
              refine ⟨4486531361176875422454077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11964083629805001126544205 4486531361176875422454077)
              ·
                refine ⟨1682449260441328283420279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4486531361176875422454077 1682449260441328283420279)
                ·
                  refine ⟨2523673890661992425130419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682449260441328283420279 2523673890661992425130419)
                  ·
                    refine ⟨3785510835992988637695629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2523673890661992425130419 3785510835992988637695629)
                    ·
                      refine ⟨1419566563497370739135861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3785510835992988637695629 1419566563497370739135861)
                      ·
                        rfl

theorem cell23_2764596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_2764596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764596 prefixEnd_2764596 := by exact prefixLift 2764596
  have htrace : WordTrace (prefixWord ++ tailWord_2764596) baseStart_2764596 baseEnd_2764596 := by
    simpa [prefixWord, tailWord_2764596, baseEnd_2764596] using wordTrace_append hprefix tailTrace_2764596
  have hstable : (prefixWord ++ tailWord_2764596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764596).length < 2 ^ (prefixWord ++ tailWord_2764596).sum := by decide
  have hdescent : baseEnd_2764596 < baseStart_2764596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764605 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2764605 : Nat := 118140960795 + 2764605 * 2 ^ 59
def prefixEnd_2764605 : Nat := 4983230072969 + 3 ^ 40 * 2764605 * 2
def baseEnd_2764605 : Nat := 1419571184823261203923319

theorem tailTrace_2764605 : CollatzResearch.WordTrace tailWord_2764605 prefixEnd_2764605 1419571184823261203923319 := by
  unfold tailWord_2764605
  simp only [CollatzResearch.WordTrace]
  refine ⟨100833428149315716788775269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67222285432877144525850179 100833428149315716788775269)
  ·
    refine ⟨18906267777996696897895363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100833428149315716788775269 18906267777996696897895363)
    ·
      refine ⟨28359401666995045346843045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18906267777996696897895363 28359401666995045346843045)
      ·
        refine ⟨5317387812561571002533071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28359401666995045346843045 5317387812561571002533071)
        ·
          refine ⟨7976081718842356503799607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317387812561571002533071 7976081718842356503799607)
          ·
            refine ⟨11964122578263534755699411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976081718842356503799607 11964122578263534755699411)
            ·
              refine ⟨17946183867395302133549117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964122578263534755699411 17946183867395302133549117)
              ·
                refine ⟨6729818950273238300080919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17946183867395302133549117 6729818950273238300080919)
                ·
                  refine ⟨10094728425409857450121379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6729818950273238300080919 10094728425409857450121379)
                  ·
                    refine ⟨15142092638114786175182069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10094728425409857450121379 15142092638114786175182069)
                    ·
                      refine ⟨1419571184823261203923319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15142092638114786175182069 1419571184823261203923319)
                      ·
                        rfl

theorem cell23_2764605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2764605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764605 prefixEnd_2764605 := by exact prefixLift 2764605
  have htrace : WordTrace (prefixWord ++ tailWord_2764605) baseStart_2764605 baseEnd_2764605 := by
    simpa [prefixWord, tailWord_2764605, baseEnd_2764605] using wordTrace_append hprefix tailTrace_2764605
  have hstable : (prefixWord ++ tailWord_2764605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764605).length < 2 ^ (prefixWord ++ tailWord_2764605).sum := by decide
  have hdescent : baseEnd_2764605 < baseStart_2764605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764629 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2764629 : Nat := 118140960795 + 2764629 * 2 ^ 59
def prefixEnd_2764629 : Nat := 4983230072969 + 3 ^ 40 * 2764629 * 2
def baseEnd_2764629 : Nat := 473194502786323036674403

theorem tailTrace_2764629 : CollatzResearch.WordTrace tailWord_2764629 prefixEnd_2764629 473194502786323036674403 := by
  unfold tailWord_2764629
  simp only [CollatzResearch.WordTrace]
  refine ⟨100834303501228768887648941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67222869000819179258432627 100834303501228768887648941)
  ·
    refine ⟨37812863812960788332868353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100834303501228768887648941 37812863812960788332868353)
    ·
      refine ⟨28359647859720591249651265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37812863812960788332868353 28359647859720591249651265)
      ·
        refine ⟨21269735894790443437238449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28359647859720591249651265 21269735894790443437238449)
        ·
          refine ⟨15952301921092832577928837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21269735894790443437238449 15952301921092832577928837)
          ·
            refine ⟨2991056610204906108361657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15952301921092832577928837 2991056610204906108361657)
            ·
              refine ⟨2243292457653679581271243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991056610204906108361657 2243292457653679581271243)
              ·
                refine ⟨3364938686480519371906865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243292457653679581271243 3364938686480519371906865)
                ·
                  refine ⟨2523704014860389528930149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3364938686480519371906865 2523704014860389528930149)
                  ·
                    refine ⟨473194502786323036674403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2523704014860389528930149 473194502786323036674403)
                    ·
                      rfl

theorem cell23_2764629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2764629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764629 prefixEnd_2764629 := by exact prefixLift 2764629
  have htrace : WordTrace (prefixWord ++ tailWord_2764629) baseStart_2764629 baseEnd_2764629 := by
    simpa [prefixWord, tailWord_2764629, baseEnd_2764629] using wordTrace_append hprefix tailTrace_2764629
  have hstable : (prefixWord ++ tailWord_2764629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764629).length < 2 ^ (prefixWord ++ tailWord_2764629).sum := by decide
  have hdescent : baseEnd_2764629 < baseStart_2764629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764636 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2764636 : Nat := 118140960795 + 2764636 * 2 ^ 59
def prefixEnd_2764636 : Nat := 4983230072969 + 3 ^ 40 * 2764636 * 2
def baseEnd_2764636 : Nat := 1419587102723550582635677

theorem tailTrace_2764636 : CollatzResearch.WordTrace tailWord_2764636 prefixEnd_2764636 1419587102723550582635677 := by
  unfold tailWord_2764636
  simp only [CollatzResearch.WordTrace]
  refine ⟨50417279406101704541576881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67223039208135606055435841 50417279406101704541576881)
  ·
    refine ⟨37812959554576278406182661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50417279406101704541576881 37812959554576278406182661)
    ·
      refine ⟨7089929916483052201159249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37812959554576278406182661 7089929916483052201159249)
      ·
        refine ⟨5317447437362289150869437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7089929916483052201159249 5317447437362289150869437)
        ·
          refine ⟨1994042789010858431576039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5317447437362289150869437 1994042789010858431576039)
          ·
            refine ⟨2991064183516287647364059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994042789010858431576039 2991064183516287647364059)
            ·
              refine ⟨4486596275274431471046089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991064183516287647364059 4486596275274431471046089)
              ·
                refine ⟨3364947206455823603284567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486596275274431471046089 3364947206455823603284567)
                ·
                  refine ⟨5047420809683735404926851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364947206455823603284567 5047420809683735404926851)
                  ·
                    refine ⟨7571131214525603107390277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5047420809683735404926851 7571131214525603107390277)
                    ·
                      refine ⟨1419587102723550582635677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7571131214525603107390277 1419587102723550582635677)
                      ·
                        rfl

theorem cell23_2764636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2764636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764636 prefixEnd_2764636 := by exact prefixLift 2764636
  have htrace : WordTrace (prefixWord ++ tailWord_2764636) baseStart_2764636 baseEnd_2764636 := by
    simpa [prefixWord, tailWord_2764636, baseEnd_2764636] using wordTrace_append hprefix tailTrace_2764636
  have hstable : (prefixWord ++ tailWord_2764636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764636).length < 2 ^ (prefixWord ++ tailWord_2764636).sum := by decide
  have hdescent : baseEnd_2764636 < baseStart_2764636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764670 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2764670 : Nat := 118140960795 + 2764670 * 2 ^ 59
def prefixEnd_2764670 : Nat := 4983230072969 + 3 ^ 40 * 2764670 * 2
def baseEnd_2764670 : Nat := 1419604561065803449610521

theorem tailTrace_2764670 : CollatzResearch.WordTrace tailWord_2764670 prefixEnd_2764670 1419604561065803449610521 := by
  unfold tailWord_2764670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604474861760029111236433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67223865929386821926594309 12604474861760029111236433)
  ·
    refine ⟨9453356146320021833427325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12604474861760029111236433 9453356146320021833427325)
    ·
      refine ⟨3545008554870008187535247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9453356146320021833427325 3545008554870008187535247)
      ·
        refine ⟨5317512832305012281302871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545008554870008187535247 5317512832305012281302871)
        ·
          refine ⟨7976269248457518421954307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317512832305012281302871 7976269248457518421954307)
          ·
            refine ⟨11964403872686277632931461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976269248457518421954307 11964403872686277632931461)
            ·
              refine ⟨2243325726128677056174649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11964403872686277632931461 2243325726128677056174649)
              ·
                refine ⟨1682494294596507792130987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243325726128677056174649 1682494294596507792130987)
                ·
                  refine ⟨2523741441894761688196481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682494294596507792130987 2523741441894761688196481)
                  ·
                    refine ⟨1892806081421071266147361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2523741441894761688196481 1892806081421071266147361)
                    ·
                      refine ⟨1419604561065803449610521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892806081421071266147361 1419604561065803449610521)
                      ·
                        rfl

theorem cell23_2764670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2764670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764670 prefixEnd_2764670 := by exact prefixLift 2764670
  have htrace : WordTrace (prefixWord ++ tailWord_2764670) baseStart_2764670 baseEnd_2764670 := by
    simpa [prefixWord, tailWord_2764670, baseEnd_2764670] using wordTrace_append hprefix tailTrace_2764670
  have hstable : (prefixWord ++ tailWord_2764670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764670).length < 2 ^ (prefixWord ++ tailWord_2764670).sum := by decide
  have hdescent : baseEnd_2764670 < baseStart_2764670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764688 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_2764688 : Nat := 118140960795 + 2764688 * 2 ^ 59
def prefixEnd_2764688 : Nat := 4983230072969 + 3 ^ 40 * 2764688 * 2
def baseEnd_2764688 : Nat := 1419613803717584379185437

theorem tailTrace_2764688 : CollatzResearch.WordTrace tailWord_2764688 prefixEnd_2764688 1419613803717584379185437 := by
  unfold tailWord_2764688
  simp only [CollatzResearch.WordTrace]
  refine ⟨50418227704007510982023359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67224303605343347976031145 50418227704007510982023359)
  ·
    refine ⟨75627341556011266473035039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50418227704007510982023359 75627341556011266473035039)
    ·
      refine ⟨113441012334016899709552559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75627341556011266473035039 113441012334016899709552559)
      ·
        refine ⟨170161518501025349564328839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113441012334016899709552559 170161518501025349564328839)
        ·
          refine ⟨255242277751538024346493259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170161518501025349564328839 255242277751538024346493259)
          ·
            refine ⟨382863416627307036519739889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255242277751538024346493259 382863416627307036519739889)
            ·
              refine ⟨287147562470480277389804917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382863416627307036519739889 287147562470480277389804917)
              ·
                refine ⟨26920083981607526005294211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287147562470480277389804917 26920083981607526005294211)
                ·
                  refine ⟨40380125972411289007941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26920083981607526005294211 40380125972411289007941317)
                  ·
                    refine ⟨7571273619827116688988997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40380125972411289007941317 7571273619827116688988997)
                    ·
                      refine ⟨1419613803717584379185437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7571273619827116688988997 1419613803717584379185437)
                      ·
                        rfl

theorem cell23_2764688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_2764688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764688 prefixEnd_2764688 := by exact prefixLift 2764688
  have htrace : WordTrace (prefixWord ++ tailWord_2764688) baseStart_2764688 baseEnd_2764688 := by
    simpa [prefixWord, tailWord_2764688, baseEnd_2764688] using wordTrace_append hprefix tailTrace_2764688
  have hstable : (prefixWord ++ tailWord_2764688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764688).length < 2 ^ (prefixWord ++ tailWord_2764688).sum := by decide
  have hdescent : baseEnd_2764688 < baseStart_2764688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764782 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2764782 : Nat := 118140960795 + 2764782 * 2 ^ 59
def prefixEnd_2764782 : Nat := 4983230072969 + 3 ^ 40 * 2764782 * 2
def baseEnd_2764782 : Nat := 1419662070899107011410005

theorem tailTrace_2764782 : CollatzResearch.WordTrace tailWord_2764782 prefixEnd_2764782 1419662070899107011410005 := by
  unfold tailWord_2764782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604985483709309502246075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67226589246449650678645733 12604985483709309502246075)
  ·
    refine ⟨18907478225563964253369113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12604985483709309502246075 18907478225563964253369113)
    ·
      refine ⟨14180608669172973190026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18907478225563964253369113 14180608669172973190026835)
      ·
        refine ⟨21270913003759459785040253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14180608669172973190026835 21270913003759459785040253)
        ·
          refine ⟨7976592376409797419390095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21270913003759459785040253 7976592376409797419390095)
          ·
            refine ⟨11964888564614696129085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7976592376409797419390095 11964888564614696129085143)
            ·
              refine ⟨17947332846922044193627715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11964888564614696129085143 17947332846922044193627715)
              ·
                refine ⟨26920999270383066290441573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17947332846922044193627715 26920999270383066290441573)
                ·
                  refine ⟨5047687363196824929457795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26920999270383066290441573 5047687363196824929457795)
                  ·
                    refine ⟨7571531044795237394186693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5047687363196824929457795 7571531044795237394186693)
                    ·
                      refine ⟨1419662070899107011410005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7571531044795237394186693 1419662070899107011410005)
                      ·
                        rfl

theorem cell23_2764782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2764782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764782 prefixEnd_2764782 := by exact prefixLift 2764782
  have htrace : WordTrace (prefixWord ++ tailWord_2764782) baseStart_2764782 baseEnd_2764782 := by
    simpa [prefixWord, tailWord_2764782, baseEnd_2764782] using wordTrace_append hprefix tailTrace_2764782
  have hstable : (prefixWord ++ tailWord_2764782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764782).length < 2 ^ (prefixWord ++ tailWord_2764782).sum := by decide
  have hdescent : baseEnd_2764782 < baseStart_2764782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764792 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_2764792 : Nat := 118140960795 + 2764792 * 2 ^ 59
def prefixEnd_2764792 : Nat := 4983230072969 + 3 ^ 40 * 2764792 * 2
def baseEnd_2764792 : Nat := 473222401901883990761653

theorem tailTrace_2764792 : CollatzResearch.WordTrace tailWord_2764792 prefixEnd_2764792 473222401901883990761653 := by
  unfold tailWord_2764792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50420124299819123862916315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67226832399758831817221753 50420124299819123862916315)
  ·
    refine ⟨75630186449728685794374473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50420124299819123862916315 75630186449728685794374473)
    ·
      refine ⟨56722639837296514345780855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75630186449728685794374473 56722639837296514345780855)
      ·
        refine ⟨85083959755944771518671283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56722639837296514345780855 85083959755944771518671283)
        ·
          refine ⟨127625939633917157278006925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85083959755944771518671283 127625939633917157278006925)
          ·
            refine ⟨47859727362718933979252597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127625939633917157278006925 47859727362718933979252597)
            ·
              refine ⟨4486849440254900060554931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47859727362718933979252597 4486849440254900060554931)
              ·
                refine ⟨6730274160382350090832397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486849440254900060554931 6730274160382350090832397)
                ·
                  refine ⟨2523852810143381284062149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6730274160382350090832397 2523852810143381284062149)
                  ·
                    refine ⟨473222401901883990761653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2523852810143381284062149 473222401901883990761653)
                    ·
                      rfl

theorem cell23_2764792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_2764792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764792 prefixEnd_2764792 := by exact prefixLift 2764792
  have htrace : WordTrace (prefixWord ++ tailWord_2764792) baseStart_2764792 baseEnd_2764792 := by
    simpa [prefixWord, tailWord_2764792, baseEnd_2764792] using wordTrace_append hprefix tailTrace_2764792
  have hstable : (prefixWord ++ tailWord_2764792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764792).length < 2 ^ (prefixWord ++ tailWord_2764792).sum := by decide
  have hdescent : baseEnd_2764792 < baseStart_2764792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764813 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2764813 : Nat := 118140960795 + 2764813 * 2 ^ 59
def prefixEnd_2764813 : Nat := 4983230072969 + 3 ^ 40 * 2764813 * 2
def baseEnd_2764813 : Nat := 473225996266465463374121

theorem tailTrace_2764813 : CollatzResearch.WordTrace tailWord_2764813 prefixEnd_2764813 473225996266465463374121 := by
  unfold tailWord_2764813
  simp only [CollatzResearch.WordTrace]
  refine ⟨100841014532562168312347093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67227343021708112208231395 100841014532562168312347093)
  ·
    refine ⟨2363461278106925819820635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 100841014532562168312347093 2363461278106925819820635)
    ·
      refine ⟨3545191917160388729730953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363461278106925819820635 3545191917160388729730953)
      ·
        refine ⟨2658893937870291547298215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545191917160388729730953 2658893937870291547298215)
        ·
          refine ⟨3988340906805437320947323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658893937870291547298215 3988340906805437320947323)
          ·
            refine ⟨5982511360208155981420985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988340906805437320947323 5982511360208155981420985)
            ·
              refine ⟨4486883520156116986065739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982511360208155981420985 4486883520156116986065739)
              ·
                refine ⟨6730325280234175479098609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486883520156116986065739 6730325280234175479098609)
                ·
                  refine ⟨5047743960175631609323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730325280234175479098609 5047743960175631609323957)
                  ·
                    refine ⟨473225996266465463374121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5047743960175631609323957 473225996266465463374121)
                    ·
                      rfl

theorem cell23_2764813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2764813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764813 prefixEnd_2764813 := by exact prefixLift 2764813
  have htrace : WordTrace (prefixWord ++ tailWord_2764813) baseStart_2764813 baseEnd_2764813 := by
    simpa [prefixWord, tailWord_2764813, baseEnd_2764813] using wordTrace_append hprefix tailTrace_2764813
  have hstable : (prefixWord ++ tailWord_2764813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764813).length < 2 ^ (prefixWord ++ tailWord_2764813).sum := by decide
  have hdescent : baseEnd_2764813 < baseStart_2764813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764872 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_2764872 : Nat := 118140960795 + 2764872 * 2 ^ 59
def prefixEnd_2764872 : Nat := 4983230072969 + 3 ^ 40 * 2764872 * 2
def baseEnd_2764872 : Nat := 1419708284158011659284591

theorem tailTrace_2764872 : CollatzResearch.WordTrace tailWord_2764872 prefixEnd_2764872 1419708284158011659284591 := by
  unfold tailWord_2764872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50421583219674210694372435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67228777626232280925829913 50421583219674210694372435)
  ·
    refine ⟨75632374829511316041558653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50421583219674210694372435 75632374829511316041558653)
    ·
      refine ⟨28362140561066743515584495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75632374829511316041558653 28362140561066743515584495)
      ·
        refine ⟨42543210841600115273376743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28362140561066743515584495 42543210841600115273376743)
        ·
          refine ⟨63814816262400172910065115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42543210841600115273376743 63814816262400172910065115)
          ·
            refine ⟨95722224393600259365097673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63814816262400172910065115 95722224393600259365097673)
            ·
              refine ⟨71791668295200194523823255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95722224393600259365097673 71791668295200194523823255)
              ·
                refine ⟨107687502442800291785734883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71791668295200194523823255 107687502442800291785734883)
                ·
                  refine ⟨161531253664200437678602325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107687502442800291785734883 161531253664200437678602325)
                  ·
                    refine ⟨1892944378877348879046121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 161531253664200437678602325 1892944378877348879046121)
                    ·
                      refine ⟨1419708284158011659284591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892944378877348879046121 1419708284158011659284591)
                      ·
                        rfl

theorem cell23_2764872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_2764872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764872 prefixEnd_2764872 := by exact prefixLift 2764872
  have htrace : WordTrace (prefixWord ++ tailWord_2764872) baseStart_2764872 baseEnd_2764872 := by
    simpa [prefixWord, tailWord_2764872, baseEnd_2764872] using wordTrace_append hprefix tailTrace_2764872
  have hstable : (prefixWord ++ tailWord_2764872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764872).length < 2 ^ (prefixWord ++ tailWord_2764872).sum := by decide
  have hdescent : baseEnd_2764872 < baseStart_2764872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764875 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_2764875 : Nat := 118140960795 + 2764875 * 2 ^ 59
def prefixEnd_2764875 : Nat := 4983230072969 + 3 ^ 40 * 2764875 * 2
def baseEnd_2764875 : Nat := 1419709824599975147547077

theorem tailTrace_2764875 : CollatzResearch.WordTrace tailWord_2764875 prefixEnd_2764875 1419709824599975147547077 := by
  unfold tailWord_2764875
  simp only [CollatzResearch.WordTrace]
  refine ⟨100843275858337552901104079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67228850572225035267402719 100843275858337552901104079)
  ·
    refine ⟨151264913787506329351656119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100843275858337552901104079 151264913787506329351656119)
    ·
      refine ⟨226897370681259494027484179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151264913787506329351656119 226897370681259494027484179)
      ·
        refine ⟨340346056021889241041226269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226897370681259494027484179 340346056021889241041226269)
        ·
          refine ⟨127629771008208465390459851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340346056021889241041226269 127629771008208465390459851)
          ·
            refine ⟨191444656512312698085689777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127629771008208465390459851 191444656512312698085689777)
            ·
              refine ⟨143583492384234523564267333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191444656512312698085689777 143583492384234523564267333)
              ·
                refine ⟨26921904822043973168300125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143583492384234523564267333 26921904822043973168300125)
                ·
                  refine ⟨10095714308266489938112547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26921904822043973168300125 10095714308266489938112547)
                  ·
                    refine ⟨15143571462399734907168821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10095714308266489938112547 15143571462399734907168821)
                    ·
                      refine ⟨1419709824599975147547077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15143571462399734907168821 1419709824599975147547077)
                      ·
                        rfl

theorem cell23_2764875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_2764875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764875 prefixEnd_2764875 := by exact prefixLift 2764875
  have htrace : WordTrace (prefixWord ++ tailWord_2764875) baseStart_2764875 baseEnd_2764875 := by
    simpa [prefixWord, tailWord_2764875, baseEnd_2764875] using wordTrace_append hprefix tailTrace_2764875
  have hstable : (prefixWord ++ tailWord_2764875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764875).length < 2 ^ (prefixWord ++ tailWord_2764875).sum := by decide
  have hdescent : baseEnd_2764875 < baseStart_2764875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764889 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 5, 2, 2]
def baseStart_2764889 : Nat := 118140960795 + 2764889 * 2 ^ 59
def prefixEnd_2764889 : Nat := 4983230072969 + 3 ^ 40 * 2764889 * 2
def baseEnd_2764889 : Nat := 1419717013329138092772013

theorem tailTrace_2764889 : CollatzResearch.WordTrace tailWord_2764889 prefixEnd_2764889 1419717013329138092772013 := by
  unfold tailWord_2764889
  simp only [CollatzResearch.WordTrace]
  refine ⟨100843786480286833292113721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67229190986857888861409147 100843786480286833292113721)
  ·
    refine ⟨75632839860215124969085291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100843786480286833292113721 75632839860215124969085291)
    ·
      refine ⟨113449259790322687453627937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75632839860215124969085291 113449259790322687453627937)
      ·
        refine ⟨85086944842742015590220953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113449259790322687453627937 85086944842742015590220953)
        ·
          refine ⟨63815208632056511692665715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85086944842742015590220953 63815208632056511692665715)
          ·
            refine ⟨95722812948084767538998573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63815208632056511692665715 95722812948084767538998573)
            ·
              refine ⟨35896054855531787827124465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95722812948084767538998573 35896054855531787827124465)
              ·
                refine ⟨26922041141648840870343349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35896054855531787827124465 26922041141648840870343349)
                ·
                  refine ⟨2523941357029578831594689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26922041141648840870343349 2523941357029578831594689)
                  ·
                    refine ⟨1892956017772184123696017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2523941357029578831594689 1892956017772184123696017)
                    ·
                      refine ⟨1419717013329138092772013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1892956017772184123696017 1419717013329138092772013)
                      ·
                        rfl

theorem cell23_2764889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_2764889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764889 prefixEnd_2764889 := by exact prefixLift 2764889
  have htrace : WordTrace (prefixWord ++ tailWord_2764889) baseStart_2764889 baseEnd_2764889 := by
    simpa [prefixWord, tailWord_2764889, baseEnd_2764889] using wordTrace_append hprefix tailTrace_2764889
  have hstable : (prefixWord ++ tailWord_2764889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764889).length < 2 ^ (prefixWord ++ tailWord_2764889).sum := by decide
  have hdescent : baseEnd_2764889 < baseStart_2764889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764899 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 2, 4]
def baseStart_2764899 : Nat := 118140960795 + 2764899 * 2 ^ 59
def prefixEnd_2764899 : Nat := 4983230072969 + 3 ^ 40 * 2764899 * 2
def baseEnd_2764899 : Nat := 473240716045227684548989

theorem tailTrace_2764899 : CollatzResearch.WordTrace tailWord_2764899 prefixEnd_2764899 473240716045227684548989 := by
  unfold tailWord_2764899
  simp only [CollatzResearch.WordTrace]
  refine ⟨100844151210250604999977751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67229434140167069999985167 100844151210250604999977751)
  ·
    refine ⟨151266226815375907499966627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100844151210250604999977751 151266226815375907499966627)
    ·
      refine ⟨226899340223063861249949941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151266226815375907499966627 226899340223063861249949941)
      ·
        refine ⟨21271813145912236992182807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226899340223063861249949941 21271813145912236992182807)
        ·
          refine ⟨31907719718868355488274211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21271813145912236992182807 31907719718868355488274211)
          ·
            refine ⟨47861579578302533232411317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31907719718868355488274211 47861579578302533232411317)
            ·
              refine ⟨4487023085465862490538561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47861579578302533232411317 4487023085465862490538561)
              ·
                refine ⟨3365267314099396867903921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487023085465862490538561 3365267314099396867903921)
                ·
                  refine ⟨2523950485574547650927941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365267314099396867903921 2523950485574547650927941)
                  ·
                    refine ⟨473240716045227684548989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2523950485574547650927941 473240716045227684548989)
                    ·
                      rfl

theorem cell23_2764899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 4].length) (baseStart_2764899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764899 prefixEnd_2764899 := by exact prefixLift 2764899
  have htrace : WordTrace (prefixWord ++ tailWord_2764899) baseStart_2764899 baseEnd_2764899 := by
    simpa [prefixWord, tailWord_2764899, baseEnd_2764899] using wordTrace_append hprefix tailTrace_2764899
  have hstable : (prefixWord ++ tailWord_2764899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764899).length < 2 ^ (prefixWord ++ tailWord_2764899).sum := by decide
  have hdescent : baseEnd_2764899 < baseStart_2764899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764919 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_2764919 : Nat := 118140960795 + 2764919 * 2 ^ 59
def prefixEnd_2764919 : Nat := 4983230072969 + 3 ^ 40 * 2764919 * 2
def baseEnd_2764919 : Nat := 1419732417748772975396875

theorem tailTrace_2764919 : CollatzResearch.WordTrace tailWord_2764919 prefixEnd_2764919 1419732417748772975396875 := by
  unfold tailWord_2764919
  simp only [CollatzResearch.WordTrace]
  refine ⟨100844880670178148415705811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67229920446785432277137207 100844880670178148415705811)
  ·
    refine ⟨151267321005267222623558717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100844880670178148415705811 151267321005267222623558717)
    ·
      refine ⟨56725245376975208483834519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151267321005267222623558717 56725245376975208483834519)
      ·
        refine ⟨85087868065462812725751779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56725245376975208483834519 85087868065462812725751779)
        ·
          refine ⟨127631802098194219088627669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85087868065462812725751779 127631802098194219088627669)
          ·
            refine ⟨2991370361676427009889711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 127631802098194219088627669 2991370361676427009889711)
            ·
              refine ⟨4487055542514640514834567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991370361676427009889711 4487055542514640514834567)
              ·
                refine ⟨6730583313771960772251851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487055542514640514834567 6730583313771960772251851)
                ·
                  refine ⟨10095874970657941158377777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730583313771960772251851 10095874970657941158377777)
                  ·
                    refine ⟨7571906227993455868783333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10095874970657941158377777 7571906227993455868783333)
                    ·
                      refine ⟨1419732417748772975396875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7571906227993455868783333 1419732417748772975396875)
                      ·
                        rfl

theorem cell23_2764919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_2764919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764919 prefixEnd_2764919 := by exact prefixLift 2764919
  have htrace : WordTrace (prefixWord ++ tailWord_2764919) baseStart_2764919 baseEnd_2764919 := by
    simpa [prefixWord, tailWord_2764919, baseEnd_2764919] using wordTrace_append hprefix tailTrace_2764919
  have hstable : (prefixWord ++ tailWord_2764919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764919).length < 2 ^ (prefixWord ++ tailWord_2764919).sum := by decide
  have hdescent : baseEnd_2764919 < baseStart_2764919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764945 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2764945 : Nat := 118140960795 + 2764945 * 2 ^ 59
def prefixEnd_2764945 : Nat := 4983230072969 + 3 ^ 40 * 2764945 * 2
def baseEnd_2764945 : Nat := 1419745768245789873671755

theorem tailTrace_2764945 : CollatzResearch.WordTrace tailWord_2764945 prefixEnd_2764945 1419745768245789873671755 := by
  unfold tailWord_2764945
  simp only [CollatzResearch.WordTrace]
  refine ⟨100845828968083954856152289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67230552645389303237434859 100845828968083954856152289)
  ·
    refine ⟨75634371726062966142114217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100845828968083954856152289 75634371726062966142114217)
    ·
      refine ⟨56725778794547224606585663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75634371726062966142114217 56725778794547224606585663)
      ·
        refine ⟨85088668191820836909878495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56725778794547224606585663 85088668191820836909878495)
        ·
          refine ⟨127633002287731255364817743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85088668191820836909878495 127633002287731255364817743)
          ·
            refine ⟨191449503431596883047226615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127633002287731255364817743 191449503431596883047226615)
            ·
              refine ⟨287174255147395324570839923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191449503431596883047226615 287174255147395324570839923)
              ·
                refine ⟨430761382721092986856259885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287174255147395324570839923 430761382721092986856259885)
                ·
                  refine ⟨161535518520409870071097457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430761382721092986856259885 161535518520409870071097457)
                  ·
                    refine ⟨121151638890307402553323093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161535518520409870071097457 121151638890307402553323093)
                    ·
                      refine ⟨1419745768245789873671755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121151638890307402553323093 1419745768245789873671755)
                      ·
                        rfl

theorem cell23_2764945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2764945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764945 prefixEnd_2764945 := by exact prefixLift 2764945
  have htrace : WordTrace (prefixWord ++ tailWord_2764945) baseStart_2764945 baseEnd_2764945 := by
    simpa [prefixWord, tailWord_2764945, baseEnd_2764945] using wordTrace_append hprefix tailTrace_2764945
  have hstable : (prefixWord ++ tailWord_2764945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764945).length < 2 ^ (prefixWord ++ tailWord_2764945).sum := by decide
  have hdescent : baseEnd_2764945 < baseStart_2764945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 8]
def baseStart_2764955 : Nat := 118140960795 + 2764955 * 2 ^ 59
def prefixEnd_2764955 : Nat := 4983230072969 + 3 ^ 40 * 2764955 * 2
def baseEnd_2764955 : Nat := 473250301017444944848903

theorem tailTrace_2764955 : CollatzResearch.WordTrace tailWord_2764955 prefixEnd_2764955 473250301017444944848903 := by
  unfold tailWord_2764955
  simp only [CollatzResearch.WordTrace]
  refine ⟨100846193698047726564016319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67230795798698484376010879 100846193698047726564016319)
  ·
    refine ⟨151269290547071589846024479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100846193698047726564016319 151269290547071589846024479)
    ·
      refine ⟨226903935820607384769036719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151269290547071589846024479 226903935820607384769036719)
      ·
        refine ⟨340355903730911077153555079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226903935820607384769036719 340355903730911077153555079)
        ·
          refine ⟨510533855596366615730332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340355903730911077153555079 510533855596366615730332619)
          ·
            refine ⟨765800783394549923595498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510533855596366615730332619 765800783394549923595498929)
            ·
              refine ⟨574350587545912442696624197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765800783394549923595498929 574350587545912442696624197)
              ·
                refine ⟨107690735164858583005617037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574350587545912442696624197 107690735164858583005617037)
                ·
                  refine ⟨40384025686821968627106389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107690735164858583005617037 40384025686821968627106389)
                  ·
                    refine ⟨473250301017444944848903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40384025686821968627106389 473250301017444944848903)
                    ·
                      rfl

theorem cell23_2764955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_2764955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764955 prefixEnd_2764955 := by exact prefixLift 2764955
  have htrace : WordTrace (prefixWord ++ tailWord_2764955) baseStart_2764955 baseEnd_2764955 := by
    simpa [prefixWord, tailWord_2764955, baseEnd_2764955] using wordTrace_append hprefix tailTrace_2764955
  have hstable : (prefixWord ++ tailWord_2764955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764955).length < 2 ^ (prefixWord ++ tailWord_2764955).sum := by decide
  have hdescent : baseEnd_2764955 < baseStart_2764955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764956 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2764956 : Nat := 118140960795 + 2764956 * 2 ^ 59
def prefixEnd_2764956 : Nat := 4983230072969 + 3 ^ 40 * 2764956 * 2
def baseEnd_2764956 : Nat := 1419751416532989330634205

theorem tailTrace_2764956 : CollatzResearch.WordTrace tailWord_2764956 prefixEnd_2764956 1419751416532989330634205 := by
  unfold tailWord_2764956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50423115085522051867401361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67230820114029402489868481 50423115085522051867401361)
  ·
    refine ⟨37817336314141538900551021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50423115085522051867401361 37817336314141538900551021)
    ·
      refine ⟨14181501117803077087706633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37817336314141538900551021 14181501117803077087706633)
      ·
        refine ⟨10636125838352307815779975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14181501117803077087706633 10636125838352307815779975)
        ·
          refine ⟨15954188757528461723669963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10636125838352307815779975 15954188757528461723669963)
          ·
            refine ⟨23931283136292692585504945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15954188757528461723669963 23931283136292692585504945)
            ·
              refine ⟨17948462352219519439128709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23931283136292692585504945 17948462352219519439128709)
              ·
                refine ⟨3365336691041159894836633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17948462352219519439128709 3365336691041159894836633)
                ·
                  refine ⟨2524002518280869921127475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365336691041159894836633 2524002518280869921127475)
                  ·
                    refine ⟨3786003777421304881691213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524002518280869921127475 3786003777421304881691213)
                    ·
                      refine ⟨1419751416532989330634205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786003777421304881691213 1419751416532989330634205)
                      ·
                        rfl

theorem cell23_2764956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2764956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764956 prefixEnd_2764956 := by exact prefixLift 2764956
  have htrace : WordTrace (prefixWord ++ tailWord_2764956) baseStart_2764956 baseEnd_2764956 := by
    simpa [prefixWord, tailWord_2764956, baseEnd_2764956] using wordTrace_append hprefix tailTrace_2764956
  have hstable : (prefixWord ++ tailWord_2764956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764956).length < 2 ^ (prefixWord ++ tailWord_2764956).sum := by decide
  have hdescent : baseEnd_2764956 < baseStart_2764956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764973 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2764973 : Nat := 118140960795 + 2764973 * 2 ^ 59
def prefixEnd_2764973 : Nat := 4983230072969 + 3 ^ 40 * 2764973 * 2
def baseEnd_2764973 : Nat := 1419760145704115764121627

theorem tailTrace_2764973 : CollatzResearch.WordTrace tailWord_2764973 prefixEnd_2764973 1419760145704115764121627 := by
  unfold tailWord_2764973
  simp only [CollatzResearch.WordTrace]
  refine ⟨100846850211982515638171573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67231233474655010425447715 100846850211982515638171573)
  ·
    refine ⟨9454392207373360841078585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100846850211982515638171573 9454392207373360841078585)
    ·
      refine ⟨7090794155530020630808939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9454392207373360841078585 7090794155530020630808939)
      ·
        refine ⟨10636191233295030946213409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090794155530020630808939 10636191233295030946213409)
        ·
          refine ⟨7977143424971273209660057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10636191233295030946213409 7977143424971273209660057)
          ·
            refine ⟨5982857568728454907245043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7977143424971273209660057 5982857568728454907245043)
            ·
              refine ⟨8974286353092682360867565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982857568728454907245043 8974286353092682360867565)
              ·
                refine ⟨3365357382409755885325337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8974286353092682360867565 3365357382409755885325337)
                ·
                  refine ⟨2524018036807316913994003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365357382409755885325337 2524018036807316913994003)
                  ·
                    refine ⟨3786027055210975370991005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524018036807316913994003 3786027055210975370991005)
                    ·
                      refine ⟨1419760145704115764121627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786027055210975370991005 1419760145704115764121627)
                      ·
                        rfl

theorem cell23_2764973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2764973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764973 prefixEnd_2764973 := by exact prefixLift 2764973
  have htrace : WordTrace (prefixWord ++ tailWord_2764973) baseStart_2764973 baseEnd_2764973 := by
    simpa [prefixWord, tailWord_2764973, baseEnd_2764973] using wordTrace_append hprefix tailTrace_2764973
  have hstable : (prefixWord ++ tailWord_2764973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764973).length < 2 ^ (prefixWord ++ tailWord_2764973).sum := by decide
  have hdescent : baseEnd_2764973 < baseStart_2764973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764979 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 4, 2]
def baseStart_2764979 : Nat := 118140960795 + 2764979 * 2 ^ 59
def prefixEnd_2764979 : Nat := 4983230072969 + 3 ^ 40 * 2764979 * 2
def baseEnd_2764979 : Nat := 1419763226588042740646599

theorem tailTrace_2764979 : CollatzResearch.WordTrace tailWord_2764979 prefixEnd_2764979 1419763226588042740646599 := by
  unfold tailWord_2764979
  simp only [CollatzResearch.WordTrace]
  refine ⟨100847069049960778662889991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67231379366640519108593327 100847069049960778662889991)
  ·
    refine ⟨151270603574941167994334987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100847069049960778662889991 151270603574941167994334987)
    ·
      refine ⟨226905905362411751991502481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151270603574941167994334987 226905905362411751991502481)
      ·
        refine ⟨170179429021808813993626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226905905362411751991502481 170179429021808813993626861)
        ·
          refine ⟨63817285883178305247610073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170179429021808813993626861 63817285883178305247610073)
          ·
            refine ⟨47862964412383728935707555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63817285883178305247610073 47862964412383728935707555)
            ·
              refine ⟨71794446618575593403561333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47862964412383728935707555 71794446618575593403561333)
              ·
                refine ⟨6730729370491461881583875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71794446618575593403561333 6730729370491461881583875)
                ·
                  refine ⟨10096094055737192822375813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730729370491461881583875 10096094055737192822375813)
                  ·
                    refine ⟨1893017635450723654195465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10096094055737192822375813 1893017635450723654195465)
                    ·
                      refine ⟨1419763226588042740646599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893017635450723654195465 1419763226588042740646599)
                      ·
                        rfl

theorem cell23_2764979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4, 2].length) (baseStart_2764979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764979 prefixEnd_2764979 := by exact prefixLift 2764979
  have htrace : WordTrace (prefixWord ++ tailWord_2764979) baseStart_2764979 baseEnd_2764979 := by
    simpa [prefixWord, tailWord_2764979, baseEnd_2764979] using wordTrace_append hprefix tailTrace_2764979
  have hstable : (prefixWord ++ tailWord_2764979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764979).length < 2 ^ (prefixWord ++ tailWord_2764979).sum := by decide
  have hdescent : baseEnd_2764979 < baseStart_2764979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764983 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_2764983 : Nat := 118140960795 + 2764983 * 2 ^ 59
def prefixEnd_2764983 : Nat := 4983230072969 + 3 ^ 40 * 2764983 * 2
def baseEnd_2764983 : Nat := 1419765280510660724996581

theorem tailTrace_2764983 : CollatzResearch.WordTrace tailWord_2764983 prefixEnd_2764983 1419765280510660724996581 := by
  unfold tailWord_2764983
  simp only [CollatzResearch.WordTrace]
  refine ⟨100847214941946287346035603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67231476627964191564023735 100847214941946287346035603)
  ·
    refine ⟨151270822412919431019053405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100847214941946287346035603 151270822412919431019053405)
    ·
      refine ⟨56726558404844786632145027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151270822412919431019053405 56726558404844786632145027)
      ·
        refine ⟨85089837607267179948217541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56726558404844786632145027 85089837607267179948217541)
        ·
          refine ⟨15954344551362596240290789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85089837607267179948217541 15954344551362596240290789)
          ·
            refine ⟨2991439603380486795054523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15954344551362596240290789 2991439603380486795054523)
            ·
              refine ⟨4487159405070730192581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991439603380486795054523 4487159405070730192581785)
              ·
                refine ⟨3365369553803047644436339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487159405070730192581785 3365369553803047644436339)
                ·
                  refine ⟨5048054330704571466654509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365369553803047644436339 5048054330704571466654509)
                  ·
                    refine ⟨1893020374014214299995441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5048054330704571466654509 1893020374014214299995441)
                    ·
                      refine ⟨1419765280510660724996581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893020374014214299995441 1419765280510660724996581)
                      ·
                        rfl

theorem cell23_2764983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_2764983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764983 prefixEnd_2764983 := by exact prefixLift 2764983
  have htrace : WordTrace (prefixWord ++ tailWord_2764983) baseStart_2764983 baseEnd_2764983 := by
    simpa [prefixWord, tailWord_2764983, baseEnd_2764983] using wordTrace_append hprefix tailTrace_2764983
  have hstable : (prefixWord ++ tailWord_2764983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764983).length < 2 ^ (prefixWord ++ tailWord_2764983).sum := by decide
  have hdescent : baseEnd_2764983 < baseStart_2764983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764996 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2764996 : Nat := 118140960795 + 2764996 * 2 ^ 59
def prefixEnd_2764996 : Nat := 4983230072969 + 3 ^ 40 * 2764996 * 2
def baseEnd_2764996 : Nat := 1419771955759169174134021

theorem tailTrace_2764996 : CollatzResearch.WordTrace tailWord_2764996 prefixEnd_2764996 1419771955759169174134021 := by
  unfold tailWord_2764996
  simp only [CollatzResearch.WordTrace]
  refine ⟨50423844545449595283129421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67231792727266127044172561 50423844545449595283129421)
  ·
    refine ⟨18908941704543598231173533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50423844545449595283129421 18908941704543598231173533)
    ·
      refine ⟨7090853139203849336690075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18908941704543598231173533 7090853139203849336690075)
      ·
        refine ⟨10636279708805774005035113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090853139203849336690075 10636279708805774005035113)
        ·
          refine ⟨7977209781604330503776335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10636279708805774005035113 7977209781604330503776335)
          ·
            refine ⟨11965814672406495755664503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977209781604330503776335 11965814672406495755664503)
            ·
              refine ⟨17948722008609743633496755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965814672406495755664503 17948722008609743633496755)
              ·
                refine ⟨26923083012914615450245133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17948722008609743633496755 26923083012914615450245133)
                ·
                  refine ⟨10096156129842980793841925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26923083012914615450245133 10096156129842980793841925)
                  ·
                    refine ⟨1893029274345558898845361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10096156129842980793841925 1893029274345558898845361)
                    ·
                      refine ⟨1419771955759169174134021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893029274345558898845361 1419771955759169174134021)
                      ·
                        rfl

theorem cell23_2764996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2764996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2764996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2764996 prefixEnd_2764996 := by exact prefixLift 2764996
  have htrace : WordTrace (prefixWord ++ tailWord_2764996) baseStart_2764996 baseEnd_2764996 := by
    simpa [prefixWord, tailWord_2764996, baseEnd_2764996] using wordTrace_append hprefix tailTrace_2764996
  have hstable : (prefixWord ++ tailWord_2764996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764996).length < 2 ^ (prefixWord ++ tailWord_2764996).sum := by decide
  have hdescent : baseEnd_2764996 < baseStart_2764996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765029 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2765029 : Nat := 118140960795 + 2765029 * 2 ^ 59
def prefixEnd_2765029 : Nat := 4983230072969 + 3 ^ 40 * 2765029 * 2
def baseEnd_2765029 : Nat := 1419788900620767545021369

theorem tailTrace_2765029 : CollatzResearch.WordTrace tailWord_2765029 prefixEnd_2765029 1419788900620767545021369 := by
  unfold tailWord_2765029
  simp only [CollatzResearch.WordTrace]
  refine ⟨100848892699779637202210141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67232595133186424801473427 100848892699779637202210141)
  ·
    refine ⟨37818334762417363950828803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100848892699779637202210141 37818334762417363950828803)
    ·
      refine ⟨56727502143626045926243205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37818334762417363950828803 56727502143626045926243205)
      ·
        refine ⟨10636406651929883611170601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56727502143626045926243205 10636406651929883611170601)
        ·
          refine ⟨7977304988947412708377951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10636406651929883611170601 7977304988947412708377951)
          ·
            refine ⟨11965957483421119062566927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7977304988947412708377951 11965957483421119062566927)
            ·
              refine ⟨17948936225131678593850391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965957483421119062566927 17948936225131678593850391)
              ·
                refine ⟨26923404337697517890775587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17948936225131678593850391 26923404337697517890775587)
                ·
                  refine ⟨40385106506546276836163381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26923404337697517890775587 40385106506546276836163381)
                  ·
                    refine ⟨3786103734988713453390317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40385106506546276836163381 3786103734988713453390317)
                    ·
                      refine ⟨1419788900620767545021369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786103734988713453390317 1419788900620767545021369)
                      ·
                        rfl

theorem cell23_2765029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2765029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765029 prefixEnd_2765029 := by exact prefixLift 2765029
  have htrace : WordTrace (prefixWord ++ tailWord_2765029) baseStart_2765029 baseEnd_2765029 := by
    simpa [prefixWord, tailWord_2765029, baseEnd_2765029] using wordTrace_append hprefix tailTrace_2765029
  have hstable : (prefixWord ++ tailWord_2765029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765029).length < 2 ^ (prefixWord ++ tailWord_2765029).sum := by decide
  have hdescent : baseEnd_2765029 < baseStart_2765029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765089 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2765089 : Nat := 118140960795 + 2765089 * 2 ^ 59
def prefixEnd_2765089 : Nat := 4983230072969 + 3 ^ 40 * 2765089 * 2
def baseEnd_2765089 : Nat := 1419819709460037310271093

theorem tailTrace_2765089 : CollatzResearch.WordTrace tailWord_2765089 prefixEnd_2765089 1419819709460037310271093 := by
  unfold tailWord_2765089
  simp only [CollatzResearch.WordTrace]
  refine ⟨100851081079562267449394321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67234054053041511632929547 100851081079562267449394321)
  ·
    refine ⟨75638310809671700587045741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100851081079562267449394321 75638310809671700587045741)
    ·
      refine ⟨28364366553626887720142153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75638310809671700587045741 28364366553626887720142153)
      ·
        refine ⟨21273274915220165790106615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28364366553626887720142153 21273274915220165790106615)
        ·
          refine ⟨31909912372830248685159923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21273274915220165790106615 31909912372830248685159923)
          ·
            refine ⟨47864868559245373027739885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31909912372830248685159923 47864868559245373027739885)
            ·
              refine ⟨17949325709717014885402457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47864868559245373027739885 17949325709717014885402457)
              ·
                refine ⟨13461994282287761164051843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17949325709717014885402457 13461994282287761164051843)
                ·
                  refine ⟨20192991423431641746077765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13461994282287761164051843 20192991423431641746077765)
                  ·
                    refine ⟨3786185891893432827389581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20192991423431641746077765 3786185891893432827389581)
                    ·
                      refine ⟨1419819709460037310271093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786185891893432827389581 1419819709460037310271093)
                      ·
                        rfl

theorem cell23_2765089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2765089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765089 prefixEnd_2765089 := by exact prefixLift 2765089
  have htrace : WordTrace (prefixWord ++ tailWord_2765089) baseStart_2765089 baseEnd_2765089 := by
    simpa [prefixWord, tailWord_2765089, baseEnd_2765089] using wordTrace_append hprefix tailTrace_2765089
  have hstable : (prefixWord ++ tailWord_2765089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765089).length < 2 ^ (prefixWord ++ tailWord_2765089).sum := by decide
  have hdescent : baseEnd_2765089 < baseStart_2765089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765146 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_2765146 : Nat := 118140960795 + 2765146 * 2 ^ 59
def prefixEnd_2765146 : Nat := 4983230072969 + 3 ^ 40 * 2765146 * 2
def baseEnd_2765146 : Nat := 1419848977857343587258331

theorem tailTrace_2765146 : CollatzResearch.WordTrace tailWord_2765146 prefixEnd_2765146 1419848977857343587258331 := by
  unfold tailWord_2765146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25213290010088941546054823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67235440026903844122812861 25213290010088941546054823)
  ·
    refine ⟨37819935015133412319082235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25213290010088941546054823 37819935015133412319082235)
    ·
      refine ⟨56729902522700118478623353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37819935015133412319082235 56729902522700118478623353)
      ·
        refine ⟨42547426892025088858967515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56729902522700118478623353 42547426892025088858967515)
        ·
          refine ⟨63821140338037633288451273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42547426892025088858967515 63821140338037633288451273)
          ·
            refine ⟨47865855253528224966338455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63821140338037633288451273 47865855253528224966338455)
            ·
              refine ⟨71798782880292337449507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47865855253528224966338455 71798782880292337449507683)
              ·
                refine ⟨107698174320438506174261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71798782880292337449507683 107698174320438506174261525)
                ·
                  refine ⟨5048351921270554976918509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107698174320438506174261525 5048351921270554976918509)
                  ·
                    refine ⟨1893131970476458116344441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5048351921270554976918509 1893131970476458116344441)
                    ·
                      refine ⟨1419848977857343587258331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893131970476458116344441 1419848977857343587258331)
                      ·
                        rfl

theorem cell23_2765146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_2765146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765146 prefixEnd_2765146 := by exact prefixLift 2765146
  have htrace : WordTrace (prefixWord ++ tailWord_2765146) baseStart_2765146 baseEnd_2765146 := by
    simpa [prefixWord, tailWord_2765146, baseEnd_2765146] using wordTrace_append hprefix tailTrace_2765146
  have hstable : (prefixWord ++ tailWord_2765146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765146).length < 2 ^ (prefixWord ++ tailWord_2765146).sum := by decide
  have hdescent : baseEnd_2765146 < baseStart_2765146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765189 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_2765189 : Nat := 118140960795 + 2765189 * 2 ^ 59
def prefixEnd_2765189 : Nat := 4983230072969 + 3 ^ 40 * 2765189 * 2
def baseEnd_2765189 : Nat := 1419871057525486919020633

theorem tailTrace_2765189 : CollatzResearch.WordTrace tailWord_2765189 prefixEnd_2765189 1419871057525486919020633 := by
  unfold tailWord_2765189
  simp only [CollatzResearch.WordTrace]
  refine ⟨100854728379199984528034621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67236485586133323018689747 100854728379199984528034621)
  ·
    refine ⟨37820523142199994198012983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100854728379199984528034621 37820523142199994198012983)
    ·
      refine ⟨56730784713299991297019475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37820523142199994198012983 56730784713299991297019475)
      ·
        refine ⟨85096177069949986945529213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56730784713299991297019475 85096177069949986945529213)
        ·
          refine ⟨31911066401231245104573455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85096177069949986945529213 31911066401231245104573455)
          ·
            refine ⟨47866599601846867656860183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31911066401231245104573455 47866599601846867656860183)
            ·
              refine ⟨71799899402770301485290275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47866599601846867656860183 71799899402770301485290275)
              ·
                refine ⟨107699849104155452227935413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71799899402770301485290275 107699849104155452227935413)
                ·
                  refine ⟨10096860853514573646368945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107699849104155452227935413 10096860853514573646368945)
                  ·
                    refine ⟨7572645640135930234776709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10096860853514573646368945 7572645640135930234776709)
                    ·
                      refine ⟨1419871057525486919020633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7572645640135930234776709 1419871057525486919020633)
                      ·
                        rfl

theorem cell23_2765189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_2765189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765189 prefixEnd_2765189 := by exact prefixLift 2765189
  have htrace : WordTrace (prefixWord ++ tailWord_2765189) baseStart_2765189 baseEnd_2765189 := by
    simpa [prefixWord, tailWord_2765189, baseEnd_2765189] using wordTrace_append hprefix tailTrace_2765189
  have hstable : (prefixWord ++ tailWord_2765189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765189).length < 2 ^ (prefixWord ++ tailWord_2765189).sum := by decide
  have hdescent : baseEnd_2765189 < baseStart_2765189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765196 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2765196 : Nat := 118140960795 + 2765196 * 2 ^ 59
def prefixEnd_2765196 : Nat := 4983230072969 + 3 ^ 40 * 2765196 * 2
def baseEnd_2765196 : Nat := 1419874651890068391633101

theorem tailTrace_2765196 : CollatzResearch.WordTrace tailWord_2765196 prefixEnd_2765196 1419874651890068391633101 := by
  unfold tailWord_2765196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50427491845087312361769721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67236655793449749815692961 50427491845087312361769721)
  ·
    refine ⟨37820618883815484271327291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50427491845087312361769721 37820618883815484271327291)
    ·
      refine ⟨56730928325723226406990937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37820618883815484271327291 56730928325723226406990937)
      ·
        refine ⟨42548196244292419805243203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56730928325723226406990937 42548196244292419805243203)
        ·
          refine ⟨63822294366438629707864805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42548196244292419805243203 63822294366438629707864805)
          ·
            refine ⟨11966680193707243070224651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63822294366438629707864805 11966680193707243070224651)
            ·
              refine ⟨17950020290560864605336977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11966680193707243070224651 17950020290560864605336977)
              ·
                refine ⟨13462515217920648454002733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17950020290560864605336977 13462515217920648454002733)
                ·
                  refine ⟨5048443206720243170251025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13462515217920648454002733 5048443206720243170251025)
                  ·
                    refine ⟨3786332405040182377688269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048443206720243170251025 3786332405040182377688269)
                    ·
                      refine ⟨1419874651890068391633101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786332405040182377688269 1419874651890068391633101)
                      ·
                        rfl

theorem cell23_2765196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2765196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765196 prefixEnd_2765196 := by exact prefixLift 2765196
  have htrace : WordTrace (prefixWord ++ tailWord_2765196) baseStart_2765196 baseEnd_2765196 := by
    simpa [prefixWord, tailWord_2765196, baseEnd_2765196] using wordTrace_append hprefix tailTrace_2765196
  have hstable : (prefixWord ++ tailWord_2765196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765196).length < 2 ^ (prefixWord ++ tailWord_2765196).sum := by decide
  have hdescent : baseEnd_2765196 < baseStart_2765196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765210 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2765210 : Nat := 118140960795 + 2765210 * 2 ^ 59
def prefixEnd_2765210 : Nat := 4983230072969 + 3 ^ 40 * 2765210 * 2
def baseEnd_2765210 : Nat := 1419881840619231336858037

theorem tailTrace_2765210 : CollatzResearch.WordTrace tailWord_2765210 prefixEnd_2765210 1419881840619231336858037 := by
  unfold tailWord_2765210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25213873578030976278637271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67236996208082603409699389 25213873578030976278637271)
  ·
    refine ⟨37820810367046464417955907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25213873578030976278637271 37820810367046464417955907)
    ·
      refine ⟨56731215550569696626933861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37820810367046464417955907 56731215550569696626933861)
      ·
        refine ⟨10637102915731818117550099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56731215550569696626933861 10637102915731818117550099)
        ·
          refine ⟨15955654373597727176325149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637102915731818117550099 15955654373597727176325149)
          ·
            refine ⟨5983370390099147691121931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15955654373597727176325149 5983370390099147691121931)
            ·
              refine ⟨8975055585148721536682897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983370390099147691121931 8975055585148721536682897)
              ·
                refine ⟨6731291688861541152512173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975055585148721536682897 6731291688861541152512173)
                ·
                  refine ⟨2524234383323077932192065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6731291688861541152512173 2524234383323077932192065)
                  ·
                    refine ⟨1893175787492308449144049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524234383323077932192065 1893175787492308449144049)
                    ·
                      refine ⟨1419881840619231336858037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893175787492308449144049 1419881840619231336858037)
                      ·
                        rfl

theorem cell23_2765210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2765210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765210 prefixEnd_2765210 := by exact prefixLift 2765210
  have htrace : WordTrace (prefixWord ++ tailWord_2765210) baseStart_2765210 baseEnd_2765210 := by
    simpa [prefixWord, tailWord_2765210, baseEnd_2765210] using wordTrace_append hprefix tailTrace_2765210
  have hstable : (prefixWord ++ tailWord_2765210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765210).length < 2 ^ (prefixWord ++ tailWord_2765210).sum := by decide
  have hdescent : baseEnd_2765210 < baseStart_2765210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765216 : List Nat := [2, 1, 1, 4, 1, 4, 3, 7]
def baseStart_2765216 : Nat := 118140960795 + 2765216 * 2 ^ 59
def prefixEnd_2765216 : Nat := 4983230072969 + 3 ^ 40 * 2765216 * 2
def baseEnd_2765216 : Nat := 52588330426042900495667

theorem tailTrace_2765216 : CollatzResearch.WordTrace tailWord_2765216 prefixEnd_2765216 52588330426042900495667 := by
  unfold tailWord_2765216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50427856575051084069633751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67237142100068112092845001 50427856575051084069633751)
  ·
    refine ⟨75641784862576626104450627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50427856575051084069633751 75641784862576626104450627)
    ·
      refine ⟨113462677293864939156675941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75641784862576626104450627 113462677293864939156675941)
      ·
        refine ⟨21274251992599676091876739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113462677293864939156675941 21274251992599676091876739)
        ·
          refine ⟨31911377988899514137815109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21274251992599676091876739 31911377988899514137815109)
          ·
            refine ⟨5983383372918658900840333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31911377988899514137815109 5983383372918658900840333)
            ·
              refine ⟨2243768764844497087815125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5983383372918658900840333 2243768764844497087815125)
              ·
                refine ⟨52588330426042900495667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2243768764844497087815125 52588330426042900495667)
                ·
                  rfl

theorem cell23_2765216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 7].length) (baseStart_2765216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765216 prefixEnd_2765216 := by exact prefixLift 2765216
  have htrace : WordTrace (prefixWord ++ tailWord_2765216) baseStart_2765216 baseEnd_2765216 := by
    simpa [prefixWord, tailWord_2765216, baseEnd_2765216] using wordTrace_append hprefix tailTrace_2765216
  have hstable : (prefixWord ++ tailWord_2765216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765216).length < 2 ^ (prefixWord ++ tailWord_2765216).sum := by decide
  have hdescent : baseEnd_2765216 < baseStart_2765216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765237 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2765237 : Nat := 118140960795 + 2765237 * 2 ^ 59
def prefixEnd_2765237 : Nat := 4983230072969 + 3 ^ 40 * 2765237 * 2
def baseEnd_2765237 : Nat := 473298568198967577073471

theorem tailTrace_2765237 : CollatzResearch.WordTrace tailWord_2765237 prefixEnd_2765237 473298568198967577073471 := by
  unfold tailWord_2765237
  simp only [CollatzResearch.WordTrace]
  refine ⟨100856479083026088725781965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67237652722017392483854643 100856479083026088725781965)
  ·
    refine ⟨37821179656134783272168237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100856479083026088725781965 37821179656134783272168237)
    ·
      refine ⟨14182942371050543727063089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37821179656134783272168237 14182942371050543727063089)
      ·
        refine ⟨10637206778287907795297317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14182942371050543727063089 10637206778287907795297317)
        ·
          refine ⟨1994476270928982711618247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10637206778287907795297317 1994476270928982711618247)
          ·
            refine ⟨2991714406393474067427371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994476270928982711618247 2991714406393474067427371)
            ·
              refine ⟨4487571609590211101141057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991714406393474067427371 4487571609590211101141057)
              ·
                refine ⟨3365678707192658325855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487571609590211101141057 3365678707192658325855793)
                ·
                  refine ⟨2524259030394493744391845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365678707192658325855793 2524259030394493744391845)
                  ·
                    refine ⟨473298568198967577073471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524259030394493744391845 473298568198967577073471)
                    ·
                      rfl

theorem cell23_2765237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2765237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765237 prefixEnd_2765237 := by exact prefixLift 2765237
  have htrace : WordTrace (prefixWord ++ tailWord_2765237) baseStart_2765237 baseEnd_2765237 := by
    simpa [prefixWord, tailWord_2765237, baseEnd_2765237] using wordTrace_append hprefix tailTrace_2765237
  have hstable : (prefixWord ++ tailWord_2765237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765237).length < 2 ^ (prefixWord ++ tailWord_2765237).sum := by decide
  have hdescent : baseEnd_2765237 < baseStart_2765237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765260 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2765260 : Nat := 118140960795 + 2765260 * 2 ^ 59
def prefixEnd_2765260 : Nat := 4983230072969 + 3 ^ 40 * 2765260 * 2
def baseEnd_2765260 : Nat := 1419907514651956141232807

theorem tailTrace_2765260 : CollatzResearch.WordTrace tailWord_2765260 prefixEnd_2765260 1419907514651956141232807 := by
  unfold tailWord_2765260
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428658980971381826934617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67238211974628509102579489 50428658980971381826934617)
  ·
    refine ⟨37821494235728536370200963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50428658980971381826934617 37821494235728536370200963)
    ·
      refine ⟨56732241353592804555301445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37821494235728536370200963 56732241353592804555301445)
      ·
        refine ⟨10637295253798650854119021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56732241353592804555301445 10637295253798650854119021)
        ·
          refine ⟨3988985720174494070294633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10637295253798650854119021 3988985720174494070294633)
          ·
            refine ⟨2991739290130870552720975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988985720174494070294633 2991739290130870552720975)
            ·
              refine ⟨4487608935196305829081463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991739290130870552720975 4487608935196305829081463)
              ·
                refine ⟨6731413402794458743622195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487608935196305829081463 6731413402794458743622195)
                ·
                  refine ⟨10097120104191688115433293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731413402794458743622195 10097120104191688115433293)
                  ·
                    refine ⟨3786420039071883043287485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10097120104191688115433293 3786420039071883043287485)
                    ·
                      refine ⟨1419907514651956141232807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786420039071883043287485 1419907514651956141232807)
                      ·
                        rfl

theorem cell23_2765260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2765260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765260 prefixEnd_2765260 := by exact prefixLift 2765260
  have htrace : WordTrace (prefixWord ++ tailWord_2765260) baseStart_2765260 baseEnd_2765260 := by
    simpa [prefixWord, tailWord_2765260, baseEnd_2765260] using wordTrace_append hprefix tailTrace_2765260
  have hstable : (prefixWord ++ tailWord_2765260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765260).length < 2 ^ (prefixWord ++ tailWord_2765260).sum := by decide
  have hdescent : baseEnd_2765260 < baseStart_2765260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765299 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_2765299 : Nat := 118140960795 + 2765299 * 2 ^ 59
def prefixEnd_2765299 : Nat := 4983230072969 + 3 ^ 40 * 2765299 * 2
def baseEnd_2765299 : Nat := 1419927540397481488645127

theorem tailTrace_2765299 : CollatzResearch.WordTrace tailWord_2765299 prefixEnd_2765299 1419927540397481488645127 := by
  unfold tailWord_2765299
  simp only [CollatzResearch.WordTrace]
  refine ⟨100858740408801473314538951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67239160272534315543025967 100858740408801473314538951)
  ·
    refine ⟨151288110613202209971808427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100858740408801473314538951 151288110613202209971808427)
    ·
      refine ⟨226932165919803314957712641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151288110613202209971808427 226932165919803314957712641)
      ·
        refine ⟨170199124439852486218284481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226932165919803314957712641 170199124439852486218284481)
        ·
          refine ⟨127649343329889364663713361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170199124439852486218284481 127649343329889364663713361)
          ·
            refine ⟨95737007497417023497785021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127649343329889364663713361 95737007497417023497785021)
            ·
              refine ⟨35901377811531383811669383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95737007497417023497785021 35901377811531383811669383)
              ·
                refine ⟨53852066717297075717504075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35901377811531383811669383 53852066717297075717504075)
                ·
                  refine ⟨80778100075945613576256113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53852066717297075717504075 80778100075945613576256113)
                  ·
                    refine ⟨60583575056959210182192085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80778100075945613576256113 60583575056959210182192085)
                    ·
                      refine ⟨1419927540397481488645127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60583575056959210182192085 1419927540397481488645127)
                      ·
                        rfl

theorem cell23_2765299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_2765299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765299 prefixEnd_2765299 := by exact prefixLift 2765299
  have htrace : WordTrace (prefixWord ++ tailWord_2765299) baseStart_2765299 baseEnd_2765299 := by
    simpa [prefixWord, tailWord_2765299, baseEnd_2765299] using wordTrace_append hprefix tailTrace_2765299
  have hstable : (prefixWord ++ tailWord_2765299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765299).length < 2 ^ (prefixWord ++ tailWord_2765299).sum := by decide
  have hdescent : baseEnd_2765299 < baseStart_2765299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765317 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_2765317 : Nat := 118140960795 + 2765317 * 2 ^ 59
def prefixEnd_2765317 : Nat := 4983230072969 + 3 ^ 40 * 2765317 * 2
def baseEnd_2765317 : Nat := 1419936783049262418220045

theorem tailTrace_2765317 : CollatzResearch.WordTrace tailWord_2765317 prefixEnd_2765317 1419936783049262418220045 := by
  unfold tailWord_2765317
  simp only [CollatzResearch.WordTrace]
  refine ⟨100859396922736262388694205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67239597948490841592462803 100859396922736262388694205)
  ·
    refine ⟨37822273846026098395760327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100859396922736262388694205 37822273846026098395760327)
    ·
      refine ⟨56733410769039147593640491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37822273846026098395760327 56733410769039147593640491)
      ·
        refine ⟨85100116153558721390460737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56733410769039147593640491 85100116153558721390460737)
        ·
          refine ⟨63825087115169041042845553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85100116153558721390460737 63825087115169041042845553)
          ·
            refine ⟨47868815336376780782134165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63825087115169041042845553 47868815336376780782134165)
            ·
              refine ⟨2243850718892661599162539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47868815336376780782134165 2243850718892661599162539)
              ·
                refine ⟨3365776078338992398743809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243850718892661599162539 3365776078338992398743809)
                ·
                  refine ⟨2524332058754244299057857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365776078338992398743809 2524332058754244299057857)
                  ·
                    refine ⟨1893249044065683224293393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524332058754244299057857 1893249044065683224293393)
                    ·
                      refine ⟨1419936783049262418220045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893249044065683224293393 1419936783049262418220045)
                      ·
                        rfl

theorem cell23_2765317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_2765317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765317 prefixEnd_2765317 := by exact prefixLift 2765317
  have htrace : WordTrace (prefixWord ++ tailWord_2765317) baseStart_2765317 baseEnd_2765317 := by
    simpa [prefixWord, tailWord_2765317, baseEnd_2765317] using wordTrace_append hprefix tailTrace_2765317
  have hstable : (prefixWord ++ tailWord_2765317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765317).length < 2 ^ (prefixWord ++ tailWord_2765317).sum := by decide
  have hdescent : baseEnd_2765317 < baseStart_2765317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765351 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2765351 : Nat := 118140960795 + 2765351 * 2 ^ 59
def prefixEnd_2765351 : Nat := 4983230072969 + 3 ^ 40 * 2765351 * 2
def baseEnd_2765351 : Nat := 1419954241391515285194889

theorem tailTrace_2765351 : CollatzResearch.WordTrace tailWord_2765351 prefixEnd_2765351 1419954241391515285194889 := by
  unfold tailWord_2765351
  simp only [CollatzResearch.WordTrace]
  refine ⟨100860637004613086195431907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67240424669742057463621271 100860637004613086195431907)
  ·
    refine ⟨151290955506919629293147861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100860637004613086195431907 151290955506919629293147861)
    ·
      refine ⟨3545881769693428811558153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 151290955506919629293147861 3545881769693428811558153)
      ·
        refine ⟨2659411327270071608668615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545881769693428811558153 2659411327270071608668615)
        ·
          refine ⟨3989116990905107413002923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659411327270071608668615 3989116990905107413002923)
          ·
            refine ⟨5983675486357661119504385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989116990905107413002923 5983675486357661119504385)
            ·
              refine ⟨4487756614768245839628289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983675486357661119504385 4487756614768245839628289)
              ·
                refine ⟨3365817461076184379721217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487756614768245839628289 3365817461076184379721217)
                ·
                  refine ⟨2524363095807138284790913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365817461076184379721217 2524363095807138284790913)
                  ·
                    refine ⟨1893272321855353713593185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524363095807138284790913 1893272321855353713593185)
                    ·
                      refine ⟨1419954241391515285194889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893272321855353713593185 1419954241391515285194889)
                      ·
                        rfl

theorem cell23_2765351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2765351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765351 prefixEnd_2765351 := by exact prefixLift 2765351
  have htrace : WordTrace (prefixWord ++ tailWord_2765351) baseStart_2765351 baseEnd_2765351 := by
    simpa [prefixWord, tailWord_2765351, baseEnd_2765351] using wordTrace_append hprefix tailTrace_2765351
  have hstable : (prefixWord ++ tailWord_2765351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765351).length < 2 ^ (prefixWord ++ tailWord_2765351).sum := by decide
  have hdescent : baseEnd_2765351 < baseStart_2765351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765383 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 5, 4]
def baseStart_2765383 : Nat := 118140960795 + 2765383 * 2 ^ 59
def prefixEnd_2765383 : Nat := 4983230072969 + 3 ^ 40 * 2765383 * 2
def baseEnd_2765383 : Nat := 473323557590819719998247

theorem tailTrace_2765383 : CollatzResearch.WordTrace tailWord_2765383 prefixEnd_2765383 473323557590819719998247 := by
  unfold tailWord_2765383
  simp only [CollatzResearch.WordTrace]
  refine ⟨100861804140497155660596803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67241202760331437107064535 100861804140497155660596803)
  ·
    refine ⟨151292706210745733490895205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100861804140497155660596803 151292706210745733490895205)
    ·
      refine ⟨28367382414514825029542851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151292706210745733490895205 28367382414514825029542851)
      ·
        refine ⟨42551073621772237544314277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28367382414514825029542851 42551073621772237544314277)
        ·
          refine ⟨7978326304082294539558927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42551073621772237544314277 7978326304082294539558927)
          ·
            refine ⟨11967489456123441809338391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978326304082294539558927 11967489456123441809338391)
            ·
              refine ⟨17951234184185162714007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11967489456123441809338391 17951234184185162714007587)
              ·
                refine ⟨26926851276277744071011381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17951234184185162714007587 26926851276277744071011381)
                ·
                  refine ⟨2524392307151038506657317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26926851276277744071011381 2524392307151038506657317)
                  ·
                    refine ⟨473323557590819719998247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524392307151038506657317 473323557590819719998247)
                    ·
                      rfl

theorem cell23_2765383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_2765383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765383 prefixEnd_2765383 := by exact prefixLift 2765383
  have htrace : WordTrace (prefixWord ++ tailWord_2765383) baseStart_2765383 baseEnd_2765383 := by
    simpa [prefixWord, tailWord_2765383, baseEnd_2765383] using wordTrace_append hprefix tailTrace_2765383
  have hstable : (prefixWord ++ tailWord_2765383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765383).length < 2 ^ (prefixWord ++ tailWord_2765383).sum := by decide
  have hdescent : baseEnd_2765383 < baseStart_2765383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765393 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_2765393 : Nat := 118140960795 + 2765393 * 2 ^ 59
def prefixEnd_2765393 : Nat := 4983230072969 + 3 ^ 40 * 2765393 * 2
def baseEnd_2765393 : Nat := 1419975807579004120869695

theorem tailTrace_2765393 : CollatzResearch.WordTrace tailWord_2765393 prefixEnd_2765393 1419975807579004120869695 := by
  unfold tailWord_2765393
  simp only [CollatzResearch.WordTrace]
  refine ⟨100862168870460927368460833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67241445913640618245640555 100862168870460927368460833)
  ·
    refine ⟨75646626652845695526345625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100862168870460927368460833 75646626652845695526345625)
    ·
      refine ⟨56734969989634271644759219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75646626652845695526345625 56734969989634271644759219)
      ·
        refine ⟨85102454984451407467138829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56734969989634271644759219 85102454984451407467138829)
        ·
          refine ⟨31913420619169277800177061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85102454984451407467138829 31913420619169277800177061)
          ·
            refine ⟨5983766366094239587533199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31913420619169277800177061 5983766366094239587533199)
            ·
              refine ⟨8975649549141359381299799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983766366094239587533199 8975649549141359381299799)
              ·
                refine ⟨13463474323712039071949699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8975649549141359381299799 13463474323712039071949699)
                ·
                  refine ⟨20195211485568058607924549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13463474323712039071949699 20195211485568058607924549)
                  ·
                    refine ⟨3786602153544010988985853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20195211485568058607924549 3786602153544010988985853)
                    ·
                      refine ⟨1419975807579004120869695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786602153544010988985853 1419975807579004120869695)
                      ·
                        rfl

theorem cell23_2765393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_2765393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765393 prefixEnd_2765393 := by exact prefixLift 2765393
  have htrace : WordTrace (prefixWord ++ tailWord_2765393) baseStart_2765393 baseEnd_2765393 := by
    simpa [prefixWord, tailWord_2765393, baseEnd_2765393] using wordTrace_append hprefix tailTrace_2765393
  have hstable : (prefixWord ++ tailWord_2765393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765393).length < 2 ^ (prefixWord ++ tailWord_2765393).sum := by decide
  have hdescent : baseEnd_2765393 < baseStart_2765393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765400 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 1, 4]
def baseStart_2765400 : Nat := 118140960795 + 2765400 * 2 ^ 59
def prefixEnd_2765400 : Nat := 4983230072969 + 3 ^ 40 * 2765400 * 2
def baseEnd_2765400 : Nat := 473326467314528531160721

theorem tailTrace_2765400 : CollatzResearch.WordTrace tailWord_2765400 prefixEnd_2765400 473326467314528531160721 := by
  unfold tailWord_2765400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431212090717783781982827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67241616120957045042643769 50431212090717783781982827)
  ·
    refine ⟨75646818136076675672974241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50431212090717783781982827 75646818136076675672974241)
    ·
      refine ⟨56735113602057506754730681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75646818136076675672974241 56735113602057506754730681)
      ·
        refine ⟨42551335201543130066048011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56735113602057506754730681 42551335201543130066048011)
        ·
          refine ⟨63827002802314695099072017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42551335201543130066048011 63827002802314695099072017)
          ·
            refine ⟨47870252101736021324304013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63827002802314695099072017 47870252101736021324304013)
            ·
              refine ⟨17951344538151007996614005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47870252101736021324304013 17951344538151007996614005)
              ·
                refine ⟨1682938550451656999682563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17951344538151007996614005 1682938550451656999682563)
                ·
                  refine ⟨2524407825677485499523845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682938550451656999682563 2524407825677485499523845)
                  ·
                    refine ⟨473326467314528531160721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524407825677485499523845 473326467314528531160721)
                    ·
                      rfl

theorem cell23_2765400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_2765400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765400 prefixEnd_2765400 := by exact prefixLift 2765400
  have htrace : WordTrace (prefixWord ++ tailWord_2765400) baseStart_2765400 baseEnd_2765400 := by
    simpa [prefixWord, tailWord_2765400, baseEnd_2765400] using wordTrace_append hprefix tailTrace_2765400
  have hstable : (prefixWord ++ tailWord_2765400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765400).length < 2 ^ (prefixWord ++ tailWord_2765400).sum := by decide
  have hdescent : baseEnd_2765400 < baseStart_2765400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765413 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 8]
def baseStart_2765413 : Nat := 118140960795 + 2765413 * 2 ^ 59
def prefixEnd_2765413 : Nat := 4983230072969 + 3 ^ 40 * 2765413 * 2
def baseEnd_2765413 : Nat := 157776230799121560291067

theorem tailTrace_2765413 : CollatzResearch.WordTrace tailWord_2765413 prefixEnd_2765413 157776230799121560291067 := by
  unfold tailWord_2765413
  simp only [CollatzResearch.WordTrace]
  refine ⟨100862898330388470784188893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67241932220258980522792595 100862898330388470784188893)
  ·
    refine ⟨37823586873895676544070835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100862898330388470784188893 37823586873895676544070835)
    ·
      refine ⟨56735380310843514816106253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37823586873895676544070835 56735380310843514816106253)
      ·
        refine ⟨21275767616566318056039845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56735380310843514816106253 21275767616566318056039845)
        ·
          refine ⟨3989206428106184635507471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21275767616566318056039845 3989206428106184635507471)
          ·
            refine ⟨5983809642159276953261207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989206428106184635507471 5983809642159276953261207)
            ·
              refine ⟨8975714463238915429891811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983809642159276953261207 8975714463238915429891811)
              ·
                refine ⟨13463571694858373144837717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8975714463238915429891811 13463571694858373144837717)
                ·
                  refine ⟨157776230799121560291067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13463571694858373144837717 157776230799121560291067)
                  ·
                    rfl

theorem cell23_2765413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_2765413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765413 prefixEnd_2765413 := by exact prefixLift 2765413
  have htrace : WordTrace (prefixWord ++ tailWord_2765413) baseStart_2765413 baseEnd_2765413 := by
    simpa [prefixWord, tailWord_2765413, baseEnd_2765413] using wordTrace_append hprefix tailTrace_2765413
  have hstable : (prefixWord ++ tailWord_2765413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765413).length < 2 ^ (prefixWord ++ tailWord_2765413).sum := by decide
  have hdescent : baseEnd_2765413 < baseStart_2765413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765436 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2765436 : Nat := 118140960795 + 2765436 * 2 ^ 59
def prefixEnd_2765436 : Nat := 4983230072969 + 3 ^ 40 * 2765436 * 2
def baseEnd_2765436 : Nat := 1419997887247147452631997

theorem tailTrace_2765436 : CollatzResearch.WordTrace tailWord_2765436 prefixEnd_2765436 1419997887247147452631997 := by
  unfold tailWord_2765436
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431868604652572856138081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67242491472870097141517441 50431868604652572856138081)
  ·
    refine ⟨37823901453489429642103561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50431868604652572856138081 37823901453489429642103561)
    ·
      refine ⟨28367926090117072231577671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37823901453489429642103561 28367926090117072231577671)
      ·
        refine ⟨42551889135175608347366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28367926090117072231577671 42551889135175608347366507)
        ·
          refine ⟨63827833702763412521049761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42551889135175608347366507 63827833702763412521049761)
          ·
            refine ⟨47870875277072559390787321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63827833702763412521049761 47870875277072559390787321)
            ·
              refine ⟨35903156457804419543090491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47870875277072559390787321 35903156457804419543090491)
              ·
                refine ⟨53854734686706629314635737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35903156457804419543090491 53854734686706629314635737)
                ·
                  refine ⟨40391051015029971985976803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53854734686706629314635737 40391051015029971985976803)
                  ·
                    refine ⟨60586576522544957978965205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40391051015029971985976803 60586576522544957978965205)
                    ·
                      refine ⟨1419997887247147452631997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60586576522544957978965205 1419997887247147452631997)
                      ·
                        rfl

theorem cell23_2765436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2765436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765436 prefixEnd_2765436 := by exact prefixLift 2765436
  have htrace : WordTrace (prefixWord ++ tailWord_2765436) baseStart_2765436 baseEnd_2765436 := by
    simpa [prefixWord, tailWord_2765436, baseEnd_2765436] using wordTrace_append hprefix tailTrace_2765436
  have hstable : (prefixWord ++ tailWord_2765436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765436).length < 2 ^ (prefixWord ++ tailWord_2765436).sum := by decide
  have hdescent : baseEnd_2765436 < baseStart_2765436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765440 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_2765440 : Nat := 118140960795 + 2765440 * 2 ^ 59
def prefixEnd_2765440 : Nat := 4983230072969 + 3 ^ 40 * 2765440 * 2
def baseEnd_2765440 : Nat := 1419999941169765436981979

theorem tailTrace_2765440 : CollatzResearch.WordTrace tailWord_2765440 prefixEnd_2765440 1419999941169765436981979 := by
  unfold tailWord_2765440
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431941550645327197710887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67242588734193769596947849 50431941550645327197710887)
  ·
    refine ⟨75647912325967990796566331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50431941550645327197710887 75647912325967990796566331)
    ·
      refine ⟨113471868488951986194849497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75647912325967990796566331 113471868488951986194849497)
      ·
        refine ⟨85103901366713989646137123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113471868488951986194849497 85103901366713989646137123)
        ·
          refine ⟨127655852050070984469205685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85103901366713989646137123 127655852050070984469205685)
          ·
            refine ⟨11967736129694154793988033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127655852050070984469205685 11967736129694154793988033)
            ·
              refine ⟨8975802097270616095491025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11967736129694154793988033 8975802097270616095491025)
              ·
                refine ⟨6731851572952962071618269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975802097270616095491025 6731851572952962071618269)
                ·
                  refine ⟨2524444339857360776856851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6731851572952962071618269 2524444339857360776856851)
                  ·
                    refine ⟨3786666509786041165285277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524444339857360776856851 3786666509786041165285277)
                    ·
                      refine ⟨1419999941169765436981979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786666509786041165285277 1419999941169765436981979)
                      ·
                        rfl

theorem cell23_2765440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_2765440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765440 prefixEnd_2765440 := by exact prefixLift 2765440
  have htrace : WordTrace (prefixWord ++ tailWord_2765440) baseStart_2765440 baseEnd_2765440 := by
    simpa [prefixWord, tailWord_2765440, baseEnd_2765440] using wordTrace_append hprefix tailTrace_2765440
  have hstable : (prefixWord ++ tailWord_2765440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765440).length < 2 ^ (prefixWord ++ tailWord_2765440).sum := by decide
  have hdescent : baseEnd_2765440 < baseStart_2765440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765443 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 1, 5]
def baseStart_2765443 : Nat := 118140960795 + 2765443 * 2 ^ 59
def prefixEnd_2765443 : Nat := 4983230072969 + 3 ^ 40 * 2765443 * 2
def baseEnd_2765443 : Nat := 473333827203909641748155

theorem tailTrace_2765443 : CollatzResearch.WordTrace tailWord_2765443 prefixEnd_2765443 473333827203909641748155 := by
  unfold tailWord_2765443
  simp only [CollatzResearch.WordTrace]
  refine ⟨100863992520279785907780983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67242661680186523938520655 100863992520279785907780983)
  ·
    refine ⟨151295988780419678861671475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100863992520279785907780983 151295988780419678861671475)
    ·
      refine ⟨226943983170629518292507213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151295988780419678861671475 226943983170629518292507213)
      ·
        refine ⟨85103993688986069359690205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226943983170629518292507213 85103993688986069359690205)
        ·
          refine ⟨31913997633369776009883827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85103993688986069359690205 31913997633369776009883827)
          ·
            refine ⟨47870996450054664014825741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31913997633369776009883827 47870996450054664014825741)
            ·
              refine ⟨17951623668770499005559653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47870996450054664014825741 17951623668770499005559653)
              ·
                refine ⟨3365929437894468563542435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17951623668770499005559653 3365929437894468563542435)
                ·
                  refine ⟨5048894156841702845313653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365929437894468563542435 5048894156841702845313653)
                  ·
                    refine ⟨473333827203909641748155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5048894156841702845313653 473333827203909641748155)
                    ·
                      rfl

theorem cell23_2765443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 5].length) (baseStart_2765443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765443 prefixEnd_2765443 := by exact prefixLift 2765443
  have htrace : WordTrace (prefixWord ++ tailWord_2765443) baseStart_2765443 baseEnd_2765443 := by
    simpa [prefixWord, tailWord_2765443, baseEnd_2765443] using wordTrace_append hprefix tailTrace_2765443
  have hstable : (prefixWord ++ tailWord_2765443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765443).length < 2 ^ (prefixWord ++ tailWord_2765443).sum := by decide
  have hdescent : baseEnd_2765443 < baseStart_2765443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765500 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2765500 : Nat := 118140960795 + 2765500 * 2 ^ 59
def prefixEnd_2765500 : Nat := 4983230072969 + 3 ^ 40 * 2765500 * 2
def baseEnd_2765500 : Nat := 1420030750009035202231703

theorem tailTrace_2765500 : CollatzResearch.WordTrace tailWord_2765500 prefixEnd_2765500 1420030750009035202231703 := by
  unfold tailWord_2765500
  simp only [CollatzResearch.WordTrace]
  refine ⟨50433035740536642321302977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67244047654048856428403969 50433035740536642321302977)
  ·
    refine ⟨37824776805402481740977233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50433035740536642321302977 37824776805402481740977233)
    ·
      refine ⟨28368582604051861305732925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37824776805402481740977233 28368582604051861305732925)
      ·
        refine ⟨10638218476519447989649847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28368582604051861305732925 10638218476519447989649847)
        ·
          refine ⟨15957327714779171984474771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638218476519447989649847 15957327714779171984474771)
          ·
            refine ⟨23935991572168757976712157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15957327714779171984474771 23935991572168757976712157)
            ·
              refine ⟨8975996839563284241267059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23935991572168757976712157 8975996839563284241267059)
              ·
                refine ⟨13463995259344926361900589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8975996839563284241267059 13463995259344926361900589)
                ·
                  refine ⟨5048998222254347385712721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13463995259344926361900589 5048998222254347385712721)
                  ·
                    refine ⟨3786748666690760539284541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5048998222254347385712721 3786748666690760539284541)
                    ·
                      refine ⟨1420030750009035202231703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786748666690760539284541 1420030750009035202231703)
                      ·
                        rfl

theorem cell23_2765500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2765500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765500 prefixEnd_2765500 := by exact prefixLift 2765500
  have htrace : WordTrace (prefixWord ++ tailWord_2765500) baseStart_2765500 baseEnd_2765500 := by
    simpa [prefixWord, tailWord_2765500, baseEnd_2765500] using wordTrace_append hprefix tailTrace_2765500
  have hstable : (prefixWord ++ tailWord_2765500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765500).length < 2 ^ (prefixWord ++ tailWord_2765500).sum := by decide
  have hdescent : baseEnd_2765500 < baseStart_2765500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765524 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_2765524 : Nat := 118140960795 + 2765524 * 2 ^ 59
def prefixEnd_2765524 : Nat := 4983230072969 + 3 ^ 40 * 2765524 * 2
def baseEnd_2765524 : Nat := 473347691181581036110531

theorem tailTrace_2765524 : CollatzResearch.WordTrace tailWord_2765524 prefixEnd_2765524 473347691181581036110531 := by
  unfold tailWord_2765524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50433473416493168370739813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67244631221990891160986417 50433473416493168370739813)
  ·
    refine ⟨9456276265592469069513715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50433473416493168370739813 9456276265592469069513715)
    ·
      refine ⟨14184414398388703604270573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456276265592469069513715 14184414398388703604270573)
      ·
        refine ⟨5319155399395763851601465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14184414398388703604270573 5319155399395763851601465)
        ·
          refine ⟨3989366549546822888701099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5319155399395763851601465 3989366549546822888701099)
          ·
            refine ⟨5984049824320234333051649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989366549546822888701099 5984049824320234333051649)
            ·
              refine ⟨4488037368240175749788737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984049824320234333051649 4488037368240175749788737)
              ·
                refine ⟨3366028026180131812341553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4488037368240175749788737 3366028026180131812341553)
                ·
                  refine ⟨2524521019635098859256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366028026180131812341553 2524521019635098859256165)
                  ·
                    refine ⟨473347691181581036110531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524521019635098859256165 473347691181581036110531)
                    ·
                      rfl

theorem cell23_2765524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_2765524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765524 prefixEnd_2765524 := by exact prefixLift 2765524
  have htrace : WordTrace (prefixWord ++ tailWord_2765524) baseStart_2765524 baseEnd_2765524 := by
    simpa [prefixWord, tailWord_2765524, baseEnd_2765524] using wordTrace_append hprefix tailTrace_2765524
  have hstable : (prefixWord ++ tailWord_2765524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765524).length < 2 ^ (prefixWord ++ tailWord_2765524).sum := by decide
  have hdescent : baseEnd_2765524 < baseStart_2765524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765525 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2765525 : Nat := 118140960795 + 2765525 * 2 ^ 59
def prefixEnd_2765525 : Nat := 4983230072969 + 3 ^ 40 * 2765525 * 2
def baseEnd_2765525 : Nat := 1420043587025397604419089

theorem tailTrace_2765525 : CollatzResearch.WordTrace tailWord_2765525 prefixEnd_2765525 1420043587025397604419089 := by
  unfold tailWord_2765525
  simp only [CollatzResearch.WordTrace]
  refine ⟨100866983305982713912266029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67244655537321809274844019 100866983305982713912266029)
  ·
    refine ⟨37825118739743517717099761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100866983305982713912266029 37825118739743517717099761)
    ·
      refine ⟨28368839054807638287824821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37825118739743517717099761 28368839054807638287824821)
      ·
        refine ⟨2659578661388216089483577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28368839054807638287824821 2659578661388216089483577)
        ·
          refine ⟨1994683996041162067112683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659578661388216089483577 1994683996041162067112683)
          ·
            refine ⟨2992025994061743100669025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994683996041162067112683 2992025994061743100669025)
            ·
              refine ⟨2244019495546307325501769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992025994061743100669025 2244019495546307325501769)
              ·
                refine ⟨1683014621659730494126327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244019495546307325501769 1683014621659730494126327)
                ·
                  refine ⟨2524521932489595741189491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683014621659730494126327 2524521932489595741189491)
                  ·
                    refine ⟨3786782898734393611784237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524521932489595741189491 3786782898734393611784237)
                    ·
                      refine ⟨1420043587025397604419089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786782898734393611784237 1420043587025397604419089)
                      ·
                        rfl

theorem cell23_2765525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2765525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765525 prefixEnd_2765525 := by exact prefixLift 2765525
  have htrace : WordTrace (prefixWord ++ tailWord_2765525) baseStart_2765525 baseEnd_2765525 := by
    simpa [prefixWord, tailWord_2765525, baseEnd_2765525] using wordTrace_append hprefix tailTrace_2765525
  have hstable : (prefixWord ++ tailWord_2765525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765525).length < 2 ^ (prefixWord ++ tailWord_2765525).sum := by decide
  have hdescent : baseEnd_2765525 < baseStart_2765525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765553 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2765553 : Nat := 118140960795 + 2765553 * 2 ^ 59
def prefixEnd_2765553 : Nat := 4983230072969 + 3 ^ 40 * 2765553 * 2
def baseEnd_2765553 : Nat := 1420057964483723494868959

theorem tailTrace_2765553 : CollatzResearch.WordTrace tailWord_2765553 prefixEnd_2765553 1420057964483723494868959 := by
  unfold tailWord_2765553
  simp only [CollatzResearch.WordTrace]
  refine ⟨100868004549881274694285313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67245336366587516462856875 100868004549881274694285313)
  ·
    refine ⟨75651003412410956020713985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100868004549881274694285313 75651003412410956020713985)
    ·
      refine ⟨56738252559308217015535489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75651003412410956020713985 56738252559308217015535489)
      ·
        refine ⟨42553689419481162761651617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56738252559308217015535489 42553689419481162761651617)
        ·
          refine ⟨31915267064610872071238713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42553689419481162761651617 31915267064610872071238713)
          ·
            refine ⟨23936450298458154053429035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31915267064610872071238713 23936450298458154053429035)
            ·
              refine ⟨35904675447687231080143553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23936450298458154053429035 35904675447687231080143553)
              ·
                refine ⟨26928506585765423310107665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35904675447687231080143553 26928506585765423310107665)
                ·
                  refine ⟨20196379939324067482580749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26928506585765423310107665 20196379939324067482580749)
                  ·
                    refine ⟨7573642477246525305967781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20196379939324067482580749 7573642477246525305967781)
                    ·
                      refine ⟨1420057964483723494868959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7573642477246525305967781 1420057964483723494868959)
                      ·
                        rfl

theorem cell23_2765553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2765553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765553 prefixEnd_2765553 := by exact prefixLift 2765553
  have htrace : WordTrace (prefixWord ++ tailWord_2765553) baseStart_2765553 baseEnd_2765553 := by
    simpa [prefixWord, tailWord_2765553, baseEnd_2765553] using wordTrace_append hprefix tailTrace_2765553
  have hstable : (prefixWord ++ tailWord_2765553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765553).length < 2 ^ (prefixWord ++ tailWord_2765553).sum := by decide
  have hdescent : baseEnd_2765553 < baseStart_2765553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765573 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_2765573 : Nat := 118140960795 + 2765573 * 2 ^ 59
def prefixEnd_2765573 : Nat := 4983230072969 + 3 ^ 40 * 2765573 * 2
def baseEnd_2765573 : Nat := 1420068234096813416618867

theorem tailTrace_2765573 : CollatzResearch.WordTrace tailWord_2765573 prefixEnd_2765573 1420068234096813416618867 := by
  unfold tailWord_2765573
  simp only [CollatzResearch.WordTrace]
  refine ⟨100868734009808818110013373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67245822673205878740008915 100868734009808818110013373)
  ·
    refine ⟨37825775253678306791255015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100868734009808818110013373 37825775253678306791255015)
    ·
      refine ⟨56738662880517460186882523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37825775253678306791255015 56738662880517460186882523)
      ·
        refine ⟨85107994320776190280323785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56738662880517460186882523 85107994320776190280323785)
        ·
          refine ⟨63830995740582142710242839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85107994320776190280323785 63830995740582142710242839)
          ·
            refine ⟨95746493610873214065364259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63830995740582142710242839 95746493610873214065364259)
            ·
              refine ⟨143619740416309821098046389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95746493610873214065364259 143619740416309821098046389)
              ·
                refine ⟨13464350664029045727941849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143619740416309821098046389 13464350664029045727941849)
                ·
                  refine ⟨10098262998021784295956387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13464350664029045727941849 10098262998021784295956387)
                  ·
                    refine ⟨15147394497032676443934581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10098262998021784295956387 15147394497032676443934581)
                    ·
                      refine ⟨1420068234096813416618867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15147394497032676443934581 1420068234096813416618867)
                      ·
                        rfl

theorem cell23_2765573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2765573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765573 prefixEnd_2765573 := by exact prefixLift 2765573
  have htrace : WordTrace (prefixWord ++ tailWord_2765573) baseStart_2765573 baseEnd_2765573 := by
    simpa [prefixWord, tailWord_2765573, baseEnd_2765573] using wordTrace_append hprefix tailTrace_2765573
  have hstable : (prefixWord ++ tailWord_2765573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765573).length < 2 ^ (prefixWord ++ tailWord_2765573).sum := by decide
  have hdescent : baseEnd_2765573 < baseStart_2765573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765583 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_2765583 : Nat := 118140960795 + 2765583 * 2 ^ 59
def prefixEnd_2765583 : Nat := 4983230072969 + 3 ^ 40 * 2765583 * 2
def baseEnd_2765583 : Nat := 1420073368903358377493821

theorem tailTrace_2765583 : CollatzResearch.WordTrace tailWord_2765583 prefixEnd_2765583 1420073368903358377493821 := by
  unfold tailWord_2765583
  simp only [CollatzResearch.WordTrace]
  refine ⟨100869098739772589817877403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67246065826515059878584935 100869098739772589817877403)
  ·
    refine ⟨151303648109658884726816105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100869098739772589817877403 151303648109658884726816105)
    ·
      refine ⟨113477736082244163545112079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151303648109658884726816105 113477736082244163545112079)
      ·
        refine ⟨170216604123366245317668119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113477736082244163545112079 170216604123366245317668119)
        ·
          refine ⟨255324906185049367976502179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170216604123366245317668119 255324906185049367976502179)
          ·
            refine ⟨382987359277574051964753269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255324906185049367976502179 382987359277574051964753269)
            ·
              refine ⟨35905064932272567371695619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 382987359277574051964753269 35905064932272567371695619)
              ·
                refine ⟨53857597398408851057543429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35905064932272567371695619 53857597398408851057543429)
                ·
                  refine ⟨10098299512201659573289393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53857597398408851057543429 10098299512201659573289393)
                  ·
                    refine ⟨7573724634151244679967045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098299512201659573289393 7573724634151244679967045)
                    ·
                      refine ⟨1420073368903358377493821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7573724634151244679967045 1420073368903358377493821)
                      ·
                        rfl

theorem cell23_2765583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_2765583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765583 prefixEnd_2765583 := by exact prefixLift 2765583
  have htrace : WordTrace (prefixWord ++ tailWord_2765583) baseStart_2765583 baseEnd_2765583 := by
    simpa [prefixWord, tailWord_2765583, baseEnd_2765583] using wordTrace_append hprefix tailTrace_2765583
  have hstable : (prefixWord ++ tailWord_2765583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765583).length < 2 ^ (prefixWord ++ tailWord_2765583).sum := by decide
  have hdescent : baseEnd_2765583 < baseStart_2765583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765587 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 4, 2, 2]
def baseStart_2765587 : Nat := 118140960795 + 2765587 * 2 ^ 59
def prefixEnd_2765587 : Nat := 4983230072969 + 3 ^ 40 * 2765587 * 2
def baseEnd_2765587 : Nat := 1420075422825976361843803

theorem tailTrace_2765587 : CollatzResearch.WordTrace tailWord_2765587 prefixEnd_2765587 1420075422825976361843803 := by
  unfold tailWord_2765587
  simp only [CollatzResearch.WordTrace]
  refine ⟨100869244631758098501023015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67246163087838732334015343 100869244631758098501023015)
  ·
    refine ⟨151303866947637147751534523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100869244631758098501023015 151303866947637147751534523)
    ·
      refine ⟨226955800421455721627301785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151303866947637147751534523 226955800421455721627301785)
      ·
        refine ⟨170216850316091791220476339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226955800421455721627301785 170216850316091791220476339)
        ·
          refine ⟨255325275474137686830714509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170216850316091791220476339 255325275474137686830714509)
          ·
            refine ⟨95746978302801632561517941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255325275474137686830714509 95746978302801632561517941)
            ·
              refine ⟨8976279215887653052642307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95746978302801632561517941 8976279215887653052642307)
              ·
                refine ⟨13464418823831479578963461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976279215887653052642307 13464418823831479578963461)
                ·
                  refine ⟨2524578529468402421055649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13464418823831479578963461 2524578529468402421055649)
                  ·
                    refine ⟨1893433897101301815791737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524578529468402421055649 1893433897101301815791737)
                    ·
                      refine ⟨1420075422825976361843803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893433897101301815791737 1420075422825976361843803)
                      ·
                        rfl

theorem cell23_2765587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2, 2].length) (baseStart_2765587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765587 prefixEnd_2765587 := by exact prefixLift 2765587
  have htrace : WordTrace (prefixWord ++ tailWord_2765587) baseStart_2765587 baseEnd_2765587 := by
    simpa [prefixWord, tailWord_2765587, baseEnd_2765587] using wordTrace_append hprefix tailTrace_2765587
  have hstable : (prefixWord ++ tailWord_2765587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765587).length < 2 ^ (prefixWord ++ tailWord_2765587).sum := by decide
  have hdescent : baseEnd_2765587 < baseStart_2765587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765600 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2765600 : Nat := 118140960795 + 2765600 * 2 ^ 59
def prefixEnd_2765600 : Nat := 4983230072969 + 3 ^ 40 * 2765600 * 2
def baseEnd_2765600 : Nat := 1420082098074484810981243

theorem tailTrace_2765600 : CollatzResearch.WordTrace tailWord_2765600 prefixEnd_2765600 1420082098074484810981243 := by
  unfold tailWord_2765600
  simp only [CollatzResearch.WordTrace]
  refine ⟨50434859390355500860623127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67246479187140667814164169 50434859390355500860623127)
  ·
    refine ⟨75652289085533251290934691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50434859390355500860623127 75652289085533251290934691)
    ·
      refine ⟨113478433628299876936402037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75652289085533251290934691 113478433628299876936402037)
      ·
        refine ⟨10638603152653113462787691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113478433628299876936402037 10638603152653113462787691)
        ·
          refine ⟨15957904728979670194181537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638603152653113462787691 15957904728979670194181537)
          ·
            refine ⟨11968428546734752645636153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15957904728979670194181537 11968428546734752645636153)
            ·
              refine ⟨8976321410051064484227115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11968428546734752645636153 8976321410051064484227115)
              ·
                refine ⟨13464482115076596726340673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976321410051064484227115 13464482115076596726340673)
                ·
                  refine ⟨10098361586307447544755505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13464482115076596726340673 10098361586307447544755505)
                  ·
                    refine ⟨7573771189730585658566629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098361586307447544755505 7573771189730585658566629)
                    ·
                      refine ⟨1420082098074484810981243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7573771189730585658566629 1420082098074484810981243)
                      ·
                        rfl

theorem cell23_2765600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2765600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765600 prefixEnd_2765600 := by exact prefixLift 2765600
  have htrace : WordTrace (prefixWord ++ tailWord_2765600) baseStart_2765600 baseEnd_2765600 := by
    simpa [prefixWord, tailWord_2765600, baseEnd_2765600] using wordTrace_append hprefix tailTrace_2765600
  have hstable : (prefixWord ++ tailWord_2765600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765600).length < 2 ^ (prefixWord ++ tailWord_2765600).sum := by decide
  have hdescent : baseEnd_2765600 < baseStart_2765600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765623 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 7]
def baseStart_2765623 : Nat := 118140960795 + 2765623 * 2 ^ 59
def prefixEnd_2765623 : Nat := 4983230072969 + 3 ^ 40 * 2765623 * 2
def baseEnd_2765623 : Nat := 473364636043179406997879

theorem tailTrace_2765623 : CollatzResearch.WordTrace tailWord_2765623 prefixEnd_2765623 473364636043179406997879 := by
  unfold tailWord_2765623
  simp only [CollatzResearch.WordTrace]
  refine ⟨100870557659627676649333523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67247038439751784432889015 100870557659627676649333523)
  ·
    refine ⟨151305836489441514974000285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100870557659627676649333523 151305836489441514974000285)
    ·
      refine ⟨56739688683540568115250107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151305836489441514974000285 56739688683540568115250107)
      ·
        refine ⟨85109533025310852172875161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56739688683540568115250107 85109533025310852172875161)
        ·
          refine ⟨63832149768983139129656371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85109533025310852172875161 63832149768983139129656371)
          ·
            refine ⟨95748224653474708694484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63832149768983139129656371 95748224653474708694484557)
            ·
              refine ⟨35905584245053015760431709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95748224653474708694484557 35905584245053015760431709)
              ·
                refine ⟨13464594091894880910161891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35905584245053015760431709 13464594091894880910161891)
                ·
                  refine ⟨20196891137842321365242837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464594091894880910161891 20196891137842321365242837)
                  ·
                    refine ⟨473364636043179406997879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20196891137842321365242837 473364636043179406997879)
                    ·
                      rfl

theorem cell23_2765623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_2765623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765623 prefixEnd_2765623 := by exact prefixLift 2765623
  have htrace : WordTrace (prefixWord ++ tailWord_2765623) baseStart_2765623 baseEnd_2765623 := by
    simpa [prefixWord, tailWord_2765623, baseEnd_2765623] using wordTrace_append hprefix tailTrace_2765623
  have hstable : (prefixWord ++ tailWord_2765623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765623).length < 2 ^ (prefixWord ++ tailWord_2765623).sum := by decide
  have hdescent : baseEnd_2765623 < baseStart_2765623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765640 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_2765640 : Nat := 118140960795 + 2765640 * 2 ^ 59
def prefixEnd_2765640 : Nat := 4983230072969 + 3 ^ 40 * 2765640 * 2
def baseEnd_2765640 : Nat := 473367545766888218160353

theorem tailTrace_2765640 : CollatzResearch.WordTrace tailWord_2765640 prefixEnd_2765640 473367545766888218160353 := by
  unfold tailWord_2765640
  simp only [CollatzResearch.WordTrace]
  refine ⟨50435588850283044276351187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67247451800377392368468249 50435588850283044276351187)
  ·
    refine ⟨75653383275424566414526781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50435588850283044276351187 75653383275424566414526781)
    ·
      refine ⟨28370018728284212405447543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75653383275424566414526781 28370018728284212405447543)
      ·
        refine ⟨42555028092426318608171315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28370018728284212405447543 42555028092426318608171315)
        ·
          refine ⟨63832542138639477912256973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42555028092426318608171315 63832542138639477912256973)
          ·
            refine ⟨23937203301989804217096365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63832542138639477912256973 23937203301989804217096365)
            ·
              refine ⟨8976451238246176581411137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23937203301989804217096365 8976451238246176581411137)
              ·
                refine ⟨6732338428684632436058353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8976451238246176581411137 6732338428684632436058353)
                ·
                  refine ⟨5049253821513474327043765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6732338428684632436058353 5049253821513474327043765)
                  ·
                    refine ⟨473367545766888218160353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5049253821513474327043765 473367545766888218160353)
                    ·
                      rfl

theorem cell23_2765640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_2765640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765640 prefixEnd_2765640 := by exact prefixLift 2765640
  have htrace : WordTrace (prefixWord ++ tailWord_2765640) baseStart_2765640 baseEnd_2765640 := by
    simpa [prefixWord, tailWord_2765640, baseEnd_2765640] using wordTrace_append hprefix tailTrace_2765640
  have hstable : (prefixWord ++ tailWord_2765640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765640).length < 2 ^ (prefixWord ++ tailWord_2765640).sum := by decide
  have hdescent : baseEnd_2765640 < baseStart_2765640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765643 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_2765643 : Nat := 118140960795 + 2765643 * 2 ^ 59
def prefixEnd_2765643 : Nat := 4983230072969 + 3 ^ 40 * 2765643 * 2
def baseEnd_2765643 : Nat := 1420104177742628142743545

theorem tailTrace_2765643 : CollatzResearch.WordTrace tailWord_2765643 prefixEnd_2765643 1420104177742628142743545 := by
  unfold tailWord_2765643
  simp only [CollatzResearch.WordTrace]
  refine ⟨100871287119555220065061583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67247524746370146710041055 100871287119555220065061583)
  ·
    refine ⟨151306930679332830097592375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100871287119555220065061583 151306930679332830097592375)
    ·
      refine ⟨226960396018999245146388563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151306930679332830097592375 226960396018999245146388563)
      ·
        refine ⟨340440594028498867719582845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226960396018999245146388563 340440594028498867719582845)
        ·
          refine ⟨127665222760687075394843567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340440594028498867719582845 127665222760687075394843567)
          ·
            refine ⟨191497834141030613092265351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127665222760687075394843567 191497834141030613092265351)
            ·
              refine ⟨287246751211545919638398027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191497834141030613092265351 287246751211545919638398027)
              ·
                refine ⟨430870126817318879457597041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287246751211545919638398027 430870126817318879457597041)
                ·
                  refine ⟨323152595112989159593197781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430870126817318879457597041 323152595112989159593197781)
                  ·
                    refine ⟨7573888947960683427965573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 323152595112989159593197781 7573888947960683427965573)
                    ·
                      refine ⟨1420104177742628142743545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7573888947960683427965573 1420104177742628142743545)
                      ·
                        rfl

theorem cell23_2765643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_2765643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765643 prefixEnd_2765643 := by exact prefixLift 2765643
  have htrace : WordTrace (prefixWord ++ tailWord_2765643) baseStart_2765643 baseEnd_2765643 := by
    simpa [prefixWord, tailWord_2765643, baseEnd_2765643] using wordTrace_append hprefix tailTrace_2765643
  have hstable : (prefixWord ++ tailWord_2765643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765643).length < 2 ^ (prefixWord ++ tailWord_2765643).sum := by decide
  have hdescent : baseEnd_2765643 < baseStart_2765643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765644 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 5]
def baseStart_2765644 : Nat := 118140960795 + 2765644 * 2 ^ 59
def prefixEnd_2765644 : Nat := 4983230072969 + 3 ^ 40 * 2765644 * 2
def baseEnd_2765644 : Nat := 157789410135920293203449

theorem tailTrace_2765644 : CollatzResearch.WordTrace tailWord_2765644 prefixEnd_2765644 157789410135920293203449 := by
  unfold tailWord_2765644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50435661796275798617923993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67247549061701064823898657 50435661796275798617923993)
  ·
    refine ⟨37826746347206848963442995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50435661796275798617923993 37826746347206848963442995)
    ·
      refine ⟨56740119520810273445164493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37826746347206848963442995 56740119520810273445164493)
      ·
        refine ⟨21277544820303852541936685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56740119520810273445164493 21277544820303852541936685)
        ·
          refine ⟨7979079307613944703226257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21277544820303852541936685 7979079307613944703226257)
          ·
            refine ⟨5984309480710458527419693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7979079307613944703226257 5984309480710458527419693)
            ·
              refine ⟨2244116055266421947782385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5984309480710458527419693 2244116055266421947782385)
              ·
                refine ⟨1683087041449816460836789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244116055266421947782385 1683087041449816460836789)
                ·
                  refine ⟨157789410135920293203449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683087041449816460836789 157789410135920293203449)
                  ·
                    rfl

theorem cell23_2765644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_2765644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765644 prefixEnd_2765644 := by exact prefixLift 2765644
  have htrace : WordTrace (prefixWord ++ tailWord_2765644) baseStart_2765644 baseEnd_2765644 := by
    simpa [prefixWord, tailWord_2765644, baseEnd_2765644] using wordTrace_append hprefix tailTrace_2765644
  have hstable : (prefixWord ++ tailWord_2765644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765644).length < 2 ^ (prefixWord ++ tailWord_2765644).sum := by decide
  have hdescent : baseEnd_2765644 < baseStart_2765644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765650 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2765650 : Nat := 118140960795 + 2765650 * 2 ^ 59
def prefixEnd_2765650 : Nat := 4983230072969 + 3 ^ 40 * 2765650 * 2
def baseEnd_2765650 : Nat := 1420107772107209615356013

theorem tailTrace_2765650 : CollatzResearch.WordTrace tailWord_2765650 prefixEnd_2765650 1420107772107209615356013 := by
  unfold tailWord_2765650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217885607632465065141601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67247694953686573507044269 25217885607632465065141601)
  ·
    refine ⟨18913414205724348798856201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25217885607632465065141601 18913414205724348798856201)
    ·
      refine ⟨14185060654293261599142151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18913414205724348798856201 14185060654293261599142151)
      ·
        refine ⟨21277590981439892398713227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185060654293261599142151 21277590981439892398713227)
        ·
          refine ⟨31916386472159838598069841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277590981439892398713227 31916386472159838598069841)
          ·
            refine ⟨23937289854119878948552381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31916386472159838598069841 23937289854119878948552381)
            ·
              refine ⟨8976483695294954605707143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23937289854119878948552381 8976483695294954605707143)
              ·
                refine ⟨13464725542942431908560715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976483695294954605707143 13464725542942431908560715)
                ·
                  refine ⟨20197088314413647862841073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464725542942431908560715 20197088314413647862841073)
                  ·
                    refine ⟨15147816235810235897130805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20197088314413647862841073 15147816235810235897130805)
                    ·
                      refine ⟨1420107772107209615356013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15147816235810235897130805 1420107772107209615356013)
                      ·
                        rfl

theorem cell23_2765650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2765650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765650 prefixEnd_2765650 := by exact prefixLift 2765650
  have htrace : WordTrace (prefixWord ++ tailWord_2765650) baseStart_2765650 baseEnd_2765650 := by
    simpa [prefixWord, tailWord_2765650, baseEnd_2765650] using wordTrace_append hprefix tailTrace_2765650
  have hstable : (prefixWord ++ tailWord_2765650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765650).length < 2 ^ (prefixWord ++ tailWord_2765650).sum := by decide
  have hdescent : baseEnd_2765650 < baseStart_2765650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2765673 : Nat := 118140960795 + 2765673 * 2 ^ 59
def prefixEnd_2765673 : Nat := 4983230072969 + 3 ^ 40 * 2765673 * 2
def baseEnd_2765673 : Nat := 1420119582162263025368407

theorem tailTrace_2765673 : CollatzResearch.WordTrace tailWord_2765673 prefixEnd_2765673 1420119582162263025368407 := by
  unfold tailWord_2765673
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872381309446535188653673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248254206297690125769115 100872381309446535188653673)
  ·
    refine ⟨75654285982084901391490255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100872381309446535188653673 75654285982084901391490255)
    ·
      refine ⟨113481428973127352087235383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75654285982084901391490255 113481428973127352087235383)
      ·
        refine ⟨170222143459691028130853075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113481428973127352087235383 170222143459691028130853075)
        ·
          refine ⟨255333215189536542196279613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170222143459691028130853075 255333215189536542196279613)
          ·
            refine ⟨95749955696076203323604855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255333215189536542196279613 95749955696076203323604855)
            ·
              refine ⟨143624933544114304985407283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95749955696076203323604855 143624933544114304985407283)
              ·
                refine ⟨215437400316171457478110925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143624933544114304985407283 215437400316171457478110925)
                ·
                  refine ⟨80789025118564296554291597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215437400316171457478110925 80789025118564296554291597)
                  ·
                    refine ⟨30295884419461611207859349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80789025118564296554291597 30295884419461611207859349)
                    ·
                      refine ⟨1420119582162263025368407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30295884419461611207859349 1420119582162263025368407)
                      ·
                        rfl

theorem cell23_2765673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2765673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765673 prefixEnd_2765673 := by exact prefixLift 2765673
  have htrace : WordTrace (prefixWord ++ tailWord_2765673) baseStart_2765673 baseEnd_2765673 := by
    simpa [prefixWord, tailWord_2765673, baseEnd_2765673] using wordTrace_append hprefix tailTrace_2765673
  have hstable : (prefixWord ++ tailWord_2765673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765673).length < 2 ^ (prefixWord ++ tailWord_2765673).sum := by decide
  have hdescent : baseEnd_2765673 < baseStart_2765673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_2765677 : Nat := 118140960795 + 2765677 * 2 ^ 59
def prefixEnd_2765677 : Nat := 4983230072969 + 3 ^ 40 * 2765677 * 2
def baseEnd_2765677 : Nat := 1420121636084881009718389

theorem tailTrace_2765677 : CollatzResearch.WordTrace tailWord_2765677 prefixEnd_2765677 1420121636084881009718389 := by
  unfold tailWord_2765677
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872527201432043871799285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248351467621362581199523 100872527201432043871799285)
  ·
    refine ⟨9456799425134254112981183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100872527201432043871799285 9456799425134254112981183)
    ·
      refine ⟨14185199137701381169471775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456799425134254112981183 14185199137701381169471775)
      ·
        refine ⟨21277798706552071754207663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185199137701381169471775 21277798706552071754207663)
        ·
          refine ⟨31916698059828107631311495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277798706552071754207663 31916698059828107631311495)
          ·
            refine ⟨47875047089742161446967243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916698059828107631311495 47875047089742161446967243)
            ·
              refine ⟨71812570634613242170450865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47875047089742161446967243 71812570634613242170450865)
              ·
                refine ⟨53859427975959931627838149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71812570634613242170450865 53859427975959931627838149)
                ·
                  refine ⟨10098642745492487180219653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53859427975959931627838149 10098642745492487180219653)
                  ·
                    refine ⟨1893495514779841346291185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10098642745492487180219653 1893495514779841346291185)
                    ·
                      refine ⟨1420121636084881009718389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893495514779841346291185 1420121636084881009718389)
                      ·
                        rfl

theorem cell23_2765677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_2765677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765677 prefixEnd_2765677 := by exact prefixLift 2765677
  have htrace : WordTrace (prefixWord ++ tailWord_2765677) baseStart_2765677 baseEnd_2765677 := by
    simpa [prefixWord, tailWord_2765677, baseEnd_2765677] using wordTrace_append hprefix tailTrace_2765677
  have hstable : (prefixWord ++ tailWord_2765677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765677).length < 2 ^ (prefixWord ++ tailWord_2765677).sum := by decide
  have hdescent : baseEnd_2765677 < baseStart_2765677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765680 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_2765680 : Nat := 118140960795 + 2765680 * 2 ^ 59
def prefixEnd_2765680 : Nat := 4983230072969 + 3 ^ 40 * 2765680 * 2
def baseEnd_2765680 : Nat := 1420123176526844497980875

theorem tailTrace_2765680 : CollatzResearch.WordTrace tailWord_2765680 prefixEnd_2765680 1420123176526844497980875 := by
  unfold tailWord_2765680
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436318310210587692079247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67248424413614116922772329 50436318310210587692079247)
  ·
    refine ⟨75654477465315881538118871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50436318310210587692079247 75654477465315881538118871)
    ·
      refine ⟨113481716197973822307178307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75654477465315881538118871 113481716197973822307178307)
      ·
        refine ⟨170222574296960733460767461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113481716197973822307178307 170222574296960733460767461)
        ·
          refine ⟨31916732680680137523893899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170222574296960733460767461 31916732680680137523893899)
          ·
            refine ⟨47875099021020206285840849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916732680680137523893899 47875099021020206285840849)
            ·
              refine ⟨35906324265765154714380637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47875099021020206285840849 35906324265765154714380637)
              ·
                refine ⟨13464871599661933017892739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35906324265765154714380637 13464871599661933017892739)
                ·
                  refine ⟨20197307399492899526839109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464871599661933017892739 20197307399492899526839109)
                  ·
                    refine ⟨3786995137404918661282333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20197307399492899526839109 3786995137404918661282333)
                    ·
                      refine ⟨1420123176526844497980875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3786995137404918661282333 1420123176526844497980875)
                      ·
                        rfl

theorem cell23_2765680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_2765680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765680 prefixEnd_2765680 := by exact prefixLift 2765680
  have htrace : WordTrace (prefixWord ++ tailWord_2765680) baseStart_2765680 baseEnd_2765680 := by
    simpa [prefixWord, tailWord_2765680, baseEnd_2765680] using wordTrace_append hprefix tailTrace_2765680
  have hstable : (prefixWord ++ tailWord_2765680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765680).length < 2 ^ (prefixWord ++ tailWord_2765680).sum := by decide
  have hdescent : baseEnd_2765680 < baseStart_2765680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765683 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 10]
def baseStart_2765683 : Nat := 118140960795 + 2765683 * 2 ^ 59
def prefixEnd_2765683 : Nat := 4983230072969 + 3 ^ 40 * 2765683 * 2
def baseEnd_2765683 : Nat := 157791635218756442915929

theorem tailTrace_2765683 : CollatzResearch.WordTrace tailWord_2765683 prefixEnd_2765683 157791635218756442915929 := by
  unfold tailWord_2765683
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872746039410306896517703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248497359606871264345135 100872746039410306896517703)
  ·
    refine ⟨151309119059115460344776555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100872746039410306896517703 151309119059115460344776555)
    ·
      refine ⟨226963678588673190517164833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151309119059115460344776555 226963678588673190517164833)
      ·
        refine ⟨170222758941504892887873625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226963678588673190517164833 170222758941504892887873625)
        ·
          refine ⟨127667069206128669665905219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170222758941504892887873625 127667069206128669665905219)
          ·
            refine ⟨191500603809193004498857829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127667069206128669665905219 191500603809193004498857829)
            ·
              refine ⟨35906363214223688343535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191500603809193004498857829 35906363214223688343535843)
              ·
                refine ⟨53859544821335532515303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35906363214223688343535843 53859544821335532515303765)
                ·
                  refine ⟨157791635218756442915929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53859544821335532515303765 157791635218756442915929)
                  ·
                    rfl

theorem cell23_2765683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 10].length) (baseStart_2765683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765683 prefixEnd_2765683 := by exact prefixLift 2765683
  have htrace : WordTrace (prefixWord ++ tailWord_2765683) baseStart_2765683 baseEnd_2765683 := by
    simpa [prefixWord, tailWord_2765683, baseEnd_2765683] using wordTrace_append hprefix tailTrace_2765683
  have hstable : (prefixWord ++ tailWord_2765683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765683).length < 2 ^ (prefixWord ++ tailWord_2765683).sum := by decide
  have hdescent : baseEnd_2765683 < baseStart_2765683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765737 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 5, 2]
def baseStart_2765737 : Nat := 118140960795 + 2765737 * 2 ^ 59
def prefixEnd_2765737 : Nat := 4983230072969 + 3 ^ 40 * 2765737 * 2
def baseEnd_2765737 : Nat := 1420152444924150774968113

theorem tailTrace_2765737 : CollatzResearch.WordTrace tailWord_2765737 prefixEnd_2765737 1420152444924150774968113 := by
  unfold tailWord_2765737
  simp only [CollatzResearch.WordTrace]
  refine ⟨100874715581214674118983465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67249810387476449412655643 100874715581214674118983465)
  ·
    refine ⟨75656036685911005589237599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100874715581214674118983465 75656036685911005589237599)
    ·
      refine ⟨113484055028866508383856399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75656036685911005589237599 113484055028866508383856399)
      ·
        refine ⟨170226082543299762575784599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113484055028866508383856399 170226082543299762575784599)
        ·
          refine ⟨255339123814949643863676899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170226082543299762575784599 255339123814949643863676899)
          ·
            refine ⟨383008685722424465795515349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255339123814949643863676899 383008685722424465795515349)
            ·
              refine ⟨8976766071619323417082391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 383008685722424465795515349 8976766071619323417082391)
              ·
                refine ⟨13465149107428985125623587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976766071619323417082391 13465149107428985125623587)
                ·
                  refine ⟨20197723661143477688435381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13465149107428985125623587 20197723661143477688435381)
                  ·
                    refine ⟨1893536593232201033290817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20197723661143477688435381 1893536593232201033290817)
                    ·
                      refine ⟨1420152444924150774968113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893536593232201033290817 1420152444924150774968113)
                      ·
                        rfl

theorem cell23_2765737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5, 2].length) (baseStart_2765737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765737 prefixEnd_2765737 := by exact prefixLift 2765737
  have htrace : WordTrace (prefixWord ++ tailWord_2765737) baseStart_2765737 baseEnd_2765737 := by
    simpa [prefixWord, tailWord_2765737, baseEnd_2765737] using wordTrace_append hprefix tailTrace_2765737
  have hstable : (prefixWord ++ tailWord_2765737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765737).length < 2 ^ (prefixWord ++ tailWord_2765737).sum := by decide
  have hdescent : baseEnd_2765737 < baseStart_2765737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765784 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2765784 : Nat := 118140960795 + 2765784 * 2 ^ 59
def prefixEnd_2765784 : Nat := 4983230072969 + 3 ^ 40 * 2765784 * 2
def baseEnd_2765784 : Nat := 1420176578514912091080397

theorem tailTrace_2765784 : CollatzResearch.WordTrace tailWord_2765784 prefixEnd_2765784 1420176578514912091080397 := by
  unfold tailWord_2765784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50438214906022200572972203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67250953208029600763962937 50438214906022200572972203)
  ·
    refine ⟨75657322359033300859458305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50438214906022200572972203 75657322359033300859458305)
    ·
      refine ⟨56742991769274975644593729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75657322359033300859458305 56742991769274975644593729)
      ·
        refine ⟨42557243826956231733445297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56742991769274975644593729 42557243826956231733445297)
        ·
          refine ⟨31917932870217173800083973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42557243826956231733445297 31917932870217173800083973)
          ·
            refine ⟨5984612413165720087515745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31917932870217173800083973 5984612413165720087515745)
            ·
              refine ⟨4488459309874290065636809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984612413165720087515745 4488459309874290065636809)
              ·
                refine ⟨3366344482405717549227607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4488459309874290065636809 3366344482405717549227607)
                ·
                  refine ⟨5049516723608576323841411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366344482405717549227607 5049516723608576323841411)
                  ·
                    refine ⟨7574275085412864485762117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5049516723608576323841411 7574275085412864485762117)
                    ·
                      refine ⟨1420176578514912091080397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7574275085412864485762117 1420176578514912091080397)
                      ·
                        rfl

theorem cell23_2765784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2765784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765784 prefixEnd_2765784 := by exact prefixLift 2765784
  have htrace : WordTrace (prefixWord ++ tailWord_2765784) baseStart_2765784 baseEnd_2765784 := by
    simpa [prefixWord, tailWord_2765784, baseEnd_2765784] using wordTrace_append hprefix tailTrace_2765784
  have hstable : (prefixWord ++ tailWord_2765784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765784).length < 2 ^ (prefixWord ++ tailWord_2765784).sum := by decide
  have hdescent : baseEnd_2765784 < baseStart_2765784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765827 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 9, 2]
def baseStart_2765827 : Nat := 118140960795 + 2765827 * 2 ^ 59
def prefixEnd_2765827 : Nat := 4983230072969 + 3 ^ 40 * 2765827 * 2
def baseEnd_2765827 : Nat := 1420198658183055422842699

theorem tailTrace_2765827 : CollatzResearch.WordTrace tailWord_2765827 prefixEnd_2765827 1420198658183055422842699 := by
  unfold tailWord_2765827
  simp only [CollatzResearch.WordTrace]
  refine ⟨100877998150888619489759735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67251998767259079659839823 100877998150888619489759735)
  ·
    refine ⟨151316997226332929234639603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100877998150888619489759735 151316997226332929234639603)
    ·
      refine ⟨226975495839499393851959405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151316997226332929234639603 226975495839499393851959405)
      ·
        refine ⟨85115810939812272694484777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226975495839499393851959405 85115810939812272694484777)
        ·
          refine ⟨63836858204859204520863583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85115810939812272694484777 63836858204859204520863583)
          ·
            refine ⟨95755287307288806781295375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63836858204859204520863583 95755287307288806781295375)
            ·
              refine ⟨143632930960933210171943063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95755287307288806781295375 143632930960933210171943063)
              ·
                refine ⟨215449396441399815257914595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143632930960933210171943063 215449396441399815257914595)
                ·
                  refine ⟨323174094662099722886871893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215449396441399815257914595 323174094662099722886871893)
                  ·
                    refine ⟨1893598210910740563790265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 323174094662099722886871893 1893598210910740563790265)
                    ·
                      refine ⟨1420198658183055422842699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893598210910740563790265 1420198658183055422842699)
                      ·
                        rfl

theorem cell23_2765827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_2765827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765827 prefixEnd_2765827 := by exact prefixLift 2765827
  have htrace : WordTrace (prefixWord ++ tailWord_2765827) baseStart_2765827 baseEnd_2765827 := by
    simpa [prefixWord, tailWord_2765827, baseEnd_2765827] using wordTrace_append hprefix tailTrace_2765827
  have hstable : (prefixWord ++ tailWord_2765827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765827).length < 2 ^ (prefixWord ++ tailWord_2765827).sum := by decide
  have hdescent : baseEnd_2765827 < baseStart_2765827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765874 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_2765874 : Nat := 118140960795 + 2765874 * 2 ^ 59
def prefixEnd_2765874 : Nat := 4983230072969 + 3 ^ 40 * 2765874 * 2
def baseEnd_2765874 : Nat := 1420222791773816738954983

theorem tailTrace_2765874 : CollatzResearch.WordTrace tailWord_2765874 prefixEnd_2765874 1420222791773816738954983 := by
  unfold tailWord_2765874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219928095429586629180169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67253141587812231011147117 25219928095429586629180169)
  ·
    refine ⟨18914946071572189971885127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25219928095429586629180169 18914946071572189971885127)
    ·
      refine ⟨28372419107358284957827691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18914946071572189971885127 28372419107358284957827691)
      ·
        refine ⟨42558628661037427436741537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28372419107358284957827691 42558628661037427436741537)
        ·
          refine ⟨31918971495778070577556153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42558628661037427436741537 31918971495778070577556153)
          ·
            refine ⟨23939228621833552933167115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31918971495778070577556153 23939228621833552933167115)
            ·
              refine ⟨35908842932750329399750673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23939228621833552933167115 35908842932750329399750673)
              ·
                refine ⟨26931632199562747049813005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35908842932750329399750673 26931632199562747049813005)
                ·
                  refine ⟨10099362074836030143679877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26931632199562747049813005 10099362074836030143679877)
                  ·
                    refine ⟨1893630389031755651939977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10099362074836030143679877 1893630389031755651939977)
                    ·
                      refine ⟨1420222791773816738954983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893630389031755651939977 1420222791773816738954983)
                      ·
                        rfl

theorem cell23_2765874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_2765874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765874 prefixEnd_2765874 := by exact prefixLift 2765874
  have htrace : WordTrace (prefixWord ++ tailWord_2765874) baseStart_2765874 baseEnd_2765874 := by
    simpa [prefixWord, tailWord_2765874, baseEnd_2765874] using wordTrace_append hprefix tailTrace_2765874
  have hstable : (prefixWord ++ tailWord_2765874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765874).length < 2 ^ (prefixWord ++ tailWord_2765874).sum := by decide
  have hdescent : baseEnd_2765874 < baseStart_2765874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765891 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 2, 2, 2]
def baseStart_2765891 : Nat := 118140960795 + 2765891 * 2 ^ 59
def prefixEnd_2765891 : Nat := 4983230072969 + 3 ^ 40 * 2765891 * 2
def baseEnd_2765891 : Nat := 1420231520944943172442405

theorem tailTrace_2765891 : CollatzResearch.WordTrace tailWord_2765891 prefixEnd_2765891 1420231520944943172442405 := by
  unfold tailWord_2765891
  simp only [CollatzResearch.WordTrace]
  refine ⟨100880332422656758420089527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67253554948437838946726351 100880332422656758420089527)
  ·
    refine ⟨151320498633985137630134291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100880332422656758420089527 151320498633985137630134291)
    ·
      refine ⟨226980747950977706445201437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151320498633985137630134291 226980747950977706445201437)
      ·
        refine ⟨85117780481616639916950539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226980747950977706445201437 85117780481616639916950539)
        ·
          refine ⟨127676670722424959875425809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85117780481616639916950539 127676670722424959875425809)
          ·
            refine ⟨95757503041818719906569357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127676670722424959875425809 95757503041818719906569357)
            ·
              refine ⟨35909063640682019964963509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95757503041818719906569357 35909063640682019964963509)
              ·
                refine ⟨3366474716313939371715329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35909063640682019964963509 3366474716313939371715329)
                ·
                  refine ⟨2524856037235454528786497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366474716313939371715329 2524856037235454528786497)
                  ·
                    refine ⟨1893642027926590896589873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524856037235454528786497 1893642027926590896589873)
                    ·
                      refine ⟨1420231520944943172442405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893642027926590896589873 1420231520944943172442405)
                      ·
                        rfl

theorem cell23_2765891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_2765891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765891 prefixEnd_2765891 := by exact prefixLift 2765891
  have htrace : WordTrace (prefixWord ++ tailWord_2765891) baseStart_2765891 baseEnd_2765891 := by
    simpa [prefixWord, tailWord_2765891, baseEnd_2765891] using wordTrace_append hprefix tailTrace_2765891
  have hstable : (prefixWord ++ tailWord_2765891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765891).length < 2 ^ (prefixWord ++ tailWord_2765891).sum := by decide
  have hdescent : baseEnd_2765891 < baseStart_2765891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3]
def baseStart_2765907 : Nat := 118140960795 + 2765907 * 2 ^ 59
def prefixEnd_2765907 : Nat := 4983230072969 + 3 ^ 40 * 2765907 * 2
def baseEnd_2765907 : Nat := 1420239736635415109842331

theorem tailTrace_2765907 : CollatzResearch.WordTrace tailWord_2765907 prefixEnd_2765907 1420239736635415109842331 := by
  unfold tailWord_2765907
  simp only [CollatzResearch.WordTrace]
  refine ⟨100880915990598793152671975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67253943993732528768447983 100880915990598793152671975)
  ·
    refine ⟨151321373985898189729007963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100880915990598793152671975 151321373985898189729007963)
    ·
      refine ⟨226982060978847284593511945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151321373985898189729007963 226982060978847284593511945)
      ·
        refine ⟨170236545734135463445133959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226982060978847284593511945 170236545734135463445133959)
        ·
          refine ⟨255354818601203195167700939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170236545734135463445133959 255354818601203195167700939)
          ·
            refine ⟨383032227901804792751551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255354818601203195167700939 383032227901804792751551409)
            ·
              refine ⟨287274170926353594563663557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383032227901804792751551409 287274170926353594563663557)
              ·
                refine ⟨53863907048691298980686917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287274170926353594563663557 53863907048691298980686917)
                ·
                  refine ⟨10099482571629618558878797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53863907048691298980686917 10099482571629618558878797)
                  ·
                    refine ⟨3787305964361106959579549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10099482571629618558878797 3787305964361106959579549)
                    ·
                      refine ⟨1420239736635415109842331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3787305964361106959579549 1420239736635415109842331)
                      ·
                        rfl

theorem cell23_2765907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_2765907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765907 prefixEnd_2765907 := by exact prefixLift 2765907
  have htrace : WordTrace (prefixWord ++ tailWord_2765907) baseStart_2765907 baseEnd_2765907 := by
    simpa [prefixWord, tailWord_2765907, baseEnd_2765907] using wordTrace_append hprefix tailTrace_2765907
  have hstable : (prefixWord ++ tailWord_2765907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765907).length < 2 ^ (prefixWord ++ tailWord_2765907).sum := by decide
  have hdescent : baseEnd_2765907 < baseStart_2765907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765964 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_2765964 : Nat := 118140960795 + 2765964 * 2 ^ 59
def prefixEnd_2765964 : Nat := 4983230072969 + 3 ^ 40 * 2765964 * 2
def baseEnd_2765964 : Nat := 1420269005032721386829569

theorem tailTrace_2765964 : CollatzResearch.WordTrace tailWord_2765964 prefixEnd_2765964 1420269005032721386829569 := by
  unfold tailWord_2765964
  simp only [CollatzResearch.WordTrace]
  refine ⟨50441497475696145943748473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67255329967594861258331297 50441497475696145943748473)
  ·
    refine ⟨37831123106772109457811355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50441497475696145943748473 37831123106772109457811355)
    ·
      refine ⟨56746684660158164186717033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37831123106772109457811355 56746684660158164186717033)
      ·
        refine ⟨42560013495118623140037775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56746684660158164186717033 42560013495118623140037775)
        ·
          refine ⟨63840020242677934710056663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42560013495118623140037775 63840020242677934710056663)
          ·
            refine ⟨95760030364016902065084995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63840020242677934710056663 95760030364016902065084995)
            ·
              refine ⟨143640045546025353097627493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95760030364016902065084995 143640045546025353097627493)
              ·
                refine ⟨26932508539879753705805155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143640045546025353097627493 26932508539879753705805155)
                ·
                  refine ⟨40398762809819630558707733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26932508539879753705805155 40398762809819630558707733)
                  ·
                    refine ⟨1893692006710295182439425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40398762809819630558707733 1893692006710295182439425)
                    ·
                      refine ⟨1420269005032721386829569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893692006710295182439425 1420269005032721386829569)
                      ·
                        rfl

theorem cell23_2765964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_2765964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2765964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2765964 prefixEnd_2765964 := by exact prefixLift 2765964
  have htrace : WordTrace (prefixWord ++ tailWord_2765964) baseStart_2765964 baseEnd_2765964 := by
    simpa [prefixWord, tailWord_2765964, baseEnd_2765964] using wordTrace_append hprefix tailTrace_2765964
  have hstable : (prefixWord ++ tailWord_2765964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765964).length < 2 ^ (prefixWord ++ tailWord_2765964).sum := by decide
  have hdescent : baseEnd_2765964 < baseStart_2765964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766027 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_2766027 : Nat := 118140960795 + 2766027 * 2 ^ 59
def prefixEnd_2766027 : Nat := 4983230072969 + 3 ^ 40 * 2766027 * 2
def baseEnd_2766027 : Nat := 1420301354313954640341779

theorem tailTrace_2766027 : CollatzResearch.WordTrace tailWord_2766027 prefixEnd_2766027 1420301354313954640341779 := by
  unfold tailWord_2766027
  simp only [CollatzResearch.WordTrace]
  refine ⟨100885292750164053647040335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67256861833442702431360223 100885292750164053647040335)
  ·
    refine ⟨151327939125246080470560503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100885292750164053647040335 151327939125246080470560503)
    ·
      refine ⟨226991908687869120705840755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151327939125246080470560503 226991908687869120705840755)
      ·
        refine ⟨340487863031803681058761133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226991908687869120705840755 340487863031803681058761133)
        ·
          refine ⟨127682948636926380397035425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340487863031803681058761133 127682948636926380397035425)
          ·
            refine ⟨95762211477694785297776569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127682948636926380397035425 95762211477694785297776569)
            ·
              refine ⟨71821658608271088973332427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95762211477694785297776569 71821658608271088973332427)
              ·
                refine ⟨107732487912406633459998641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71821658608271088973332427 107732487912406633459998641)
                ·
                  refine ⟨80799365934304975094998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107732487912406633459998641 80799365934304975094998981)
                  ·
                    refine ⟨15149881112682182830312309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80799365934304975094998981 15149881112682182830312309)
                    ·
                      refine ⟨1420301354313954640341779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15149881112682182830312309 1420301354313954640341779)
                      ·
                        rfl

theorem cell23_2766027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_2766027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766027 prefixEnd_2766027 := by exact prefixLift 2766027
  have htrace : WordTrace (prefixWord ++ tailWord_2766027) baseStart_2766027 baseEnd_2766027 := by
    simpa [prefixWord, tailWord_2766027, baseEnd_2766027] using wordTrace_append hprefix tailTrace_2766027
  have hstable : (prefixWord ++ tailWord_2766027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766027).length < 2 ^ (prefixWord ++ tailWord_2766027).sum := by decide
  have hdescent : baseEnd_2766027 < baseStart_2766027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766064 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_2766064 : Nat := 118140960795 + 2766064 * 2 ^ 59
def prefixEnd_2766064 : Nat := 4983230072969 + 3 ^ 40 * 2766064 * 2
def baseEnd_2766064 : Nat := 473440117699390331859703

theorem tailTrace_2766064 : CollatzResearch.WordTrace tailWord_2766064 prefixEnd_2766064 473440117699390331859703 := by
  unfold tailWord_2766064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50443321125515004483068623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67257761500686672644091497 50443321125515004483068623)
  ·
    refine ⟨75664981688272506724602935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50443321125515004483068623 75664981688272506724602935)
    ·
      refine ⟨113497472532408760086904403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75664981688272506724602935 113497472532408760086904403)
      ·
        refine ⟨170246208798613140130356605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113497472532408760086904403 170246208798613140130356605)
        ·
          refine ⟨63842328299479927548883727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170246208798613140130356605 63842328299479927548883727)
          ·
            refine ⟨95763492449219891323325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63842328299479927548883727 95763492449219891323325591)
            ·
              refine ⟨143645238673829836984988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95763492449219891323325591 143645238673829836984988387)
              ·
                refine ⟨215467858010744755477482581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143645238673829836984988387 215467858010744755477482581)
                ·
                  refine ⟨2525013961063415103251749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 215467858010744755477482581 2525013961063415103251749)
                  ·
                    refine ⟨473440117699390331859703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525013961063415103251749 473440117699390331859703)
                    ·
                      rfl

theorem cell23_2766064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_2766064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766064 prefixEnd_2766064 := by exact prefixLift 2766064
  have htrace : WordTrace (prefixWord ++ tailWord_2766064) baseStart_2766064 baseEnd_2766064 := by
    simpa [prefixWord, tailWord_2766064, baseEnd_2766064] using wordTrace_append hprefix tailTrace_2766064
  have hstable : (prefixWord ++ tailWord_2766064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766064).length < 2 ^ (prefixWord ++ tailWord_2766064).sum := by decide
  have hdescent : baseEnd_2766064 < baseStart_2766064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766088 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2766088 : Nat := 118140960795 + 2766088 * 2 ^ 59
def prefixEnd_2766088 : Nat := 4983230072969 + 3 ^ 40 * 2766088 * 2
def baseEnd_2766088 : Nat := 1420332676633878901678999

theorem tailTrace_2766088 : CollatzResearch.WordTrace tailWord_2766088 prefixEnd_2766088 1420332676633878901678999 := by
  unfold tailWord_2766088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50443758801471530532505459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67258345068628707376673945 50443758801471530532505459)
  ·
    refine ⟨75665638202207295798758189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50443758801471530532505459 75665638202207295798758189)
    ·
      refine ⟨28374614325827735924534321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75665638202207295798758189 28374614325827735924534321)
      ·
        refine ⟨21280960744370801943400741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28374614325827735924534321 21280960744370801943400741)
        ·
          refine ⟨3990180139569525364387639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21280960744370801943400741 3990180139569525364387639)
          ·
            refine ⟨5985270209354288046581459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990180139569525364387639 5985270209354288046581459)
            ·
              refine ⟨8977905314031432069872189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985270209354288046581459 8977905314031432069872189)
              ·
                refine ⟨3366714492761787026202071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977905314031432069872189 3366714492761787026202071)
                ·
                  refine ⟨5050071739142680539303107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366714492761787026202071 5050071739142680539303107)
                  ·
                    refine ⟨7575107608714020808954661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050071739142680539303107 7575107608714020808954661)
                    ·
                      refine ⟨1420332676633878901678999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7575107608714020808954661 1420332676633878901678999)
                      ·
                        rfl

theorem cell23_2766088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2766088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766088 prefixEnd_2766088 := by exact prefixLift 2766088
  have htrace : WordTrace (prefixWord ++ tailWord_2766088) baseStart_2766088 baseEnd_2766088 := by
    simpa [prefixWord, tailWord_2766088, baseEnd_2766088] using wordTrace_append hprefix tailTrace_2766088
  have hstable : (prefixWord ++ tailWord_2766088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766088).length < 2 ^ (prefixWord ++ tailWord_2766088).sum := by decide
  have hdescent : baseEnd_2766088 < baseStart_2766088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766094 : List Nat := [4, 1, 1, 2, 1, 4, 10]
def baseStart_2766094 : Nat := 118140960795 + 2766094 * 2 ^ 59
def prefixEnd_2766094 : Nat := 4983230072969 + 3 ^ 40 * 2766094 * 2
def baseEnd_2766094 : Nat := 17535009352071677508691

theorem tailTrace_2766094 : CollatzResearch.WordTrace tailWord_2766094 prefixEnd_2766094 17535009352071677508691 := by
  unfold tailWord_2766094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610967055115165511216167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67258490960614216059819557 12610967055115165511216167)
  ·
    refine ⟨18916450582672748266824251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610967055115165511216167 18916450582672748266824251)
    ·
      refine ⟨28374675874009122400236377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18916450582672748266824251 28374675874009122400236377)
      ·
        refine ⟨21281006905506841800177283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28374675874009122400236377 21281006905506841800177283)
        ·
          refine ⟨31921510358260262700265925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21281006905506841800177283 31921510358260262700265925)
          ·
            refine ⟨5985283192173799256299861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31921510358260262700265925 5985283192173799256299861)
            ·
              refine ⟨17535009352071677508691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5985283192173799256299861 17535009352071677508691)
              ·
                rfl

theorem cell23_2766094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 10].length) (baseStart_2766094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766094 prefixEnd_2766094 := by exact prefixLift 2766094
  have htrace : WordTrace (prefixWord ++ tailWord_2766094) baseStart_2766094 baseEnd_2766094 := by
    simpa [prefixWord, tailWord_2766094, baseEnd_2766094] using wordTrace_append hprefix tailTrace_2766094
  have hstable : (prefixWord ++ tailWord_2766094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766094).length < 2 ^ (prefixWord ++ tailWord_2766094).sum := by decide
  have hdescent : baseEnd_2766094 < baseStart_2766094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766125 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2766125 : Nat := 118140960795 + 2766125 * 2 ^ 59
def prefixEnd_2766125 : Nat := 4983230072969 + 3 ^ 40 * 2766125 * 2
def baseEnd_2766125 : Nat := 1420351675418095256916329

theorem tailTrace_2766125 : CollatzResearch.WordTrace tailWord_2766125 prefixEnd_2766125 1420351675418095256916329 := by
  unfold tailWord_2766125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100888867103809016384107829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67259244735872677589405219 100888867103809016384107829)
  ·
    refine ⟨9458331290982095286010109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100888867103809016384107829 9458331290982095286010109)
    ·
      refine ⟨3546874234118285732253791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9458331290982095286010109 3546874234118285732253791)
      ·
        refine ⟨5320311351177428598380687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546874234118285732253791 5320311351177428598380687)
        ·
          refine ⟨7980467026766142897571031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320311351177428598380687 7980467026766142897571031)
          ·
            refine ⟨11970700540149214346356547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980467026766142897571031 11970700540149214346356547)
            ·
              refine ⟨17956050810223821519534821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970700540149214346356547 17956050810223821519534821)
              ·
                refine ⟨3366759526916966534912779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17956050810223821519534821 3366759526916966534912779)
                ·
                  refine ⟨5050139290375449802369169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366759526916966534912779 5050139290375449802369169)
                  ·
                    refine ⟨3787604467781587351776877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050139290375449802369169 3787604467781587351776877)
                    ·
                      refine ⟨1420351675418095256916329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3787604467781587351776877 1420351675418095256916329)
                      ·
                        rfl

theorem cell23_2766125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2766125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766125 prefixEnd_2766125 := by exact prefixLift 2766125
  have htrace : WordTrace (prefixWord ++ tailWord_2766125) baseStart_2766125 baseEnd_2766125 := by
    simpa [prefixWord, tailWord_2766125, baseEnd_2766125] using wordTrace_append hprefix tailTrace_2766125
  have hstable : (prefixWord ++ tailWord_2766125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766125).length < 2 ^ (prefixWord ++ tailWord_2766125).sum := by decide
  have hdescent : baseEnd_2766125 < baseStart_2766125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766154 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2766154 : Nat := 118140960795 + 2766154 * 2 ^ 59
def prefixEnd_2766154 : Nat := 4983230072969 + 3 ^ 40 * 2766154 * 2
def baseEnd_2766154 : Nat := 473455522119025214484565

theorem tailTrace_2766154 : CollatzResearch.WordTrace tailWord_2766154 prefixEnd_2766154 473455522119025214484565 := by
  unfold tailWord_2766154
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222481205175988584228379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67259949880469302891275677 25222481205175988584228379)
  ·
    refine ⟨37833721807763982876342569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25222481205175988584228379 37833721807763982876342569)
    ·
      refine ⟨28375291355822987157256927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37833721807763982876342569 28375291355822987157256927)
      ·
        refine ⟨42562937033734480735885391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28375291355822987157256927 42562937033734480735885391)
        ·
          refine ⟨63844405550601721103828087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42562937033734480735885391 63844405550601721103828087)
          ·
            refine ⟨95766608325902581655742131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63844405550601721103828087 95766608325902581655742131)
            ·
              refine ⟨143649912488853872483613197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95766608325902581655742131 143649912488853872483613197)
              ·
                refine ⟨53868717183320202181354949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143649912488853872483613197 53868717183320202181354949)
                ·
                  refine ⟨10100384471872537909004053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53868717183320202181354949 10100384471872537909004053)
                  ·
                    refine ⟨473455522119025214484565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10100384471872537909004053 473455522119025214484565)
                    ·
                      rfl

theorem cell23_2766154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2766154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766154 prefixEnd_2766154 := by exact prefixLift 2766154
  have htrace : WordTrace (prefixWord ++ tailWord_2766154) baseStart_2766154 baseEnd_2766154 := by
    simpa [prefixWord, tailWord_2766154, baseEnd_2766154] using wordTrace_append hprefix tailTrace_2766154
  have hstable : (prefixWord ++ tailWord_2766154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766154).length < 2 ^ (prefixWord ++ tailWord_2766154).sum := by decide
  have hdescent : baseEnd_2766154 < baseStart_2766154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766212 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2766212 : Nat := 118140960795 + 2766212 * 2 ^ 59
def prefixEnd_2766212 : Nat := 4983230072969 + 3 ^ 40 * 2766212 * 2
def baseEnd_2766212 : Nat := 1420396348235036416528429

theorem tailTrace_2766212 : CollatzResearch.WordTrace tailWord_2766212 prefixEnd_2766212 1420396348235036416528429 := by
  unfold tailWord_2766212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50446020127246915121262445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67261360169662553495016593 50446020127246915121262445)
  ·
    refine ⟨18917257547717593170473417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50446020127246915121262445 18917257547717593170473417)
    ·
      refine ⟨14187943160788194877855063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18917257547717593170473417 14187943160788194877855063)
      ·
        refine ⟨21281914741182292316782595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187943160788194877855063 21281914741182292316782595)
        ·
          refine ⟨31922872111773438475173893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21281914741182292316782595 31922872111773438475173893)
          ·
            refine ⟨5985538520957519714095105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31922872111773438475173893 5985538520957519714095105)
            ·
              refine ⟨4489153890718139785571329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985538520957519714095105 4489153890718139785571329)
              ·
                refine ⟨3366865418038604839178497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489153890718139785571329 3366865418038604839178497)
                ·
                  refine ⟨2525149063528953629383873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366865418038604839178497 2525149063528953629383873)
                  ·
                    refine ⟨1893861797646715222037905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525149063528953629383873 1893861797646715222037905)
                    ·
                      refine ⟨1420396348235036416528429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1893861797646715222037905 1420396348235036416528429)
                      ·
                        rfl

theorem cell23_2766212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2766212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766212 prefixEnd_2766212 := by exact prefixLift 2766212
  have htrace : WordTrace (prefixWord ++ tailWord_2766212) baseStart_2766212 baseEnd_2766212 := by
    simpa [prefixWord, tailWord_2766212, baseEnd_2766212] using wordTrace_append hprefix tailTrace_2766212
  have hstable : (prefixWord ++ tailWord_2766212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766212).length < 2 ^ (prefixWord ++ tailWord_2766212).sum := by decide
  have hdescent : baseEnd_2766212 < baseStart_2766212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766228 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2766228 : Nat := 118140960795 + 2766228 * 2 ^ 59
def prefixEnd_2766228 : Nat := 4983230072969 + 3 ^ 40 * 2766228 * 2
def baseEnd_2766228 : Nat := 1420404563925508353928355

theorem tailTrace_2766228 : CollatzResearch.WordTrace tailWord_2766228 prefixEnd_2766228 1420404563925508353928355 := by
  unfold tailWord_2766228
  simp only [CollatzResearch.WordTrace]
  refine ⟨50446311911217932487553669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67261749214957243316738225 50446311911217932487553669)
  ·
    refine ⟨9458683483353362341416313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50446311911217932487553669 9458683483353362341416313)
    ·
      refine ⟨7094012612515021756062235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9458683483353362341416313 7094012612515021756062235)
      ·
        refine ⟨10641018918772532634093353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094012612515021756062235 10641018918772532634093353)
        ·
          refine ⟨7980764189079399475570015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641018918772532634093353 7980764189079399475570015)
          ·
            refine ⟨11971146283619099213355023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980764189079399475570015 11971146283619099213355023)
            ·
              refine ⟨17956719425428648820032535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971146283619099213355023 17956719425428648820032535)
              ·
                refine ⟨26935079138142973230048803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17956719425428648820032535 26935079138142973230048803)
                ·
                  refine ⟨40402618707214459845073205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26935079138142973230048803 40402618707214459845073205)
                  ·
                    refine ⟨3787745503801355610475613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40402618707214459845073205 3787745503801355610475613)
                    ·
                      refine ⟨1420404563925508353928355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3787745503801355610475613 1420404563925508353928355)
                      ·
                        rfl

theorem cell23_2766228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2766228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766228 prefixEnd_2766228 := by exact prefixLift 2766228
  have htrace : WordTrace (prefixWord ++ tailWord_2766228) baseStart_2766228 baseEnd_2766228 := by
    simpa [prefixWord, tailWord_2766228, baseEnd_2766228] using wordTrace_append hprefix tailTrace_2766228
  have hstable : (prefixWord ++ tailWord_2766228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766228).length < 2 ^ (prefixWord ++ tailWord_2766228).sum := by decide
  have hdescent : baseEnd_2766228 < baseStart_2766228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766341 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_2766341 : Nat := 118140960795 + 2766341 * 2 ^ 59
def prefixEnd_2766341 : Nat := 4983230072969 + 3 ^ 40 * 2766341 * 2
def baseEnd_2766341 : Nat := 1420462587239466411815335

theorem tailTrace_2766341 : CollatzResearch.WordTrace tailWord_2766341 prefixEnd_2766341 1420462587239466411815335 := by
  unfold tailWord_2766341
  simp only [CollatzResearch.WordTrace]
  refine ⟨100896745271026485273970877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67264496847350990182647251 100896745271026485273970877)
  ·
    refine ⟨37836279476634931977739079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100896745271026485273970877 37836279476634931977739079)
    ·
      refine ⟨56754419214952397966608619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37836279476634931977739079 56754419214952397966608619)
      ·
        refine ⟨85131628822428596949912929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56754419214952397966608619 85131628822428596949912929)
        ·
          refine ⟨63848721616821447712434697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85131628822428596949912929 63848721616821447712434697)
          ·
            refine ⟨47886541212616085784326023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63848721616821447712434697 47886541212616085784326023)
            ·
              refine ⟨71829811818924128676489035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47886541212616085784326023 71829811818924128676489035)
              ·
                refine ⟨107744717728386193014733553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71829811818924128676489035 107744717728386193014733553)
                ·
                  refine ⟨80808538296289644761050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107744717728386193014733553 80808538296289644761050165)
                  ·
                    refine ⟨7575800465277154196348453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80808538296289644761050165 7575800465277154196348453)
                    ·
                      refine ⟨1420462587239466411815335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7575800465277154196348453 1420462587239466411815335)
                      ·
                        rfl

theorem cell23_2766341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2766341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766341 prefixEnd_2766341 := by exact prefixLift 2766341
  have htrace : WordTrace (prefixWord ++ tailWord_2766341) baseStart_2766341 baseEnd_2766341 := by
    simpa [prefixWord, tailWord_2766341, baseEnd_2766341] using wordTrace_append hprefix tailTrace_2766341
  have hstable : (prefixWord ++ tailWord_2766341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766341).length < 2 ^ (prefixWord ++ tailWord_2766341).sum := by decide
  have hdescent : baseEnd_2766341 < baseStart_2766341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766355 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 1, 5]
def baseStart_2766355 : Nat := 118140960795 + 2766355 * 2 ^ 59
def prefixEnd_2766355 : Nat := 4983230072969 + 3 ^ 40 * 2766355 * 2
def baseEnd_2766355 : Nat := 473489925322876452346757

theorem tailTrace_2766355 : CollatzResearch.WordTrace tailWord_2766355 prefixEnd_2766355 473489925322876452346757 := by
  unfold tailWord_2766355
  simp only [CollatzResearch.WordTrace]
  refine ⟨100897255892975765664980519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67264837261983843776653679 100897255892975765664980519)
  ·
    refine ⟨151345883839463648497470779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100897255892975765664980519 151345883839463648497470779)
    ·
      refine ⟨227018825759195472746206169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151345883839463648497470779 227018825759195472746206169)
      ·
        refine ⟨170264119319396604559654627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227018825759195472746206169 170264119319396604559654627)
        ·
          refine ⟨255396178979094906839481941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170264119319396604559654627 255396178979094906839481941)
          ·
            refine ⟨2992923972411268439525179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 255396178979094906839481941 2992923972411268439525179)
            ·
              refine ⟨4489385958616902659287769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992923972411268439525179 4489385958616902659287769)
              ·
                refine ⟨3367039468962676994465827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489385958616902659287769 3367039468962676994465827)
                ·
                  refine ⟨5050559203444015491698741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367039468962676994465827 5050559203444015491698741)
                  ·
                    refine ⟨473489925322876452346757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5050559203444015491698741 473489925322876452346757)
                    ·
                      rfl

theorem cell23_2766355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 5].length) (baseStart_2766355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766355 prefixEnd_2766355 := by exact prefixLift 2766355
  have htrace : WordTrace (prefixWord ++ tailWord_2766355) baseStart_2766355 baseEnd_2766355 := by
    simpa [prefixWord, tailWord_2766355, baseEnd_2766355] using wordTrace_append hprefix tailTrace_2766355
  have hstable : (prefixWord ++ tailWord_2766355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766355).length < 2 ^ (prefixWord ++ tailWord_2766355).sum := by decide
  have hdescent : baseEnd_2766355 < baseStart_2766355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766368 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_2766368 : Nat := 118140960795 + 2766368 * 2 ^ 59
def prefixEnd_2766368 : Nat := 4983230072969 + 3 ^ 40 * 2766368 * 2
def baseEnd_2766368 : Nat := 473492150405712602059237

theorem tailTrace_2766368 : CollatzResearch.WordTrace tailWord_2766368 prefixEnd_2766368 473492150405712602059237 := by
  unfold tailWord_2766368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50448865020964334442601879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67265153361285779256802505 50448865020964334442601879)
  ·
    refine ⟨75673297531446501663902819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50448865020964334442601879 75673297531446501663902819)
    ·
      refine ⟨113509946297169752495854229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75673297531446501663902819 113509946297169752495854229)
      ·
        refine ⟨5320778732679832148243167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113509946297169752495854229 5320778732679832148243167)
        ·
          refine ⟨7981168099019748222364751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320778732679832148243167 7981168099019748222364751)
          ·
            refine ⟨11971752148529622333547127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981168099019748222364751 11971752148529622333547127)
            ·
              refine ⟨17957628222794433500320691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971752148529622333547127 17957628222794433500320691)
              ·
                refine ⟨26936442334191650250481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17957628222794433500320691 26936442334191650250481037)
                ·
                  refine ⟨10101165875321868843930389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26936442334191650250481037 10101165875321868843930389)
                  ·
                    refine ⟨473492150405712602059237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10101165875321868843930389 473492150405712602059237)
                    ·
                      rfl

theorem cell23_2766368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_2766368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766368 prefixEnd_2766368 := by exact prefixLift 2766368
  have htrace : WordTrace (prefixWord ++ tailWord_2766368) baseStart_2766368 baseEnd_2766368 := by
    simpa [prefixWord, tailWord_2766368, baseEnd_2766368] using wordTrace_append hprefix tailTrace_2766368
  have hstable : (prefixWord ++ tailWord_2766368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766368).length < 2 ^ (prefixWord ++ tailWord_2766368).sum := by decide
  have hdescent : baseEnd_2766368 < baseStart_2766368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766411 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 7]
def baseStart_2766411 : Nat := 118140960795 + 2766411 * 2 ^ 59
def prefixEnd_2766411 : Nat := 4983230072969 + 3 ^ 40 * 2766411 * 2
def baseEnd_2766411 : Nat := 473499510295093712646671

theorem tailTrace_2766411 : CollatzResearch.WordTrace tailWord_2766411 prefixEnd_2766411 473499510295093712646671 := by
  unfold tailWord_2766411
  simp only [CollatzResearch.WordTrace]
  refine ⟨100899298380772887229019087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67266198920515258152679391 100899298380772887229019087)
  ·
    refine ⟨151348947571159330843528631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100899298380772887229019087 151348947571159330843528631)
    ·
      refine ⟨227023421356738996265292947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151348947571159330843528631 227023421356738996265292947)
      ·
        refine ⟨340535132035108494397939421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227023421356738996265292947 340535132035108494397939421)
        ·
          refine ⟨127700674513165685399227283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340535132035108494397939421 127700674513165685399227283)
          ·
            refine ⟨191551011769748528098840925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127700674513165685399227283 191551011769748528098840925)
            ·
              refine ⟨71831629413655698037065347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191551011769748528098840925 71831629413655698037065347)
              ·
                refine ⟨107747444120483547055598021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71831629413655698037065347 107747444120483547055598021)
                ·
                  refine ⟨20202645772590665072924629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107747444120483547055598021 20202645772590665072924629)
                  ·
                    refine ⟨473499510295093712646671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20202645772590665072924629 473499510295093712646671)
                    ·
                      rfl

theorem cell23_2766411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_2766411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766411 prefixEnd_2766411 := by exact prefixLift 2766411
  have htrace : WordTrace (prefixWord ++ tailWord_2766411) baseStart_2766411 baseEnd_2766411 := by
    simpa [prefixWord, tailWord_2766411, baseEnd_2766411] using wordTrace_append hprefix tailTrace_2766411
  have hstable : (prefixWord ++ tailWord_2766411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766411).length < 2 ^ (prefixWord ++ tailWord_2766411).sum := by decide
  have hdescent : baseEnd_2766411 < baseStart_2766411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766442 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2766442 : Nat := 118140960795 + 2766442 * 2 ^ 59
def prefixEnd_2766442 : Nat := 4983230072969 + 3 ^ 40 * 2766442 * 2
def baseEnd_2766442 : Nat := 1420514448785570516652371

theorem tailTrace_2766442 : CollatzResearch.WordTrace tailWord_2766442 prefixEnd_2766442 1420514448785570516652371 := by
  unfold tailWord_2766442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25225107260915144880849395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67266952695773719682265053 25225107260915144880849395)
  ·
    refine ⟨37837660891372717321274093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25225107260915144880849395 37837660891372717321274093)
    ·
      refine ⟨14189122834264768995477785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37837660891372717321274093 14189122834264768995477785)
      ·
        refine ⟨10641842125698576746608339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189122834264768995477785 10641842125698576746608339)
        ·
          refine ⟨15962763188547865119912509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641842125698576746608339 15962763188547865119912509)
          ·
            refine ⟨5986036195705449419967191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15962763188547865119912509 5986036195705449419967191)
            ·
              refine ⟨8979054293558174129950787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986036195705449419967191 8979054293558174129950787)
              ·
                refine ⟨13468581440337261194926181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979054293558174129950787 13468581440337261194926181)
                ·
                  refine ⟨2525359020063236474048659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13468581440337261194926181 2525359020063236474048659)
                  ·
                    refine ⟨3788038530094854711072989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525359020063236474048659 3788038530094854711072989)
                    ·
                      refine ⟨1420514448785570516652371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788038530094854711072989 1420514448785570516652371)
                      ·
                        rfl

theorem cell23_2766442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2766442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766442 prefixEnd_2766442 := by exact prefixLift 2766442
  have htrace : WordTrace (prefixWord ++ tailWord_2766442) baseStart_2766442 baseEnd_2766442 := by
    simpa [prefixWord, tailWord_2766442, baseEnd_2766442] using wordTrace_append hprefix tailTrace_2766442
  have hstable : (prefixWord ++ tailWord_2766442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766442).length < 2 ^ (prefixWord ++ tailWord_2766442).sum := by decide
  have hdescent : baseEnd_2766442 < baseStart_2766442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766510 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2766510 : Nat := 118140960795 + 2766510 * 2 ^ 59
def prefixEnd_2766510 : Nat := 4983230072969 + 3 ^ 40 * 2766510 * 2
def baseEnd_2766510 : Nat := 1420549365470076250602059

theorem tailTrace_2766510 : CollatzResearch.WordTrace tailWord_2766510 prefixEnd_2766510 1420549365470076250602059 := by
  unfold tailWord_2766510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612863650926778392109123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67268606138276151424581989 12612863650926778392109123)
  ·
    refine ⟨18919295476390167588163685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12612863650926778392109123 18919295476390167588163685)
    ·
      refine ⟨3547367901823156422780691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18919295476390167588163685 3547367901823156422780691)
      ·
        refine ⟨5321051852734734634171037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547367901823156422780691 5321051852734734634171037)
        ·
          refine ⟨1995394444775525487814139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5321051852734734634171037 1995394444775525487814139)
          ·
            refine ⟨2993091667163288231721209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995394444775525487814139 2993091667163288231721209)
            ·
              refine ⟨2244818750372466173790907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993091667163288231721209 2244818750372466173790907)
              ·
                refine ⟨3367228125558699260686361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244818750372466173790907 3367228125558699260686361)
                ·
                  refine ⟨2525421094169024445514771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367228125558699260686361 2525421094169024445514771)
                  ·
                    refine ⟨3788131641253536668272157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525421094169024445514771 3788131641253536668272157)
                    ·
                      refine ⟨1420549365470076250602059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788131641253536668272157 1420549365470076250602059)
                      ·
                        rfl

theorem cell23_2766510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2766510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766510 prefixEnd_2766510 := by exact prefixLift 2766510
  have htrace : WordTrace (prefixWord ++ tailWord_2766510) baseStart_2766510 baseEnd_2766510 := by
    simpa [prefixWord, tailWord_2766510, baseEnd_2766510] using wordTrace_append hprefix tailTrace_2766510
  have hstable : (prefixWord ++ tailWord_2766510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766510).length < 2 ^ (prefixWord ++ tailWord_2766510).sum := by decide
  have hdescent : baseEnd_2766510 < baseStart_2766510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766528 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_2766528 : Nat := 118140960795 + 2766528 * 2 ^ 59
def prefixEnd_2766528 : Nat := 4983230072969 + 3 ^ 40 * 2766528 * 2
def baseEnd_2766528 : Nat := 1420558608121857180176975

theorem tailTrace_2766528 : CollatzResearch.WordTrace tailWord_2766528 prefixEnd_2766528 1420558608121857180176975 := by
  unfold tailWord_2766528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50451782860674508105514119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67269043814232677474018825 50451782860674508105514119)
  ·
    refine ⟨75677674291011762158271179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50451782860674508105514119 75677674291011762158271179)
    ·
      refine ⟨113516511436517643237406769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75677674291011762158271179 113516511436517643237406769)
      ·
        refine ⟨85137383577388232428055077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113516511436517643237406769 85137383577388232428055077)
        ·
          refine ⟨15963259420760293580260327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85137383577388232428055077 15963259420760293580260327)
          ·
            refine ⟨23944889131140440370390491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15963259420760293580260327 23944889131140440370390491)
            ·
              refine ⟨35917333696710660555585737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23944889131140440370390491 35917333696710660555585737)
              ·
                refine ⟨26938000272532995416689303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35917333696710660555585737 26938000272532995416689303)
                ·
                  refine ⟨40407000408799493125033955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26938000272532995416689303 40407000408799493125033955)
                  ·
                    refine ⟨60610500613199239687550933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40407000408799493125033955 60610500613199239687550933)
                    ·
                      refine ⟨1420558608121857180176975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60610500613199239687550933 1420558608121857180176975)
                      ·
                        rfl

theorem cell23_2766528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_2766528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766528 prefixEnd_2766528 := by exact prefixLift 2766528
  have htrace : WordTrace (prefixWord ++ tailWord_2766528) baseStart_2766528 baseEnd_2766528 := by
    simpa [prefixWord, tailWord_2766528, baseEnd_2766528] using wordTrace_append hprefix tailTrace_2766528
  have hstable : (prefixWord ++ tailWord_2766528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766528).length < 2 ^ (prefixWord ++ tailWord_2766528).sum := by decide
  have hdescent : baseEnd_2766528 < baseStart_2766528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766535 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 2, 5]
def baseStart_2766535 : Nat := 118140960795 + 2766535 * 2 ^ 59
def prefixEnd_2766535 : Nat := 4983230072969 + 3 ^ 40 * 2766535 * 2
def baseEnd_2766535 : Nat := 473520734162146217596481

theorem tailTrace_2766535 : CollatzResearch.WordTrace tailWord_2766535 prefixEnd_2766535 473520734162146217596481 := by
  unfold tailWord_2766535
  simp only [CollatzResearch.WordTrace]
  refine ⟨100903821032323656406533059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67269214021549104271022039 100903821032323656406533059)
  ·
    refine ⟨151355731548485484609799589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100903821032323656406533059 151355731548485484609799589)
    ·
      refine ⟨28379199665341028364337423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151355731548485484609799589 28379199665341028364337423)
      ·
        refine ⟨42568799498011542546506135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28379199665341028364337423 42568799498011542546506135)
        ·
          refine ⟨63853199247017313819759203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42568799498011542546506135 63853199247017313819759203)
          ·
            refine ⟨95779798870525970729638805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63853199247017313819759203 95779798870525970729638805)
            ·
              refine ⟨4489678072055904877951819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95779798870525970729638805 4489678072055904877951819)
              ·
                refine ⟨6734517108083857316927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489678072055904877951819 6734517108083857316927729)
                ·
                  refine ⟨5050887831062892987695797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6734517108083857316927729 5050887831062892987695797)
                  ·
                    refine ⟨473520734162146217596481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5050887831062892987695797 473520734162146217596481)
                    ·
                      rfl

theorem cell23_2766535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_2766535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766535 prefixEnd_2766535 := by exact prefixLift 2766535
  have htrace : WordTrace (prefixWord ++ tailWord_2766535) baseStart_2766535 baseEnd_2766535 := by
    simpa [prefixWord, tailWord_2766535, baseEnd_2766535] using wordTrace_append hprefix tailTrace_2766535
  have hstable : (prefixWord ++ tailWord_2766535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766535).length < 2 ^ (prefixWord ++ tailWord_2766535).sum := by decide
  have hdescent : baseEnd_2766535 < baseStart_2766535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766550 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2766550 : Nat := 118140960795 + 2766550 * 2 ^ 59
def prefixEnd_2766550 : Nat := 4983230072969 + 3 ^ 40 * 2766550 * 2
def baseEnd_2766550 : Nat := 1420569904696256094101875

theorem tailTrace_2766550 : CollatzResearch.WordTrace tailWord_2766550 prefixEnd_2766550 1420569904696256094101875 := by
  unfold tailWord_2766550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306523007954332123020569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67269578751512875978886069 6306523007954332123020569)
  ·
    refine ⟨4729892255965749092265427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6306523007954332123020569 4729892255965749092265427)
    ·
      refine ⟨7094838383948623638398141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4729892255965749092265427 7094838383948623638398141)
      ·
        refine ⟨2660564393980733864399303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7094838383948623638398141 2660564393980733864399303)
        ·
          refine ⟨3990846590971100796598955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660564393980733864399303 3990846590971100796598955)
          ·
            refine ⟨5986269886456651194898433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990846590971100796598955 5986269886456651194898433)
            ·
              refine ⟨4489702414842488396173825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5986269886456651194898433 4489702414842488396173825)
              ·
                refine ⟨3367276811131866297130369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489702414842488396173825 3367276811131866297130369)
                ·
                  refine ⟨2525457608348899722847777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367276811131866297130369 2525457608348899722847777)
                  ·
                    refine ⟨1894093206261674792135833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525457608348899722847777 1894093206261674792135833)
                    ·
                      refine ⟨1420569904696256094101875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894093206261674792135833 1420569904696256094101875)
                      ·
                        rfl

theorem cell23_2766550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2766550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766550 prefixEnd_2766550 := by exact prefixLift 2766550
  have htrace : WordTrace (prefixWord ++ tailWord_2766550) baseStart_2766550 baseEnd_2766550 := by
    simpa [prefixWord, tailWord_2766550, baseEnd_2766550] using wordTrace_append hprefix tailTrace_2766550
  have hstable : (prefixWord ++ tailWord_2766550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766550).length < 2 ^ (prefixWord ++ tailWord_2766550).sum := by decide
  have hdescent : baseEnd_2766550 < baseStart_2766550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766575 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_2766575 : Nat := 118140960795 + 2766575 * 2 ^ 59
def prefixEnd_2766575 : Nat := 4983230072969 + 3 ^ 40 * 2766575 * 2
def baseEnd_2766575 : Nat := 1420582741712618496289259

theorem tailTrace_2766575 : CollatzResearch.WordTrace tailWord_2766575 prefixEnd_2766575 1420582741712618496289259 := by
  unfold tailWord_2766575
  simp only [CollatzResearch.WordTrace]
  refine ⟨100905279952178743237989179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67270186634785828825326119 100905279952178743237989179)
  ·
    refine ⟨151357919928268114856983769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100905279952178743237989179 151357919928268114856983769)
    ·
      refine ⟨113518439946201086142737827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151357919928268114856983769 113518439946201086142737827)
      ·
        refine ⟨170277659919301629214106741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113518439946201086142737827 170277659919301629214106741)
        ·
          refine ⟨15963530617434527738822507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170277659919301629214106741 15963530617434527738822507)
          ·
            refine ⟨23945295926151791608233761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15963530617434527738822507 23945295926151791608233761)
            ·
              refine ⟨17958971944613843706175321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23945295926151791608233761 17958971944613843706175321)
              ·
                refine ⟨13469228958460382779631491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17958971944613843706175321 13469228958460382779631491)
                ·
                  refine ⟨20203843437690574169447237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13469228958460382779631491 20203843437690574169447237)
                  ·
                    refine ⟨3788220644566982656771357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20203843437690574169447237 3788220644566982656771357)
                    ·
                      refine ⟨1420582741712618496289259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788220644566982656771357 1420582741712618496289259)
                      ·
                        rfl

theorem cell23_2766575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_2766575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766575 prefixEnd_2766575 := by exact prefixLift 2766575
  have htrace : WordTrace (prefixWord ++ tailWord_2766575) baseStart_2766575 baseEnd_2766575 := by
    simpa [prefixWord, tailWord_2766575, baseEnd_2766575] using wordTrace_append hprefix tailTrace_2766575
  have hstable : (prefixWord ++ tailWord_2766575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766575).length < 2 ^ (prefixWord ++ tailWord_2766575).sum := by decide
  have hdescent : baseEnd_2766575 < baseStart_2766575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766582 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2766582 : Nat := 118140960795 + 2766582 * 2 ^ 59
def prefixEnd_2766582 : Nat := 4983230072969 + 3 ^ 40 * 2766582 * 2
def baseEnd_2766582 : Nat := 473528778692399989633909

theorem tailTrace_2766582 : CollatzResearch.WordTrace tailWord_2766582 prefixEnd_2766582 473528778692399989633909 := by
  unfold tailWord_2766582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306595953947086464593375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67270356842102255622329333 6306595953947086464593375)
  ·
    refine ⟨9459893930920629696890063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6306595953947086464593375 9459893930920629696890063)
    ·
      refine ⟨14189840896380944545335095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9459893930920629696890063 14189840896380944545335095)
      ·
        refine ⟨21284761344571416818002643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14189840896380944545335095 21284761344571416818002643)
        ·
          refine ⟨31927142016857125227003965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21284761344571416818002643 31927142016857125227003965)
          ·
            refine ⟨11972678256321421960126487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31927142016857125227003965 11972678256321421960126487)
            ·
              refine ⟨17959017384482132940189731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972678256321421960126487 17959017384482132940189731)
              ·
                refine ⟨26938526076723199410284597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17959017384482132940189731 26938526076723199410284597)
                ·
                  refine ⟨2525486819692799944714181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26938526076723199410284597 2525486819692799944714181)
                  ·
                    refine ⟨473528778692399989633909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525486819692799944714181 473528778692399989633909)
                    ·
                      rfl

theorem cell23_2766582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2766582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766582 prefixEnd_2766582 := by exact prefixLift 2766582
  have htrace : WordTrace (prefixWord ++ tailWord_2766582) baseStart_2766582 baseEnd_2766582 := by
    simpa [prefixWord, tailWord_2766582, baseEnd_2766582] using wordTrace_append hprefix tailTrace_2766582
  have hstable : (prefixWord ++ tailWord_2766582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766582).length < 2 ^ (prefixWord ++ tailWord_2766582).sum := by decide
  have hdescent : baseEnd_2766582 < baseStart_2766582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766615 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2766615 : Nat := 118140960795 + 2766615 * 2 ^ 59
def prefixEnd_2766615 : Nat := 4983230072969 + 3 ^ 40 * 2766615 * 2
def baseEnd_2766615 : Nat := 1420603280938798339789075

theorem tailTrace_2766615 : CollatzResearch.WordTrace tailWord_2766615 prefixEnd_2766615 1420603280938798339789075 := by
  unfold tailWord_2766615
  simp only [CollatzResearch.WordTrace]
  refine ⟨100906738872033830069445299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67271159248022553379630199 100906738872033830069445299)
  ·
    refine ⟨151360108308050745104167949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100906738872033830069445299 151360108308050745104167949)
    ·
      refine ⟨56760040615519029414062981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151360108308050745104167949 56760040615519029414062981)
      ·
        refine ⟨10642507615409818015136809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56760040615519029414062981 10642507615409818015136809)
        ·
          refine ⟨7981880711557363511352607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10642507615409818015136809 7981880711557363511352607)
          ·
            refine ⟨11972821067336045267028911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981880711557363511352607 11972821067336045267028911)
            ·
              refine ⟨17959231601004067900543367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972821067336045267028911 17959231601004067900543367)
              ·
                refine ⟨26938847401506101850815051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17959231601004067900543367 26938847401506101850815051)
                ·
                  refine ⟨40408271102259152776222577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26938847401506101850815051 40408271102259152776222577)
                  ·
                    refine ⟨30306203326694364582166933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40408271102259152776222577 30306203326694364582166933)
                    ·
                      refine ⟨1420603280938798339789075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30306203326694364582166933 1420603280938798339789075)
                      ·
                        rfl

theorem cell23_2766615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2766615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766615 prefixEnd_2766615 := by exact prefixLift 2766615
  have htrace : WordTrace (prefixWord ++ tailWord_2766615) baseStart_2766615 baseEnd_2766615 := by
    simpa [prefixWord, tailWord_2766615, baseEnd_2766615] using wordTrace_append hprefix tailTrace_2766615
  have hstable : (prefixWord ++ tailWord_2766615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766615).length < 2 ^ (prefixWord ++ tailWord_2766615).sum := by decide
  have hdescent : baseEnd_2766615 < baseStart_2766615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766642 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2766642 : Nat := 118140960795 + 2766642 * 2 ^ 59
def prefixEnd_2766642 : Nat := 4983230072969 + 3 ^ 40 * 2766642 * 2
def baseEnd_2766642 : Nat := 473539048305489911383817

theorem tailTrace_2766642 : CollatzResearch.WordTrace tailWord_2766642 prefixEnd_2766642 473539048305489911383817 := by
  unfold tailWord_2766642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226930910734003420169545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67271815761957342453785453 25226930910734003420169545)
  ·
    refine ⟨18920198183050502565127159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25226930910734003420169545 18920198183050502565127159)
    ·
      refine ⟨28380297274575753847690739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18920198183050502565127159 28380297274575753847690739)
      ·
        refine ⟨42570445911863630771536109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28380297274575753847690739 42570445911863630771536109)
        ·
          refine ⟨15963917216948861539326041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42570445911863630771536109 15963917216948861539326041)
          ·
            refine ⟨11972937912711646154494531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15963917216948861539326041 11972937912711646154494531)
            ·
              refine ⟨17959406869067469231741797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972937912711646154494531 17959406869067469231741797)
              ·
                refine ⟨3367388787950150480951587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17959406869067469231741797 3367388787950150480951587)
                ·
                  refine ⟨5051083181925225721427381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367388787950150480951587 5051083181925225721427381)
                  ·
                    refine ⟨473539048305489911383817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5051083181925225721427381 473539048305489911383817)
                    ·
                      rfl

theorem cell23_2766642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2766642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766642 prefixEnd_2766642 := by exact prefixLift 2766642
  have htrace : WordTrace (prefixWord ++ tailWord_2766642) baseStart_2766642 baseEnd_2766642 := by
    simpa [prefixWord, tailWord_2766642, baseEnd_2766642] using wordTrace_append hprefix tailTrace_2766642
  have hstable : (prefixWord ++ tailWord_2766642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766642).length < 2 ^ (prefixWord ++ tailWord_2766642).sum := by decide
  have hdescent : baseEnd_2766642 < baseStart_2766642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766672 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_2766672 : Nat := 118140960795 + 2766672 * 2 ^ 59
def prefixEnd_2766672 : Nat := 4983230072969 + 3 ^ 40 * 2766672 * 2
def baseEnd_2766672 : Nat := 473544183112034872258771

theorem tailTrace_2766672 : CollatzResearch.WordTrace tailWord_2766672 prefixEnd_2766672 473544183112034872258771 := by
  unfold tailWord_2766672
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454408916413664402135135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67272545221884885869513513 50454408916413664402135135)
  ·
    refine ⟨75681613374620496603202703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50454408916413664402135135 75681613374620496603202703)
    ·
      refine ⟨113522420061930744904804055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75681613374620496603202703 113522420061930744904804055)
      ·
        refine ⟨170283630092896117357206083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113522420061930744904804055 170283630092896117357206083)
        ·
          refine ⟨255425445139344176035809125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170283630092896117357206083 255425445139344176035809125)
          ·
            refine ⟨47892270963627033006714211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255425445139344176035809125 47892270963627033006714211)
            ·
              refine ⟨71838406445440549510071317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47892270963627033006714211 71838406445440549510071317)
              ·
                refine ⟨3367425302130025758284593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71838406445440549510071317 3367425302130025758284593)
                ·
                  refine ⟨2525568976597519318713445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367425302130025758284593 2525568976597519318713445)
                  ·
                    refine ⟨473544183112034872258771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525568976597519318713445 473544183112034872258771)
                    ·
                      rfl

theorem cell23_2766672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_2766672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766672 prefixEnd_2766672 := by exact prefixLift 2766672
  have htrace : WordTrace (prefixWord ++ tailWord_2766672) baseStart_2766672 baseEnd_2766672 := by
    simpa [prefixWord, tailWord_2766672, baseEnd_2766672] using wordTrace_append hprefix tailTrace_2766672
  have hstable : (prefixWord ++ tailWord_2766672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766672).length < 2 ^ (prefixWord ++ tailWord_2766672).sum := by decide
  have hdescent : baseEnd_2766672 < baseStart_2766672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766673 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_2766673 : Nat := 118140960795 + 2766673 * 2 ^ 59
def prefixEnd_2766673 : Nat := 4983230072969 + 3 ^ 40 * 2766673 * 2
def baseEnd_2766673 : Nat := 1420633062816759112863809

theorem tailTrace_2766673 : CollatzResearch.WordTrace tailWord_2766673 prefixEnd_2766673 1420633062816759112863809 := by
  unfold tailWord_2766673
  simp only [CollatzResearch.WordTrace]
  refine ⟨100908854305823705975056673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67272569537215803983371115 100908854305823705975056673)
  ·
    refine ⟨75681640729367779481292505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100908854305823705975056673 75681640729367779481292505)
    ·
      refine ⟨56761230547025834610969379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75681640729367779481292505 56761230547025834610969379)
      ·
        refine ⟨85141845820538751916454069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56761230547025834610969379 85141845820538751916454069)
        ·
          refine ⟨7982048045675507992167569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85141845820538751916454069 7982048045675507992167569)
          ·
            refine ⟨5986536034256630994125677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7982048045675507992167569 5986536034256630994125677)
            ·
              refine ⟨2244951012846236622797129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5986536034256630994125677 2244951012846236622797129)
              ·
                refine ⟨1683713259634677467097847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244951012846236622797129 1683713259634677467097847)
                ·
                  refine ⟨2525569889452016200646771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683713259634677467097847 2525569889452016200646771)
                  ·
                    refine ⟨3788354834178024300970157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525569889452016200646771 3788354834178024300970157)
                    ·
                      refine ⟨1420633062816759112863809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788354834178024300970157 1420633062816759112863809)
                      ·
                        rfl

theorem cell23_2766673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_2766673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766673 prefixEnd_2766673 := by exact prefixLift 2766673
  have htrace : WordTrace (prefixWord ++ tailWord_2766673) baseStart_2766673 baseEnd_2766673 := by
    simpa [prefixWord, tailWord_2766673, baseEnd_2766673] using wordTrace_append hprefix tailTrace_2766673
  have hstable : (prefixWord ++ tailWord_2766673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766673).length < 2 ^ (prefixWord ++ tailWord_2766673).sum := by decide
  have hdescent : baseEnd_2766673 < baseStart_2766673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766682 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2766682 : Nat := 118140960795 + 2766682 * 2 ^ 59
def prefixEnd_2766682 : Nat := 4983230072969 + 3 ^ 40 * 2766682 * 2
def baseEnd_2766682 : Nat := 1420637684142649577651267

theorem tailTrace_2766682 : CollatzResearch.WordTrace tailWord_2766682 prefixEnd_2766682 1420637684142649577651267 := by
  unfold tailWord_2766682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227295640697775128033575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67272788375194067008089533 25227295640697775128033575)
  ·
    refine ⟨37840943461046662692050363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25227295640697775128033575 37840943461046662692050363)
    ·
      refine ⟨56761415191569994038075545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37840943461046662692050363 56761415191569994038075545)
      ·
        refine ⟨42571061393677495528556659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56761415191569994038075545 42571061393677495528556659)
        ·
          refine ⟨63856592090516243292834989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42571061393677495528556659 63856592090516243292834989)
          ·
            refine ⟨23946222033943591234813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63856592090516243292834989 23946222033943591234813121)
            ·
              refine ⟨17959666525457693426109841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23946222033943591234813121 17959666525457693426109841)
              ·
                refine ⟨13469749894093270069582381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17959666525457693426109841 13469749894093270069582381)
                ·
                  refine ⟨5051156210284976276093393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13469749894093270069582381 5051156210284976276093393)
                  ·
                    refine ⟨3788367157713732207070045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5051156210284976276093393 3788367157713732207070045)
                    ·
                      refine ⟨1420637684142649577651267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788367157713732207070045 1420637684142649577651267)
                      ·
                        rfl

theorem cell23_2766682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2766682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766682 prefixEnd_2766682 := by exact prefixLift 2766682
  have htrace : WordTrace (prefixWord ++ tailWord_2766682) baseStart_2766682 baseEnd_2766682 := by
    simpa [prefixWord, tailWord_2766682, baseEnd_2766682] using wordTrace_append hprefix tailTrace_2766682
  have hstable : (prefixWord ++ tailWord_2766682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766682).length < 2 ^ (prefixWord ++ tailWord_2766682).sum := by decide
  have hdescent : baseEnd_2766682 < baseStart_2766682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766702 : List Nat := [4, 1, 2, 3, 1, 1, 2, 9]
def baseStart_2766702 : Nat := 118140960795 + 2766702 * 2 ^ 59
def prefixEnd_2766702 : Nat := 4983230072969 + 3 ^ 40 * 2766702 * 2
def baseEnd_2766702 : Nat := 52616590879842203681525

theorem tailTrace_2766702 : CollatzResearch.WordTrace tailWord_2766702 prefixEnd_2766702 52616590879842203681525 := by
  unfold tailWord_2766702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613739002839830490982795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67273274681812429285241573 12613739002839830490982795)
  ·
    refine ⟨18920608504259745736474193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12613739002839830490982795 18920608504259745736474193)
    ·
      refine ⟨14190456378194809302355645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18920608504259745736474193 14190456378194809302355645)
      ·
        refine ⟨5321421141823053488383367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14190456378194809302355645 5321421141823053488383367)
        ·
          refine ⟨7982131712734580232575051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321421141823053488383367 7982131712734580232575051)
          ·
            refine ⟨11973197569101870348862577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982131712734580232575051 11973197569101870348862577)
            ·
              refine ⟨8979898176826402761646933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11973197569101870348862577 8979898176826402761646933)
              ·
                refine ⟨52616590879842203681525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8979898176826402761646933 52616590879842203681525)
                ·
                  rfl

theorem cell23_2766702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_2766702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766702 prefixEnd_2766702 := by exact prefixLift 2766702
  have htrace : WordTrace (prefixWord ++ tailWord_2766702) baseStart_2766702 baseEnd_2766702 := by
    simpa [prefixWord, tailWord_2766702, baseEnd_2766702] using wordTrace_append hprefix tailTrace_2766702
  have hstable : (prefixWord ++ tailWord_2766702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766702).length < 2 ^ (prefixWord ++ tailWord_2766702).sum := by decide
  have hdescent : baseEnd_2766702 < baseStart_2766702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766730 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2766730 : Nat := 118140960795 + 2766730 * 2 ^ 59
def prefixEnd_2766730 : Nat := 4983230072969 + 3 ^ 40 * 2766730 * 2
def baseEnd_2766730 : Nat := 1420662331214065389851047

theorem tailTrace_2766730 : CollatzResearch.WordTrace tailWord_2766730 prefixEnd_2766730 1420662331214065389851047 := by
  unfold tailWord_2766730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227733316654301177470411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67273955511078136473254429 25227733316654301177470411)
  ·
    refine ⟨37841599974981451766205617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25227733316654301177470411 37841599974981451766205617)
    ·
      refine ⟨28381199981236088824654213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37841599974981451766205617 28381199981236088824654213)
      ·
        refine ⟨5321474996481766654622665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28381199981236088824654213 5321474996481766654622665)
        ·
          refine ⟨3991106247361324990966999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5321474996481766654622665 3991106247361324990966999)
          ·
            refine ⟨5986659371041987486450499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991106247361324990966999 5986659371041987486450499)
            ·
              refine ⟨8979989056562981229675749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986659371041987486450499 8979989056562981229675749)
              ·
                refine ⟨1683747948105558980564203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8979989056562981229675749 1683747948105558980564203)
                ·
                  refine ⟨2525621922158338470846305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683747948105558980564203 2525621922158338470846305)
                  ·
                    refine ⟨1894216441618753853134729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525621922158338470846305 1894216441618753853134729)
                    ·
                      refine ⟨1420662331214065389851047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894216441618753853134729 1420662331214065389851047)
                      ·
                        rfl

theorem cell23_2766730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2766730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766730 prefixEnd_2766730 := by exact prefixLift 2766730
  have htrace : WordTrace (prefixWord ++ tailWord_2766730) baseStart_2766730 baseEnd_2766730 := by
    simpa [prefixWord, tailWord_2766730, baseEnd_2766730] using wordTrace_append hprefix tailTrace_2766730
  have hstable : (prefixWord ++ tailWord_2766730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766730).length < 2 ^ (prefixWord ++ tailWord_2766730).sum := by decide
  have hdescent : baseEnd_2766730 < baseStart_2766730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766745 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_2766745 : Nat := 118140960795 + 2766745 * 2 ^ 59
def prefixEnd_2766745 : Nat := 4983230072969 + 3 ^ 40 * 2766745 * 2
def baseEnd_2766745 : Nat := 473556677807960943721159

theorem tailTrace_2766745 : CollatzResearch.WordTrace tailWord_2766745 prefixEnd_2766745 473556677807960943721159 := by
  unfold tailWord_2766745
  simp only [CollatzResearch.WordTrace]
  refine ⟨100911480361562862271677689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67274320241041908181118459 100911480361562862271677689)
  ·
    refine ⟨75683610271172146703758267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100911480361562862271677689 75683610271172146703758267)
    ·
      refine ⟨113525415406758220055637401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75683610271172146703758267 113525415406758220055637401)
      ·
        refine ⟨85144061555068665041728051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113525415406758220055637401 85144061555068665041728051)
        ·
          refine ⟨127716092332602997562592077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85144061555068665041728051 127716092332602997562592077)
          ·
            refine ⟨47893534624726124085972029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127716092332602997562592077 47893534624726124085972029)
            ·
              refine ⟨17960075484272296532239511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47893534624726124085972029 17960075484272296532239511)
              ·
                refine ⟨26940113226408444798359267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17960075484272296532239511 26940113226408444798359267)
                ·
                  refine ⟨40410169839612667197538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26940113226408444798359267 40410169839612667197538901)
                  ·
                    refine ⟨473556677807960943721159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40410169839612667197538901 473556677807960943721159)
                    ·
                      rfl

theorem cell23_2766745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_2766745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766745 prefixEnd_2766745 := by exact prefixLift 2766745
  have htrace : WordTrace (prefixWord ++ tailWord_2766745) baseStart_2766745 baseEnd_2766745 := by
    simpa [prefixWord, tailWord_2766745, baseEnd_2766745] using wordTrace_append hprefix tailTrace_2766745
  have hstable : (prefixWord ++ tailWord_2766745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766745).length < 2 ^ (prefixWord ++ tailWord_2766745).sum := by decide
  have hdescent : baseEnd_2766745 < baseStart_2766745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766746 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2766746 : Nat := 118140960795 + 2766746 * 2 ^ 59
def prefixEnd_2766746 : Nat := 4983230072969 + 3 ^ 40 * 2766746 * 2
def baseEnd_2766746 : Nat := 1420670546904537327250973

theorem tailTrace_2766746 : CollatzResearch.WordTrace tailWord_2766746 prefixEnd_2766746 1420670546904537327250973 := by
  unfold tailWord_2766746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25227879208639809860616023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67274344556372826294976061 25227879208639809860616023)
  ·
    refine ⟨37841818812959714790924035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25227879208639809860616023 37841818812959714790924035)
    ·
      refine ⟨56762728219439572186386053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37841818812959714790924035 56762728219439572186386053)
      ·
        refine ⟨10643011541144919784947385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56762728219439572186386053 10643011541144919784947385)
        ·
          refine ⟨7982258655858689838710539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10643011541144919784947385 7982258655858689838710539)
          ·
            refine ⟨11973387983788034758065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982258655858689838710539 11973387983788034758065809)
            ·
              refine ⟨8980040987841026068549357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11973387983788034758065809 8980040987841026068549357)
              ·
                refine ⟨3367515370440384775706009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8980040987841026068549357 3367515370440384775706009)
                ·
                  refine ⟨2525636527830288581779507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367515370440384775706009 2525636527830288581779507)
                  ·
                    refine ⟨3788454791745432872669261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525636527830288581779507 3788454791745432872669261)
                    ·
                      refine ⟨1420670546904537327250973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788454791745432872669261 1420670546904537327250973)
                      ·
                        rfl

theorem cell23_2766746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2766746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766746 prefixEnd_2766746 := by exact prefixLift 2766746
  have htrace : WordTrace (prefixWord ++ tailWord_2766746) baseStart_2766746 baseEnd_2766746 := by
    simpa [prefixWord, tailWord_2766746, baseEnd_2766746] using wordTrace_append hprefix tailTrace_2766746
  have hstable : (prefixWord ++ tailWord_2766746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766746).length < 2 ^ (prefixWord ++ tailWord_2766746).sum := by decide
  have hdescent : baseEnd_2766746 < baseStart_2766746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766773 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_2766773 : Nat := 118140960795 + 2766773 * 2 ^ 59
def prefixEnd_2766773 : Nat := 4983230072969 + 3 ^ 40 * 2766773 * 2
def baseEnd_2766773 : Nat := 1420684410882208721613349

theorem tailTrace_2766773 : CollatzResearch.WordTrace tailWord_2766773 prefixEnd_2766773 1420684410882208721613349 := by
  unfold tailWord_2766773
  simp only [CollatzResearch.WordTrace]
  refine ⟨100912501605461423053696973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67275001070307615369131315 100912501605461423053696973)
  ·
    refine ⟨37842188102048033645136365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100912501605461423053696973 37842188102048033645136365)
    ·
      refine ⟨14190820538268012616926137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37842188102048033645136365 14190820538268012616926137)
      ·
        refine ⟨10643115403701009462694603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14190820538268012616926137 10643115403701009462694603)
        ·
          refine ⟨15964673105551514194041905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10643115403701009462694603 15964673105551514194041905)
          ·
            refine ⟨11973504829163635645531429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15964673105551514194041905 11973504829163635645531429)
            ·
              refine ⟨2245032155468181683537143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11973504829163635645531429 2245032155468181683537143)
              ·
                refine ⟨3367548233202272525305715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245032155468181683537143 3367548233202272525305715)
                ·
                  refine ⟨5051322349803408787958573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367548233202272525305715 5051322349803408787958573)
                  ·
                    refine ⟨1894245881176278295484465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5051322349803408787958573 1894245881176278295484465)
                    ·
                      refine ⟨1420684410882208721613349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894245881176278295484465 1420684410882208721613349)
                      ·
                        rfl

theorem cell23_2766773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_2766773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766773 prefixEnd_2766773 := by exact prefixLift 2766773
  have htrace : WordTrace (prefixWord ++ tailWord_2766773) baseStart_2766773 baseEnd_2766773 := by
    simpa [prefixWord, tailWord_2766773, baseEnd_2766773] using wordTrace_append hprefix tailTrace_2766773
  have hstable : (prefixWord ++ tailWord_2766773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766773).length < 2 ^ (prefixWord ++ tailWord_2766773).sum := by decide
  have hdescent : baseEnd_2766773 < baseStart_2766773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766775 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 11]
def baseStart_2766775 : Nat := 118140960795 + 2766775 * 2 ^ 59
def prefixEnd_2766775 : Nat := 4983230072969 + 3 ^ 40 * 2766775 * 2
def baseEnd_2766775 : Nat := 157853937538168634865371

theorem tailTrace_2766775 : CollatzResearch.WordTrace tailWord_2766775 prefixEnd_2766775 157853937538168634865371 := by
  unfold tailWord_2766775
  simp only [CollatzResearch.WordTrace]
  refine ⟨100912574551454177395269779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67275049700969451596846519 100912574551454177395269779)
  ·
    refine ⟨151368861827181266092904669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100912574551454177395269779 151368861827181266092904669)
    ·
      refine ⟨56763323185192974784839251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151368861827181266092904669 56763323185192974784839251)
      ·
        refine ⟨85144984777789462177258877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56763323185192974784839251 85144984777789462177258877)
        ·
          refine ⟨31929369291671048316472079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85144984777789462177258877 31929369291671048316472079)
          ·
            refine ⟨47894053937506572474708119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31929369291671048316472079 47894053937506572474708119)
            ·
              refine ⟨71841080906259858712062179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47894053937506572474708119 71841080906259858712062179)
              ·
                refine ⟨107761621359389788068093269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71841080906259858712062179 107761621359389788068093269)
                ·
                  refine ⟨157853937538168634865371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 107761621359389788068093269 157853937538168634865371)
                  ·
                    rfl

theorem cell23_2766775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 11].length) (baseStart_2766775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766775 prefixEnd_2766775 := by exact prefixLift 2766775
  have htrace : WordTrace (prefixWord ++ tailWord_2766775) baseStart_2766775 baseEnd_2766775 := by
    simpa [prefixWord, tailWord_2766775, baseEnd_2766775] using wordTrace_append hprefix tailTrace_2766775
  have hstable : (prefixWord ++ tailWord_2766775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766775).length < 2 ^ (prefixWord ++ tailWord_2766775).sum := by decide
  have hdescent : baseEnd_2766775 < baseStart_2766775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766780 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2766780 : Nat := 118140960795 + 2766780 * 2 ^ 59
def prefixEnd_2766780 : Nat := 4983230072969 + 3 ^ 40 * 2766780 * 2
def baseEnd_2766780 : Nat := 1420688005246790194225817

theorem tailTrace_2766780 : CollatzResearch.WordTrace tailWord_2766780 prefixEnd_2766780 1420688005246790194225817 := by
  unfold tailWord_2766780
  simp only [CollatzResearch.WordTrace]
  refine ⟨50456378458218031624600897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67275171277624042166134529 50456378458218031624600897)
  ·
    refine ⟨37842283843663523718450673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50456378458218031624600897 37842283843663523718450673)
    ·
      refine ⟨28381712882747642788838005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37842283843663523718450673 28381712882747642788838005)
      ·
        refine ⟨2660785582757591511453563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28381712882747642788838005 2660785582757591511453563)
        ·
          refine ⟨3991178374136387267180345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660785582757591511453563 3991178374136387267180345)
          ·
            refine ⟨2993383780602290450385259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3991178374136387267180345 2993383780602290450385259)
            ·
              refine ⟨4490075670903435675577889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993383780602290450385259 4490075670903435675577889)
              ·
                refine ⟨3367556753177576756683417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4490075670903435675577889 3367556753177576756683417)
                ·
                  refine ⟨2525667564883182567512563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367556753177576756683417 2525667564883182567512563)
                  ·
                    refine ⟨3788501347324773851268845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525667564883182567512563 3788501347324773851268845)
                    ·
                      refine ⟨1420688005246790194225817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788501347324773851268845 1420688005246790194225817)
                      ·
                        rfl

theorem cell23_2766780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2766780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766780 prefixEnd_2766780 := by exact prefixLift 2766780
  have htrace : WordTrace (prefixWord ++ tailWord_2766780) baseStart_2766780 baseEnd_2766780 := by
    simpa [prefixWord, tailWord_2766780, baseEnd_2766780] using wordTrace_append hprefix tailTrace_2766780
  have hstable : (prefixWord ++ tailWord_2766780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766780).length < 2 ^ (prefixWord ++ tailWord_2766780).sum := by decide
  have hdescent : baseEnd_2766780 < baseStart_2766780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766792 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 7]
def baseStart_2766792 : Nat := 118140960795 + 2766792 * 2 ^ 59
def prefixEnd_2766792 : Nat := 4983230072969 + 3 ^ 40 * 2766792 * 2
def baseEnd_2766792 : Nat := 157854907446071571919529

theorem tailTrace_2766792 : CollatzResearch.WordTrace tailWord_2766792 prefixEnd_2766792 157854907446071571919529 := by
  unfold tailWord_2766792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50456597296196294649319315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67275463061595059532425753 50456597296196294649319315)
  ·
    refine ⟨75684895944294441973978973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50456597296196294649319315 75684895944294441973978973)
    ·
      refine ⟨28381835979110415740242115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75684895944294441973978973 28381835979110415740242115)
      ·
        refine ⟨42572753968665623610363173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28381835979110415740242115 42572753968665623610363173)
        ·
          refine ⟨7982391369124804426943095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42572753968665623610363173 7982391369124804426943095)
          ·
            refine ⟨11973587053687206640414643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982391369124804426943095 11973587053687206640414643)
            ·
              refine ⟨17960380580530809960621965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11973587053687206640414643 17960380580530809960621965)
              ·
                refine ⟨6735142717699053735233237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17960380580530809960621965 6735142717699053735233237)
                ·
                  refine ⟨157854907446071571919529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6735142717699053735233237 157854907446071571919529)
                  ·
                    rfl

theorem cell23_2766792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_2766792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766792 prefixEnd_2766792 := by exact prefixLift 2766792
  have htrace : WordTrace (prefixWord ++ tailWord_2766792) baseStart_2766792 baseEnd_2766792 := by
    simpa [prefixWord, tailWord_2766792, baseEnd_2766792] using wordTrace_append hprefix tailTrace_2766792
  have hstable : (prefixWord ++ tailWord_2766792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766792).length < 2 ^ (prefixWord ++ tailWord_2766792).sum := by decide
  have hdescent : baseEnd_2766792 < baseStart_2766792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766859 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 6, 2]
def baseStart_2766859 : Nat := 118140960795 + 2766859 * 2 ^ 59
def prefixEnd_2766859 : Nat := 4983230072969 + 3 ^ 40 * 2766859 * 2
def baseEnd_2766859 : Nat := 1420728570218495385137953

theorem tailTrace_2766859 : CollatzResearch.WordTrace tailWord_2766859 prefixEnd_2766859 1420728570218495385137953 := by
  unfold tailWord_2766859
  simp only [CollatzResearch.WordTrace]
  refine ⟨100915638283149859741327631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67277092188766573160885087 100915638283149859741327631)
  ·
    refine ⟨151373457424724789611991447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100915638283149859741327631 151373457424724789611991447)
    ·
      refine ⟨227060186137087184417987171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151373457424724789611991447 227060186137087184417987171)
      ·
        refine ⟨340590279205630776626980757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227060186137087184417987171 340590279205630776626980757)
        ·
          refine ⟨15965169337763942654389723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 340590279205630776626980757 15965169337763942654389723)
          ·
            refine ⟨23947754006645913981584585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15965169337763942654389723 23947754006645913981584585)
            ·
              refine ⟨17960815504984435486188439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23947754006645913981584585 17960815504984435486188439)
              ·
                refine ⟨26941223257476653229282659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17960815504984435486188439 26941223257476653229282659)
                ·
                  refine ⟨40411834886214979843923989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26941223257476653229282659 40411834886214979843923989)
                  ·
                    refine ⟨1894304760291327180183937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40411834886214979843923989 1894304760291327180183937)
                    ·
                      refine ⟨1420728570218495385137953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894304760291327180183937 1420728570218495385137953)
                      ·
                        rfl

theorem cell23_2766859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6, 2].length) (baseStart_2766859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766859 prefixEnd_2766859 := by exact prefixLift 2766859
  have htrace : WordTrace (prefixWord ++ tailWord_2766859) baseStart_2766859 baseEnd_2766859 := by
    simpa [prefixWord, tailWord_2766859, baseEnd_2766859] using wordTrace_append hprefix tailTrace_2766859
  have hstable : (prefixWord ++ tailWord_2766859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766859).length < 2 ^ (prefixWord ++ tailWord_2766859).sum := by decide
  have hdescent : baseEnd_2766859 < baseStart_2766859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766876 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2766876 : Nat := 118140960795 + 2766876 * 2 ^ 59
def prefixEnd_2766876 : Nat := 4983230072969 + 3 ^ 40 * 2766876 * 2
def baseEnd_2766876 : Nat := 1420737299389621818625375

theorem tailTrace_2766876 : CollatzResearch.WordTrace tailWord_2766876 prefixEnd_2766876 1420737299389621818625375 := by
  unfold tailWord_2766876
  simp only [CollatzResearch.WordTrace]
  refine ⟨50458129162044135822348241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67277505549392181096464321 50458129162044135822348241)
  ·
    refine ⟨37843596871533101866761181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50458129162044135822348241 37843596871533101866761181)
    ·
      refine ⟨14191348826824913200035443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37843596871533101866761181 14191348826824913200035443)
      ·
        refine ⟨21287023240237369800053165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191348826824913200035443 21287023240237369800053165)
        ·
          refine ⟨7982633715089013675019937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21287023240237369800053165 7982633715089013675019937)
          ·
            refine ⟨5986975286316760256264953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7982633715089013675019937 5986975286316760256264953)
            ·
              refine ⟨4490231464737570192198715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5986975286316760256264953 4490231464737570192198715)
              ·
                refine ⟨6735347197106355288298073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490231464737570192198715 6735347197106355288298073)
                ·
                  refine ⟨5051510397829766466223555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6735347197106355288298073 5051510397829766466223555)
                  ·
                    refine ⟨7577265596744649699335333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5051510397829766466223555 7577265596744649699335333)
                    ·
                      refine ⟨1420737299389621818625375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7577265596744649699335333 1420737299389621818625375)
                      ·
                        rfl

theorem cell23_2766876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2766876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766876 prefixEnd_2766876 := by exact prefixLift 2766876
  have htrace : WordTrace (prefixWord ++ tailWord_2766876) baseStart_2766876 baseEnd_2766876 := by
    simpa [prefixWord, tailWord_2766876, baseEnd_2766876] using wordTrace_append hprefix tailTrace_2766876
  have hstable : (prefixWord ++ tailWord_2766876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766876).length < 2 ^ (prefixWord ++ tailWord_2766876).sum := by decide
  have hdescent : baseEnd_2766876 < baseStart_2766876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766903 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 1, 4]
def baseStart_2766903 : Nat := 118140960795 + 2766903 * 2 ^ 59
def prefixEnd_2766903 : Nat := 4983230072969 + 3 ^ 40 * 2766903 * 2
def baseEnd_2766903 : Nat := 473583721122431070995917

theorem tailTrace_2766903 : CollatzResearch.WordTrace tailWord_2766903 prefixEnd_2766903 473583721122431070995917 := by
  unfold tailWord_2766903
  simp only [CollatzResearch.WordTrace]
  refine ⟨100917243094990455255929363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67278162063326970170619575 100917243094990455255929363)
  ·
    refine ⟨151375864642485682883894045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100917243094990455255929363 151375864642485682883894045)
    ·
      refine ⟨56765949240932131081460267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151375864642485682883894045 56765949240932131081460267)
      ·
        refine ⟨85148923861398196622190401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56765949240932131081460267 85148923861398196622190401)
        ·
          refine ⟨63861692896048647466642801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85148923861398196622190401 63861692896048647466642801)
          ·
            refine ⟨47896269672036485599982101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63861692896048647466642801 47896269672036485599982101)
            ·
              refine ⟨2245137640876710262499161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47896269672036485599982101 2245137640876710262499161)
              ·
                refine ⟨1683853230657532696874371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245137640876710262499161 1683853230657532696874371)
                ·
                  refine ⟨2525779845986299045311557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683853230657532696874371 2525779845986299045311557)
                  ·
                    refine ⟨473583721122431070995917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525779845986299045311557 473583721122431070995917)
                    ·
                      rfl

theorem cell23_2766903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_2766903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766903 prefixEnd_2766903 := by exact prefixLift 2766903
  have htrace : WordTrace (prefixWord ++ tailWord_2766903) baseStart_2766903 baseEnd_2766903 := by
    simpa [prefixWord, tailWord_2766903, baseEnd_2766903] using wordTrace_append hprefix tailTrace_2766903
  have hstable : (prefixWord ++ tailWord_2766903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766903).length < 2 ^ (prefixWord ++ tailWord_2766903).sum := by decide
  have hdescent : baseEnd_2766903 < baseStart_2766903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766922 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2766922 : Nat := 118140960795 + 2766922 * 2 ^ 59
def prefixEnd_2766922 : Nat := 4983230072969 + 3 ^ 40 * 2766922 * 2
def baseEnd_2766922 : Nat := 1420760919499728638650163

theorem tailTrace_2766922 : CollatzResearch.WordTrace tailWord_2766922 prefixEnd_2766922 1420760919499728638650163 := by
  unfold tailWord_2766922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25229484020480405375217755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67278624054614414333914013 25229484020480405375217755)
  ·
    refine ⟨37844226030720608062826633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25229484020480405375217755 37844226030720608062826633)
    ·
      refine ⟨28383169523040456047119975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37844226030720608062826633 28383169523040456047119975)
      ·
        refine ⟨42574754284560684070679963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28383169523040456047119975 42574754284560684070679963)
        ·
          refine ⟨63862131426841026106019945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42574754284560684070679963 63862131426841026106019945)
          ·
            refine ⟨47896598570130769579514959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63862131426841026106019945 47896598570130769579514959)
            ·
              refine ⟨71844897855196154369272439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47896598570130769579514959 71844897855196154369272439)
              ·
                refine ⟨107767346782794231553908659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71844897855196154369272439 107767346782794231553908659)
                ·
                  refine ⟨161651020174191347330862989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107767346782794231553908659 161651020174191347330862989)
                  ·
                    refine ⟨60619132565321755249073621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161651020174191347330862989 60619132565321755249073621)
                    ·
                      refine ⟨1420760919499728638650163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60619132565321755249073621 1420760919499728638650163)
                      ·
                        rfl

theorem cell23_2766922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2766922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766922 prefixEnd_2766922 := by exact prefixLift 2766922
  have htrace : WordTrace (prefixWord ++ tailWord_2766922) baseStart_2766922 baseEnd_2766922 := by
    simpa [prefixWord, tailWord_2766922, baseEnd_2766922] using wordTrace_append hprefix tailTrace_2766922
  have hstable : (prefixWord ++ tailWord_2766922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766922).length < 2 ^ (prefixWord ++ tailWord_2766922).sum := by decide
  have hdescent : baseEnd_2766922 < baseStart_2766922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766926 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2766926 : Nat := 118140960795 + 2766926 * 2 ^ 59
def prefixEnd_2766926 : Nat := 4983230072969 + 3 ^ 40 * 2766926 * 2
def baseEnd_2766926 : Nat := 1420762973422346623000145

theorem tailTrace_2766926 : CollatzResearch.WordTrace tailWord_2766926 prefixEnd_2766926 1420762973422346623000145 := by
  unfold tailWord_2766926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614760246738391273002079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67278721315938086789344421 12614760246738391273002079)
  ·
    refine ⟨18922140370107586909503119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614760246738391273002079 18922140370107586909503119)
    ·
      refine ⟨28383210555161380364254679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18922140370107586909503119 28383210555161380364254679)
      ·
        refine ⟨42574815832742070546382019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28383210555161380364254679 42574815832742070546382019)
        ·
          refine ⟨63862223749113105819573029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42574815832742070546382019 63862223749113105819573029)
          ·
            refine ⟨11974166952958707341169943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63862223749113105819573029 11974166952958707341169943)
            ·
              refine ⟨17961250429438061011754915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11974166952958707341169943 17961250429438061011754915)
              ·
                refine ⟨26941875644157091517632373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17961250429438061011754915 26941875644157091517632373)
                ·
                  refine ⟨2525800841639727329778035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26941875644157091517632373 2525800841639727329778035)
                  ·
                    refine ⟨3788701262459590994667053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525800841639727329778035 3788701262459590994667053)
                    ·
                      refine ⟨1420762973422346623000145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788701262459590994667053 1420762973422346623000145)
                      ·
                        rfl

theorem cell23_2766926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2766926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766926 prefixEnd_2766926 := by exact prefixLift 2766926
  have htrace : WordTrace (prefixWord ++ tailWord_2766926) baseStart_2766926 baseEnd_2766926 := by
    simpa [prefixWord, tailWord_2766926, baseEnd_2766926] using wordTrace_append hprefix tailTrace_2766926
  have hstable : (prefixWord ++ tailWord_2766926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766926).length < 2 ^ (prefixWord ++ tailWord_2766926).sum := by decide
  have hdescent : baseEnd_2766926 < baseStart_2766926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766929 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2766929 : Nat := 118140960795 + 2766929 * 2 ^ 59
def prefixEnd_2766929 : Nat := 4983230072969 + 3 ^ 40 * 2766929 * 2
def baseEnd_2766929 : Nat := 473588171288103370420877

theorem tailTrace_2766929 : CollatzResearch.WordTrace tailWord_2766929 prefixEnd_2766929 473588171288103370420877 := by
  unfold tailWord_2766929
  simp only [CollatzResearch.WordTrace]
  refine ⟨100918191392896261696375841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67278794261930841130917227 100918191392896261696375841)
  ·
    refine ⟨75688643544672196272281881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100918191392896261696375841 75688643544672196272281881)
    ·
      refine ⟨56766482658504147204211411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75688643544672196272281881 56766482658504147204211411)
      ·
        refine ⟨85149723987756220806317117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56766482658504147204211411 85149723987756220806317117)
        ·
          refine ⟨31931146495408582802368919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85149723987756220806317117 31931146495408582802368919)
          ·
            refine ⟨47896719743112874203553379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31931146495408582802368919 47896719743112874203553379)
            ·
              refine ⟨71845079614669311305330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47896719743112874203553379 71845079614669311305330069)
              ·
                refine ⟨3367738106937623967437347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71845079614669311305330069 3367738106937623967437347)
                ·
                  refine ⟨5051607160406435951156021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367738106937623967437347 5051607160406435951156021)
                  ·
                    refine ⟨473588171288103370420877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5051607160406435951156021 473588171288103370420877)
                    ·
                      rfl

theorem cell23_2766929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2766929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766929 prefixEnd_2766929 := by exact prefixLift 2766929
  have htrace : WordTrace (prefixWord ++ tailWord_2766929) baseStart_2766929 baseEnd_2766929 := by
    simpa [prefixWord, tailWord_2766929, baseEnd_2766929] using wordTrace_append hprefix tailTrace_2766929
  have hstable : (prefixWord ++ tailWord_2766929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766929).length < 2 ^ (prefixWord ++ tailWord_2766929).sum := by decide
  have hdescent : baseEnd_2766929 < baseStart_2766929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766930 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_2766930 : Nat := 118140960795 + 2766930 * 2 ^ 59
def prefixEnd_2766930 : Nat := 4983230072969 + 3 ^ 40 * 2766930 * 2
def baseEnd_2766930 : Nat := 1420765027344964607350127

theorem tailTrace_2766930 : CollatzResearch.WordTrace tailWord_2766930 prefixEnd_2766930 1420765027344964607350127 := by
  unfold tailWord_2766930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25229556966473159716790561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67278818577261759244774829 25229556966473159716790561)
  ·
    refine ⟨18922167724854869787592921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25229556966473159716790561 18922167724854869787592921)
    ·
      refine ⟨14191625793641152340694691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18922167724854869787592921 14191625793641152340694691)
      ·
        refine ⟨21287438690461728511042037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191625793641152340694691 21287438690461728511042037)
        ·
          refine ⟨1995697377230787047910191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21287438690461728511042037 1995697377230787047910191)
          ·
            refine ⟨2993546065846180571865287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995697377230787047910191 2993546065846180571865287)
            ·
              refine ⟨4490319098769270857797931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993546065846180571865287 4490319098769270857797931)
              ·
                refine ⟨6735478648153906286696897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490319098769270857797931 6735478648153906286696897)
                ·
                  refine ⟨5051608986115429715022673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6735478648153906286696897 5051608986115429715022673)
                  ·
                    refine ⟨3788706739586572286267005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5051608986115429715022673 3788706739586572286267005)
                    ·
                      refine ⟨1420765027344964607350127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788706739586572286267005 1420765027344964607350127)
                      ·
                        rfl

theorem cell23_2766930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_2766930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766930 prefixEnd_2766930 := by exact prefixLift 2766930
  have htrace : WordTrace (prefixWord ++ tailWord_2766930) baseStart_2766930 baseEnd_2766930 := by
    simpa [prefixWord, tailWord_2766930, baseEnd_2766930] using wordTrace_append hprefix tailTrace_2766930
  have hstable : (prefixWord ++ tailWord_2766930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766930).length < 2 ^ (prefixWord ++ tailWord_2766930).sum := by decide
  have hdescent : baseEnd_2766930 < baseStart_2766930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766936 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_2766936 : Nat := 118140960795 + 2766936 * 2 ^ 59
def prefixEnd_2766936 : Nat := 4983230072969 + 3 ^ 40 * 2766936 * 2
def baseEnd_2766936 : Nat := 1420768108228891583875099

theorem tailTrace_2766936 : CollatzResearch.WordTrace tailWord_2766936 prefixEnd_2766936 1420768108228891583875099 := by
  unfold tailWord_2766936
  simp only [CollatzResearch.WordTrace]
  refine ⟨50459223351935450945940331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67278964469247267927920441 50459223351935450945940331)
  ·
    refine ⟨75688835027903176418910497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50459223351935450945940331 75688835027903176418910497)
    ·
      refine ⟨56766626270927382314182873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75688835027903176418910497 56766626270927382314182873)
      ·
        refine ⟨42574969703195536735637155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56766626270927382314182873 42574969703195536735637155)
        ·
          refine ⟨63862454554793305103455733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42574969703195536735637155 63862454554793305103455733)
          ·
            refine ⟨5987105114511872353448975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63862454554793305103455733 5987105114511872353448975)
            ·
              refine ⟨8980657671767808530173463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987105114511872353448975 8980657671767808530173463)
              ·
                refine ⟨13470986507651712795260195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8980657671767808530173463 13470986507651712795260195)
                ·
                  refine ⟨20206479761477569192890293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13470986507651712795260195 20206479761477569192890293)
                  ·
                    refine ⟨1894357477638522111833465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20206479761477569192890293 1894357477638522111833465)
                    ·
                      refine ⟨1420768108228891583875099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894357477638522111833465 1420768108228891583875099)
                      ·
                        rfl

theorem cell23_2766936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_2766936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766936 prefixEnd_2766936 := by exact prefixLift 2766936
  have htrace : WordTrace (prefixWord ++ tailWord_2766936) baseStart_2766936 baseEnd_2766936 := by
    simpa [prefixWord, tailWord_2766936, baseEnd_2766936] using wordTrace_append hprefix tailTrace_2766936
  have hstable : (prefixWord ++ tailWord_2766936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766936).length < 2 ^ (prefixWord ++ tailWord_2766936).sum := by decide
  have hdescent : baseEnd_2766936 < baseStart_2766936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766969 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2766969 : Nat := 118140960795 + 2766969 * 2 ^ 59
def prefixEnd_2766969 : Nat := 4983230072969 + 3 ^ 40 * 2766969 * 2
def baseEnd_2766969 : Nat := 1420785053090489954762447

theorem tailTrace_2766969 : CollatzResearch.WordTrace tailWord_2766969 prefixEnd_2766969 1420785053090489954762447 := by
  unfold tailWord_2766969
  simp only [CollatzResearch.WordTrace]
  refine ⟨100919650312751348527831961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67279766875167565685221307 100919650312751348527831961)
  ·
    refine ⟨75689737734563511395873971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100919650312751348527831961 75689737734563511395873971)
    ·
      refine ⟨113534606601845267093810957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75689737734563511395873971 113534606601845267093810957)
      ·
        refine ⟨42575477475691975160179109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113534606601845267093810957 42575477475691975160179109)
        ·
          refine ⟨7982902026692245342533583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42575477475691975160179109 7982902026692245342533583)
          ·
            refine ⟨11974353040038368013800375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982902026692245342533583 11974353040038368013800375)
            ·
              refine ⟨17961529560057552020700563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11974353040038368013800375 17961529560057552020700563)
              ·
                refine ⟨26942294340086328031050845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17961529560057552020700563 26942294340086328031050845)
                ·
                  refine ⟨10103360377532373011644067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26942294340086328031050845 10103360377532373011644067)
                  ·
                    refine ⟨15155040566298559517466101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10103360377532373011644067 15155040566298559517466101)
                    ·
                      refine ⟨1420785053090489954762447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15155040566298559517466101 1420785053090489954762447)
                      ·
                        rfl

theorem cell23_2766969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2766969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766969 prefixEnd_2766969 := by exact prefixLift 2766969
  have htrace : WordTrace (prefixWord ++ tailWord_2766969) baseStart_2766969 baseEnd_2766969 := by
    simpa [prefixWord, tailWord_2766969, baseEnd_2766969] using wordTrace_append hprefix tailTrace_2766969
  have hstable : (prefixWord ++ tailWord_2766969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766969).length < 2 ^ (prefixWord ++ tailWord_2766969).sum := by decide
  have hdescent : baseEnd_2766969 < baseStart_2766969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766979 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_2766979 : Nat := 118140960795 + 2766979 * 2 ^ 59
def prefixEnd_2766979 : Nat := 4983230072969 + 3 ^ 40 * 2766979 * 2
def baseEnd_2766979 : Nat := 1420790187897034915637401

theorem tailTrace_2766979 : CollatzResearch.WordTrace tailWord_2766979 prefixEnd_2766979 1420790187897034915637401 := by
  unfold tailWord_2766979
  simp only [CollatzResearch.WordTrace]
  refine ⟨100920015042715120235695991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67280010028476746823797327 100920015042715120235695991)
  ·
    refine ⟨151380022564072680353543987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100920015042715120235695991 151380022564072680353543987)
    ·
      refine ⟨227070033846109020530315981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151380022564072680353543987 227070033846109020530315981)
      ·
        refine ⟨85151262692290882698868493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227070033846109020530315981 85151262692290882698868493)
        ·
          refine ⟨31931723509609081012075685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85151262692290882698868493 31931723509609081012075685)
          ·
            refine ⟨5987198158051702689764191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31931723509609081012075685 5987198158051702689764191)
            ·
              refine ⟨8980797237077554034646287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987198158051702689764191 8980797237077554034646287)
              ·
                refine ⟨13471195855616331051969431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8980797237077554034646287 13471195855616331051969431)
                ·
                  refine ⟨20206793783424496577954147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13471195855616331051969431 20206793783424496577954147)
                  ·
                    refine ⟨30310190675136744866931221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20206793783424496577954147 30310190675136744866931221)
                    ·
                      refine ⟨1420790187897034915637401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30310190675136744866931221 1420790187897034915637401)
                      ·
                        rfl

theorem cell23_2766979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_2766979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766979 prefixEnd_2766979 := by exact prefixLift 2766979
  have htrace : WordTrace (prefixWord ++ tailWord_2766979) baseStart_2766979 baseEnd_2766979 := by
    simpa [prefixWord, tailWord_2766979, baseEnd_2766979] using wordTrace_append hprefix tailTrace_2766979
  have hstable : (prefixWord ++ tailWord_2766979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766979).length < 2 ^ (prefixWord ++ tailWord_2766979).sum := by decide
  have hdescent : baseEnd_2766979 < baseStart_2766979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766983 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_2766983 : Nat := 118140960795 + 2766983 * 2 ^ 59
def prefixEnd_2766983 : Nat := 4983230072969 + 3 ^ 40 * 2766983 * 2
def baseEnd_2766983 : Nat := 1420792241819652899987383

theorem tailTrace_2766983 : CollatzResearch.WordTrace tailWord_2766983 prefixEnd_2766983 1420792241819652899987383 := by
  unfold tailWord_2766983
  simp only [CollatzResearch.WordTrace]
  refine ⟨100920160934700628918841603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67280107289800419279227735 100920160934700628918841603)
  ·
    refine ⟨151380241402050943378262405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100920160934700628918841603 151380241402050943378262405)
    ·
      refine ⟨28383795262884551883424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151380241402050943378262405 28383795262884551883424201)
      ·
        refine ⟨21287846447163413912568151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28383795262884551883424201 21287846447163413912568151)
        ·
          refine ⟨31931769670745120868852227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21287846447163413912568151 31931769670745120868852227)
          ·
            refine ⟨47897654506117681303278341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31931769670745120868852227 47897654506117681303278341)
            ·
              refine ⟨8980810219897065244364689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47897654506117681303278341 8980810219897065244364689)
              ·
                refine ⟨6735607664922798933273517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8980810219897065244364689 6735607664922798933273517)
                ·
                  refine ⟨2525852874346049599977569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6735607664922798933273517 2525852874346049599977569)
                  ·
                    refine ⟨1894389655759537199983177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525852874346049599977569 1894389655759537199983177)
                    ·
                      refine ⟨1420792241819652899987383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894389655759537199983177 1420792241819652899987383)
                      ·
                        rfl

theorem cell23_2766983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_2766983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2766983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2766983 prefixEnd_2766983 := by exact prefixLift 2766983
  have htrace : WordTrace (prefixWord ++ tailWord_2766983) baseStart_2766983 baseEnd_2766983 := by
    simpa [prefixWord, tailWord_2766983, baseEnd_2766983] using wordTrace_append hprefix tailTrace_2766983
  have hstable : (prefixWord ++ tailWord_2766983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766983).length < 2 ^ (prefixWord ++ tailWord_2766983).sum := by decide
  have hdescent : baseEnd_2766983 < baseStart_2766983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767033 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2767033 : Nat := 118140960795 + 2767033 * 2 ^ 59
def prefixEnd_2767033 : Nat := 4983230072969 + 3 ^ 40 * 2767033 * 2
def baseEnd_2767033 : Nat := 1420817915852377704362153

theorem tailTrace_2767033 : CollatzResearch.WordTrace tailWord_2767033 prefixEnd_2767033 1420817915852377704362153 := by
  unfold tailWord_2767033
  simp only [CollatzResearch.WordTrace]
  refine ⟨100921984584519487458161753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67281323056346324972107835 100921984584519487458161753)
  ·
    refine ⟨75691488438389615593621315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100921984584519487458161753 75691488438389615593621315)
    ·
      refine ⟨113537232657584423390431973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75691488438389615593621315 113537232657584423390431973)
      ·
        refine ⟨21288231123297079385705995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113537232657584423390431973 21288231123297079385705995)
        ·
          refine ⟨31932346684945619078558993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21288231123297079385705995 31932346684945619078558993)
          ·
            refine ⟨23949260013709214308919245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31932346684945619078558993 23949260013709214308919245)
            ·
              refine ⟨8980972505140955365844717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23949260013709214308919245 8980972505140955365844717)
              ·
                refine ⟨3367864689427858262191769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8980972505140955365844717 3367864689427858262191769)
                ·
                  refine ⟨2525898517070893696643827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367864689427858262191769 2525898517070893696643827)
                  ·
                    refine ⟨3788847775606340544965741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525898517070893696643827 3788847775606340544965741)
                    ·
                      refine ⟨1420817915852377704362153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788847775606340544965741 1420817915852377704362153)
                      ·
                        rfl

theorem cell23_2767033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2767033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767033 prefixEnd_2767033 := by exact prefixLift 2767033
  have htrace : WordTrace (prefixWord ++ tailWord_2767033) baseStart_2767033 baseEnd_2767033 := by
    simpa [prefixWord, tailWord_2767033, baseEnd_2767033] using wordTrace_append hprefix tailTrace_2767033
  have hstable : (prefixWord ++ tailWord_2767033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767033).length < 2 ^ (prefixWord ++ tailWord_2767033).sum := by decide
  have hdescent : baseEnd_2767033 < baseStart_2767033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767059 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3]
def baseStart_2767059 : Nat := 118140960795 + 2767059 * 2 ^ 59
def prefixEnd_2767059 : Nat := 4983230072969 + 3 ^ 40 * 2767059 * 2
def baseEnd_2767059 : Nat := 1420831266349394602637033

theorem tailTrace_2767059 : CollatzResearch.WordTrace tailWord_2767059 prefixEnd_2767059 1420831266349394602637033 := by
  unfold tailWord_2767059
  simp only [CollatzResearch.WordTrace]
  refine ⟨100922932882425293898608231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67281955254950195932405487 100922932882425293898608231)
  ·
    refine ⟨151384399323637940847912347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100922932882425293898608231 151384399323637940847912347)
    ·
      refine ⟨227076598985456911271868521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151384399323637940847912347 227076598985456911271868521)
      ·
        refine ⟨170307449239092683453901391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227076598985456911271868521 170307449239092683453901391)
        ·
          refine ⟨255461173858639025180852087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170307449239092683453901391 255461173858639025180852087)
          ·
            refine ⟨383191760787958537771278131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255461173858639025180852087 383191760787958537771278131)
            ·
              refine ⟨574787641181937806656917197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383191760787958537771278131 574787641181937806656917197)
              ·
                refine ⟨215545365443226677496343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574787641181937806656917197 215545365443226677496343949)
                ·
                  refine ⟨80829512041210004061128981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215545365443226677496343949 80829512041210004061128981)
                  ·
                    refine ⟨3788883376931718940365421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80829512041210004061128981 3788883376931718940365421)
                    ·
                      refine ⟨1420831266349394602637033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3788883376931718940365421 1420831266349394602637033)
                      ·
                        rfl

theorem cell23_2767059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_2767059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767059 prefixEnd_2767059 := by exact prefixLift 2767059
  have htrace : WordTrace (prefixWord ++ tailWord_2767059) baseStart_2767059 baseEnd_2767059 := by
    simpa [prefixWord, tailWord_2767059, baseEnd_2767059] using wordTrace_append hprefix tailTrace_2767059
  have hstable : (prefixWord ++ tailWord_2767059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767059).length < 2 ^ (prefixWord ++ tailWord_2767059).sum := by decide
  have hdescent : baseEnd_2767059 < baseStart_2767059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767068 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2767068 : Nat := 118140960795 + 2767068 * 2 ^ 59
def prefixEnd_2767068 : Nat := 4983230072969 + 3 ^ 40 * 2767068 * 2
def baseEnd_2767068 : Nat := 1420835887675285067424493

theorem tailTrace_2767068 : CollatzResearch.WordTrace tailWord_2767068 prefixEnd_2767068 1420835887675285067424493 := by
  unfold tailWord_2767068
  simp only [CollatzResearch.WordTrace]
  refine ⟨50461630569696344217842929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67282174092928458957123905 50461630569696344217842929)
  ·
    refine ⟨37846222927272258163382197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50461630569696344217842929 37846222927272258163382197)
    ·
      refine ⟨3548083399431774202817081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37846222927272258163382197 3548083399431774202817081)
      ·
        refine ⟨2661062549573830652112811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3548083399431774202817081 2661062549573830652112811)
        ·
          refine ⟨3991593824360745978169217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661062549573830652112811 3991593824360745978169217)
          ·
            refine ⟨2993695368270559483626913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3991593824360745978169217 2993695368270559483626913)
            ·
              refine ⟨2245271526202919612720185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993695368270559483626913 2245271526202919612720185)
              ·
                refine ⟨1683953644652189709540139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245271526202919612720185 1683953644652189709540139)
                ·
                  refine ⟨2525930466978284564310209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683953644652189709540139 2525930466978284564310209)
                  ·
                    refine ⟨1894447850233713423232657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525930466978284564310209 1894447850233713423232657)
                    ·
                      refine ⟨1420835887675285067424493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894447850233713423232657 1420835887675285067424493)
                      ·
                        rfl

theorem cell23_2767068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2767068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767068 prefixEnd_2767068 := by exact prefixLift 2767068
  have htrace : WordTrace (prefixWord ++ tailWord_2767068) baseStart_2767068 baseEnd_2767068 := by
    simpa [prefixWord, tailWord_2767068, baseEnd_2767068] using wordTrace_append hprefix tailTrace_2767068
  have hstable : (prefixWord ++ tailWord_2767068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767068).length < 2 ^ (prefixWord ++ tailWord_2767068).sum := by decide
  have hdescent : baseEnd_2767068 < baseStart_2767068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767090 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2767090 : Nat := 118140960795 + 2767090 * 2 ^ 59
def prefixEnd_2767090 : Nat := 4983230072969 + 3 ^ 40 * 2767090 * 2
def baseEnd_2767090 : Nat := 1420847184249683981349391

theorem tailTrace_2767090 : CollatzResearch.WordTrace tailWord_2767090 prefixEnd_2767090 1420847184249683981349391 := by
  unfold tailWord_2767090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25231015886328246548246681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67282709030208657461991149 25231015886328246548246681)
  ·
    refine ⟨18923261914746184911185011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25231015886328246548246681 18923261914746184911185011)
    ·
      refine ⟨28384892872119277366777517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18923261914746184911185011 28384892872119277366777517)
      ·
        refine ⟨10644334827044729012541569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28384892872119277366777517 10644334827044729012541569)
        ·
          refine ⟨7983251120283546759406177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644334827044729012541569 7983251120283546759406177)
          ·
            refine ⟨5987438340212660069554633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7983251120283546759406177 5987438340212660069554633)
            ·
              refine ⟨4490578755159495052165975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5987438340212660069554633 4490578755159495052165975)
              ·
                refine ⟨6735868132739242578248963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490578755159495052165975 6735868132739242578248963)
                ·
                  refine ⟨10103802199108863867373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735868132739242578248963 10103802199108863867373445)
                  ·
                    refine ⟨1894462912332911975132521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10103802199108863867373445 1894462912332911975132521)
                    ·
                      refine ⟨1420847184249683981349391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894462912332911975132521 1420847184249683981349391)
                      ·
                        rfl

theorem cell23_2767090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2767090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767090 prefixEnd_2767090 := by exact prefixLift 2767090
  have htrace : WordTrace (prefixWord ++ tailWord_2767090) baseStart_2767090 baseEnd_2767090 := by
    simpa [prefixWord, tailWord_2767090, baseEnd_2767090] using wordTrace_append hprefix tailTrace_2767090
  have hstable : (prefixWord ++ tailWord_2767090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767090).length < 2 ^ (prefixWord ++ tailWord_2767090).sum := by decide
  have hdescent : baseEnd_2767090 < baseStart_2767090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767111 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2767111 : Nat := 118140960795 + 2767111 * 2 ^ 59
def prefixEnd_2767111 : Nat := 4983230072969 + 3 ^ 40 * 2767111 * 2
def baseEnd_2767111 : Nat := 1420857967343428399186795

theorem tailTrace_2767111 : CollatzResearch.WordTrace tailWord_2767111 prefixEnd_2767111 1420857967343428399186795 := by
  unfold tailWord_2767111
  simp only [CollatzResearch.WordTrace]
  refine ⟨100924829478236906779501187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67283219652157937853000791 100924829478236906779501187)
  ·
    refine ⟨151387244217355360169251781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100924829478236906779501187 151387244217355360169251781)
    ·
      refine ⟨28385108290754130031734709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151387244217355360169251781 28385108290754130031734709)
      ·
        refine ⟨2661103902258199690475129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28385108290754130031734709 2661103902258199690475129)
        ·
          refine ⟨1995827926693649767856347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2661103902258199690475129 1995827926693649767856347)
          ·
            refine ⟨2993741890040474651784521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995827926693649767856347 2993741890040474651784521)
            ·
              refine ⟨2245306417530355988838391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993741890040474651784521 2245306417530355988838391)
              ·
                refine ⟨3367959626295533983257587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245306417530355988838391 3367959626295533983257587)
                ·
                  refine ⟨5051939439443300974886381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367959626295533983257587 5051939439443300974886381)
                  ·
                    refine ⟨1894477289791237865582393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5051939439443300974886381 1894477289791237865582393)
                    ·
                      refine ⟨1420857967343428399186795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894477289791237865582393 1420857967343428399186795)
                      ·
                        rfl

theorem cell23_2767111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2767111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767111 prefixEnd_2767111 := by exact prefixLift 2767111
  have htrace : WordTrace (prefixWord ++ tailWord_2767111) baseStart_2767111 baseEnd_2767111 := by
    simpa [prefixWord, tailWord_2767111, baseEnd_2767111] using wordTrace_append hprefix tailTrace_2767111
  have hstable : (prefixWord ++ tailWord_2767111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767111).length < 2 ^ (prefixWord ++ tailWord_2767111).sum := by decide
  have hdescent : baseEnd_2767111 < baseStart_2767111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767113 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 5]
def baseStart_2767113 : Nat := 118140960795 + 2767113 * 2 ^ 59
def prefixEnd_2767113 : Nat := 4983230072969 + 3 ^ 40 * 2767113 * 2
def baseEnd_2767113 : Nat := 157873221589415265706865

theorem tailTrace_2767113 : CollatzResearch.WordTrace tailWord_2767113 prefixEnd_2767113 157873221589415265706865 := by
  unfold tailWord_2767113
  simp only [CollatzResearch.WordTrace]
  refine ⟨100924902424229661121073993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67283268282819774080715995 100924902424229661121073993)
  ·
    refine ⟨75693676818172245840805495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100924902424229661121073993 75693676818172245840805495)
    ·
      refine ⟨113540515227258368761208243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75693676818172245840805495 113540515227258368761208243)
      ·
        refine ⟨170310772840887553141812365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113540515227258368761208243 170310772840887553141812365)
        ·
          refine ⟨63866539815332832428179637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170310772840887553141812365 63866539815332832428179637)
          ·
            refine ⟨5987488107687453040141841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63866539815332832428179637 5987488107687453040141841)
            ·
              refine ⟨4490616080765589780106381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5987488107687453040141841 4490616080765589780106381)
              ·
                refine ⟨1683981030287096167539893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4490616080765589780106381 1683981030287096167539893)
                ·
                  refine ⟨157873221589415265706865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683981030287096167539893 157873221589415265706865)
                  ·
                    rfl

theorem cell23_2767113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 5].length) (baseStart_2767113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767113 prefixEnd_2767113 := by exact prefixLift 2767113
  have htrace : WordTrace (prefixWord ++ tailWord_2767113) baseStart_2767113 baseEnd_2767113 := by
    simpa [prefixWord, tailWord_2767113, baseEnd_2767113] using wordTrace_append hprefix tailTrace_2767113
  have hstable : (prefixWord ++ tailWord_2767113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767113).length < 2 ^ (prefixWord ++ tailWord_2767113).sum := by decide
  have hdescent : baseEnd_2767113 < baseStart_2767113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767119 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_2767119 : Nat := 118140960795 + 2767119 * 2 ^ 59
def prefixEnd_2767119 : Nat := 4983230072969 + 3 ^ 40 * 2767119 * 2
def baseEnd_2767119 : Nat := 1420862075188664367886757

theorem tailTrace_2767119 : CollatzResearch.WordTrace tailWord_2767119 prefixEnd_2767119 1420862075188664367886757 := by
  unfold tailWord_2767119
  simp only [CollatzResearch.WordTrace]
  refine ⟨100925121262207924145792411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67283414174805282763861607 100925121262207924145792411)
  ·
    refine ⟨151387681893311886218688617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100925121262207924145792411 151387681893311886218688617)
    ·
      refine ⟨113540761419983914664016463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151387681893311886218688617 113540761419983914664016463)
      ·
        refine ⟨170311142129975871996024695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113540761419983914664016463 170311142129975871996024695)
        ·
          refine ⟨255466713194963807994037043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170311142129975871996024695 255466713194963807994037043)
          ·
            refine ⟨383200069792445711991055565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255466713194963807994037043 383200069792445711991055565)
            ·
              refine ⟨143700026172167141996645837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383200069792445711991055565 143700026172167141996645837)
              ·
                refine ⟨53887509814562678248742189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143700026172167141996645837 53887509814562678248742189)
                ·
                  refine ⟨20207816180461004343278321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53887509814562678248742189 20207816180461004343278321)
                  ·
                    refine ⟨15155862135345753257458741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20207816180461004343278321 15155862135345753257458741)
                    ·
                      refine ⟨1420862075188664367886757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15155862135345753257458741 1420862075188664367886757)
                      ·
                        rfl

theorem cell23_2767119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_2767119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767119 prefixEnd_2767119 := by exact prefixLift 2767119
  have htrace : WordTrace (prefixWord ++ tailWord_2767119) baseStart_2767119 baseEnd_2767119 := by
    simpa [prefixWord, tailWord_2767119, baseEnd_2767119] using wordTrace_append hprefix tailTrace_2767119
  have hstable : (prefixWord ++ tailWord_2767119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767119).length < 2 ^ (prefixWord ++ tailWord_2767119).sum := by decide
  have hdescent : baseEnd_2767119 < baseStart_2767119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767186 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_2767186 : Nat := 118140960795 + 2767186 * 2 ^ 59
def prefixEnd_2767186 : Nat := 4983230072969 + 3 ^ 40 * 2767186 * 2
def baseEnd_2767186 : Nat := 157877386488057289527661

theorem tailTrace_2767186 : CollatzResearch.WordTrace tailWord_2767186 prefixEnd_2767186 157877386488057289527661 := by
  unfold tailWord_2767186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25231891238241298647120353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67285043301976796392320941 25231891238241298647120353)
  ·
    refine ⟨18923918428680973985340265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25231891238241298647120353 18923918428680973985340265)
    ·
      refine ⟨14192938821510730489005199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18923918428680973985340265 14192938821510730489005199)
      ·
        refine ⟨21289408232266095733507799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14192938821510730489005199 21289408232266095733507799)
        ·
          refine ⟨31934112348399143600261699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21289408232266095733507799 31934112348399143600261699)
          ·
            refine ⟨47901168522598715400392549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31934112348399143600261699 47901168522598715400392549)
            ·
              refine ⟨8981469097987259137573603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47901168522598715400392549 8981469097987259137573603)
              ·
                refine ⟨13472203646980888706360405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981469097987259137573603 13472203646980888706360405)
                ·
                  refine ⟨157877386488057289527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13472203646980888706360405 157877386488057289527661)
                  ·
                    rfl

theorem cell23_2767186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_2767186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767186 prefixEnd_2767186 := by exact prefixLift 2767186
  have htrace : WordTrace (prefixWord ++ tailWord_2767186) baseStart_2767186 baseEnd_2767186 := by
    simpa [prefixWord, tailWord_2767186, baseEnd_2767186] using wordTrace_append hprefix tailTrace_2767186
  have hstable : (prefixWord ++ tailWord_2767186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767186).length < 2 ^ (prefixWord ++ tailWord_2767186).sum := by decide
  have hdescent : baseEnd_2767186 < baseStart_2767186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767240 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2767240 : Nat := 118140960795 + 2767240 * 2 ^ 59
def prefixEnd_2767240 : Nat := 4983230072969 + 3 ^ 40 * 2767240 * 2
def baseEnd_2767240 : Nat := 1420924206347858394473701

theorem tailTrace_2767240 : CollatzResearch.WordTrace tailWord_2767240 prefixEnd_2767240 1420924206347858394473701 := by
  unfold tailWord_2767240
  simp only [CollatzResearch.WordTrace]
  refine ⟨50464767247384780905473587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67286356329846374540631449 50464767247384780905473587)
  ·
    refine ⟨75697150871077171358210381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50464767247384780905473587 75697150871077171358210381)
    ·
      refine ⟨28386431576653939259328893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75697150871077171358210381 28386431576653939259328893)
      ·
        refine ⟨10644911841245227222248335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28386431576653939259328893 10644911841245227222248335)
        ·
          refine ⟨15967367761867840833372503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10644911841245227222248335 15967367761867840833372503)
          ·
            refine ⟨23951051642801761250058755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967367761867840833372503 23951051642801761250058755)
            ·
              refine ⟨35926577464202641875088133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23951051642801761250058755 35926577464202641875088133)
              ·
                refine ⟨6736233274537995351579025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35926577464202641875088133 6736233274537995351579025)
                ·
                  refine ⟨5052174955903496513684269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6736233274537995351579025 5052174955903496513684269)
                  ·
                    refine ⟨1894565608463811192631601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5052174955903496513684269 1894565608463811192631601)
                    ·
                      refine ⟨1420924206347858394473701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894565608463811192631601 1420924206347858394473701)
                      ·
                        rfl

theorem cell23_2767240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2767240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767240 prefixEnd_2767240 := by exact prefixLift 2767240
  have htrace : WordTrace (prefixWord ++ tailWord_2767240) baseStart_2767240 baseEnd_2767240 := by
    simpa [prefixWord, tailWord_2767240, baseEnd_2767240] using wordTrace_append hprefix tailTrace_2767240
  have hstable : (prefixWord ++ tailWord_2767240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767240).length < 2 ^ (prefixWord ++ tailWord_2767240).sum := by decide
  have hdescent : baseEnd_2767240 < baseStart_2767240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767253 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_2767253 : Nat := 118140960795 + 2767253 * 2 ^ 59
def prefixEnd_2767253 : Nat := 4983230072969 + 3 ^ 40 * 2767253 * 2
def baseEnd_2767253 : Nat := 1420930881596366843611141

theorem tailTrace_2767253 : CollatzResearch.WordTrace tailWord_2767253 prefixEnd_2767253 1420930881596366843611141 := by
  unfold tailWord_2767253
  simp only [CollatzResearch.WordTrace]
  refine ⟨100930008643722465031170413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67286672429148310020780275 100930008643722465031170413)
  ·
    refine ⟨37848753241395924386688905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100930008643722465031170413 37848753241395924386688905)
    ·
      refine ⟨28386564931046943290016679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37848753241395924386688905 28386564931046943290016679)
      ·
        refine ⟨42579847396570414935025019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28386564931046943290016679 42579847396570414935025019)
        ·
          refine ⟨63869771094855622402537529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42579847396570414935025019 63869771094855622402537529)
          ·
            refine ⟨47902328321141716801903147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63869771094855622402537529 47902328321141716801903147)
            ·
              refine ⟨71853492481712575202854721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47902328321141716801903147 71853492481712575202854721)
              ·
                refine ⟨53890119361284431402141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71853492481712575202854721 53890119361284431402141041)
                ·
                  refine ⟨40417589520963323551605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53890119361284431402141041 40417589520963323551605781)
                  ·
                    refine ⟨1894574508795155791481521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40417589520963323551605781 1894574508795155791481521)
                    ·
                      refine ⟨1420930881596366843611141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894574508795155791481521 1420930881596366843611141)
                      ·
                        rfl

theorem cell23_2767253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_2767253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767253 prefixEnd_2767253 := by exact prefixLift 2767253
  have htrace : WordTrace (prefixWord ++ tailWord_2767253) baseStart_2767253 baseEnd_2767253 := by
    simpa [prefixWord, tailWord_2767253, baseEnd_2767253] using wordTrace_append hprefix tailTrace_2767253
  have hstable : (prefixWord ++ tailWord_2767253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767253).length < 2 ^ (prefixWord ++ tailWord_2767253).sum := by decide
  have hdescent : baseEnd_2767253 < baseStart_2767253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767263 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 6]
def baseStart_2767263 : Nat := 118140960795 + 2767263 * 2 ^ 59
def prefixEnd_2767263 : Nat := 4983230072969 + 3 ^ 40 * 2767263 * 2
def baseEnd_2767263 : Nat := 473645338800970601495365

theorem tailTrace_2767263 : CollatzResearch.WordTrace tailWord_2767263 prefixEnd_2767263 473645338800970601495365 := by
  unfold tailWord_2767263
  simp only [CollatzResearch.WordTrace]
  refine ⟨100930373373686236739034443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67286915582457491159356295 100930373373686236739034443)
  ·
    refine ⟨151395560060529355108551665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100930373373686236739034443 151395560060529355108551665)
    ·
      refine ⟨113546670045397016331413749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151395560060529355108551665 113546670045397016331413749)
      ·
        refine ⟨10645000316755970281070039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113546670045397016331413749 10645000316755970281070039)
        ·
          refine ⟨15967500475133955421605059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645000316755970281070039 15967500475133955421605059)
          ·
            refine ⟨23951250712700933132407589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967500475133955421605059 23951250712700933132407589)
            ·
              refine ⟨4490859508631424962326423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23951250712700933132407589 4490859508631424962326423)
              ·
                refine ⟨6736289262947137443489635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490859508631424962326423 6736289262947137443489635)
                ·
                  refine ⟨10104433894420706165234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736289262947137443489635 10104433894420706165234453)
                  ·
                    refine ⟨473645338800970601495365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10104433894420706165234453 473645338800970601495365)
                    ·
                      rfl

theorem cell23_2767263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_2767263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767263 prefixEnd_2767263 := by exact prefixLift 2767263
  have htrace : WordTrace (prefixWord ++ tailWord_2767263) baseStart_2767263 baseEnd_2767263 := by
    simpa [prefixWord, tailWord_2767263, baseEnd_2767263] using wordTrace_append hprefix tailTrace_2767263
  have hstable : (prefixWord ++ tailWord_2767263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767263).length < 2 ^ (prefixWord ++ tailWord_2767263).sum := by decide
  have hdescent : baseEnd_2767263 < baseStart_2767263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767284 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2767284 : Nat := 118140960795 + 2767284 * 2 ^ 59
def prefixEnd_2767284 : Nat := 4983230072969 + 3 ^ 40 * 2767284 * 2
def baseEnd_2767284 : Nat := 473648933165552074107833

theorem tailTrace_2767284 : CollatzResearch.WordTrace tailWord_2767284 prefixEnd_2767284 473648933165552074107833 := by
  unfold tailWord_2767284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465569653305078662774453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67287426204406771550365937 50465569653305078662774453)
  ·
    refine ⟨4731147154997351124635105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50465569653305078662774453 4731147154997351124635105)
    ·
      refine ⟨3548360366248013343476329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4731147154997351124635105 3548360366248013343476329)
      ·
        refine ⟨2661270274686010007607247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3548360366248013343476329 2661270274686010007607247)
        ·
          refine ⟨3991905412029015011410871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661270274686010007607247 3991905412029015011410871)
          ·
            refine ⟨5987858118043522517116307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991905412029015011410871 5987858118043522517116307)
            ·
              refine ⟨8981787177065283775674461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987858118043522517116307 8981787177065283775674461)
              ·
                refine ⟨3368170191399481415877923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8981787177065283775674461 3368170191399481415877923)
                ·
                  refine ⟨5052255287099222123816885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368170191399481415877923 5052255287099222123816885)
                  ·
                    refine ⟨473648933165552074107833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5052255287099222123816885 473648933165552074107833)
                    ·
                      rfl

theorem cell23_2767284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2767284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767284 prefixEnd_2767284 := by exact prefixLift 2767284
  have htrace : WordTrace (prefixWord ++ tailWord_2767284) baseStart_2767284 baseEnd_2767284 := by
    simpa [prefixWord, tailWord_2767284, baseEnd_2767284] using wordTrace_append hprefix tailTrace_2767284
  have hstable : (prefixWord ++ tailWord_2767284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767284).length < 2 ^ (prefixWord ++ tailWord_2767284).sum := by decide
  have hdescent : baseEnd_2767284 < baseStart_2767284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767287 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_2767287 : Nat := 118140960795 + 2767287 * 2 ^ 59
def prefixEnd_2767287 : Nat := 4983230072969 + 3 ^ 40 * 2767287 * 2
def baseEnd_2767287 : Nat := 1420948339938619710585985

theorem tailTrace_2767287 : CollatzResearch.WordTrace tailWord_2767287 prefixEnd_2767287 1420948339938619710585985 := by
  unfold tailWord_2767287
  simp only [CollatzResearch.WordTrace]
  refine ⟨100931248725599288837908115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67287499150399525891938743 100931248725599288837908115)
  ·
    refine ⟨151396873088398933256862173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100931248725599288837908115 151396873088398933256862173)
    ·
      refine ⟨56773827408149599971323315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151396873088398933256862173 56773827408149599971323315)
      ·
        refine ⟨85160741112224399956984973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56773827408149599971323315 85160741112224399956984973)
        ·
          refine ⟨31935277917084149983869365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85160741112224399956984973 31935277917084149983869365)
          ·
            refine ⟨2993932304726639060987753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31935277917084149983869365 2993932304726639060987753)
            ·
              refine ⟨2245449228544979295740815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993932304726639060987753 2245449228544979295740815)
              ·
                refine ⟨3368173842817468943611223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245449228544979295740815 3368173842817468943611223)
                ·
                  refine ⟨5052260764226203415416835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368173842817468943611223 5052260764226203415416835)
                  ·
                    refine ⟨7578391146339305123125253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5052260764226203415416835 7578391146339305123125253)
                    ·
                      refine ⟨1420948339938619710585985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7578391146339305123125253 1420948339938619710585985)
                      ·
                        rfl

theorem cell23_2767287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_2767287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767287 prefixEnd_2767287 := by exact prefixLift 2767287
  have htrace : WordTrace (prefixWord ++ tailWord_2767287) baseStart_2767287 baseEnd_2767287 := by
    simpa [prefixWord, tailWord_2767287, baseEnd_2767287] using wordTrace_append hprefix tailTrace_2767287
  have hstable : (prefixWord ++ tailWord_2767287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767287).length < 2 ^ (prefixWord ++ tailWord_2767287).sum := by decide
  have hdescent : baseEnd_2767287 < baseStart_2767287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767296 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_2767296 : Nat := 118140960795 + 2767296 * 2 ^ 59
def prefixEnd_2767296 : Nat := 4983230072969 + 3 ^ 40 * 2767296 * 2
def baseEnd_2767296 : Nat := 1420952961264510175373443

theorem tailTrace_2767296 : CollatzResearch.WordTrace tailWord_2767296 prefixEnd_2767296 1420952961264510175373443 := by
  unfold tailWord_2767296
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465788491283341687492871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67287717988377788916657161 50465788491283341687492871)
  ·
    refine ⟨75698682736925012531239307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50465788491283341687492871 75698682736925012531239307)
    ·
      refine ⟨113548024105387518796858961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75698682736925012531239307 113548024105387518796858961)
      ·
        refine ⟨85161018079040639097644221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113548024105387518796858961 85161018079040639097644221)
        ·
          refine ⟨31935381779640239661616583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85161018079040639097644221 31935381779640239661616583)
          ·
            refine ⟨47903072669460359492424875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31935381779640239661616583 47903072669460359492424875)
            ·
              refine ⟨71854609004190539238637313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47903072669460359492424875 71854609004190539238637313)
              ·
                refine ⟨53890956753142904428977985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71854609004190539238637313 53890956753142904428977985)
                ·
                  refine ⟨40418217564857178321733489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53890956753142904428977985 40418217564857178321733489)
                  ·
                    refine ⟨30313663173642883741300117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40418217564857178321733489 30313663173642883741300117)
                    ·
                      refine ⟨1420952961264510175373443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30313663173642883741300117 1420952961264510175373443)
                      ·
                        rfl

theorem cell23_2767296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_2767296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767296 prefixEnd_2767296 := by exact prefixLift 2767296
  have htrace : WordTrace (prefixWord ++ tailWord_2767296) baseStart_2767296 baseEnd_2767296 := by
    simpa [prefixWord, tailWord_2767296, baseEnd_2767296] using wordTrace_append hprefix tailTrace_2767296
  have hstable : (prefixWord ++ tailWord_2767296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767296).length < 2 ^ (prefixWord ++ tailWord_2767296).sum := by decide
  have hdescent : baseEnd_2767296 < baseStart_2767296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767304 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_2767304 : Nat := 118140960795 + 2767304 * 2 ^ 59
def prefixEnd_2767304 : Nat := 4983230072969 + 3 ^ 40 * 2767304 * 2
def baseEnd_2767304 : Nat := 1420957069109746144073407

theorem tailTrace_2767304 : CollatzResearch.WordTrace tailWord_2767304 prefixEnd_2767304 1420957069109746144073407 := by
  unfold tailWord_2767304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465934383268850370638483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67287912511025133827517977 50465934383268850370638483)
  ·
    refine ⟨75698901574903275555957725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50465934383268850370638483 75698901574903275555957725)
    ·
      refine ⟨28387088090588728333484147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75698901574903275555957725 28387088090588728333484147)
      ·
        refine ⟨42580632135883092500226221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28387088090588728333484147 42580632135883092500226221)
        ·
          refine ⟨15967737050956159687584833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42580632135883092500226221 15967737050956159687584833)
          ·
            refine ⟨11975802788217119765688625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15967737050956159687584833 11975802788217119765688625)
            ·
              refine ⟨8981852091162839824266469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11975802788217119765688625 8981852091162839824266469)
              ·
                refine ⟨1684097267093032467049963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8981852091162839824266469 1684097267093032467049963)
                ·
                  refine ⟨2526145900639548700574945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684097267093032467049963 2526145900639548700574945)
                  ·
                    refine ⟨1894609425479661525431209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2526145900639548700574945 1894609425479661525431209)
                    ·
                      refine ⟨1420957069109746144073407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894609425479661525431209 1420957069109746144073407)
                      ·
                        rfl

theorem cell23_2767304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_2767304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767304 prefixEnd_2767304 := by exact prefixLift 2767304
  have htrace : WordTrace (prefixWord ++ tailWord_2767304) baseStart_2767304 baseEnd_2767304 := by
    simpa [prefixWord, tailWord_2767304, baseEnd_2767304] using wordTrace_append hprefix tailTrace_2767304
  have hstable : (prefixWord ++ tailWord_2767304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767304).length < 2 ^ (prefixWord ++ tailWord_2767304).sum := by decide
  have hdescent : baseEnd_2767304 < baseStart_2767304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767314 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2767314 : Nat := 118140960795 + 2767314 * 2 ^ 59
def prefixEnd_2767314 : Nat := 4983230072969 + 3 ^ 40 * 2767314 * 2
def baseEnd_2767314 : Nat := 473654067972097034982787

theorem tailTrace_2767314 : CollatzResearch.WordTrace tailWord_2767314 prefixEnd_2767314 473654067972097034982787 := by
  unfold tailWord_2767314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25233058374125368112285249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67288155664334314966093997 25233058374125368112285249)
  ·
    refine ⟨18924793780594026084213937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25233058374125368112285249 18924793780594026084213937)
    ·
      refine ⟨14193595335445519563160453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18924793780594026084213937 14193595335445519563160453)
      ·
        refine ⟨2661299125396034918092585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14193595335445519563160453 2661299125396034918092585)
        ·
          refine ⟨1995974344047026188569439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2661299125396034918092585 1995974344047026188569439)
          ·
            refine ⟨2993961516070539282854159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995974344047026188569439 2993961516070539282854159)
            ·
              refine ⟨4490942274105808924281239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993961516070539282854159 4490942274105808924281239)
              ·
                refine ⟨6736413411158713386421859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490942274105808924281239 6736413411158713386421859)
                ·
                  refine ⟨10104620116738070079632789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736413411158713386421859 10104620116738070079632789)
                  ·
                    refine ⟨473654067972097034982787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10104620116738070079632789 473654067972097034982787)
                    ·
                      rfl

theorem cell23_2767314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2767314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767314 prefixEnd_2767314 := by exact prefixLift 2767314
  have htrace : WordTrace (prefixWord ++ tailWord_2767314) baseStart_2767314 baseEnd_2767314 := by
    simpa [prefixWord, tailWord_2767314, baseEnd_2767314] using wordTrace_append hprefix tailTrace_2767314
  have hstable : (prefixWord ++ tailWord_2767314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767314).length < 2 ^ (prefixWord ++ tailWord_2767314).sum := by decide
  have hdescent : baseEnd_2767314 < baseStart_2767314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767363 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3]
def baseStart_2767363 : Nat := 118140960795 + 2767363 * 2 ^ 59
def prefixEnd_2767363 : Nat := 4983230072969 + 3 ^ 40 * 2767363 * 2
def baseEnd_2767363 : Nat := 1420987364468361413235635

theorem tailTrace_2767363 : CollatzResearch.WordTrace tailWord_2767363 prefixEnd_2767363 1420987364468361413235635 := by
  unfold tailWord_2767363
  simp only [CollatzResearch.WordTrace]
  refine ⟨100934020673323953817674743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67289347115549302545116495 100934020673323953817674743)
  ·
    refine ⟨151401031009985930726512115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100934020673323953817674743 151401031009985930726512115)
    ·
      refine ⟨227101546514978896089768173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151401031009985930726512115 227101546514978896089768173)
      ·
        refine ⟨85163079943117086033663065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227101546514978896089768173 85163079943117086033663065)
        ·
          refine ⟨63872309957337814525247299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85163079943117086033663065 63872309957337814525247299)
          ·
            refine ⟨95808464936006721787870949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63872309957337814525247299 95808464936006721787870949)
            ·
              refine ⟨17964087175501260335225803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95808464936006721787870949 17964087175501260335225803)
              ·
                refine ⟨26946130763251890502838705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17964087175501260335225803 26946130763251890502838705)
                ·
                  refine ⟨20209598072438917877129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26946130763251890502838705 20209598072438917877129029)
                  ·
                    refine ⟨3789299638582297101961693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20209598072438917877129029 3789299638582297101961693)
                    ·
                      refine ⟨1420987364468361413235635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789299638582297101961693 1420987364468361413235635)
                      ·
                        rfl

theorem cell23_2767363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_2767363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767363 prefixEnd_2767363 := by exact prefixLift 2767363
  have htrace : WordTrace (prefixWord ++ tailWord_2767363) baseStart_2767363 baseEnd_2767363 := by
    simpa [prefixWord, tailWord_2767363, baseEnd_2767363] using wordTrace_append hprefix tailTrace_2767363
  have hstable : (prefixWord ++ tailWord_2767363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767363).length < 2 ^ (prefixWord ++ tailWord_2767363).sum := by decide
  have hdescent : baseEnd_2767363 < baseStart_2767363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767423 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_2767423 : Nat := 118140960795 + 2767423 * 2 ^ 59
def prefixEnd_2767423 : Nat := 4983230072969 + 3 ^ 40 * 2767423 * 2
def baseEnd_2767423 : Nat := 1421018173307631178485359

theorem tailTrace_2767423 : CollatzResearch.WordTrace tailWord_2767423 prefixEnd_2767423 1421018173307631178485359 := by
  unfold tailWord_2767423
  simp only [CollatzResearch.WordTrace]
  refine ⟨100936209053106584064858923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67290806035404389376572615 100936209053106584064858923)
  ·
    refine ⟨151404313579659876097288385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100936209053106584064858923 151404313579659876097288385)
    ·
      refine ⟨113553235184744907072966289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151404313579659876097288385 113553235184744907072966289)
      ·
        refine ⟨85164926388558680304724717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113553235184744907072966289 85164926388558680304724717)
        ·
          refine ⟨31936847395709505114271769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85164926388558680304724717 31936847395709505114271769)
          ·
            refine ⟨23952635546782128835703827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31936847395709505114271769 23952635546782128835703827)
            ·
              refine ⟨35928953320173193253555741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23952635546782128835703827 35928953320173193253555741)
              ·
                refine ⟨13473357495064947470083403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35928953320173193253555741 13473357495064947470083403)
                ·
                  refine ⟨20210036242597421205125105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13473357495064947470083403 20210036242597421205125105)
                  ·
                    refine ⟨15157527181948065903843829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20210036242597421205125105 15157527181948065903843829)
                    ·
                      refine ⟨1421018173307631178485359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15157527181948065903843829 1421018173307631178485359)
                      ·
                        rfl

theorem cell23_2767423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_2767423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767423 prefixEnd_2767423 := by exact prefixLift 2767423
  have htrace : WordTrace (prefixWord ++ tailWord_2767423) baseStart_2767423 baseEnd_2767423 := by
    simpa [prefixWord, tailWord_2767423, baseEnd_2767423] using wordTrace_append hprefix tailTrace_2767423
  have hstable : (prefixWord ++ tailWord_2767423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767423).length < 2 ^ (prefixWord ++ tailWord_2767423).sum := by decide
  have hdescent : baseEnd_2767423 < baseStart_2767423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767428 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2767428 : Nat := 118140960795 + 2767428 * 2 ^ 59
def prefixEnd_2767428 : Nat := 4983230072969 + 3 ^ 40 * 2767428 * 2
def baseEnd_2767428 : Nat := 1421020740710903658922837

theorem tailTrace_2767428 : CollatzResearch.WordTrace tailWord_2767428 prefixEnd_2767428 1421020740710903658922837 := by
  unfold tailWord_2767428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50468195709044234959395469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67290927612058979945860625 50468195709044234959395469)
  ·
    refine ⟨18925573390891588109773301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50468195709044234959395469 18925573390891588109773301)
    ·
      refine ⟨1774272505396086385291247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18925573390891588109773301 1774272505396086385291247)
      ·
        refine ⟨2661408758094129577936871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774272505396086385291247 2661408758094129577936871)
        ·
          refine ⟨3992113137141194366905307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661408758094129577936871 3992113137141194366905307)
          ·
            refine ⟨5988169705711791550357961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992113137141194366905307 5988169705711791550357961)
            ·
              refine ⟨4491127279283843662768471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5988169705711791550357961 4491127279283843662768471)
              ·
                refine ⟨6736690918925765494152707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491127279283843662768471 6736690918925765494152707)
                ·
                  refine ⟨10105036378388648241229061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736690918925765494152707 10105036378388648241229061)
                  ·
                    refine ⟨1894694320947871545230449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10105036378388648241229061 1894694320947871545230449)
                    ·
                      refine ⟨1421020740710903658922837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894694320947871545230449 1421020740710903658922837)
                      ·
                        rfl

theorem cell23_2767428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2767428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767428 prefixEnd_2767428 := by exact prefixLift 2767428
  have htrace : WordTrace (prefixWord ++ tailWord_2767428) baseStart_2767428 baseEnd_2767428 := by
    simpa [prefixWord, tailWord_2767428, baseEnd_2767428] using wordTrace_append hprefix tailTrace_2767428
  have hstable : (prefixWord ++ tailWord_2767428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767428).length < 2 ^ (prefixWord ++ tailWord_2767428).sum := by decide
  have hdescent : baseEnd_2767428 < baseStart_2767428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767460 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2767460 : Nat := 118140960795 + 2767460 * 2 ^ 59
def prefixEnd_2767460 : Nat := 4983230072969 + 3 ^ 40 * 2767460 * 2
def baseEnd_2767460 : Nat := 473679057363949177907563

theorem tailTrace_2767460 : CollatzResearch.WordTrace tailWord_2767460 prefixEnd_2767460 473679057363949177907563 := by
  unfold tailWord_2767460
  simp only [CollatzResearch.WordTrace]
  refine ⟨50468779276986269691977917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67291705702648359589303889 50468779276986269691977917)
  ·
    refine ⟨18925792228869851134491719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50468779276986269691977917 18925792228869851134491719)
    ·
      refine ⟨28388688343304776701737579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18925792228869851134491719 28388688343304776701737579)
      ·
        refine ⟨42583032514957165052606369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28388688343304776701737579 42583032514957165052606369)
        ·
          refine ⟨31937274386217873789454777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42583032514957165052606369 31937274386217873789454777)
          ·
            refine ⟨23952955789663405342091083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31937274386217873789454777 23952955789663405342091083)
            ·
              refine ⟨35929433684495108013136625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23952955789663405342091083 35929433684495108013136625)
              ·
                refine ⟨26947075263371331009852469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35929433684495108013136625 26947075263371331009852469)
                ·
                  refine ⟨2526288305941062282173669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26947075263371331009852469 2526288305941062282173669)
                  ·
                    refine ⟨473679057363949177907563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2526288305941062282173669 473679057363949177907563)
                    ·
                      rfl

theorem cell23_2767460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2767460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767460 prefixEnd_2767460 := by exact prefixLift 2767460
  have htrace : WordTrace (prefixWord ++ tailWord_2767460) baseStart_2767460 baseEnd_2767460 := by
    simpa [prefixWord, tailWord_2767460, baseEnd_2767460] using wordTrace_append hprefix tailTrace_2767460
  have hstable : (prefixWord ++ tailWord_2767460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767460).length < 2 ^ (prefixWord ++ tailWord_2767460).sum := by decide
  have hdescent : baseEnd_2767460 < baseStart_2767460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767517 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2767517 : Nat := 118140960795 + 2767517 * 2 ^ 59
def prefixEnd_2767517 : Nat := 4983230072969 + 3 ^ 40 * 2767517 * 2
def baseEnd_2767517 : Nat := 1421066440489153810709927

theorem tailTrace_2767517 : CollatzResearch.WordTrace tailWord_2767517 prefixEnd_2767517 1421066440489153810709927 := by
  unfold tailWord_2767517
  simp only [CollatzResearch.WordTrace]
  refine ⟨100939637514766038118780805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67293091676510692079187203 100939637514766038118780805)
  ·
    refine ⟨18926182034018632147271401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100939637514766038118780805 18926182034018632147271401)
    ·
      refine ⟨14194636525513974110453551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18926182034018632147271401 14194636525513974110453551)
      ·
        refine ⟨21291954788270961165680327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194636525513974110453551 21291954788270961165680327)
        ·
          refine ⟨31937932182406441748520491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21291954788270961165680327 31937932182406441748520491)
          ·
            refine ⟨47906898273609662622780737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31937932182406441748520491 47906898273609662622780737)
            ·
              refine ⟨35930173705207246967085553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47906898273609662622780737 35930173705207246967085553)
              ·
                refine ⟨26947630278905435225314165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35930173705207246967085553 26947630278905435225314165)
                ·
                  refine ⟨2526340338647384552373203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26947630278905435225314165 2526340338647384552373203)
                  ·
                    refine ⟨3789510507971076828559805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526340338647384552373203 3789510507971076828559805)
                    ·
                      refine ⟨1421066440489153810709927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789510507971076828559805 1421066440489153810709927)
                      ·
                        rfl

theorem cell23_2767517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2767517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767517 prefixEnd_2767517 := by exact prefixLift 2767517
  have htrace : WordTrace (prefixWord ++ tailWord_2767517) baseStart_2767517 baseEnd_2767517 := by
    simpa [prefixWord, tailWord_2767517, baseEnd_2767517] using wordTrace_append hprefix tailTrace_2767517
  have hstable : (prefixWord ++ tailWord_2767517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767517).length < 2 ^ (prefixWord ++ tailWord_2767517).sum := by decide
  have hdescent : baseEnd_2767517 < baseStart_2767517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767607 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_2767607 : Nat := 118140960795 + 2767607 * 2 ^ 59
def prefixEnd_2767607 : Nat := 4983230072969 + 3 ^ 40 * 2767607 * 2
def baseEnd_2767607 : Nat := 1421112653748058458584513

theorem tailTrace_2767607 : CollatzResearch.WordTrace tailWord_2767607 prefixEnd_2767607 1421112653748058458584513 := by
  unfold tailWord_2767607
  simp only [CollatzResearch.WordTrace]
  refine ⟨100942920084439983489557075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67295280056293322326371383 100942920084439983489557075)
  ·
    refine ⟨151414380126659975234335613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100942920084439983489557075 151414380126659975234335613)
    ·
      refine ⟨56780392547497490712875855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151414380126659975234335613 56780392547497490712875855)
      ·
        refine ⟨85170588821246236069313783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56780392547497490712875855 85170588821246236069313783)
        ·
          refine ⟨127755883231869354103970675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85170588821246236069313783 127755883231869354103970675)
          ·
            refine ⟨191633824847804031155956013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127755883231869354103970675 191633824847804031155956013)
            ·
              refine ⟨71862684317926511683483505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191633824847804031155956013 71862684317926511683483505)
              ·
                refine ⟨53897013238444883762612629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71862684317926511683483505 53897013238444883762612629)
                ·
                  refine ⟨2526422495552103926372467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53897013238444883762612629 2526422495552103926372467)
                  ·
                    refine ⟨3789633743328155889558701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526422495552103926372467 3789633743328155889558701)
                    ·
                      refine ⟨1421112653748058458584513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789633743328155889558701 1421112653748058458584513)
                      ·
                        rfl

theorem cell23_2767607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_2767607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767607 prefixEnd_2767607 := by exact prefixLift 2767607
  have htrace : WordTrace (prefixWord ++ tailWord_2767607) baseStart_2767607 baseEnd_2767607 := by
    simpa [prefixWord, tailWord_2767607, baseEnd_2767607] using wordTrace_append hprefix tailTrace_2767607
  have hstable : (prefixWord ++ tailWord_2767607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767607).length < 2 ^ (prefixWord ++ tailWord_2767607).sum := by decide
  have hdescent : baseEnd_2767607 < baseStart_2767607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767614 : List Nat := [4, 2, 2, 1, 2, 2, 3, 7]
def baseStart_2767614 : Nat := 118140960795 + 2767614 * 2 ^ 59
def prefixEnd_2767614 : Nat := 4983230072969 + 3 ^ 40 * 2767614 * 2
def baseEnd_2767614 : Nat := 52633935115282960414703

theorem tailTrace_2767614 : CollatzResearch.WordTrace tailWord_2767614 prefixEnd_2767614 52633935115282960414703 := by
  unfold tailWord_2767614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617896924426827960632737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67295450263609749123374597 12617896924426827960632737)
  ·
    refine ⟨9463422693320120970474553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12617896924426827960632737 9463422693320120970474553)
    ·
      refine ⟨7097567019990090727855915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9463422693320120970474553 7097567019990090727855915)
      ·
        refine ⟨10646350529985136091783873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097567019990090727855915 10646350529985136091783873)
        ·
          refine ⟨7984762897488852068837905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10646350529985136091783873 7984762897488852068837905)
          ·
            refine ⟨5988572173116639051628429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7984762897488852068837905 5988572173116639051628429)
            ·
              refine ⟨2245714564918739644360661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5988572173116639051628429 2245714564918739644360661)
              ·
                refine ⟨52633935115282960414703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2245714564918739644360661 52633935115282960414703)
                ·
                  rfl

theorem cell23_2767614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_2767614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767614 prefixEnd_2767614 := by exact prefixLift 2767614
  have htrace : WordTrace (prefixWord ++ tailWord_2767614) baseStart_2767614 baseEnd_2767614 := by
    simpa [prefixWord, tailWord_2767614, baseEnd_2767614] using wordTrace_append hprefix tailTrace_2767614
  have hstable : (prefixWord ++ tailWord_2767614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767614).length < 2 ^ (prefixWord ++ tailWord_2767614).sum := by decide
  have hdescent : baseEnd_2767614 < baseStart_2767614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767658 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2767658 : Nat := 118140960795 + 2767658 * 2 ^ 59
def prefixEnd_2767658 : Nat := 4983230072969 + 3 ^ 40 * 2767658 * 2
def baseEnd_2767658 : Nat := 1421138841261437759046779

theorem tailTrace_2767658 : CollatzResearch.WordTrace tailWord_2767658 prefixEnd_2767658 1421138841261437759046779 := by
  unfold tailWord_2767658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236195051813804799915907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67296520138170146133109085 25236195051813804799915907)
  ·
    refine ⟨37854292577720707199873861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25236195051813804799915907 37854292577720707199873861)
    ·
      refine ⟨7097679858322632599976349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37854292577720707199873861 7097679858322632599976349)
      ·
        refine ⟨2661629946870987224991131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7097679858322632599976349 2661629946870987224991131)
        ·
          refine ⟨3992444920306480837486697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661629946870987224991131 3992444920306480837486697)
          ·
            refine ⟨2994333690229860628115023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992444920306480837486697 2994333690229860628115023)
            ·
              refine ⟨4491500535344790942172535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994333690229860628115023 4491500535344790942172535)
              ·
                refine ⟨6737250803017186413258803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491500535344790942172535 6737250803017186413258803)
                ·
                  refine ⟨10105876204525779619888205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6737250803017186413258803 10105876204525779619888205)
                  ·
                    refine ⟨3789703576697167357458077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10105876204525779619888205 3789703576697167357458077)
                    ·
                      refine ⟨1421138841261437759046779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789703576697167357458077 1421138841261437759046779)
                      ·
                        rfl

theorem cell23_2767658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2767658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767658 prefixEnd_2767658 := by exact prefixLift 2767658
  have htrace : WordTrace (prefixWord ++ tailWord_2767658) baseStart_2767658 baseEnd_2767658 := by
    simpa [prefixWord, tailWord_2767658, baseEnd_2767658] using wordTrace_append hprefix tailTrace_2767658
  have hstable : (prefixWord ++ tailWord_2767658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767658).length < 2 ^ (prefixWord ++ tailWord_2767658).sum := by decide
  have hdescent : baseEnd_2767658 < baseStart_2767658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767715 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2767715 : Nat := 118140960795 + 2767715 * 2 ^ 59
def prefixEnd_2767715 : Nat := 4983230072969 + 3 ^ 40 * 2767715 * 2
def baseEnd_2767715 : Nat := 1421168109658744036034017

theorem tailTrace_2767715 : CollatzResearch.WordTrace tailWord_2767715 prefixEnd_2767715 1421168109658744036034017 := by
  unfold tailWord_2767715
  simp only [CollatzResearch.WordTrace]
  refine ⟨100946859168048717934488599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67297906112032478622992399 100946859168048717934488599)
  ·
    refine ⟨151420288752073076901732899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100946859168048717934488599 151420288752073076901732899)
    ·
      refine ⟨227130433128109615352599349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151420288752073076901732899 227130433128109615352599349)
      ·
        refine ⟨21293478105760276439306189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227130433128109615352599349 21293478105760276439306189)
        ·
          refine ⟨7985054289660103664739821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21293478105760276439306189 7985054289660103664739821)
          ·
            refine ⟨2994395358622538874277433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7985054289660103664739821 2994395358622538874277433)
            ·
              refine ⟨2245796518966904155708075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994395358622538874277433 2245796518966904155708075)
              ·
                refine ⟨3368694778450356233562113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245796518966904155708075 3368694778450356233562113)
                ·
                  refine ⟨2526521083837767175171585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368694778450356233562113 2526521083837767175171585)
                  ·
                    refine ⟨1894890812878325381378689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2526521083837767175171585 1894890812878325381378689)
                    ·
                      refine ⟨1421168109658744036034017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1894890812878325381378689 1421168109658744036034017)
                      ·
                        rfl

theorem cell23_2767715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2767715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767715 prefixEnd_2767715 := by exact prefixLift 2767715
  have htrace : WordTrace (prefixWord ++ tailWord_2767715) baseStart_2767715 baseEnd_2767715 := by
    simpa [prefixWord, tailWord_2767715, baseEnd_2767715] using wordTrace_append hprefix tailTrace_2767715
  have hstable : (prefixWord ++ tailWord_2767715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767715).length < 2 ^ (prefixWord ++ tailWord_2767715).sum := by decide
  have hdescent : baseEnd_2767715 < baseStart_2767715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3]
def baseStart_2767787 : Nat := 118140960795 + 2767787 * 2 ^ 59
def prefixEnd_2767787 : Nat := 4983230072969 + 3 ^ 40 * 2767787 * 2
def baseEnd_2767787 : Nat := 1421205080265867754333685

theorem tailTrace_2767787 : CollatzResearch.WordTrace tailWord_2767787 prefixEnd_2767787 1421205080265867754333685 := by
  unfold tailWord_2767787
  simp only [CollatzResearch.WordTrace]
  refine ⟨100949485223787874231109615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67299656815858582820739743 100949485223787874231109615)
  ·
    refine ⟨151424227835681811346664423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100949485223787874231109615 151424227835681811346664423)
    ·
      refine ⟨227136341753522717019996635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151424227835681811346664423 227136341753522717019996635)
      ·
        refine ⟨340704512630284075529994953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227136341753522717019996635 340704512630284075529994953)
        ·
          refine ⟨255528384472713056647496215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340704512630284075529994953 255528384472713056647496215)
          ·
            refine ⟨383292576709069584971244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255528384472713056647496215 383292576709069584971244323)
            ·
              refine ⟨574938865063604377456866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383292576709069584971244323 574938865063604377456866485)
              ·
                refine ⟨53900518599712910386581233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574938865063604377456866485 53900518599712910386581233)
                ·
                  refine ⟨40425388949784682789935925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53900518599712910386581233 40425388949784682789935925)
                  ·
                    refine ⟨3789880214042314011556493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40425388949784682789935925 3789880214042314011556493)
                    ·
                      refine ⟨1421205080265867754333685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789880214042314011556493 1421205080265867754333685)
                      ·
                        rfl

theorem cell23_2767787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].length) (baseStart_2767787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767787 prefixEnd_2767787 := by exact prefixLift 2767787
  have htrace : WordTrace (prefixWord ++ tailWord_2767787) baseStart_2767787 baseEnd_2767787 := by
    simpa [prefixWord, tailWord_2767787, baseEnd_2767787] using wordTrace_append hprefix tailTrace_2767787
  have hstable : (prefixWord ++ tailWord_2767787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767787).length < 2 ^ (prefixWord ++ tailWord_2767787).sum := by decide
  have hdescent : baseEnd_2767787 < baseStart_2767787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767807 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 5, 5]
def baseStart_2767807 : Nat := 118140960795 + 2767807 * 2 ^ 59
def prefixEnd_2767807 : Nat := 4983230072969 + 3 ^ 40 * 2767807 * 2
def baseEnd_2767807 : Nat := 473738449959652558694531

theorem tailTrace_2767807 : CollatzResearch.WordTrace tailWord_2767807 prefixEnd_2767807 473738449959652558694531 := by
  unfold tailWord_2767807
  simp only [CollatzResearch.WordTrace]
  refine ⟨100950214683715417646837675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67300143122476945097891783 100950214683715417646837675)
  ·
    refine ⟨151425322025573126470256513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100950214683715417646837675 151425322025573126470256513)
    ·
      refine ⟨113568991519179844852692385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151425322025573126470256513 113568991519179844852692385)
      ·
        refine ⟨85176743639384883639519289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113568991519179844852692385 85176743639384883639519289)
        ·
          refine ⟨63882557729538662729639467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85176743639384883639519289 63882557729538662729639467)
          ·
            refine ⟨95823836594307994094459201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63882557729538662729639467 95823836594307994094459201)
            ·
              refine ⟨71867877445730995570844401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95823836594307994094459201 71867877445730995570844401)
              ·
                refine ⟨53900908084298246678133301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71867877445730995570844401 53900908084298246678133301)
                ·
                  refine ⟨5053210132902960626074997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53900908084298246678133301 5053210132902960626074997)
                  ·
                    refine ⟨473738449959652558694531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5053210132902960626074997 473738449959652558694531)
                    ·
                      rfl

theorem cell23_2767807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_2767807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767807 prefixEnd_2767807 := by exact prefixLift 2767807
  have htrace : WordTrace (prefixWord ++ tailWord_2767807) baseStart_2767807 baseEnd_2767807 := by
    simpa [prefixWord, tailWord_2767807, baseEnd_2767807] using wordTrace_append hprefix tailTrace_2767807
  have hstable : (prefixWord ++ tailWord_2767807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767807).length < 2 ^ (prefixWord ++ tailWord_2767807).sum := by decide
  have hdescent : baseEnd_2767807 < baseStart_2767807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767855 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 1, 1, 3]
def baseStart_2767855 : Nat := 118140960795 + 2767855 * 2 ^ 59
def prefixEnd_2767855 : Nat := 4983230072969 + 3 ^ 40 * 2767855 * 2
def baseEnd_2767855 : Nat := 1421239996950373488283373

theorem tailTrace_2767855 : CollatzResearch.WordTrace tailWord_2767855 prefixEnd_2767855 1421239996950373488283373 := by
  unfold tailWord_2767855
  simp only [CollatzResearch.WordTrace]
  refine ⟨100951965387541521844585019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67301310258361014563056679 100951965387541521844585019)
  ·
    refine ⟨151427948081312282766877529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100951965387541521844585019 151427948081312282766877529)
    ·
      refine ⟨113570961060984212075158147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151427948081312282766877529 113570961060984212075158147)
      ·
        refine ⟨170356441591476318112737221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113570961060984212075158147 170356441591476318112737221)
        ·
          refine ⟨31941832798401809646138229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170356441591476318112737221 31941832798401809646138229)
          ·
            refine ⟨2994546824850169654325459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31941832798401809646138229 2994546824850169654325459)
            ·
              refine ⟨4491820237275254481488189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994546824850169654325459 4491820237275254481488189)
              ·
                refine ⟨1684432588978220430558071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4491820237275254481488189 1684432588978220430558071)
                ·
                  refine ⟨2526648883467330645837107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684432588978220430558071 2526648883467330645837107)
                  ·
                    refine ⟨3789973325200995968755661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526648883467330645837107 3789973325200995968755661)
                    ·
                      refine ⟨1421239996950373488283373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789973325200995968755661 1421239996950373488283373)
                      ·
                        rfl

theorem cell23_2767855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 1, 3].length) (baseStart_2767855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767855 prefixEnd_2767855 := by exact prefixLift 2767855
  have htrace : WordTrace (prefixWord ++ tailWord_2767855) baseStart_2767855 baseEnd_2767855 := by
    simpa [prefixWord, tailWord_2767855, baseEnd_2767855] using wordTrace_append hprefix tailTrace_2767855
  have hstable : (prefixWord ++ tailWord_2767855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767855).length < 2 ^ (prefixWord ++ tailWord_2767855).sum := by decide
  have hdescent : baseEnd_2767855 < baseStart_2767855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767864 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_2767864 : Nat := 118140960795 + 2767864 * 2 ^ 59
def prefixEnd_2767864 : Nat := 4983230072969 + 3 ^ 40 * 2767864 * 2
def baseEnd_2767864 : Nat := 1421244618276263953070831

theorem tailTrace_2767864 : CollatzResearch.WordTrace tailWord_2767864 prefixEnd_2767864 1421244618276263953070831 := by
  unfold tailWord_2767864
  simp only [CollatzResearch.WordTrace]
  refine ⟨50476146822254458190831323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67301529096339277587775097 50476146822254458190831323)
  ·
    refine ⟨75714220233381687286246985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50476146822254458190831323 75714220233381687286246985)
    ·
      refine ⟨56785665175036265464685239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75714220233381687286246985 56785665175036265464685239)
      ·
        refine ⟨85178497762554398197027859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56785665175036265464685239 85178497762554398197027859)
        ·
          refine ⟨127767746643831597295541789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85178497762554398197027859 127767746643831597295541789)
          ·
            refine ⟨47912904991436848985828171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127767746643831597295541789 47912904991436848985828171)
            ·
              refine ⟨71869357487155273478742257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47912904991436848985828171 71869357487155273478742257)
              ·
                refine ⟨53902018115366455109056693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71869357487155273478742257 53902018115366455109056693)
                ·
                  refine ⟨5053314198315605166474065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53902018115366455109056693 5053314198315605166474065)
                  ·
                    refine ⟨3789985648736703874855549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5053314198315605166474065 3789985648736703874855549)
                    ·
                      refine ⟨1421244618276263953070831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3789985648736703874855549 1421244618276263953070831)
                      ·
                        rfl

theorem cell23_2767864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_2767864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767864 prefixEnd_2767864 := by exact prefixLift 2767864
  have htrace : WordTrace (prefixWord ++ tailWord_2767864) baseStart_2767864 baseEnd_2767864 := by
    simpa [prefixWord, tailWord_2767864, baseEnd_2767864] using wordTrace_append hprefix tailTrace_2767864
  have hstable : (prefixWord ++ tailWord_2767864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767864).length < 2 ^ (prefixWord ++ tailWord_2767864).sum := by decide
  have hdescent : baseEnd_2767864 < baseStart_2767864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767884 : List Nat := [2, 2, 1, 2, 3, 3, 2, 8]
def baseStart_2767884 : Nat := 118140960795 + 2767884 * 2 ^ 59
def prefixEnd_2767884 : Nat := 4983230072969 + 3 ^ 40 * 2767884 * 2
def baseEnd_2767884 : Nat := 52639069921827921289657

theorem tailTrace_2767884 : CollatzResearch.WordTrace tailWord_2767884 prefixEnd_2767884 52639069921827921289657 := by
  unfold tailWord_2767884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50476511552218229898695353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67302015402957639864927137 50476511552218229898695353)
  ·
    refine ⟨37857383664163672424021515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50476511552218229898695353 37857383664163672424021515)
    ·
      refine ⟨56786075496245508636032273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37857383664163672424021515 56786075496245508636032273)
      ·
        refine ⟨42589556622184131477024205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56786075496245508636032273 42589556622184131477024205)
        ·
          refine ⟨15971083733319049303884077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42589556622184131477024205 15971083733319049303884077)
          ·
            refine ⟨5989156399994643488956529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15971083733319049303884077 5989156399994643488956529)
            ·
              refine ⟨4491867299995982616717397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5989156399994643488956529 4491867299995982616717397)
              ·
                refine ⟨52639069921827921289657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4491867299995982616717397 52639069921827921289657)
                ·
                  rfl

theorem cell23_2767884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 8].length) (baseStart_2767884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767884 prefixEnd_2767884 := by exact prefixLift 2767884
  have htrace : WordTrace (prefixWord ++ tailWord_2767884) baseStart_2767884 baseEnd_2767884 := by
    simpa [prefixWord, tailWord_2767884, baseEnd_2767884] using wordTrace_append hprefix tailTrace_2767884
  have hstable : (prefixWord ++ tailWord_2767884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767884).length < 2 ^ (prefixWord ++ tailWord_2767884).sum := by decide
  have hdescent : baseEnd_2767884 < baseStart_2767884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767928 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_2767928 : Nat := 118140960795 + 2767928 * 2 ^ 59
def prefixEnd_2767928 : Nat := 4983230072969 + 3 ^ 40 * 2767928 * 2
def baseEnd_2767928 : Nat := 1421277481038151702670537

theorem tailTrace_2767928 : CollatzResearch.WordTrace tailWord_2767928 prefixEnd_2767928 1421277481038151702670537 := by
  unfold tailWord_2767928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50477313958138527655996219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67303085277518036874661625 50477313958138527655996219)
  ·
    refine ⟨75715970937207791483994329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50477313958138527655996219 75715970937207791483994329)
    ·
      refine ⟨56786978202905843612995747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75715970937207791483994329 56786978202905843612995747)
      ·
        refine ⟨85180467304358765419493621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56786978202905843612995747 85180467304358765419493621)
        ·
          refine ⟨7985668809783634258077527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85180467304358765419493621 7985668809783634258077527)
          ·
            refine ⟨11978503214675451387116291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985668809783634258077527 11978503214675451387116291)
            ·
              refine ⟨17967754822013177080674437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11978503214675451387116291 17967754822013177080674437)
              ·
                refine ⟨3368954029127470702626457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17967754822013177080674437 3368954029127470702626457)
                ·
                  refine ⟨2526715521845603026969843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368954029127470702626457 2526715521845603026969843)
                  ·
                    refine ⟨3790073282768404540454765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526715521845603026969843 3790073282768404540454765)
                    ·
                      refine ⟨1421277481038151702670537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790073282768404540454765 1421277481038151702670537)
                      ·
                        rfl

theorem cell23_2767928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_2767928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767928 prefixEnd_2767928 := by exact prefixLift 2767928
  have htrace : WordTrace (prefixWord ++ tailWord_2767928) baseStart_2767928 baseEnd_2767928 := by
    simpa [prefixWord, tailWord_2767928, baseEnd_2767928] using wordTrace_append hprefix tailTrace_2767928
  have hstable : (prefixWord ++ tailWord_2767928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767928).length < 2 ^ (prefixWord ++ tailWord_2767928).sum := by decide
  have hdescent : baseEnd_2767928 < baseStart_2767928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767929 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2767929 : Nat := 118140960795 + 2767929 * 2 ^ 59
def prefixEnd_2767929 : Nat := 4983230072969 + 3 ^ 40 * 2767929 * 2
def baseEnd_2767929 : Nat := 1421277994518806198758033

theorem tailTrace_2767929 : CollatzResearch.WordTrace tailWord_2767929 prefixEnd_2767929 1421277994518806198758033 := by
  unfold tailWord_2767929
  simp only [CollatzResearch.WordTrace]
  refine ⟨100954664389273432482778841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67303109592848954988519227 100954664389273432482778841)
  ·
    refine ⟨75715998291955074362084131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100954664389273432482778841 75715998291955074362084131)
    ·
      refine ⟨113573997437932611543126197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75715998291955074362084131 113573997437932611543126197)
      ·
        refine ⟨10647562259806182332168081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113573997437932611543126197 10647562259806182332168081)
        ·
          refine ⟨7985671694854636749126061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10647562259806182332168081 7985671694854636749126061)
          ·
            refine ⟨2994626885570488780922273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7985671694854636749126061 2994626885570488780922273)
            ·
              refine ⟨2245970164177866585691705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994626885570488780922273 2245970164177866585691705)
              ·
                refine ⟨1684477623133399939268779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245970164177866585691705 1684477623133399939268779)
                ·
                  refine ⟨2526716434700099908903169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684477623133399939268779 2526716434700099908903169)
                  ·
                    refine ⟨1895037326025074931677377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2526716434700099908903169 1895037326025074931677377)
                    ·
                      refine ⟨1421277994518806198758033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895037326025074931677377 1421277994518806198758033)
                      ·
                        rfl

theorem cell23_2767929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2767929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767929 prefixEnd_2767929 := by exact prefixLift 2767929
  have htrace : WordTrace (prefixWord ++ tailWord_2767929) baseStart_2767929 baseEnd_2767929 := by
    simpa [prefixWord, tailWord_2767929, baseEnd_2767929] using wordTrace_append hprefix tailTrace_2767929
  have hstable : (prefixWord ++ tailWord_2767929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767929).length < 2 ^ (prefixWord ++ tailWord_2767929).sum := by decide
  have hdescent : baseEnd_2767929 < baseStart_2767929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767944 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_2767944 : Nat := 118140960795 + 2767944 * 2 ^ 59
def prefixEnd_2767944 : Nat := 4983230072969 + 3 ^ 40 * 2767944 * 2
def baseEnd_2767944 : Nat := 473761898909541213356821

theorem tailTrace_2767944 : CollatzResearch.WordTrace tailWord_2767944 prefixEnd_2767944 473761898909541213356821 := by
  unfold tailWord_2767944
  simp only [CollatzResearch.WordTrace]
  refine ⟨50477605742109545022287443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67303474322812726696383257 50477605742109545022287443)
  ·
    refine ⟨75716408613164317533431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50477605742109545022287443 75716408613164317533431165)
    ·
      refine ⟨28393653229936619075036687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75716408613164317533431165 28393653229936619075036687)
      ·
        refine ⟨42590479844904928612555031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28393653229936619075036687 42590479844904928612555031)
        ·
          refine ⟨63885719767357392918832547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42590479844904928612555031 63885719767357392918832547)
          ·
            refine ⟨95828579651036089378248821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63885719767357392918832547 95828579651036089378248821)
            ·
              refine ⟨8983929342284633379210827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95828579651036089378248821 8983929342284633379210827)
              ·
                refine ⟨13475894013426950068816241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8983929342284633379210827 13475894013426950068816241)
                ·
                  refine ⟨10106920510070212551612181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13475894013426950068816241 10106920510070212551612181)
                  ·
                    refine ⟨473761898909541213356821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10106920510070212551612181 473761898909541213356821)
                    ·
                      rfl

theorem cell23_2767944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_2767944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767944 prefixEnd_2767944 := by exact prefixLift 2767944
  have htrace : WordTrace (prefixWord ++ tailWord_2767944) baseStart_2767944 baseEnd_2767944 := by
    simpa [prefixWord, tailWord_2767944, baseEnd_2767944] using wordTrace_append hprefix tailTrace_2767944
  have hstable : (prefixWord ++ tailWord_2767944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767944).length < 2 ^ (prefixWord ++ tailWord_2767944).sum := by decide
  have hdescent : baseEnd_2767944 < baseStart_2767944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767968 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2]
def baseStart_2767968 : Nat := 118140960795 + 2767968 * 2 ^ 59
def prefixEnd_2767968 : Nat := 4983230072969 + 3 ^ 40 * 2767968 * 2
def baseEnd_2767968 : Nat := 1421298020264331546170353

theorem tailTrace_2767968 : CollatzResearch.WordTrace tailWord_2767968 prefixEnd_2767968 1421298020264331546170353 := by
  unfold tailWord_2767968
  simp only [CollatzResearch.WordTrace]
  refine ⟨50478043418066071071724279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67304057890754761428965705 50478043418066071071724279)
  ·
    refine ⟨75717065127099106607586419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50478043418066071071724279 75717065127099106607586419)
    ·
      refine ⟨113575597690648659911379629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75717065127099106607586419 113575597690648659911379629)
      ·
        refine ⟨42590849133993247466767361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113575597690648659911379629 42590849133993247466767361)
        ·
          refine ⟨31943136850494935600075521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42590849133993247466767361 31943136850494935600075521)
          ·
            refine ⟨23957352637871201700056641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31943136850494935600075521 23957352637871201700056641)
            ·
              refine ⟨17968014478403401275042481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23957352637871201700056641 17968014478403401275042481)
              ·
                refine ⟨13476010858802550956281861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17968014478403401275042481 13476010858802550956281861)
                ·
                  refine ⟨2526752036025478304302849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13476010858802550956281861 2526752036025478304302849)
                  ·
                    refine ⟨1895064027019108728227137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2526752036025478304302849 1895064027019108728227137)
                    ·
                      refine ⟨1421298020264331546170353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895064027019108728227137 1421298020264331546170353)
                      ·
                        rfl

theorem cell23_2767968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_2767968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767968 prefixEnd_2767968 := by exact prefixLift 2767968
  have htrace : WordTrace (prefixWord ++ tailWord_2767968) baseStart_2767968 baseEnd_2767968 := by
    simpa [prefixWord, tailWord_2767968, baseEnd_2767968] using wordTrace_append hprefix tailTrace_2767968
  have hstable : (prefixWord ++ tailWord_2767968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767968).length < 2 ^ (prefixWord ++ tailWord_2767968).sum := by decide
  have hdescent : baseEnd_2767968 < baseStart_2767968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767981 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2767981 : Nat := 118140960795 + 2767981 * 2 ^ 59
def prefixEnd_2767981 : Nat := 4983230072969 + 3 ^ 40 * 2767981 * 2
def baseEnd_2767981 : Nat := 1421304695512839995307793

theorem tailTrace_2767981 : CollatzResearch.WordTrace tailWord_2767981 prefixEnd_2767981 1421304695512839995307793 := by
  unfold tailWord_2767981
  simp only [CollatzResearch.WordTrace]
  refine ⟨100956560985085045363671797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67304373990056696909114531 100956560985085045363671797)
  ·
    refine ⟨9464677592351723002844231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100956560985085045363671797 9464677592351723002844231)
    ·
      refine ⟨14197016388527584504266347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9464677592351723002844231 14197016388527584504266347)
      ·
        refine ⟨21295524582791376756399521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14197016388527584504266347 21295524582791376756399521)
        ·
          refine ⟨15971643437093532567299641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21295524582791376756399521 15971643437093532567299641)
          ·
            refine ⟨11978732577820149425474731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15971643437093532567299641 11978732577820149425474731)
            ·
              refine ⟨17968098866730224138212097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11978732577820149425474731 17968098866730224138212097)
              ·
                refine ⟨13476074150047668103659073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17968098866730224138212097 13476074150047668103659073)
                ·
                  refine ⟨10107055612535751077744305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13476074150047668103659073 10107055612535751077744305)
                  ·
                    refine ⟨7580291709401813308308229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10107055612535751077744305 7580291709401813308308229)
                    ·
                      refine ⟨1421304695512839995307793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7580291709401813308308229 1421304695512839995307793)
                      ·
                        rfl

theorem cell23_2767981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2767981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767981 prefixEnd_2767981 := by exact prefixLift 2767981
  have htrace : WordTrace (prefixWord ++ tailWord_2767981) baseStart_2767981 baseEnd_2767981 := by
    simpa [prefixWord, tailWord_2767981, baseEnd_2767981] using wordTrace_append hprefix tailTrace_2767981
  have hstable : (prefixWord ++ tailWord_2767981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767981).length < 2 ^ (prefixWord ++ tailWord_2767981).sum := by decide
  have hdescent : baseEnd_2767981 < baseStart_2767981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767991 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 5]
def baseStart_2767991 : Nat := 118140960795 + 2767991 * 2 ^ 59
def prefixEnd_2767991 : Nat := 4983230072969 + 3 ^ 40 * 2767991 * 2
def baseEnd_2767991 : Nat := 157923314479931661798083

theorem tailTrace_2767991 : CollatzResearch.WordTrace tailWord_2767991 prefixEnd_2767991 157923314479931661798083 := by
  unfold tailWord_2767991
  simp only [CollatzResearch.WordTrace]
  refine ⟨100956925715048817071535827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67304617143365878047690551 100956925715048817071535827)
  ·
    refine ⟨151435388572573225607303741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100956925715048817071535827 151435388572573225607303741)
    ·
      refine ⟨56788270714714959602738903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151435388572573225607303741 56788270714714959602738903)
      ·
        refine ⟨85182406072072439404108355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56788270714714959602738903 85182406072072439404108355)
        ·
          refine ⟨127773609108108659106162533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85182406072072439404108355 127773609108108659106162533)
          ·
            refine ⟨23957551707770373582405475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127773609108108659106162533 23957551707770373582405475)
            ·
              refine ⟨35936327561655560373608213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23957551707770373582405475 35936327561655560373608213)
              ·
                refine ⟨1684515354452604392512885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35936327561655560373608213 1684515354452604392512885)
                ·
                  refine ⟨157923314479931661798083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1684515354452604392512885 157923314479931661798083)
                  ·
                    rfl

theorem cell23_2767991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 5].length) (baseStart_2767991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2767991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2767991 prefixEnd_2767991 := by exact prefixLift 2767991
  have htrace : WordTrace (prefixWord ++ tailWord_2767991) baseStart_2767991 baseEnd_2767991 := by
    simpa [prefixWord, tailWord_2767991, baseEnd_2767991] using wordTrace_append hprefix tailTrace_2767991
  have hstable : (prefixWord ++ tailWord_2767991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767991).length < 2 ^ (prefixWord ++ tailWord_2767991).sum := by decide
  have hdescent : baseEnd_2767991 < baseStart_2767991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768011 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 5, 2]
def baseStart_2768011 : Nat := 118140960795 + 2768011 * 2 ^ 59
def prefixEnd_2768011 : Nat := 4983230072969 + 3 ^ 40 * 2768011 * 2
def baseEnd_2768011 : Nat := 1421320099932474877932655

theorem tailTrace_2768011 : CollatzResearch.WordTrace tailWord_2768011 prefixEnd_2768011 1421320099932474877932655 := by
  unfold tailWord_2768011
  simp only [CollatzResearch.WordTrace]
  refine ⟨100957655174976360487263887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67305103449984240324842591 100957655174976360487263887)
  ·
    refine ⟨151436482762464540730895831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100957655174976360487263887 151436482762464540730895831)
    ·
      refine ⟨227154724143696811096343747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151436482762464540730895831 227154724143696811096343747)
      ·
        refine ⟨340732086215545216644515621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227154724143696811096343747 340732086215545216644515621)
        ·
          refine ⟨63887266165414728120846679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340732086215545216644515621 63887266165414728120846679)
          ·
            refine ⟨95830899248122092181270019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63887266165414728120846679 95830899248122092181270019)
            ·
              refine ⟨143746348872183138271905029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95830899248122092181270019 143746348872183138271905029)
              ·
                refine ⟨26952440413534338425982193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143746348872183138271905029 26952440413534338425982193)
                ·
                  refine ⟨20214330310150753819486645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26952440413534338425982193 20214330310150753819486645)
                  ·
                    refine ⟨1895093466576633170576873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20214330310150753819486645 1895093466576633170576873)
                    ·
                      refine ⟨1421320099932474877932655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895093466576633170576873 1421320099932474877932655)
                      ·
                        rfl

theorem cell23_2768011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5, 2].length) (baseStart_2768011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768011 prefixEnd_2768011 := by exact prefixLift 2768011
  have htrace : WordTrace (prefixWord ++ tailWord_2768011) baseStart_2768011 baseEnd_2768011 := by
    simpa [prefixWord, tailWord_2768011, baseEnd_2768011] using wordTrace_append hprefix tailTrace_2768011
  have hstable : (prefixWord ++ tailWord_2768011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768011).length < 2 ^ (prefixWord ++ tailWord_2768011).sum := by decide
  have hdescent : baseEnd_2768011 < baseStart_2768011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768041 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 6, 2]
def baseStart_2768041 : Nat := 118140960795 + 2768041 * 2 ^ 59
def prefixEnd_2768041 : Nat := 4983230072969 + 3 ^ 40 * 2768041 * 2
def baseEnd_2768041 : Nat := 1421335504352109760557517

theorem tailTrace_2768041 : CollatzResearch.WordTrace tailWord_2768041 prefixEnd_2768041 1421335504352109760557517 := by
  unfold tailWord_2768041
  simp only [CollatzResearch.WordTrace]
  refine ⟨100958749364867675610855977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67305832909911783740570651 100958749364867675610855977)
  ·
    refine ⟨75719062023650756708141983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100958749364867675610855977 75719062023650756708141983)
    ·
      refine ⟨113578593035476135062212975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75719062023650756708141983 113578593035476135062212975)
      ·
        refine ⟨170367889553214202593319463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113578593035476135062212975 170367889553214202593319463)
        ·
          refine ⟨255551834329821303889979195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170367889553214202593319463 255551834329821303889979195)
          ·
            refine ⟨383327751494731955834968793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255551834329821303889979195 383327751494731955834968793)
            ·
              refine ⟨287495813621048966876226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383327751494731955834968793 287495813621048966876226595)
              ·
                refine ⟨431243720431573450314339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287495813621048966876226595 431243720431573450314339893)
                ·
                  refine ⟨40429098790460010966969365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431243720431573450314339893 40429098790460010966969365)
                  ·
                    refine ⟨1895114005802813014076689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40429098790460010966969365 1895114005802813014076689)
                    ·
                      refine ⟨1421335504352109760557517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895114005802813014076689 1421335504352109760557517)
                      ·
                        rfl

theorem cell23_2768041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6, 2].length) (baseStart_2768041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768041 prefixEnd_2768041 := by exact prefixLift 2768041
  have htrace : WordTrace (prefixWord ++ tailWord_2768041) baseStart_2768041 baseEnd_2768041 := by
    simpa [prefixWord, tailWord_2768041, baseEnd_2768041] using wordTrace_append hprefix tailTrace_2768041
  have hstable : (prefixWord ++ tailWord_2768041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768041).length < 2 ^ (prefixWord ++ tailWord_2768041).sum := by decide
  have hdescent : baseEnd_2768041 < baseStart_2768041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768042 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_2768042 : Nat := 118140960795 + 2768042 * 2 ^ 59
def prefixEnd_2768042 : Nat := 4983230072969 + 3 ^ 40 * 2768042 * 2
def baseEnd_2768042 : Nat := 157926224203640472960557

theorem tailTrace_2768042 : CollatzResearch.WordTrace tailWord_2768042 prefixEnd_2768042 157926224203640472960557 := by
  unfold tailWord_2768042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25239696459466013195410595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67305857225242701854428253 25239696459466013195410595)
  ·
    refine ⟨37859544689199019793115893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25239696459466013195410595 37859544689199019793115893)
    ·
      refine ⟨3549332314612408105604615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37859544689199019793115893 3549332314612408105604615)
      ·
        refine ⟨5323998471918612158406923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549332314612408105604615 5323998471918612158406923)
        ·
          refine ⟨7985997707877918237610385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323998471918612158406923 7985997707877918237610385)
          ·
            refine ⟨5989498280908438678207789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7985997707877918237610385 5989498280908438678207789)
            ·
              refine ⟨2246061855340664504327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989498280908438678207789 2246061855340664504327921)
              ·
                refine ⟨1684546391505498378245941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246061855340664504327921 1684546391505498378245941)
                ·
                  refine ⟨157926224203640472960557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1684546391505498378245941 157926224203640472960557)
                  ·
                    rfl

theorem cell23_2768042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_2768042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768042 prefixEnd_2768042 := by exact prefixLift 2768042
  have htrace : WordTrace (prefixWord ++ tailWord_2768042) baseStart_2768042 baseEnd_2768042 := by
    simpa [prefixWord, tailWord_2768042, baseEnd_2768042] using wordTrace_append hprefix tailTrace_2768042
  have hstable : (prefixWord ++ tailWord_2768042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768042).length < 2 ^ (prefixWord ++ tailWord_2768042).sum := by decide
  have hdescent : baseEnd_2768042 < baseStart_2768042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768044 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2768044 : Nat := 118140960795 + 2768044 * 2 ^ 59
def prefixEnd_2768044 : Nat := 4983230072969 + 3 ^ 40 * 2768044 * 2
def baseEnd_2768044 : Nat := 1421337044794073248820003

theorem tailTrace_2768044 : CollatzResearch.WordTrace tailWord_2768044 prefixEnd_2768044 1421337044794073248820003 := by
  unfold tailWord_2768044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50479429391928403561607593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67305905855904538082143457 50479429391928403561607593)
  ·
    refine ⟨37859572043946302671205695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50479429391928403561607593 37859572043946302671205695)
    ·
      refine ⟨56789358065919454006808543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37859572043946302671205695 56789358065919454006808543)
      ·
        refine ⟨85184037098879181010212815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56789358065919454006808543 85184037098879181010212815)
        ·
          refine ⟨127776055648318771515319223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85184037098879181010212815 127776055648318771515319223)
          ·
            refine ⟨191664083472478157272978835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127776055648318771515319223 191664083472478157272978835)
            ·
              refine ⟨287496125208717235909468253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191664083472478157272978835 287496125208717235909468253)
              ·
                refine ⟨107811046953268963466050595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287496125208717235909468253 107811046953268963466050595)
                ·
                  refine ⟨161716570429903445199075893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107811046953268963466050595 161716570429903445199075893)
                  ·
                    refine ⟨15160928477803447987413365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161716570429903445199075893 15160928477803447987413365)
                    ·
                      refine ⟨1421337044794073248820003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15160928477803447987413365 1421337044794073248820003)
                      ·
                        rfl

theorem cell23_2768044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2768044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768044 prefixEnd_2768044 := by exact prefixLift 2768044
  have htrace : WordTrace (prefixWord ++ tailWord_2768044) baseStart_2768044 baseEnd_2768044 := by
    simpa [prefixWord, tailWord_2768044, baseEnd_2768044] using wordTrace_append hprefix tailTrace_2768044
  have hstable : (prefixWord ++ tailWord_2768044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768044).length < 2 ^ (prefixWord ++ tailWord_2768044).sum := by decide
  have hdescent : baseEnd_2768044 < baseStart_2768044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768061 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2768061 : Nat := 118140960795 + 2768061 * 2 ^ 59
def prefixEnd_2768061 : Nat := 4983230072969 + 3 ^ 40 * 2768061 * 2
def baseEnd_2768061 : Nat := 1421345773965199682307425

theorem tailTrace_2768061 : CollatzResearch.WordTrace tailWord_2768061 prefixEnd_2768061 1421345773965199682307425 := by
  unfold tailWord_2768061
  simp only [CollatzResearch.WordTrace]
  refine ⟨100959478824795219026584037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67306319216530146017722691 100959478824795219026584037)
  ·
    refine ⟨18929902279649103567484507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100959478824795219026584037 18929902279649103567484507)
    ·
      refine ⟨28394853419473655351226761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18929902279649103567484507 28394853419473655351226761)
      ·
        refine ⟨21296140064605241513420071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28394853419473655351226761 21296140064605241513420071)
        ·
          refine ⟨31944210096907862270130107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296140064605241513420071 31944210096907862270130107)
          ·
            refine ⟨47916315145361793405195161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31944210096907862270130107 47916315145361793405195161)
            ·
              refine ⟨35937236359021345053896371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47916315145361793405195161 35937236359021345053896371)
              ·
                refine ⟨53905854538532017580844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35937236359021345053896371 53905854538532017580844557)
                ·
                  refine ⟨20214695451949506592816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53905854538532017580844557 20214695451949506592816709)
                  ·
                    refine ⟨3790255397240532486153133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20214695451949506592816709 3790255397240532486153133)
                    ·
                      refine ⟨1421345773965199682307425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790255397240532486153133 1421345773965199682307425)
                      ·
                        rfl

theorem cell23_2768061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2768061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768061 prefixEnd_2768061 := by exact prefixLift 2768061
  have htrace : WordTrace (prefixWord ++ tailWord_2768061) baseStart_2768061 baseEnd_2768061 := by
    simpa [prefixWord, tailWord_2768061, baseEnd_2768061] using wordTrace_append hprefix tailTrace_2768061
  have hstable : (prefixWord ++ tailWord_2768061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768061).length < 2 ^ (prefixWord ++ tailWord_2768061).sum := by decide
  have hdescent : baseEnd_2768061 < baseStart_2768061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768142 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2768142 : Nat := 118140960795 + 2768142 * 2 ^ 59
def prefixEnd_2768142 : Nat := 4983230072969 + 3 ^ 40 * 2768142 * 2
def baseEnd_2768142 : Nat := 1421387365898213865394553

theorem tailTrace_2768142 : CollatzResearch.WordTrace tailWord_2768142 prefixEnd_2768142 1421387365898213865394553 := by
  unfold tailWord_2768142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620304142187721232535335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67308288758334513240188453 12620304142187721232535335)
  ·
    refine ⟨18930456213281581848803003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12620304142187721232535335 18930456213281581848803003)
    ·
      refine ⟨28395684319922372773204505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18930456213281581848803003 28395684319922372773204505)
      ·
        refine ⟨21296763239941779579903379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28395684319922372773204505 21296763239941779579903379)
        ·
          refine ⟨31945144859912669369855069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296763239941779579903379 31945144859912669369855069)
          ·
            refine ⟨11979429322467251013695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31945144859912669369855069 11979429322467251013695651)
            ·
              refine ⟨17969143983700876520543477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979429322467251013695651 17969143983700876520543477)
              ·
                refine ⟨1684607248471957173800951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17969143983700876520543477 1684607248471957173800951)
                ·
                  refine ⟨2526910872707935760701427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684607248471957173800951 2526910872707935760701427)
                  ·
                    refine ⟨3790366309061903641052141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526910872707935760701427 3790366309061903641052141)
                    ·
                      refine ⟨1421387365898213865394553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790366309061903641052141 1421387365898213865394553)
                      ·
                        rfl

theorem cell23_2768142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2768142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768142 prefixEnd_2768142 := by exact prefixLift 2768142
  have htrace : WordTrace (prefixWord ++ tailWord_2768142) baseStart_2768142 baseEnd_2768142 := by
    simpa [prefixWord, tailWord_2768142, baseEnd_2768142] using wordTrace_append hprefix tailTrace_2768142
  have hstable : (prefixWord ++ tailWord_2768142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768142).length < 2 ^ (prefixWord ++ tailWord_2768142).sum := by decide
  have hdescent : baseEnd_2768142 < baseStart_2768142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768161 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2768161 : Nat := 118140960795 + 2768161 * 2 ^ 59
def prefixEnd_2768161 : Nat := 4983230072969 + 3 ^ 40 * 2768161 * 2
def baseEnd_2768161 : Nat := 1421397122030649291056965

theorem tailTrace_2768161 : CollatzResearch.WordTrace tailWord_2768161 prefixEnd_2768161 1421397122030649291056965 := by
  unfold tailWord_2768161
  simp only [CollatzResearch.WordTrace]
  refine ⟨100963126124432936105224337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67308750749621957403482891 100963126124432936105224337)
  ·
    refine ⟨75722344593324702078918253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100963126124432936105224337 75722344593324702078918253)
    ·
      refine ⟨28395879222496763279594345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75722344593324702078918253 28395879222496763279594345)
      ·
        refine ⟨21296909416872572459695759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28395879222496763279594345 21296909416872572459695759)
        ·
          refine ⟨31945364125308858689543639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21296909416872572459695759 31945364125308858689543639)
          ·
            refine ⟨47918046187963288034315459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31945364125308858689543639 47918046187963288034315459)
            ·
              refine ⟨71877069281944932051473189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47918046187963288034315459 71877069281944932051473189)
              ·
                refine ⟨13476950490364674759651223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71877069281944932051473189 13476950490364674759651223)
                ·
                  refine ⟨20215425735547012139476835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13476950490364674759651223 20215425735547012139476835)
                  ·
                    refine ⟨30323138603320518209215253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20215425735547012139476835 30323138603320518209215253)
                    ·
                      refine ⟨1421397122030649291056965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30323138603320518209215253 1421397122030649291056965)
                      ·
                        rfl

theorem cell23_2768161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2768161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768161 prefixEnd_2768161 := by exact prefixLift 2768161
  have htrace : WordTrace (prefixWord ++ tailWord_2768161) baseStart_2768161 baseEnd_2768161 := by
    simpa [prefixWord, tailWord_2768161, baseEnd_2768161] using wordTrace_append hprefix tailTrace_2768161
  have hstable : (prefixWord ++ tailWord_2768161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768161).length < 2 ^ (prefixWord ++ tailWord_2768161).sum := by decide
  have hdescent : baseEnd_2768161 < baseStart_2768161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768168 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2768168 : Nat := 118140960795 + 2768168 * 2 ^ 59
def prefixEnd_2768168 : Nat := 4983230072969 + 3 ^ 40 * 2768168 * 2
def baseEnd_2768168 : Nat := 1421400716395230763669433

theorem tailTrace_2768168 : CollatzResearch.WordTrace tailWord_2768168 prefixEnd_2768168 1421400716395230763669433 := by
  unfold tailWord_2768168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50481690717703788150364579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67308920956938384200486105 50481690717703788150364579)
  ·
    refine ⟨75722536076555682225546869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50481690717703788150364579 75722536076555682225546869)
    ·
      refine ⟨7098987757177095208645019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75722536076555682225546869 7098987757177095208645019)
      ·
        refine ⟨10648481635765642812967529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098987757177095208645019 10648481635765642812967529)
        ·
          refine ⟨7986361226824232109725647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10648481635765642812967529 7986361226824232109725647)
          ·
            refine ⟨11979541840236348164588471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986361226824232109725647 11979541840236348164588471)
            ·
              refine ⟨17969312760354522246882707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979541840236348164588471 17969312760354522246882707)
              ·
                refine ⟨26953969140531783370324061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17969312760354522246882707 26953969140531783370324061)
                ·
                  refine ⟨10107738427699418763871523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26953969140531783370324061 10107738427699418763871523)
                  ·
                    refine ⟨15161607641549128145807285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10107738427699418763871523 15161607641549128145807285)
                    ·
                      refine ⟨1421400716395230763669433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15161607641549128145807285 1421400716395230763669433)
                      ·
                        rfl

theorem cell23_2768168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2768168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768168 prefixEnd_2768168 := by exact prefixLift 2768168
  have htrace : WordTrace (prefixWord ++ tailWord_2768168) baseStart_2768168 baseEnd_2768168 := by
    simpa [prefixWord, tailWord_2768168, baseEnd_2768168] using wordTrace_append hprefix tailTrace_2768168
  have hstable : (prefixWord ++ tailWord_2768168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768168).length < 2 ^ (prefixWord ++ tailWord_2768168).sum := by decide
  have hdescent : baseEnd_2768168 < baseStart_2768168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768178 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2768178 : Nat := 118140960795 + 2768178 * 2 ^ 59
def prefixEnd_2768178 : Nat := 4983230072969 + 3 ^ 40 * 2768178 * 2
def baseEnd_2768178 : Nat := 1421405851201775724544387

theorem tailTrace_2768178 : CollatzResearch.WordTrace tailWord_2768178 prefixEnd_2768178 1421405851201775724544387 := by
  unfold tailWord_2768178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240936541342837002148297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67309164110247565339062125 25240936541342837002148297)
  ·
    refine ⟨18930702406007127751611223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25240936541342837002148297 18930702406007127751611223)
    ·
      refine ⟨28396053609010691627416835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18930702406007127751611223 28396053609010691627416835)
      ·
        refine ⟨42594080413516037441125253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28396053609010691627416835 42594080413516037441125253)
        ·
          refine ⟨7986390077534257020210985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42594080413516037441125253 7986390077534257020210985)
          ·
            refine ⟨5989792558150692765158239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986390077534257020210985 5989792558150692765158239)
            ·
              refine ⟨8984688837226039147737359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989792558150692765158239 8984688837226039147737359)
              ·
                refine ⟨13477033255839058721606039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8984688837226039147737359 13477033255839058721606039)
                ·
                  refine ⟨20215549883758588082409059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13477033255839058721606039 20215549883758588082409059)
                  ·
                    refine ⟨30323324825637882123613589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20215549883758588082409059 30323324825637882123613589)
                    ·
                      refine ⟨1421405851201775724544387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30323324825637882123613589 1421405851201775724544387)
                      ·
                        rfl

theorem cell23_2768178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2768178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768178 prefixEnd_2768178 := by exact prefixLift 2768178
  have htrace : WordTrace (prefixWord ++ tailWord_2768178) baseStart_2768178 baseEnd_2768178 := by
    simpa [prefixWord, tailWord_2768178, baseEnd_2768178] using wordTrace_append hprefix tailTrace_2768178
  have hstable : (prefixWord ++ tailWord_2768178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768178).length < 2 ^ (prefixWord ++ tailWord_2768178).sum := by decide
  have hdescent : baseEnd_2768178 < baseStart_2768178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768188 : List Nat := [2, 2, 2, 2, 1, 3, 4, 7]
def baseStart_2768188 : Nat := 118140960795 + 2768188 * 2 ^ 59
def prefixEnd_2768188 : Nat := 4983230072969 + 3 ^ 40 * 2768188 * 2
def baseEnd_2768188 : Nat := 52644851333641506867383

theorem tailTrace_2768188 : CollatzResearch.WordTrace tailWord_2768188 prefixEnd_2768188 52644851333641506867383 := by
  unfold tailWord_2768188
  simp only [CollatzResearch.WordTrace]
  refine ⟨50482055447667559858228609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67309407263556746477638145 50482055447667559858228609)
  ·
    refine ⟨37861541585750669893671457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50482055447667559858228609 37861541585750669893671457)
    ·
      refine ⟨28396156189313002420253593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37861541585750669893671457 28396156189313002420253593)
      ·
        refine ⟨21297117141984751815190195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28396156189313002420253593 21297117141984751815190195)
        ·
          refine ⟨31945675712977127722785293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21297117141984751815190195 31945675712977127722785293)
          ·
            refine ⟨11979628392366422896044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31945675712977127722785293 11979628392366422896044485)
            ·
              refine ⟨2246180323568704293008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11979628392366422896044485 2246180323568704293008341)
              ·
                refine ⟨52644851333641506867383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2246180323568704293008341 52644851333641506867383)
                ·
                  rfl

theorem cell23_2768188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 7].length) (baseStart_2768188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768188 prefixEnd_2768188 := by exact prefixLift 2768188
  have htrace : WordTrace (prefixWord ++ tailWord_2768188) baseStart_2768188 baseEnd_2768188 := by
    simpa [prefixWord, tailWord_2768188, baseEnd_2768188] using wordTrace_append hprefix tailTrace_2768188
  have hstable : (prefixWord ++ tailWord_2768188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768188).length < 2 ^ (prefixWord ++ tailWord_2768188).sum := by decide
  have hdescent : baseEnd_2768188 < baseStart_2768188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768199 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_2768199 : Nat := 118140960795 + 2768199 * 2 ^ 59
def prefixEnd_2768199 : Nat := 4983230072969 + 3 ^ 40 * 2768199 * 2
def baseEnd_2768199 : Nat := 1421416634295520142381791

theorem tailTrace_2768199 : CollatzResearch.WordTrace tailWord_2768199 prefixEnd_2768199 1421416634295520142381791 := by
  unfold tailWord_2768199
  simp only [CollatzResearch.WordTrace]
  refine ⟨100964512098295268595107651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67309674732196845730071767 100964512098295268595107651)
  ·
    refine ⟨151446768147442902892661477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100964512098295268595107651 151446768147442902892661477)
    ·
      refine ⟨28396269027645544292374027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151446768147442902892661477 28396269027645544292374027)
      ·
        refine ⟨42594403541468316438561041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28396269027645544292374027 42594403541468316438561041)
        ·
          refine ⟨31945802656101237328920781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42594403541468316438561041 31945802656101237328920781)
          ·
            refine ⟨11979675996037963998345293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31945802656101237328920781 11979675996037963998345293)
            ·
              refine ⟨4492378498514236499379485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11979675996037963998345293 4492378498514236499379485)
              ·
                refine ⟨1684641936942838687267307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4492378498514236499379485 1684641936942838687267307)
                ·
                  refine ⟨2526962905414258030900961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684641936942838687267307 2526962905414258030900961)
                  ·
                    refine ⟨1895222179060693523175721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2526962905414258030900961 1895222179060693523175721)
                    ·
                      refine ⟨1421416634295520142381791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895222179060693523175721 1421416634295520142381791)
                      ·
                        rfl

theorem cell23_2768199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_2768199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768199 prefixEnd_2768199 := by exact prefixLift 2768199
  have htrace : WordTrace (prefixWord ++ tailWord_2768199) baseStart_2768199 baseEnd_2768199 := by
    simpa [prefixWord, tailWord_2768199, baseEnd_2768199] using wordTrace_append hprefix tailTrace_2768199
  have hstable : (prefixWord ++ tailWord_2768199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768199).length < 2 ^ (prefixWord ++ tailWord_2768199).sum := by decide
  have hdescent : baseEnd_2768199 < baseStart_2768199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768211 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_2768211 : Nat := 118140960795 + 2768211 * 2 ^ 59
def prefixEnd_2768211 : Nat := 4983230072969 + 3 ^ 40 * 2768211 * 2
def baseEnd_2768211 : Nat := 1421422796063374095431735

theorem tailTrace_2768211 : CollatzResearch.WordTrace tailWord_2768211 prefixEnd_2768211 1421422796063374095431735 := by
  unfold tailWord_2768211
  simp only [CollatzResearch.WordTrace]
  refine ⟨100964949774251794644544487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67309966516167863096362991 100964949774251794644544487)
  ·
    refine ⟨151447424661377691966816731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100964949774251794644544487 151447424661377691966816731)
    ·
      refine ⟨227171136992066537950225097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151447424661377691966816731 227171136992066537950225097)
      ·
        refine ⟨170378352744049903462668823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227171136992066537950225097 170378352744049903462668823)
        ·
          refine ⟨255567529116074855194003235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170378352744049903462668823 255567529116074855194003235)
          ·
            refine ⟨383351293674112282791004853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255567529116074855194003235 383351293674112282791004853)
            ·
              refine ⟨35939183781948026511656705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383351293674112282791004853 35939183781948026511656705)
              ·
                refine ⟨26954387836461019883742529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35939183781948026511656705 26954387836461019883742529)
                ·
                  refine ⟨20215790877345764912806897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26954387836461019883742529 20215790877345764912806897)
                  ·
                    refine ⟨15161843158009323684605173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20215790877345764912806897 15161843158009323684605173)
                    ·
                      refine ⟨1421422796063374095431735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15161843158009323684605173 1421422796063374095431735)
                      ·
                        rfl

theorem cell23_2768211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_2768211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768211 prefixEnd_2768211 := by exact prefixLift 2768211
  have htrace : WordTrace (prefixWord ++ tailWord_2768211) baseStart_2768211 baseEnd_2768211 := by
    simpa [prefixWord, tailWord_2768211, baseEnd_2768211] using wordTrace_append hprefix tailTrace_2768211
  have hstable : (prefixWord ++ tailWord_2768211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768211).length < 2 ^ (prefixWord ++ tailWord_2768211).sum := by decide
  have hdescent : baseEnd_2768211 < baseStart_2768211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768215 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_2768215 : Nat := 118140960795 + 2768215 * 2 ^ 59
def prefixEnd_2768215 : Nat := 4983230072969 + 3 ^ 40 * 2768215 * 2
def baseEnd_2768215 : Nat := 1421424849985992079781717

theorem tailTrace_2768215 : CollatzResearch.WordTrace tailWord_2768215 prefixEnd_2768215 1421424849985992079781717 := by
  unfold tailWord_2768215
  simp only [CollatzResearch.WordTrace]
  refine ⟨100965095666237303327690099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67310063777491535551793399 100965095666237303327690099)
  ·
    refine ⟨151447643499355954991535149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100965095666237303327690099 151447643499355954991535149)
    ·
      refine ⟨56792866312258483121825681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151447643499355954991535149 56792866312258483121825681)
      ·
        refine ⟨42594649734193862341369261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56792866312258483121825681 42594649734193862341369261)
        ·
          refine ⟨15972993650322698378013473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42594649734193862341369261 15972993650322698378013473)
          ·
            refine ⟨11979745237742023783510105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15972993650322698378013473 11979745237742023783510105)
            ·
              refine ⟨8984808928306517837632579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11979745237742023783510105 8984808928306517837632579)
              ·
                refine ⟨13477213392459776756448869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8984808928306517837632579 13477213392459776756448869)
                ·
                  refine ⟨2526977511086208141834163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13477213392459776756448869 2526977511086208141834163)
                  ·
                    refine ⟨3790466266629312212751245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526977511086208141834163 3790466266629312212751245)
                    ·
                      refine ⟨1421424849985992079781717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790466266629312212751245 1421424849985992079781717)
                      ·
                        rfl

theorem cell23_2768215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_2768215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768215 prefixEnd_2768215 := by exact prefixLift 2768215
  have htrace : WordTrace (prefixWord ++ tailWord_2768215) baseStart_2768215 baseEnd_2768215 := by
    simpa [prefixWord, tailWord_2768215, baseEnd_2768215] using wordTrace_append hprefix tailTrace_2768215
  have hstable : (prefixWord ++ tailWord_2768215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768215).length < 2 ^ (prefixWord ++ tailWord_2768215).sum := by decide
  have hdescent : baseEnd_2768215 < baseStart_2768215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768259 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 1, 3, 2]
def baseStart_2768259 : Nat := 118140960795 + 2768259 * 2 ^ 59
def prefixEnd_2768259 : Nat := 4983230072969 + 3 ^ 40 * 2768259 * 2
def baseEnd_2768259 : Nat := 1421447443134789907631515

theorem tailTrace_2768259 : CollatzResearch.WordTrace tailWord_2768259 prefixEnd_2768259 1421447443134789907631515 := by
  unfold tailWord_2768259
  simp only [CollatzResearch.WordTrace]
  refine ⟨100966700478077898842291831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67311133652051932561527887 100966700478077898842291831)
  ·
    refine ⟨151450050717116848263437747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100966700478077898842291831 151450050717116848263437747)
    ·
      refine ⟨227175076075675272395156621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151450050717116848263437747 227175076075675272395156621)
      ·
        refine ⟨85190653528378227148183733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227175076075675272395156621 85190653528378227148183733)
        ·
          refine ⟨7986623768285458795142225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85190653528378227148183733 7986623768285458795142225)
          ·
            refine ⟨5989967826214094096356669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986623768285458795142225 5989967826214094096356669)
            ·
              refine ⟨2246237934830285286133751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989967826214094096356669 2246237934830285286133751)
              ·
                refine ⟨3369356902245427929200627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246237934830285286133751 3369356902245427929200627)
                ·
                  refine ⟨5054035353368141893800941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369356902245427929200627 5054035353368141893800941)
                  ·
                    refine ⟨1895263257513053210175353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5054035353368141893800941 1895263257513053210175353)
                    ·
                      refine ⟨1421447443134789907631515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895263257513053210175353 1421447443134789907631515)
                      ·
                        rfl

theorem cell23_2768259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_2768259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768259 prefixEnd_2768259 := by exact prefixLift 2768259
  have htrace : WordTrace (prefixWord ++ tailWord_2768259) baseStart_2768259 baseEnd_2768259 := by
    simpa [prefixWord, tailWord_2768259, baseEnd_2768259] using wordTrace_append hprefix tailTrace_2768259
  have hstable : (prefixWord ++ tailWord_2768259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768259).length < 2 ^ (prefixWord ++ tailWord_2768259).sum := by decide
  have hdescent : baseEnd_2768259 < baseStart_2768259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768268 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2768268 : Nat := 118140960795 + 2768268 * 2 ^ 59
def prefixEnd_2768268 : Nat := 4983230072969 + 3 ^ 40 * 2768268 * 2
def baseEnd_2768268 : Nat := 1421452064460680372418973

theorem tailTrace_2768268 : CollatzResearch.WordTrace tailWord_2768268 prefixEnd_2768268 1421452064460680372418973 := by
  unfold tailWord_2768268
  simp only [CollatzResearch.WordTrace]
  refine ⟨50483514367522646689684729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67311352490030195586246305 50483514367522646689684729)
  ·
    refine ⟨37862635775641985017263547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50483514367522646689684729 37862635775641985017263547)
    ·
      refine ⟨56793953663462977525895321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37862635775641985017263547 56793953663462977525895321)
      ·
        refine ⟨42595465247597233144421491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56793953663462977525895321 42595465247597233144421491)
        ·
          refine ⟨63893197871395849716632237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42595465247597233144421491 63893197871395849716632237)
          ·
            refine ⟨23959949201773443643737089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63893197871395849716632237 23959949201773443643737089)
            ·
              refine ⟨17969961901330082732802817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23959949201773443643737089 17969961901330082732802817)
              ·
                refine ⟨13477471425997562049602113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17969961901330082732802817 13477471425997562049602113)
                ·
                  refine ⟨10108103569498171537201585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13477471425997562049602113 10108103569498171537201585)
                  ·
                    refine ⟨7581077677123628652901189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10108103569498171537201585 7581077677123628652901189)
                    ·
                      refine ⟨1421452064460680372418973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7581077677123628652901189 1421452064460680372418973)
                      ·
                        rfl

theorem cell23_2768268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2768268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768268 prefixEnd_2768268 := by exact prefixLift 2768268
  have htrace : WordTrace (prefixWord ++ tailWord_2768268) baseStart_2768268 baseEnd_2768268 := by
    simpa [prefixWord, tailWord_2768268, baseEnd_2768268] using wordTrace_append hprefix tailTrace_2768268
  have hstable : (prefixWord ++ tailWord_2768268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768268).length < 2 ^ (prefixWord ++ tailWord_2768268).sum := by decide
  have hdescent : baseEnd_2768268 < baseStart_2768268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768285 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2768285 : Nat := 118140960795 + 2768285 * 2 ^ 59
def prefixEnd_2768285 : Nat := 4983230072969 + 3 ^ 40 * 2768285 * 2
def baseEnd_2768285 : Nat := 1421460793631806805906395

theorem tailTrace_2768285 : CollatzResearch.WordTrace tailWord_2768285 prefixEnd_2768285 1421460793631806805906395 := by
  unfold tailWord_2768285
  simp only [CollatzResearch.WordTrace]
  refine ⟨100967648775983705282738309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67311765850655803521825539 100967648775983705282738309)
  ·
    refine ⟨18931434145496944740513433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100967648775983705282738309 18931434145496944740513433)
    ·
      refine ⟨14198575609122708555385075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18931434145496944740513433 14198575609122708555385075)
      ·
        refine ⟨21297863413684062833077613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14198575609122708555385075 21297863413684062833077613)
        ·
          refine ⟨7986698780131523562404105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21297863413684062833077613 7986698780131523562404105)
          ·
            refine ⟨5990024085098642671803079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986698780131523562404105 5990024085098642671803079)
            ·
              refine ⟨8985036127647964007704619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990024085098642671803079 8985036127647964007704619)
              ·
                refine ⟨13477554191471946011556929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985036127647964007704619 13477554191471946011556929)
                ·
                  refine ⟨10108165643603959508667697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13477554191471946011556929 10108165643603959508667697)
                  ·
                    refine ⟨7581124232702969631500773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10108165643603959508667697 7581124232702969631500773)
                    ·
                      refine ⟨1421460793631806805906395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7581124232702969631500773 1421460793631806805906395)
                      ·
                        rfl

theorem cell23_2768285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2768285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768285 prefixEnd_2768285 := by exact prefixLift 2768285
  have htrace : WordTrace (prefixWord ++ tailWord_2768285) baseStart_2768285 baseEnd_2768285 := by
    simpa [prefixWord, tailWord_2768285, baseEnd_2768285] using wordTrace_append hprefix tailTrace_2768285
  have hstable : (prefixWord ++ tailWord_2768285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768285).length < 2 ^ (prefixWord ++ tailWord_2768285).sum := by decide
  have hdescent : baseEnd_2768285 < baseStart_2768285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768368 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 8]
def baseStart_2768368 : Nat := 118140960795 + 2768368 * 2 ^ 59
def prefixEnd_2768368 : Nat := 4983230072969 + 3 ^ 40 * 2768368 * 2
def baseEnd_2768368 : Nat := 157944823614014442352057

theorem tailTrace_2768368 : CollatzResearch.WordTrace tailWord_2768368 prefixEnd_2768368 157944823614014442352057 := by
  unfold tailWord_2768368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50485338017341505229004879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67313784023122006972006505 50485338017341505229004879)
  ·
    refine ⟨75728007026012257843507319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50485338017341505229004879 75728007026012257843507319)
    ·
      refine ⟨113592010539018386765260979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75728007026012257843507319 113592010539018386765260979)
      ·
        refine ⟨170388015808527580147891469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113592010539018386765260979 170388015808527580147891469)
        ·
          refine ⟨63895505928197842555459301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170388015808527580147891469 63895505928197842555459301)
          ·
            refine ⟨11980407361537095479148619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63895505928197842555459301 11980407361537095479148619)
            ·
              refine ⟨17970611042305643218722929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980407361537095479148619 17970611042305643218722929)
              ·
                refine ⟨13477958281729232414042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17970611042305643218722929 13477958281729232414042197)
                ·
                  refine ⟨157944823614014442352057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13477958281729232414042197 157944823614014442352057)
                  ·
                    rfl

theorem cell23_2768368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_2768368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768368 prefixEnd_2768368 := by exact prefixLift 2768368
  have htrace : WordTrace (prefixWord ++ tailWord_2768368) baseStart_2768368 baseEnd_2768368 := by
    simpa [prefixWord, tailWord_2768368, baseEnd_2768368] using wordTrace_append hprefix tailTrace_2768368
  have hstable : (prefixWord ++ tailWord_2768368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768368).length < 2 ^ (prefixWord ++ tailWord_2768368).sum := by decide
  have hdescent : baseEnd_2768368 < baseStart_2768368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768412 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2768412 : Nat := 118140960795 + 2768412 * 2 ^ 59
def prefixEnd_2768412 : Nat := 4983230072969 + 3 ^ 40 * 2768412 * 2
def baseEnd_2768412 : Nat := 1421526005674927809018311

theorem tailTrace_2768412 : CollatzResearch.WordTrace tailWord_2768412 prefixEnd_2768412 1421526005674927809018311 := by
  unfold tailWord_2768412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50486140423261802986305745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67314853897682403981740993 50486140423261802986305745)
  ·
    refine ⟨37864605317446352239729309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50486140423261802986305745 37864605317446352239729309)
    ·
      refine ⟨14199226994042382089898491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37864605317446352239729309 14199226994042382089898491)
      ·
        refine ⟨21298840491063573134847737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14199226994042382089898491 21298840491063573134847737)
        ·
          refine ⟨15974130368297679851135803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21298840491063573134847737 15974130368297679851135803)
          ·
            refine ⟨23961195552446519776703705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15974130368297679851135803 23961195552446519776703705)
            ·
              refine ⟨17970896664334889832527779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23961195552446519776703705 17970896664334889832527779)
              ·
                refine ⟨26956344996502334748791669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17970896664334889832527779 26956344996502334748791669)
                ·
                  refine ⟨2527157343422093882699219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26956344996502334748791669 2527157343422093882699219)
                  ·
                    refine ⟨3790736015133140824048829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527157343422093882699219 3790736015133140824048829)
                    ·
                      refine ⟨1421526005674927809018311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790736015133140824048829 1421526005674927809018311)
                      ·
                        rfl

theorem cell23_2768412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2768412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768412 prefixEnd_2768412 := by exact prefixLift 2768412
  have htrace : WordTrace (prefixWord ++ tailWord_2768412) baseStart_2768412 baseEnd_2768412 := by
    simpa [prefixWord, tailWord_2768412, baseEnd_2768412] using wordTrace_append hprefix tailTrace_2768412
  have hstable : (prefixWord ++ tailWord_2768412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768412).length < 2 ^ (prefixWord ++ tailWord_2768412).sum := by decide
  have hdescent : baseEnd_2768412 < baseStart_2768412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768472 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2768472 : Nat := 118140960795 + 2768472 * 2 ^ 59
def prefixEnd_2768472 : Nat := 4983230072969 + 3 ^ 40 * 2768472 * 2
def baseEnd_2768472 : Nat := 1421556814514197574268035

theorem tailTrace_2768472 : CollatzResearch.WordTrace tailWord_2768472 prefixEnd_2768472 1421556814514197574268035 := by
  unfold tailWord_2768472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50487234613153118109897835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67316312817537490813197113 50487234613153118109897835)
  ·
    refine ⟨75730851919729677164846753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50487234613153118109897835 75730851919729677164846753)
    ·
      refine ⟨56798138939797257873635065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75730851919729677164846753 56798138939797257873635065)
      ·
        refine ⟨42598604204847943405226299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56798138939797257873635065 42598604204847943405226299)
        ·
          refine ⟨63897906307271915107839449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42598604204847943405226299 63897906307271915107839449)
          ·
            refine ⟨47923429730453936330879587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63897906307271915107839449 47923429730453936330879587)
            ·
              refine ⟨71885144595680904496319381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47923429730453936330879587 71885144595680904496319381)
              ·
                refine ⟨3369616152922542398264971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71885144595680904496319381 3369616152922542398264971)
                ·
                  refine ⟨5054424229383813597397457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369616152922542398264971 5054424229383813597397457)
                  ·
                    refine ⟨3790818172037860198048093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5054424229383813597397457 3790818172037860198048093)
                    ·
                      refine ⟨1421556814514197574268035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790818172037860198048093 1421556814514197574268035)
                      ·
                        rfl

theorem cell23_2768472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2768472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768472 prefixEnd_2768472 := by exact prefixLift 2768472
  have htrace : WordTrace (prefixWord ++ tailWord_2768472) baseStart_2768472 baseEnd_2768472 := by
    simpa [prefixWord, tailWord_2768472, baseEnd_2768472] using wordTrace_append hprefix tailTrace_2768472
  have hstable : (prefixWord ++ tailWord_2768472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768472).length < 2 ^ (prefixWord ++ tailWord_2768472).sum := by decide
  have hdescent : baseEnd_2768472 < baseStart_2768472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768489 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 1, 2, 3]
def baseStart_2768489 : Nat := 118140960795 + 2768489 * 2 ^ 59
def prefixEnd_2768489 : Nat := 4983230072969 + 3 ^ 40 * 2768489 * 2
def baseEnd_2768489 : Nat := 1421565543685324007755457

theorem tailTrace_2768489 : CollatzResearch.WordTrace tailWord_2768489 prefixEnd_2768489 1421565543685324007755457 := by
  unfold tailWord_2768489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100975089267244648123164521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67316726178163098748776347 100975089267244648123164521)
  ·
    refine ⟨75731316950433486092373391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100975089267244648123164521 75731316950433486092373391)
    ·
      refine ⟨113596975425650229138560087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75731316950433486092373391 113596975425650229138560087)
      ·
        refine ⟨170395463138475343707840131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113596975425650229138560087 170395463138475343707840131)
        ·
          refine ⟨255593194707713015561760197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170395463138475343707840131 255593194707713015561760197)
          ·
            refine ⟨47923724007696190417830037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255593194707713015561760197 47923724007696190417830037)
            ·
              refine ⟨2246424562860758925835783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47923724007696190417830037 2246424562860758925835783)
              ·
                refine ⟨3369636844291138388753675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246424562860758925835783 3369636844291138388753675)
                ·
                  refine ⟨5054455266436707583130513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369636844291138388753675 5054455266436707583130513)
                  ·
                    refine ⟨3790841449827530687347885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5054455266436707583130513 3790841449827530687347885)
                    ·
                      refine ⟨1421565543685324007755457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790841449827530687347885 1421565543685324007755457)
                      ·
                        rfl

theorem cell23_2768489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 2, 3].length) (baseStart_2768489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768489 prefixEnd_2768489 := by exact prefixLift 2768489
  have htrace : WordTrace (prefixWord ++ tailWord_2768489) baseStart_2768489 baseEnd_2768489 := by
    simpa [prefixWord, tailWord_2768489, baseEnd_2768489] using wordTrace_append hprefix tailTrace_2768489
  have hstable : (prefixWord ++ tailWord_2768489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768489).length < 2 ^ (prefixWord ++ tailWord_2768489).sum := by decide
  have hdescent : baseEnd_2768489 < baseStart_2768489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768516 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2768516 : Nat := 118140960795 + 2768516 * 2 ^ 59
def prefixEnd_2768516 : Nat := 4983230072969 + 3 ^ 40 * 2768516 * 2
def baseEnd_2768516 : Nat := 1421579407662995402117833

theorem tailTrace_2768516 : CollatzResearch.WordTrace tailWord_2768516 prefixEnd_2768516 1421579407662995402117833 := by
  unfold tailWord_2768516
  simp only [CollatzResearch.WordTrace]
  refine ⟨50488037019073415867198701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67317382692097887822931601 50488037019073415867198701)
  ·
    refine ⟨18933013882152530950199513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50488037019073415867198701 18933013882152530950199513)
    ·
      refine ⟨14199760411614398212649635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18933013882152530950199513 14199760411614398212649635)
      ·
        refine ⟨21299640617421597318974453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14199760411614398212649635 21299640617421597318974453)
        ·
          refine ⟨1996841307883274748653855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21299640617421597318974453 1996841307883274748653855)
          ·
            refine ⟨2995261961824912122980783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996841307883274748653855 2995261961824912122980783)
            ·
              refine ⟨4492892942737368184471175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995261961824912122980783 4492892942737368184471175)
              ·
                refine ⟨6739339414106052276706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492892942737368184471175 6739339414106052276706763)
                ·
                  refine ⟨10109009121159078415060145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6739339414106052276706763 10109009121159078415060145)
                  ·
                    refine ⟨7581756840869308811295109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10109009121159078415060145 7581756840869308811295109)
                    ·
                      refine ⟨1421579407662995402117833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7581756840869308811295109 1421579407662995402117833)
                      ·
                        rfl

theorem cell23_2768516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2768516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768516 prefixEnd_2768516 := by exact prefixLift 2768516
  have htrace : WordTrace (prefixWord ++ tailWord_2768516) baseStart_2768516 baseEnd_2768516 := by
    simpa [prefixWord, tailWord_2768516, baseEnd_2768516] using wordTrace_append hprefix tailTrace_2768516
  have hstable : (prefixWord ++ tailWord_2768516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768516).length < 2 ^ (prefixWord ++ tailWord_2768516).sum := by decide
  have hdescent : baseEnd_2768516 < baseStart_2768516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768519 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2768519 : Nat := 118140960795 + 2768519 * 2 ^ 59
def prefixEnd_2768519 : Nat := 4983230072969 + 3 ^ 40 * 2768519 * 2
def baseEnd_2768519 : Nat := 1421580948104958890380319

theorem tailTrace_2768519 : CollatzResearch.WordTrace tailWord_2768519 prefixEnd_2768519 1421580948104958890380319 := by
  unfold tailWord_2768519
  simp only [CollatzResearch.WordTrace]
  refine ⟨100976183457135963246756611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67317455638090642164504407 100976183457135963246756611)
  ·
    refine ⟨151464275185703944870134917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100976183457135963246756611 151464275185703944870134917)
    ·
      refine ⟨28399551597319489663150297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151464275185703944870134917 28399551597319489663150297)
      ·
        refine ⟨21299663697989617247362723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28399551597319489663150297 21299663697989617247362723)
        ·
          refine ⟨31949495546984425871044085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21299663697989617247362723 31949495546984425871044085)
          ·
            refine ⟨2995265207529789925410383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31949495546984425871044085 2995265207529789925410383)
            ·
              refine ⟨4492897811294684888115575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995265207529789925410383 4492897811294684888115575)
              ·
                refine ⟨6739346716942027332173363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492897811294684888115575 6739346716942027332173363)
                ·
                  refine ⟨10109020075413040998260045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6739346716942027332173363 10109020075413040998260045)
                  ·
                    refine ⟨3790882528279890374347517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10109020075413040998260045 3790882528279890374347517)
                    ·
                      refine ⟨1421580948104958890380319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3790882528279890374347517 1421580948104958890380319)
                      ·
                        rfl

theorem cell23_2768519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2768519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768519 prefixEnd_2768519 := by exact prefixLift 2768519
  have htrace : WordTrace (prefixWord ++ tailWord_2768519) baseStart_2768519 baseEnd_2768519 := by
    simpa [prefixWord, tailWord_2768519, baseEnd_2768519] using wordTrace_append hprefix tailTrace_2768519
  have hstable : (prefixWord ++ tailWord_2768519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768519).length < 2 ^ (prefixWord ++ tailWord_2768519).sum := by decide
  have hdescent : baseEnd_2768519 < baseStart_2768519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768559 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 4, 2, 2]
def baseStart_2768559 : Nat := 118140960795 + 2768559 * 2 ^ 59
def prefixEnd_2768559 : Nat := 4983230072969 + 3 ^ 40 * 2768559 * 2
def baseEnd_2768559 : Nat := 1421601487331138733880135

theorem tailTrace_2768559 : CollatzResearch.WordTrace tailWord_2768559 prefixEnd_2768559 1421601487331138733880135 := by
  unfold tailWord_2768559
  simp only [CollatzResearch.WordTrace]
  refine ⟨100977642376991050078212731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67318428251327366718808487 100977642376991050078212731)
  ·
    refine ⟨151466463565486575117319097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100977642376991050078212731 151466463565486575117319097)
    ·
      refine ⟨113599847674114931337989323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151466463565486575117319097 113599847674114931337989323)
      ·
        refine ⟨170399771511172397006983985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113599847674114931337989323 170399771511172397006983985)
        ·
          refine ⟨127799828633379297755237989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170399771511172397006983985 127799828633379297755237989)
          ·
            refine ⟨23962467868758618329107123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127799828633379297755237989 23962467868758618329107123)
            ·
              refine ⟨35943701803137927493660685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23962467868758618329107123 35943701803137927493660685)
              ·
                refine ⟨13478888176176722810122757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35943701803137927493660685 13478888176176722810122757)
                ·
                  refine ⟨2527291533033135526898017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13478888176176722810122757 2527291533033135526898017)
                  ·
                    refine ⟨1895468649774851645173513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2527291533033135526898017 1895468649774851645173513)
                    ·
                      refine ⟨1421601487331138733880135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895468649774851645173513 1421601487331138733880135)
                      ·
                        rfl

theorem cell23_2768559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2, 2].length) (baseStart_2768559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768559 prefixEnd_2768559 := by exact prefixLift 2768559
  have htrace : WordTrace (prefixWord ++ tailWord_2768559) baseStart_2768559 baseEnd_2768559 := by
    simpa [prefixWord, tailWord_2768559, baseEnd_2768559] using wordTrace_append hprefix tailTrace_2768559
  have hstable : (prefixWord ++ tailWord_2768559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768559).length < 2 ^ (prefixWord ++ tailWord_2768559).sum := by decide
  have hdescent : baseEnd_2768559 < baseStart_2768559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768576 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2]
def baseStart_2768576 : Nat := 118140960795 + 2768576 * 2 ^ 59
def prefixEnd_2768576 : Nat := 4983230072969 + 3 ^ 40 * 2768576 * 2
def baseEnd_2768576 : Nat := 1421610216502265167367557

theorem tailTrace_2768576 : CollatzResearch.WordTrace tailWord_2768576 prefixEnd_2768576 1421610216502265167367557 := by
  unfold tailWord_2768576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489131208964730990790791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67318841611952974654387721 50489131208964730990790791)
  ·
    refine ⟨75733696813447096486186187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50489131208964730990790791 75733696813447096486186187)
    ·
      refine ⟨113600545220170644729279281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75733696813447096486186187 113600545220170644729279281)
      ·
        refine ⟨85200408915127983546959461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113600545220170644729279281 85200408915127983546959461)
        ·
          refine ⟨15975076671586496915054899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85200408915127983546959461 15975076671586496915054899)
          ·
            refine ⟨23962615007379745372582349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975076671586496915054899 23962615007379745372582349)
            ·
              refine ⟨8985980627767404514718381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23962615007379745372582349 8985980627767404514718381)
              ·
                refine ⟨3369742735412776693019393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8985980627767404514718381 3369742735412776693019393)
                ·
                  refine ⟨2527307051559582519764545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369742735412776693019393 2527307051559582519764545)
                  ·
                    refine ⟨1895480288669686889823409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2527307051559582519764545 1895480288669686889823409)
                    ·
                      refine ⟨1421610216502265167367557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895480288669686889823409 1421610216502265167367557)
                      ·
                        rfl

theorem cell23_2768576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_2768576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768576 prefixEnd_2768576 := by exact prefixLift 2768576
  have htrace : WordTrace (prefixWord ++ tailWord_2768576) baseStart_2768576 baseEnd_2768576 := by
    simpa [prefixWord, tailWord_2768576, baseEnd_2768576] using wordTrace_append hprefix tailTrace_2768576
  have hstable : (prefixWord ++ tailWord_2768576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768576).length < 2 ^ (prefixWord ++ tailWord_2768576).sum := by decide
  have hdescent : baseEnd_2768576 < baseStart_2768576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768612 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2768612 : Nat := 118140960795 + 2768612 * 2 ^ 59
def prefixEnd_2768612 : Nat := 4983230072969 + 3 ^ 40 * 2768612 * 2
def baseEnd_2768612 : Nat := 473876233935275675505797

theorem tailTrace_2768612 : CollatzResearch.WordTrace tailWord_2768612 prefixEnd_2768612 473876233935275675505797 := by
  unfold tailWord_2768612
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489787722899520064946045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67319716963866026753261393 50489787722899520064946045)
  ·
    refine ⟨18933670396087320024354767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50489787722899520064946045 18933670396087320024354767)
    ·
      refine ⟨28400505594130980036532151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18933670396087320024354767 28400505594130980036532151)
      ·
        refine ⟨42600758391196470054798227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28400505594130980036532151 42600758391196470054798227)
        ·
          refine ⟨63901137586794705082197341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42600758391196470054798227 63901137586794705082197341)
          ·
            refine ⟨23962926595048014405824003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63901137586794705082197341 23962926595048014405824003)
            ·
              refine ⟨35944389892572021608736005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23962926595048014405824003 35944389892572021608736005)
              ·
                refine ⟨6739573104857254051638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35944389892572021608736005 6739573104857254051638001)
                ·
                  refine ⟨5054679828642940538728501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6739573104857254051638001 5054679828642940538728501)
                  ·
                    refine ⟨473876233935275675505797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5054679828642940538728501 473876233935275675505797)
                    ·
                      rfl

theorem cell23_2768612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2768612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768612 prefixEnd_2768612 := by exact prefixLift 2768612
  have htrace : WordTrace (prefixWord ++ tailWord_2768612) baseStart_2768612 baseEnd_2768612 := by
    simpa [prefixWord, tailWord_2768612, baseEnd_2768612] using wordTrace_append hprefix tailTrace_2768612
  have hstable : (prefixWord ++ tailWord_2768612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768612).length < 2 ^ (prefixWord ++ tailWord_2768612).sum := by decide
  have hdescent : baseEnd_2768612 < baseStart_2768612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768616 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 5]
def baseStart_2768616 : Nat := 118140960795 + 2768616 * 2 ^ 59
def prefixEnd_2768616 : Nat := 4983230072969 + 3 ^ 40 * 2768616 * 2
def baseEnd_2768616 : Nat := 157958972858716112318597

theorem tailTrace_2768616 : CollatzResearch.WordTrace tailWord_2768616 prefixEnd_2768616 157958972858716112318597 := by
  unfold tailWord_2768616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489860668892274406518851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67319814225189699208691801 50489860668892274406518851)
  ·
    refine ⟨75734791003338411609778277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50489860668892274406518851 75734791003338411609778277)
    ·
      refine ⟨14200273313125952176833427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75734791003338411609778277 14200273313125952176833427)
      ·
        refine ⟨21300409969688928265250141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14200273313125952176833427 21300409969688928265250141)
        ·
          refine ⟨7987653738633348099468803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21300409969688928265250141 7987653738633348099468803)
          ·
            refine ⟨11981480607950022149203205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7987653738633348099468803 11981480607950022149203205)
            ·
              refine ⟨2246527613990629152975601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11981480607950022149203205 2246527613990629152975601)
              ·
                refine ⟨1684895710492971864731701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246527613990629152975601 1684895710492971864731701)
                ·
                  refine ⟨157958972858716112318597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1684895710492971864731701 157958972858716112318597)
                  ·
                    rfl

theorem cell23_2768616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 5].length) (baseStart_2768616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768616 prefixEnd_2768616 := by exact prefixLift 2768616
  have htrace : WordTrace (prefixWord ++ tailWord_2768616) baseStart_2768616 baseEnd_2768616 := by
    simpa [prefixWord, tailWord_2768616, baseEnd_2768616] using wordTrace_append hprefix tailTrace_2768616
  have hstable : (prefixWord ++ tailWord_2768616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768616).length < 2 ^ (prefixWord ++ tailWord_2768616).sum := by decide
  have hdescent : baseEnd_2768616 < baseStart_2768616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768622 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2768622 : Nat := 118140960795 + 2768622 * 2 ^ 59
def prefixEnd_2768622 : Nat := 4983230072969 + 3 ^ 40 * 2768622 * 2
def baseEnd_2768622 : Nat := 1421633836612371987392345

theorem tailTrace_2768622 : CollatzResearch.WordTrace tailWord_2768622 prefixEnd_2768622 1421633836612371987392345 := by
  unfold tailWord_2768622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622492521970351479719515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67319960117175207891837413 12622492521970351479719515)
  ·
    refine ⟨18933738782955527219579273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622492521970351479719515 18933738782955527219579273)
    ·
      refine ⟨14200304087216645414684455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18933738782955527219579273 14200304087216645414684455)
      ·
        refine ⟨21300456130824968122026683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14200304087216645414684455 21300456130824968122026683)
        ·
          refine ⟨31950684196237452183040025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21300456130824968122026683 31950684196237452183040025)
          ·
            refine ⟨23963013147178089137280019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31950684196237452183040025 23963013147178089137280019)
            ·
              refine ⟨35944519720767133705920029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23963013147178089137280019 35944519720767133705920029)
              ·
                refine ⟨13479194895287675139720011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35944519720767133705920029 13479194895287675139720011)
                ·
                  refine ⟨20218792342931512709580017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13479194895287675139720011 20218792342931512709580017)
                  ·
                    refine ⟨15164094257198634532185013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20218792342931512709580017 15164094257198634532185013)
                    ·
                      refine ⟨1421633836612371987392345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15164094257198634532185013 1421633836612371987392345)
                      ·
                        rfl

theorem cell23_2768622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2768622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768622 prefixEnd_2768622 := by exact prefixLift 2768622
  have htrace : WordTrace (prefixWord ++ tailWord_2768622) baseStart_2768622 baseEnd_2768622 := by
    simpa [prefixWord, tailWord_2768622, baseEnd_2768622] using wordTrace_append hprefix tailTrace_2768622
  have hstable : (prefixWord ++ tailWord_2768622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768622).length < 2 ^ (prefixWord ++ tailWord_2768622).sum := by decide
  have hdescent : baseEnd_2768622 < baseStart_2768622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768672 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 8]
def baseStart_2768672 : Nat := 118140960795 + 2768672 * 2 ^ 59
def prefixEnd_2768672 : Nat := 4983230072969 + 3 ^ 40 * 2768672 * 2
def baseEnd_2768672 : Nat := 157962167849455199085235

theorem tailTrace_2768672 : CollatzResearch.WordTrace tailWord_2768672 prefixEnd_2768672 157962167849455199085235 := by
  unfold tailWord_2768672
  simp only [CollatzResearch.WordTrace]
  refine ⟨50490881912790835188538135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67321175883721113584717513 50490881912790835188538135)
  ·
    refine ⟨75736322869186252782807203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50490881912790835188538135 75736322869186252782807203)
    ·
      refine ⟨113604484303779379174210805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75736322869186252782807203 113604484303779379174210805)
      ·
        refine ⟨10650420403479316797582263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113604484303779379174210805 10650420403479316797582263)
        ·
          refine ⟨15975630605218975196373395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650420403479316797582263 15975630605218975196373395)
          ·
            refine ⟨23963445907828462794560093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975630605218975196373395 23963445907828462794560093)
            ·
              refine ⟨8986292215435673547960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23963445907828462794560093 8986292215435673547960035)
              ·
                refine ⟨13479438323153510321940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8986292215435673547960035 13479438323153510321940053)
                ·
                  refine ⟨157962167849455199085235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13479438323153510321940053 157962167849455199085235)
                  ·
                    rfl

theorem cell23_2768672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_2768672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768672 prefixEnd_2768672 := by exact prefixLift 2768672
  have htrace : WordTrace (prefixWord ++ tailWord_2768672) baseStart_2768672 baseEnd_2768672 := by
    simpa [prefixWord, tailWord_2768672, baseEnd_2768672] using wordTrace_append hprefix tailTrace_2768672
  have hstable : (prefixWord ++ tailWord_2768672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768672).length < 2 ^ (prefixWord ++ tailWord_2768672).sum := by decide
  have hdescent : baseEnd_2768672 < baseStart_2768672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768676 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_2768676 : Nat := 118140960795 + 2768676 * 2 ^ 59
def prefixEnd_2768676 : Nat := 4983230072969 + 3 ^ 40 * 2768676 * 2
def baseEnd_2768676 : Nat := 473887188189238258705699

theorem tailTrace_2768676 : CollatzResearch.WordTrace tailWord_2768676 prefixEnd_2768676 473887188189238258705699 := by
  unfold tailWord_2768676
  simp only [CollatzResearch.WordTrace]
  refine ⟨50490954858783589530110941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67321273145044786040147921 50490954858783589530110941)
  ·
    refine ⟨18934108072043846073791603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50490954858783589530110941 18934108072043846073791603)
    ·
      refine ⟨28401162108065769110687405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934108072043846073791603 28401162108065769110687405)
      ·
        refine ⟨10650435790524663416507777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28401162108065769110687405 10650435790524663416507777)
        ·
          refine ⟨7987826842893497562380833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10650435790524663416507777 7987826842893497562380833)
          ·
            refine ⟨5990870132170123171785625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7987826842893497562380833 5990870132170123171785625)
            ·
              refine ⟨4493152599127592378839219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990870132170123171785625 4493152599127592378839219)
              ·
                refine ⟨6739728898691388568258829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493152599127592378839219 6739728898691388568258829)
                ·
                  refine ⟨2527398337009270713097061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6739728898691388568258829 2527398337009270713097061)
                  ·
                    refine ⟨473887188189238258705699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527398337009270713097061 473887188189238258705699)
                    ·
                      rfl

theorem cell23_2768676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_2768676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768676 prefixEnd_2768676 := by exact prefixLift 2768676
  have htrace : WordTrace (prefixWord ++ tailWord_2768676) baseStart_2768676 baseEnd_2768676 := by
    simpa [prefixWord, tailWord_2768676, baseEnd_2768676] using wordTrace_append hprefix tailTrace_2768676
  have hstable : (prefixWord ++ tailWord_2768676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768676).length < 2 ^ (prefixWord ++ tailWord_2768676).sum := by decide
  have hdescent : baseEnd_2768676 < baseStart_2768676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768709 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_2768709 : Nat := 118140960795 + 2768709 * 2 ^ 59
def prefixEnd_2768709 : Nat := 4983230072969 + 3 ^ 40 * 2768709 * 2
def baseEnd_2768709 : Nat := 1421678509429313147004445

theorem tailTrace_2768709 : CollatzResearch.WordTrace tailWord_2768709 prefixEnd_2768709 1421678509429313147004445 := by
  unfold tailWord_2768709
  simp only [CollatzResearch.WordTrace]
  refine ⟨100983113326447625696173181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67322075550965083797448787 100983113326447625696173181)
  ·
    refine ⟨37868667497417859636064943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100983113326447625696173181 37868667497417859636064943)
    ·
      refine ⟨56803001246126789454097415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37868667497417859636064943 56803001246126789454097415)
      ·
        refine ⟨85204501869190184181146123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56803001246126789454097415 85204501869190184181146123)
        ·
          refine ⟨127806752803785276271719185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85204501869190184181146123 127806752803785276271719185)
          ·
            refine ⟨95855064602838957203789389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127806752803785276271719185 95855064602838957203789389)
            ·
              refine ⟨35945649226064608951421021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95855064602838957203789389 35945649226064608951421021)
              ·
                refine ⟨13479618459774228356782883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35945649226064608951421021 13479618459774228356782883)
                ·
                  refine ⟨20219427689661342535174325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13479618459774228356782883 20219427689661342535174325)
                  ·
                    refine ⟨1895571345905750862672593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20219427689661342535174325 1895571345905750862672593)
                    ·
                      refine ⟨1421678509429313147004445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895571345905750862672593 1421678509429313147004445)
                      ·
                        rfl

theorem cell23_2768709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_2768709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768709 prefixEnd_2768709 := by exact prefixLift 2768709
  have htrace : WordTrace (prefixWord ++ tailWord_2768709) baseStart_2768709 baseEnd_2768709 := by
    simpa [prefixWord, tailWord_2768709, baseEnd_2768709] using wordTrace_append hprefix tailTrace_2768709
  have hstable : (prefixWord ++ tailWord_2768709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768709).length < 2 ^ (prefixWord ++ tailWord_2768709).sum := by decide
  have hdescent : baseEnd_2768709 < baseStart_2768709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
