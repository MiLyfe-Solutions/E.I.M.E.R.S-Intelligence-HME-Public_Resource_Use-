import V185TrunkScan23Chunk0149

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_886569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_886569 : Nat := 118140960795 + 886569 * 2 ^ 59
def prefixEnd_886569 : Nat := 4983230072969 + 3 ^ 40 * 886569 * 2
def baseEnd_886569 : Nat := 455236030376047028410249

theorem tailTrace_886569 : CollatzResearch.WordTrace tailWord_886569 prefixEnd_886569 455236030376047028410249 := by
  unfold tailWord_886569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335827925119401775630761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21557218616746267850420507 32335827925119401775630761)
  ·
    refine ⟨24251870943839551331723071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32335827925119401775630761 24251870943839551331723071)
    ·
      refine ⟨36377806415759326997584607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24251870943839551331723071 36377806415759326997584607)
      ·
        refine ⟨54566709623638990496376911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36377806415759326997584607 54566709623638990496376911)
        ·
          refine ⟨81850064435458485744565367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54566709623638990496376911 81850064435458485744565367)
          ·
            refine ⟨122775096653187728616848051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81850064435458485744565367 122775096653187728616848051)
            ·
              refine ⟨184162644979781592925272077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122775096653187728616848051 184162644979781592925272077)
              ·
                refine ⟨69060991867418097346977029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184162644979781592925272077 69060991867418097346977029)
                ·
                  refine ⟨12948935975140893252558193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69060991867418097346977029 12948935975140893252558193)
                  ·
                    refine ⟨9711701981355669939418645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12948935975140893252558193 9711701981355669939418645)
                    ·
                      refine ⟨455236030376047028410249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9711701981355669939418645 455236030376047028410249)
                      ·
                        rfl

theorem cell23_886569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_886569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886569 prefixEnd_886569 := by exact prefixLift 886569
  have htrace : WordTrace (prefixWord ++ tailWord_886569) baseStart_886569 baseEnd_886569 := by
    simpa [prefixWord, tailWord_886569, baseEnd_886569] using wordTrace_append hprefix tailTrace_886569
  have hstable : (prefixWord ++ tailWord_886569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886569).length < 2 ^ (prefixWord ++ tailWord_886569).sum := by decide
  have hdescent : baseEnd_886569 < baseStart_886569 := by decide
  rcases family_descends (prefixWord ++ tailWord_886569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886577 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_886577 : Nat := 118140960795 + 886577 * 2 ^ 59
def prefixEnd_886577 : Nat := 4983230072969 + 3 ^ 40 * 886577 * 2
def baseEnd_886577 : Nat := 455240138221282997110213

theorem tailTrace_886577 : CollatzResearch.WordTrace tailWord_886577 prefixEnd_886577 455240138221282997110213 := by
  unfold tailWord_886577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32336119709090419141921985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21557413139393612761281323 32336119709090419141921985)
  ·
    refine ⟨24252089781817814356441489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32336119709090419141921985 24252089781817814356441489)
    ·
      refine ⟨18189067336363360767331117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24252089781817814356441489 18189067336363360767331117)
      ·
        refine ⟨6820900251136260287749169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18189067336363360767331117 6820900251136260287749169)
        ·
          refine ⟨5115675188352195215811877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6820900251136260287749169 5115675188352195215811877)
          ·
            refine ⟨959189097816036602964727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5115675188352195215811877 959189097816036602964727)
            ·
              refine ⟨1438783646724054904447091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959189097816036602964727 1438783646724054904447091)
              ·
                refine ⟨2158175470086082356670637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438783646724054904447091 2158175470086082356670637)
                ·
                  refine ⟨809315801282280883751489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2158175470086082356670637 809315801282280883751489)
                  ·
                    refine ⟨606986850961710662813617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809315801282280883751489 606986850961710662813617)
                    ·
                      refine ⟨455240138221282997110213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 606986850961710662813617 455240138221282997110213)
                      ·
                        rfl

theorem cell23_886577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_886577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886577 prefixEnd_886577 := by exact prefixLift 886577
  have htrace : WordTrace (prefixWord ++ tailWord_886577) baseStart_886577 baseEnd_886577 := by
    simpa [prefixWord, tailWord_886577, baseEnd_886577] using wordTrace_append hprefix tailTrace_886577
  have hstable : (prefixWord ++ tailWord_886577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886577).length < 2 ^ (prefixWord ++ tailWord_886577).sum := by decide
  have hdescent : baseEnd_886577 < baseStart_886577 := by decide
  rcases family_descends (prefixWord ++ tailWord_886577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886627 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 3]
def baseStart_886627 : Nat := 118140960795 + 886627 * 2 ^ 59
def prefixEnd_886627 : Nat := 4983230072969 + 3 ^ 40 * 886627 * 2
def baseEnd_886627 : Nat := 455265812254007801484983

theorem tailTrace_886627 : CollatzResearch.WordTrace tailWord_886627 prefixEnd_886627 455265812254007801484983 := by
  unfold tailWord_886627
  simp only [CollatzResearch.WordTrace]
  refine ⟨32337943358909277681242135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21558628905939518454161423 32337943358909277681242135)
  ·
    refine ⟨48506915038363916521863203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32337943358909277681242135 48506915038363916521863203)
    ·
      refine ⟨72760372557545874782794805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48506915038363916521863203 72760372557545874782794805)
      ·
        refine ⟨6821284927269925760887013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72760372557545874782794805 6821284927269925760887013)
        ·
          refine ⟨1278990923863111080166315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6821284927269925760887013 1278990923863111080166315)
          ·
            refine ⟨1918486385794666620249473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278990923863111080166315 1918486385794666620249473)
            ·
              refine ⟨1438864789345999965187105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918486385794666620249473 1438864789345999965187105)
              ·
                refine ⟨1079148592009499973890329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438864789345999965187105 1079148592009499973890329)
                ·
                  refine ⟨809361444007124980417747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079148592009499973890329 809361444007124980417747)
                  ·
                    refine ⟨1214042166010687470626621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809361444007124980417747 1214042166010687470626621)
                    ·
                      refine ⟨455265812254007801484983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214042166010687470626621 455265812254007801484983)
                      ·
                        rfl

theorem cell23_886627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_886627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886627 prefixEnd_886627 := by exact prefixLift 886627
  have htrace : WordTrace (prefixWord ++ tailWord_886627) baseStart_886627 baseEnd_886627 := by
    simpa [prefixWord, tailWord_886627, baseEnd_886627] using wordTrace_append hprefix tailTrace_886627
  have hstable : (prefixWord ++ tailWord_886627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886627).length < 2 ^ (prefixWord ++ tailWord_886627).sum := by decide
  have hdescent : baseEnd_886627 < baseStart_886627 := by decide
  rcases family_descends (prefixWord ++ tailWord_886627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886628 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_886628 : Nat := 118140960795 + 886628 * 2 ^ 59
def prefixEnd_886628 : Nat := 4983230072969 + 3 ^ 40 * 886628 * 2
def baseEnd_886628 : Nat := 455266325734662297572479

theorem tailTrace_886628 : CollatzResearch.WordTrace tailWord_886628 prefixEnd_886628 455266325734662297572479 := by
  unfold tailWord_886628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168989915952827426014269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21558653221270436568019025 16168989915952827426014269)
  ·
    refine ⟨6063371218482310284755351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16168989915952827426014269 6063371218482310284755351)
    ·
      refine ⟨9095056827723465427133027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063371218482310284755351 9095056827723465427133027)
      ·
        refine ⟨13642585241585198140699541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9095056827723465427133027 13642585241585198140699541)
        ·
          refine ⟨639496183199306162845291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13642585241585198140699541 639496183199306162845291)
          ·
            refine ⟨959244274798959244267937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639496183199306162845291 959244274798959244267937)
            ·
              refine ⟨719433206099219433200953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959244274798959244267937 719433206099219433200953)
              ·
                refine ⟨539574904574414574900715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719433206099219433200953 539574904574414574900715)
                ·
                  refine ⟨809362356861621862351073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539574904574414574900715 809362356861621862351073)
                  ·
                    refine ⟨607021767646216396763305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809362356861621862351073 607021767646216396763305)
                    ·
                      refine ⟨455266325734662297572479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607021767646216396763305 455266325734662297572479)
                      ·
                        rfl

theorem cell23_886628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_886628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886628 prefixEnd_886628 := by exact prefixLift 886628
  have htrace : WordTrace (prefixWord ++ tailWord_886628) baseStart_886628 baseEnd_886628 := by
    simpa [prefixWord, tailWord_886628, baseEnd_886628] using wordTrace_append hprefix tailTrace_886628
  have hstable : (prefixWord ++ tailWord_886628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886628).length < 2 ^ (prefixWord ++ tailWord_886628).sum := by decide
  have hdescent : baseEnd_886628 < baseStart_886628 := by decide
  rcases family_descends (prefixWord ++ tailWord_886628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886656 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 7]
def baseStart_886656 : Nat := 118140960795 + 886656 * 2 ^ 59
def prefixEnd_886656 : Nat := 4983230072969 + 3 ^ 40 * 886656 * 2
def baseEnd_886656 : Nat := 50586744799220909780261

theorem tailTrace_886656 : CollatzResearch.WordTrace tailWord_886656 prefixEnd_886656 50586744799220909780261 := by
  unfold tailWord_886656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169500537902107817023911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21559334050536143756031881 16169500537902107817023911)
  ·
    refine ⟨24254250806853161725535867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16169500537902107817023911 24254250806853161725535867)
    ·
      refine ⟨36381376210279742588303801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24254250806853161725535867 36381376210279742588303801)
      ·
        refine ⟨27286032157709806941227851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36381376210279742588303801 27286032157709806941227851)
        ·
          refine ⟨40929048236564710411841777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286032157709806941227851 40929048236564710411841777)
          ·
            refine ⟨30696786177423532808881333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40929048236564710411841777 30696786177423532808881333)
            ·
              refine ⟨2877823704133456200832625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30696786177423532808881333 2877823704133456200832625)
              ·
                refine ⟨2158367778100092150624469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877823704133456200832625 2158367778100092150624469)
                ·
                  refine ⟨50586744799220909780261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2158367778100092150624469 50586744799220909780261)
                  ·
                    rfl

theorem cell23_886656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_886656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886656 prefixEnd_886656 := by exact prefixLift 886656
  have htrace : WordTrace (prefixWord ++ tailWord_886656) baseStart_886656 baseEnd_886656 := by
    simpa [prefixWord, tailWord_886656, baseEnd_886656] using wordTrace_append hprefix tailTrace_886656
  have hstable : (prefixWord ++ tailWord_886656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886656).length < 2 ^ (prefixWord ++ tailWord_886656).sum := by decide
  have hdescent : baseEnd_886656 < baseStart_886656 := by decide
  rcases family_descends (prefixWord ++ tailWord_886656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886673 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 5]
def baseStart_886673 : Nat := 118140960795 + 886673 * 2 ^ 59
def prefixEnd_886673 : Nat := 4983230072969 + 3 ^ 40 * 886673 * 2
def baseEnd_886673 : Nat := 50587714707123846834419

theorem tailTrace_886673 : CollatzResearch.WordTrace tailWord_886673 prefixEnd_886673 50587714707123846834419 := by
  unfold tailWord_886673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32339621116742627537416673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559747411161751691611115 32339621116742627537416673)
  ·
    refine ⟨24254715837556970653062505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32339621116742627537416673 24254715837556970653062505)
    ·
      refine ⟨18191036878167727989796879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24254715837556970653062505 18191036878167727989796879)
      ·
        refine ⟨27286555317251591984695319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191036878167727989796879 27286555317251591984695319)
        ·
          refine ⟨40929832975877387977042979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286555317251591984695319 40929832975877387977042979)
          ·
            refine ⟨61394749463816081965564469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40929832975877387977042979 61394749463816081965564469)
            ·
              refine ⟨5755757762232757684271669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61394749463816081965564469 5755757762232757684271669)
              ·
                refine ⟨539602290209321032900469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5755757762232757684271669 539602290209321032900469)
                ·
                  refine ⟨50587714707123846834419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539602290209321032900469 50587714707123846834419)
                  ·
                    rfl

theorem cell23_886673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 5].length) (baseStart_886673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886673 prefixEnd_886673 := by exact prefixLift 886673
  have htrace : WordTrace (prefixWord ++ tailWord_886673) baseStart_886673 baseEnd_886673 := by
    simpa [prefixWord, tailWord_886673, baseEnd_886673] using wordTrace_append hprefix tailTrace_886673
  have hstable : (prefixWord ++ tailWord_886673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886673).length < 2 ^ (prefixWord ++ tailWord_886673).sum := by decide
  have hdescent : baseEnd_886673 < baseStart_886673 := by decide
  rcases family_descends (prefixWord ++ tailWord_886673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886678 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_886678 : Nat := 118140960795 + 886678 * 2 ^ 59
def prefixEnd_886678 : Nat := 4983230072969 + 3 ^ 40 * 886678 * 2
def baseEnd_886678 : Nat := 455291999767387101947249

theorem tailTrace_886678 : CollatzResearch.WordTrace tailWord_886678 prefixEnd_886678 455291999767387101947249 := by
  unfold tailWord_886678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021237717607782086959293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21559868987816342260899125 2021237717607782086959293)
  ·
    refine ⟨757964144102918282609735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2021237717607782086959293 757964144102918282609735)
    ·
      refine ⟨1136946216154377423914603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757964144102918282609735 1136946216154377423914603)
      ·
        refine ⟨1705419324231566135871905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136946216154377423914603 1705419324231566135871905)
        ·
          refine ⟨1279064493173674601903929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705419324231566135871905 1279064493173674601903929)
          ·
            refine ⟨959298369880255951427947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279064493173674601903929 959298369880255951427947)
            ·
              refine ⟨1438947554820383927141921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959298369880255951427947 1438947554820383927141921)
              ·
                refine ⟨1079210666115287945356441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438947554820383927141921 1079210666115287945356441)
                ·
                  refine ⟨809407999586465959017331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079210666115287945356441 809407999586465959017331)
                  ·
                    refine ⟨1214111999379698938525997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809407999586465959017331 1214111999379698938525997)
                    ·
                      refine ⟨455291999767387101947249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214111999379698938525997 455291999767387101947249)
                      ·
                        rfl

theorem cell23_886678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_886678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886678 prefixEnd_886678 := by exact prefixLift 886678
  have htrace : WordTrace (prefixWord ++ tailWord_886678) baseStart_886678 baseEnd_886678 := by
    simpa [prefixWord, tailWord_886678, baseEnd_886678] using wordTrace_append hprefix tailTrace_886678
  have hstable : (prefixWord ++ tailWord_886678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886678).length < 2 ^ (prefixWord ++ tailWord_886678).sum := by decide
  have hdescent : baseEnd_886678 < baseStart_886678 := by decide
  rcases family_descends (prefixWord ++ tailWord_886678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886684 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_886684 : Nat := 118140960795 + 886684 * 2 ^ 59
def prefixEnd_886684 : Nat := 4983230072969 + 3 ^ 40 * 886684 * 2
def baseEnd_886684 : Nat := 455295080651314078472221

theorem tailTrace_886684 : CollatzResearch.WordTrace tailWord_886684 prefixEnd_886684 455295080651314078472221 := by
  unfold tailWord_886684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170011159851388208033553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21560014879801850944044737 16170011159851388208033553)
  ·
    refine ⟨12127508369888541156025165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16170011159851388208033553 12127508369888541156025165)
    ·
      refine ⟨4547815638708202933509437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12127508369888541156025165 4547815638708202933509437)
      ·
        refine ⟨1705430864515576100066039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4547815638708202933509437 1705430864515576100066039)
        ·
          refine ⟨2558146296773364150099059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705430864515576100066039 2558146296773364150099059)
          ·
            refine ⟨3837219445160046225148589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558146296773364150099059 3837219445160046225148589)
            ·
              refine ⟨1438957291935017334430721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837219445160046225148589 1438957291935017334430721)
              ·
                refine ⟨1079217968951263000823041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438957291935017334430721 1079217968951263000823041)
                ·
                  refine ⟨809413476713447250617281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079217968951263000823041 809413476713447250617281)
                  ·
                    refine ⟨607060107535085437962961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809413476713447250617281 607060107535085437962961)
                    ·
                      refine ⟨455295080651314078472221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607060107535085437962961 455295080651314078472221)
                      ·
                        rfl

theorem cell23_886684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_886684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886684 prefixEnd_886684 := by exact prefixLift 886684
  have htrace : WordTrace (prefixWord ++ tailWord_886684) baseStart_886684 baseEnd_886684 := by
    simpa [prefixWord, tailWord_886684, baseEnd_886684] using wordTrace_append hprefix tailTrace_886684
  have hstable : (prefixWord ++ tailWord_886684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886684).length < 2 ^ (prefixWord ++ tailWord_886684).sum := by decide
  have hdescent : baseEnd_886684 < baseStart_886684 := by decide
  rcases family_descends (prefixWord ++ tailWord_886684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886690 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_886690 : Nat := 118140960795 + 886690 * 2 ^ 59
def prefixEnd_886690 : Nat := 4983230072969 + 3 ^ 40 * 886690 * 2
def baseEnd_886690 : Nat := 50588684615026783888577

theorem tailTrace_886690 : CollatzResearch.WordTrace tailWord_886690 prefixEnd_886690 50588684615026783888577 := by
  unfold tailWord_886690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085060289420259860196381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21560160771787359627190349 8085060289420259860196381)
  ·
    refine ⟨3031897608532597447573643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8085060289420259860196381 3031897608532597447573643)
    ·
      refine ⟨4547846412798896171360465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031897608532597447573643 4547846412798896171360465)
      ·
        refine ⟨3410884809599172128520349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4547846412798896171360465 3410884809599172128520349)
        ·
          refine ⟨1279081803599689548195131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3410884809599172128520349 1279081803599689548195131)
          ·
            refine ⟨1918622705399534322292697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279081803599689548195131 1918622705399534322292697)
            ·
              refine ⟨1438967029049650741719523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918622705399534322292697 1438967029049650741719523)
              ·
                refine ⟨2158450543574476112579285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438967029049650741719523 2158450543574476112579285)
                ·
                  refine ⟨50588684615026783888577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2158450543574476112579285 50588684615026783888577)
                  ·
                    rfl

theorem cell23_886690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_886690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886690 prefixEnd_886690 := by exact prefixLift 886690
  have htrace : WordTrace (prefixWord ++ tailWord_886690) baseStart_886690 baseEnd_886690 := by
    simpa [prefixWord, tailWord_886690, baseEnd_886690] using wordTrace_append hprefix tailTrace_886690
  have hstable : (prefixWord ++ tailWord_886690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886690).length < 2 ^ (prefixWord ++ tailWord_886690).sum := by decide
  have hdescent : baseEnd_886690 < baseStart_886690 := by decide
  rcases family_descends (prefixWord ++ tailWord_886690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886693 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_886693 : Nat := 118140960795 + 886693 * 2 ^ 59
def prefixEnd_886693 : Nat := 4983230072969 + 3 ^ 40 * 886693 * 2
def baseEnd_886693 : Nat := 455299701977204543259679

theorem tailTrace_886693 : CollatzResearch.WordTrace tailWord_886693 prefixEnd_886693 455299701977204543259679 := by
  unfold tailWord_886693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32340350576670170953144733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21560233717780113968763155 32340350576670170953144733)
  ·
    refine ⟨12127631466251314107429275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32340350576670170953144733 12127631466251314107429275)
    ·
      refine ⟨18191447199376971161143913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127631466251314107429275 18191447199376971161143913)
      ·
        refine ⟨13643585399532728370857935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18191447199376971161143913 13643585399532728370857935)
        ·
          refine ⟨20465378099299092556286903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13643585399532728370857935 20465378099299092556286903)
          ·
            refine ⟨30698067148948638834430355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20465378099299092556286903 30698067148948638834430355)
            ·
              refine ⟨46047100723422958251645533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698067148948638834430355 46047100723422958251645533)
              ·
                refine ⟨17267662771283609344367075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46047100723422958251645533 17267662771283609344367075)
                ·
                  refine ⟨25901494156925414016550613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17267662771283609344367075 25901494156925414016550613)
                  ·
                    refine ⟨607066269302939391012905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25901494156925414016550613 607066269302939391012905)
                    ·
                      refine ⟨455299701977204543259679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607066269302939391012905 455299701977204543259679)
                      ·
                        rfl

theorem cell23_886693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_886693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886693 prefixEnd_886693 := by exact prefixLift 886693
  have htrace : WordTrace (prefixWord ++ tailWord_886693) baseStart_886693 baseEnd_886693 := by
    simpa [prefixWord, tailWord_886693, baseEnd_886693] using wordTrace_append hprefix tailTrace_886693
  have hstable : (prefixWord ++ tailWord_886693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886693).length < 2 ^ (prefixWord ++ tailWord_886693).sum := by decide
  have hdescent : baseEnd_886693 < baseStart_886693 := by decide
  rcases family_descends (prefixWord ++ tailWord_886693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886736 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_886736 : Nat := 118140960795 + 886736 * 2 ^ 59
def prefixEnd_886736 : Nat := 4983230072969 + 3 ^ 40 * 886736 * 2
def baseEnd_886736 : Nat := 455321781645347875021981

theorem tailTrace_886736 : CollatzResearch.WordTrace tailWord_886736 prefixEnd_886736 455321781645347875021981 := by
  unfold tailWord_886736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170959457757194648480031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21561279277009592864640041 16170959457757194648480031)
  ·
    refine ⟨24256439186635791972720047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170959457757194648480031 24256439186635791972720047)
    ·
      refine ⟨36384658779953687959080071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24256439186635791972720047 36384658779953687959080071)
      ·
        refine ⟨54576988169930531938620107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36384658779953687959080071 54576988169930531938620107)
        ·
          refine ⟨81865482254895797907930161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54576988169930531938620107 81865482254895797907930161)
          ·
            refine ⟨61399111691171848430947621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81865482254895797907930161 61399111691171848430947621)
            ·
              refine ⟨11512333442094721580802679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61399111691171848430947621 11512333442094721580802679)
              ·
                refine ⟨17268500163142082371204019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512333442094721580802679 17268500163142082371204019)
                ·
                  refine ⟨25902750244713123556806029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17268500163142082371204019 25902750244713123556806029)
                  ·
                    refine ⟨9713531341767421333802261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25902750244713123556806029 9713531341767421333802261)
                    ·
                      refine ⟨455321781645347875021981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9713531341767421333802261 455321781645347875021981)
                      ·
                        rfl

theorem cell23_886736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_886736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886736 prefixEnd_886736 := by exact prefixLift 886736
  have htrace : WordTrace (prefixWord ++ tailWord_886736) baseStart_886736 baseEnd_886736 := by
    simpa [prefixWord, tailWord_886736, baseEnd_886736] using wordTrace_append hprefix tailTrace_886736
  have hstable : (prefixWord ++ tailWord_886736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886736).length < 2 ^ (prefixWord ++ tailWord_886736).sum := by decide
  have hdescent : baseEnd_886736 < baseStart_886736 := by decide
  rcases family_descends (prefixWord ++ tailWord_886736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886740 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_886740 : Nat := 118140960795 + 886740 * 2 ^ 59
def prefixEnd_886740 : Nat := 4983230072969 + 3 ^ 40 * 886740 * 2
def baseEnd_886740 : Nat := 455323835567965859371963

theorem tailTrace_886740 : CollatzResearch.WordTrace tailWord_886740 prefixEnd_886740 455323835567965859371963 := by
  unfold tailWord_886740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171032403749948990052837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21561376538333265320070449 16171032403749948990052837)
  ·
    refine ⟨3032068575703115435634907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16171032403749948990052837 3032068575703115435634907)
    ·
      refine ⟨4548102863554673153452361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032068575703115435634907 4548102863554673153452361)
      ·
        refine ⟨3411077147666004865089271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4548102863554673153452361 3411077147666004865089271)
        ·
          refine ⟨5116615721499007297633907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411077147666004865089271 5116615721499007297633907)
          ·
            refine ⟨7674923582248510946450861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116615721499007297633907 7674923582248510946450861)
            ·
              refine ⟨2878096343343191604919073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7674923582248510946450861 2878096343343191604919073)
              ·
                refine ⟨2158572257507393703689305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878096343343191604919073 2158572257507393703689305)
                ·
                  refine ⟨1618929193130545277766979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158572257507393703689305 1618929193130545277766979)
                  ·
                    refine ⟨2428393789695817916650469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618929193130545277766979 2428393789695817916650469)
                    ·
                      refine ⟨455323835567965859371963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2428393789695817916650469 455323835567965859371963)
                      ·
                        rfl

theorem cell23_886740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_886740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886740 prefixEnd_886740 := by exact prefixLift 886740
  have htrace : WordTrace (prefixWord ++ tailWord_886740) baseStart_886740 baseEnd_886740 := by
    simpa [prefixWord, tailWord_886740, baseEnd_886740] using wordTrace_append hprefix tailTrace_886740
  have hstable : (prefixWord ++ tailWord_886740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886740).length < 2 ^ (prefixWord ++ tailWord_886740).sum := by decide
  have hdescent : baseEnd_886740 < baseStart_886740 := by decide
  rcases family_descends (prefixWord ++ tailWord_886740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886834 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_886834 : Nat := 118140960795 + 886834 * 2 ^ 59
def prefixEnd_886834 : Nat := 4983230072969 + 3 ^ 40 * 886834 * 2
def baseEnd_886834 : Nat := 455372102749488491596531

theorem tailTrace_886834 : CollatzResearch.WordTrace tailWord_886834 prefixEnd_886834 455372102749488491596531 := by
  unfold tailWord_886834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086373317289838008506889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21563662179439568022685037 8086373317289838008506889)
  ·
    refine ⟨6064779987967378506380167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8086373317289838008506889 6064779987967378506380167)
    ·
      refine ⟨9097169981951067759570251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6064779987967378506380167 9097169981951067759570251)
      ·
        refine ⟨13645754972926601639355377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097169981951067759570251 13645754972926601639355377)
        ·
          refine ⟨10234316229694951229516533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13645754972926601639355377 10234316229694951229516533)
          ·
            refine ⟨959467146533901677767175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10234316229694951229516533 959467146533901677767175)
            ·
              refine ⟨1439200719800852516650763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959467146533901677767175 1439200719800852516650763)
              ·
                refine ⟨2158801079701278774976145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439200719800852516650763 2158801079701278774976145)
                ·
                  refine ⟨1619100809775959081232109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158801079701278774976145 1619100809775959081232109)
                  ·
                    refine ⟨607162803665984655462041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619100809775959081232109 607162803665984655462041)
                    ·
                      refine ⟨455372102749488491596531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607162803665984655462041 455372102749488491596531)
                      ·
                        rfl

theorem cell23_886834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_886834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886834 prefixEnd_886834 := by exact prefixLift 886834
  have htrace : WordTrace (prefixWord ++ tailWord_886834) baseStart_886834 baseEnd_886834 := by
    simpa [prefixWord, tailWord_886834, baseEnd_886834] using wordTrace_append hprefix tailTrace_886834
  have hstable : (prefixWord ++ tailWord_886834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886834).length < 2 ^ (prefixWord ++ tailWord_886834).sum := by decide
  have hdescent : baseEnd_886834 < baseStart_886834 := by decide
  rcases family_descends (prefixWord ++ tailWord_886834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886841 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 1, 1, 3]
def baseStart_886841 : Nat := 118140960795 + 886841 * 2 ^ 59
def prefixEnd_886841 : Nat := 4983230072969 + 3 ^ 40 * 886841 * 2
def baseEnd_886841 : Nat := 455375697114069964208999

theorem tailTrace_886841 : CollatzResearch.WordTrace tailWord_886841 prefixEnd_886841 455375697114069964208999 := by
  unfold tailWord_886841
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345748580133992229532377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21563832386755994819688251 32345748580133992229532377)
  ·
    refine ⟨24259311435100494172149283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32345748580133992229532377 24259311435100494172149283)
    ·
      refine ⟨36388967152650741258223925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24259311435100494172149283 36388967152650741258223925)
      ·
        refine ⟨3411465670561006992958493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36388967152650741258223925 3411465670561006992958493)
        ·
          refine ⟨1279299626460377622359435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3411465670561006992958493 1279299626460377622359435)
          ·
            refine ⟨1918949439690566433539153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279299626460377622359435 1918949439690566433539153)
            ·
              refine ⟨1439212079767924825154365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918949439690566433539153 1439212079767924825154365)
              ·
                refine ⟨539704529912971809432887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439212079767924825154365 539704529912971809432887)
                ·
                  refine ⟨809556794869457714149331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539704529912971809432887 809556794869457714149331)
                  ·
                    refine ⟨1214335192304186571223997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809556794869457714149331 1214335192304186571223997)
                    ·
                      refine ⟨455375697114069964208999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214335192304186571223997 455375697114069964208999)
                      ·
                        rfl

theorem cell23_886841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_886841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886841 prefixEnd_886841 := by exact prefixLift 886841
  have htrace : WordTrace (prefixWord ++ tailWord_886841) baseStart_886841 baseEnd_886841 := by
    simpa [prefixWord, tailWord_886841, baseEnd_886841] using wordTrace_append hprefix tailTrace_886841
  have hstable : (prefixWord ++ tailWord_886841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886841).length < 2 ^ (prefixWord ++ tailWord_886841).sum := by decide
  have hdescent : baseEnd_886841 < baseStart_886841 := by decide
  rcases family_descends (prefixWord ++ tailWord_886841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886847 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 1, 1, 4]
def baseStart_886847 : Nat := 118140960795 + 886847 * 2 ^ 59
def prefixEnd_886847 : Nat := 4983230072969 + 3 ^ 40 * 886847 * 2
def baseEnd_886847 : Nat := 455378777997996940733971

theorem tailTrace_886847 : CollatzResearch.WordTrace tailWord_886847 prefixEnd_886847 455378777997996940733971 := by
  unfold tailWord_886847
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345967418112255254250795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21563978278741503502833863 32345967418112255254250795)
  ·
    refine ⟨48518951127168382881376193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345967418112255254250795 48518951127168382881376193)
    ·
      refine ⟨36389213345376287161032145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48518951127168382881376193 36389213345376287161032145)
      ·
        refine ⟨27291910009032215370774109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36389213345376287161032145 27291910009032215370774109)
        ·
          refine ⟨10234466253387080764040291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27291910009032215370774109 10234466253387080764040291)
          ·
            refine ⟨15351699380080621146060437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234466253387080764040291 15351699380080621146060437)
            ·
              refine ⟨719610908441279116221583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15351699380080621146060437 719610908441279116221583)
              ·
                refine ⟨1079416362661918674332375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719610908441279116221583 1079416362661918674332375)
                ·
                  refine ⟨1619124543992878011498563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079416362661918674332375 1619124543992878011498563)
                  ·
                    refine ⟨2428686815989317017247845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619124543992878011498563 2428686815989317017247845)
                    ·
                      refine ⟨455378777997996940733971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2428686815989317017247845 455378777997996940733971)
                      ·
                        rfl

theorem cell23_886847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_886847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886847 prefixEnd_886847 := by exact prefixLift 886847
  have htrace : WordTrace (prefixWord ++ tailWord_886847) baseStart_886847 baseEnd_886847 := by
    simpa [prefixWord, tailWord_886847, baseEnd_886847] using wordTrace_append hprefix tailTrace_886847
  have hstable : (prefixWord ++ tailWord_886847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886847).length < 2 ^ (prefixWord ++ tailWord_886847).sum := by decide
  have hdescent : baseEnd_886847 < baseStart_886847 := by decide
  rcases family_descends (prefixWord ++ tailWord_886847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886877 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_886877 : Nat := 118140960795 + 886877 * 2 ^ 59
def prefixEnd_886877 : Nat := 4983230072969 + 3 ^ 40 * 886877 * 2
def baseEnd_886877 : Nat := 455394182417631823358833

theorem tailTrace_886877 : CollatzResearch.WordTrace tailWord_886877 prefixEnd_886877 455394182417631823358833 := by
  unfold tailWord_886877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32347061608003570377842885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21564707738669046918561923 32347061608003570377842885)
  ·
    refine ⟨6065074051500669445845541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32347061608003570377842885 6065074051500669445845541)
    ·
      refine ⟨1137201384656375521096039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6065074051500669445845541 1137201384656375521096039)
      ·
        refine ⟨1705802076984563281644059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137201384656375521096039 1705802076984563281644059)
        ·
          refine ⟨2558703115476844922466089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705802076984563281644059 2558703115476844922466089)
          ·
            refine ⟨1919027336607633691849567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558703115476844922466089 1919027336607633691849567)
            ·
              refine ⟨2878541004911450537774351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919027336607633691849567 2878541004911450537774351)
              ·
                refine ⟨4317811507367175806661527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878541004911450537774351 4317811507367175806661527)
                ·
                  refine ⟨6476717261050763709992291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317811507367175806661527 6476717261050763709992291)
                  ·
                    refine ⟨9715075891576145564988437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476717261050763709992291 9715075891576145564988437)
                    ·
                      refine ⟨455394182417631823358833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9715075891576145564988437 455394182417631823358833)
                      ·
                        rfl

theorem cell23_886877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_886877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886877 prefixEnd_886877 := by exact prefixLift 886877
  have htrace : WordTrace (prefixWord ++ tailWord_886877) baseStart_886877 baseEnd_886877 := by
    simpa [prefixWord, tailWord_886877, baseEnd_886877] using wordTrace_append hprefix tailTrace_886877
  have hstable : (prefixWord ++ tailWord_886877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886877).length < 2 ^ (prefixWord ++ tailWord_886877).sum := by decide
  have hdescent : baseEnd_886877 < baseStart_886877 := by decide
  rcases family_descends (prefixWord ++ tailWord_886877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886883 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 7]
def baseStart_886883 : Nat := 118140960795 + 886883 * 2 ^ 59
def prefixEnd_886883 : Nat := 4983230072969 + 3 ^ 40 * 886883 * 2
def baseEnd_886883 : Nat := 151799087767186266627935

theorem tailTrace_886883 : CollatzResearch.WordTrace tailWord_886883 prefixEnd_886883 151799087767186266627935 := by
  unfold tailWord_886883
  simp only [CollatzResearch.WordTrace]
  refine ⟨32347280445981833402561303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21564853630654555601707535 32347280445981833402561303)
  ·
    refine ⟨48520920668972750103841955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32347280445981833402561303 48520920668972750103841955)
    ·
      refine ⟨72781381003459125155762933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48520920668972750103841955 72781381003459125155762933)
      ·
        refine ⟨6823254469074292983352775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72781381003459125155762933 6823254469074292983352775)
        ·
          refine ⟨10234881703611439475029163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823254469074292983352775 10234881703611439475029163)
          ·
            refine ⟨15352322555417159212543745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234881703611439475029163 15352322555417159212543745)
            ·
              refine ⟨11514241916562869409407809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352322555417159212543745 11514241916562869409407809)
              ·
                refine ⟨8635681437422152057055857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514241916562869409407809 8635681437422152057055857)
                ·
                  refine ⟨6476761078066614042791893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635681437422152057055857 6476761078066614042791893)
                  ·
                    refine ⟨151799087767186266627935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6476761078066614042791893 151799087767186266627935)
                    ·
                      rfl

theorem cell23_886883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_886883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886883 prefixEnd_886883 := by exact prefixLift 886883
  have htrace : WordTrace (prefixWord ++ tailWord_886883) baseStart_886883 baseEnd_886883 := by
    simpa [prefixWord, tailWord_886883, baseEnd_886883] using wordTrace_append hprefix tailTrace_886883
  have hstable : (prefixWord ++ tailWord_886883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886883).length < 2 ^ (prefixWord ++ tailWord_886883).sum := by decide
  have hdescent : baseEnd_886883 < baseStart_886883 := by decide
  rcases family_descends (prefixWord ++ tailWord_886883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886898 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_886898 : Nat := 118140960795 + 886898 * 2 ^ 59
def prefixEnd_886898 : Nat := 4983230072969 + 3 ^ 40 * 886898 * 2
def baseEnd_886898 : Nat := 455404965511376241196237

theorem tailTrace_886898 : CollatzResearch.WordTrace tailWord_886898 prefixEnd_886898 455404965511376241196237 := by
  unfold tailWord_886898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086956885231872741089337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21565218360618327309571565 8086956885231872741089337)
  ·
    refine ⟨6065217663923904555817003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8086956885231872741089337 6065217663923904555817003)
    ·
      refine ⟨9097826495885856833725505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065217663923904555817003 9097826495885856833725505)
      ·
        refine ⟨6823369871914392625294129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9097826495885856833725505 6823369871914392625294129)
        ·
          refine ⟨5117527403935794468970597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6823369871914392625294129 5117527403935794468970597)
          ·
            refine ⟨959536388237961462931987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5117527403935794468970597 959536388237961462931987)
            ·
              refine ⟨1439304582356942194397981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959536388237961462931987 1439304582356942194397981)
              ·
                refine ⟨539739218383853322899243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439304582356942194397981 539739218383853322899243)
                ·
                  refine ⟨809608827575779984348865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539739218383853322899243 809608827575779984348865)
                  ·
                    refine ⟨607206620681834988261649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809608827575779984348865 607206620681834988261649)
                    ·
                      refine ⟨455404965511376241196237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607206620681834988261649 455404965511376241196237)
                      ·
                        rfl

theorem cell23_886898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_886898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886898 prefixEnd_886898 := by exact prefixLift 886898
  have htrace : WordTrace (prefixWord ++ tailWord_886898) baseStart_886898 baseEnd_886898 := by
    simpa [prefixWord, tailWord_886898, baseEnd_886898] using wordTrace_append hprefix tailTrace_886898
  have hstable : (prefixWord ++ tailWord_886898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886898).length < 2 ^ (prefixWord ++ tailWord_886898).sum := by decide
  have hdescent : baseEnd_886898 < baseStart_886898 := by decide
  rcases family_descends (prefixWord ++ tailWord_886898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886930 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_886930 : Nat := 118140960795 + 886930 * 2 ^ 59
def prefixEnd_886930 : Nat := 4983230072969 + 3 ^ 40 * 886930 * 2
def baseEnd_886930 : Nat := 151807132297440038665363

theorem tailTrace_886930 : CollatzResearch.WordTrace tailWord_886930 prefixEnd_886930 151807132297440038665363 := by
  unfold tailWord_886930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087248669202890107380561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21565996451207706953014829 8087248669202890107380561)
  ·
    refine ⟨6065436501902167580535421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8087248669202890107380561 6065436501902167580535421)
    ·
      refine ⟨2274538688213312842700783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6065436501902167580535421 2274538688213312842700783)
      ·
        refine ⟨3411808032319969264051175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274538688213312842700783 3411808032319969264051175)
        ·
          refine ⟨5117712048479953896076763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411808032319969264051175 5117712048479953896076763)
          ·
            refine ⟨7676568072719930844115145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117712048479953896076763 7676568072719930844115145)
            ·
              refine ⟨5757426054539948133086359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7676568072719930844115145 5757426054539948133086359)
              ·
                refine ⟨8636139081809922199629539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757426054539948133086359 8636139081809922199629539)
                ·
                  refine ⟨12954208622714883299444309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636139081809922199629539 12954208622714883299444309)
                  ·
                    refine ⟨151807132297440038665363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12954208622714883299444309 151807132297440038665363)
                    ·
                      rfl

theorem cell23_886930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_886930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886930 prefixEnd_886930 := by exact prefixLift 886930
  have htrace : WordTrace (prefixWord ++ tailWord_886930) baseStart_886930 baseEnd_886930 := by
    simpa [prefixWord, tailWord_886930, baseEnd_886930] using wordTrace_append hprefix tailTrace_886930
  have hstable : (prefixWord ++ tailWord_886930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886930).length < 2 ^ (prefixWord ++ tailWord_886930).sum := by decide
  have hdescent : baseEnd_886930 < baseStart_886930 := by decide
  rcases family_descends (prefixWord ++ tailWord_886930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886940 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_886940 : Nat := 118140960795 + 886940 * 2 ^ 59
def prefixEnd_886940 : Nat := 4983230072969 + 3 ^ 40 * 886940 * 2
def baseEnd_886940 : Nat := 455426531698865076871043

theorem tailTrace_886940 : CollatzResearch.WordTrace tailWord_886940 prefixEnd_886940 455426531698865076871043 := by
  unfold tailWord_886940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174679703387666068693137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21566239604516888091590849 16174679703387666068693137)
  ·
    refine ⟨12131009777540749551519853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16174679703387666068693137 12131009777540749551519853)
    ·
      refine ⟨4549128666577781081819945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12131009777540749551519853 4549128666577781081819945)
      ·
        refine ⟨3411846499933335811364959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4549128666577781081819945 3411846499933335811364959)
        ·
          refine ⟨5117769749900003717047439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411846499933335811364959 5117769749900003717047439)
          ·
            refine ⟨7676654624850005575571159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117769749900003717047439 7676654624850005575571159)
            ·
              refine ⟨11514981937275008363356739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676654624850005575571159 11514981937275008363356739)
              ·
                refine ⟨17272472905912512545035109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514981937275008363356739 17272472905912512545035109)
                ·
                  refine ⟨3238588669858596102194083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17272472905912512545035109 3238588669858596102194083)
                  ·
                    refine ⟨4857883004787894153291125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238588669858596102194083 4857883004787894153291125)
                    ·
                      refine ⟨455426531698865076871043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4857883004787894153291125 455426531698865076871043)
                      ·
                        rfl

theorem cell23_886940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_886940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886940 prefixEnd_886940 := by exact prefixLift 886940
  have htrace : WordTrace (prefixWord ++ tailWord_886940) baseStart_886940 baseEnd_886940 := by
    simpa [prefixWord, tailWord_886940, baseEnd_886940] using wordTrace_append hprefix tailTrace_886940
  have hstable : (prefixWord ++ tailWord_886940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886940).length < 2 ^ (prefixWord ++ tailWord_886940).sum := by decide
  have hdescent : baseEnd_886940 < baseStart_886940 := by decide
  rcases family_descends (prefixWord ++ tailWord_886940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886941 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_886941 : Nat := 118140960795 + 886941 * 2 ^ 59
def prefixEnd_886941 : Nat := 4983230072969 + 3 ^ 40 * 886941 * 2
def baseEnd_886941 : Nat := 455427045179519572958539

theorem tailTrace_886941 : CollatzResearch.WordTrace tailWord_886941 prefixEnd_886941 455427045179519572958539 := by
  unfold tailWord_886941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349395879771709308172677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21566263919847806205448451 32349395879771709308172677)
  ·
    refine ⟨6065511727457195495282377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32349395879771709308172677 6065511727457195495282377)
    ·
      refine ⟨4549133795592896621461783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6065511727457195495282377 4549133795592896621461783)
      ·
        refine ⟨6823700693389344932192675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549133795592896621461783 6823700693389344932192675)
        ·
          refine ⟨10235551040084017398289013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823700693389344932192675 10235551040084017398289013)
          ·
            refine ⟨959582910007876631089595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10235551040084017398289013 959582910007876631089595)
            ·
              refine ⟨1439374365011814946634393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959582910007876631089595 1439374365011814946634393)
              ·
                refine ⟨1079530773758861209975795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439374365011814946634393 1079530773758861209975795)
                ·
                  refine ⟨1619296160638291814963693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079530773758861209975795 1619296160638291814963693)
                  ·
                    refine ⟨607236060239359430611385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619296160638291814963693 607236060239359430611385)
                    ·
                      refine ⟨455427045179519572958539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607236060239359430611385 455427045179519572958539)
                      ·
                        rfl

theorem cell23_886941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_886941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886941 prefixEnd_886941 := by exact prefixLift 886941
  have htrace : WordTrace (prefixWord ++ tailWord_886941) baseStart_886941 baseEnd_886941 := by
    simpa [prefixWord, tailWord_886941, baseEnd_886941] using wordTrace_append hprefix tailTrace_886941
  have hstable : (prefixWord ++ tailWord_886941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886941).length < 2 ^ (prefixWord ++ tailWord_886941).sum := by decide
  have hdescent : baseEnd_886941 < baseStart_886941 := by decide
  rcases family_descends (prefixWord ++ tailWord_886941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886957 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_886957 : Nat := 118140960795 + 886957 * 2 ^ 59
def prefixEnd_886957 : Nat := 4983230072969 + 3 ^ 40 * 886957 * 2
def baseEnd_886957 : Nat := 455435260869991510358465

theorem tailTrace_886957 : CollatzResearch.WordTrace tailWord_886957 prefixEnd_886957 455435260869991510358465 := by
  unfold tailWord_886957
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349979447713744040755125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21566652965142496027170083 32349979447713744040755125)
  ·
    refine ⟨3032810573223163503820793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32349979447713744040755125 3032810573223163503820793)
    ·
      refine ⟨2274607929917372627865595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3032810573223163503820793 2274607929917372627865595)
      ·
        refine ⟨3411911894876058941798393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274607929917372627865595 3411911894876058941798393)
        ·
          refine ⟨2558933921157044206348795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411911894876058941798393 2558933921157044206348795)
          ·
            refine ⟨3838400881735566309523193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558933921157044206348795 3838400881735566309523193)
            ·
              refine ⟨2878800661301674732142395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838400881735566309523193 2878800661301674732142395)
              ·
                refine ⟨4318200991952512098213593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878800661301674732142395 4318200991952512098213593)
                ·
                  refine ⟨3238650743964384073660195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318200991952512098213593 3238650743964384073660195)
                  ·
                    refine ⟨4857976115946576110490293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238650743964384073660195 4857976115946576110490293)
                    ·
                      refine ⟨455435260869991510358465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4857976115946576110490293 455435260869991510358465)
                      ·
                        rfl

theorem cell23_886957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_886957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_886957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_886957 prefixEnd_886957 := by exact prefixLift 886957
  have htrace : WordTrace (prefixWord ++ tailWord_886957) baseStart_886957 baseEnd_886957 := by
    simpa [prefixWord, tailWord_886957, baseEnd_886957] using wordTrace_append hprefix tailTrace_886957
  have hstable : (prefixWord ++ tailWord_886957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886957).length < 2 ^ (prefixWord ++ tailWord_886957).sum := by decide
  have hdescent : baseEnd_886957 < baseStart_886957 := by decide
  rcases family_descends (prefixWord ++ tailWord_886957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887011 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 5]
def baseStart_887011 : Nat := 118140960795 + 887011 * 2 ^ 59
def prefixEnd_887011 : Nat := 4983230072969 + 3 ^ 40 * 887011 * 2
def baseEnd_887011 : Nat := 50606998758370477675913

theorem tailTrace_887011 : CollatzResearch.WordTrace tailWord_887011 prefixEnd_887011 50606998758370477675913 := by
  unfold tailWord_887011
  simp only [CollatzResearch.WordTrace]
  refine ⟨32351948989518111263220887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21567965993012074175480591 32351948989518111263220887)
  ·
    refine ⟨48527923484277166894831331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32351948989518111263220887 48527923484277166894831331)
    ·
      refine ⟨72791885226415750342246997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48527923484277166894831331 72791885226415750342246997)
      ·
        refine ⟨853029904997059574323207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 72791885226415750342246997 853029904997059574323207)
        ·
          refine ⟨1279544857495589361484811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853029904997059574323207 1279544857495589361484811)
          ·
            refine ⟨1919317286243384042227217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279544857495589361484811 1919317286243384042227217)
            ·
              refine ⟨1439487964682538031670413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919317286243384042227217 1439487964682538031670413)
              ·
                refine ⟨539807986755951761876405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439487964682538031670413 539807986755951761876405)
                ·
                  refine ⟨50606998758370477675913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539807986755951761876405 50606998758370477675913)
                  ·
                    rfl

theorem cell23_887011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 5].length) (baseStart_887011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887011 prefixEnd_887011 := by exact prefixLift 887011
  have htrace : WordTrace (prefixWord ++ tailWord_887011) baseStart_887011 baseEnd_887011 := by
    simpa [prefixWord, tailWord_887011, baseEnd_887011] using wordTrace_append hprefix tailTrace_887011
  have hstable : (prefixWord ++ tailWord_887011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887011).length < 2 ^ (prefixWord ++ tailWord_887011).sum := by decide
  have hdescent : baseEnd_887011 < baseStart_887011 := by decide
  rcases family_descends (prefixWord ++ tailWord_887011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887027 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 4, 2]
def baseStart_887027 : Nat := 118140960795 + 887027 * 2 ^ 59
def prefixEnd_887027 : Nat := 4983230072969 + 3 ^ 40 * 887027 * 2
def baseEnd_887027 : Nat := 455471204515806236483143

theorem tailTrace_887027 : CollatzResearch.WordTrace tailWord_887027 prefixEnd_887027 455471204515806236483143 := by
  unfold tailWord_887027
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352532557460145995803335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21568355038306763997202223 32352532557460145995803335)
  ·
    refine ⟨48528798836190218993705003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32352532557460145995803335 48528798836190218993705003)
    ·
      refine ⟨72793198254285328490557505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48528798836190218993705003 72793198254285328490557505)
      ·
        refine ⟨54594898690713996367918129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72793198254285328490557505 54594898690713996367918129)
        ·
          refine ⟨40946174018035497275938597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54594898690713996367918129 40946174018035497275938597)
          ·
            refine ⟨7677407628381655739238487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40946174018035497275938597 7677407628381655739238487)
            ·
              refine ⟨11516111442572483608857731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677407628381655739238487 11516111442572483608857731)
              ·
                refine ⟨17274167163858725413286597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516111442572483608857731 17274167163858725413286597)
                ·
                  refine ⟨3238906343223511014991237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17274167163858725413286597 3238906343223511014991237)
                  ·
                    refine ⟨607294939354408315310857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3238906343223511014991237 607294939354408315310857)
                    ·
                      refine ⟨455471204515806236483143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607294939354408315310857 455471204515806236483143)
                      ·
                        rfl

theorem cell23_887027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4, 2].length) (baseStart_887027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887027 prefixEnd_887027 := by exact prefixLift 887027
  have htrace : WordTrace (prefixWord ++ tailWord_887027) baseStart_887027 baseEnd_887027 := by
    simpa [prefixWord, tailWord_887027, baseEnd_887027] using wordTrace_append hprefix tailTrace_887027
  have hstable : (prefixWord ++ tailWord_887027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887027).length < 2 ^ (prefixWord ++ tailWord_887027).sum := by decide
  have hdescent : baseEnd_887027 < baseStart_887027 := by decide
  rcases family_descends (prefixWord ++ tailWord_887027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887071 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 1, 4]
def baseStart_887071 : Nat := 118140960795 + 887071 * 2 ^ 59
def prefixEnd_887071 : Nat := 4983230072969 + 3 ^ 40 * 887071 * 2
def baseEnd_887071 : Nat := 151831265888201354777647

theorem tailTrace_887071 : CollatzResearch.WordTrace tailWord_887071 prefixEnd_887071 151831265888201354777647 := by
  unfold tailWord_887071
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354137369300741510405067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21569424912867161006936711 32354137369300741510405067)
  ·
    refine ⟨48531206053951112265607601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32354137369300741510405067 48531206053951112265607601)
    ·
      refine ⟨36398404540463334199205701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48531206053951112265607601 36398404540463334199205701)
      ·
        refine ⟨6824700851336875162351069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36398404540463334199205701 6824700851336875162351069)
        ·
          refine ⟨2559262819251328185881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6824700851336875162351069 2559262819251328185881651)
          ·
            refine ⟨3838894228876992278822477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559262819251328185881651 3838894228876992278822477)
            ·
              refine ⟨1439585335828872104558429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3838894228876992278822477 1439585335828872104558429)
              ·
                refine ⟨539844500935827039209411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439585335828872104558429 539844500935827039209411)
                ·
                  refine ⟨809766751403740558814117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539844500935827039209411 809766751403740558814117)
                  ·
                    refine ⟨151831265888201354777647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 809766751403740558814117 151831265888201354777647)
                    ·
                      rfl

theorem cell23_887071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_887071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887071 prefixEnd_887071 := by exact prefixLift 887071
  have htrace : WordTrace (prefixWord ++ tailWord_887071) baseStart_887071 baseEnd_887071 := by
    simpa [prefixWord, tailWord_887071, baseEnd_887071] using wordTrace_append hprefix tailTrace_887071
  have hstable : (prefixWord ++ tailWord_887071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887071).length < 2 ^ (prefixWord ++ tailWord_887071).sum := by decide
  have hdescent : baseEnd_887071 < baseStart_887071 := by decide
  rcases family_descends (prefixWord ++ tailWord_887071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887121 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_887121 : Nat := 118140960795 + 887121 * 2 ^ 59
def prefixEnd_887121 : Nat := 4983230072969 + 3 ^ 40 * 887121 * 2
def baseEnd_887121 : Nat := 455519471697328868707711

theorem tailTrace_887121 : CollatzResearch.WordTrace tailWord_887121 prefixEnd_887121 455519471697328868707711 := by
  unfold tailWord_887121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32355961019119600049725217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21570640679413066699816811 32355961019119600049725217)
  ·
    refine ⟨24266970764339700037293913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32355961019119600049725217 24266970764339700037293913)
    ·
      refine ⟨18200228073254775027970435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24266970764339700037293913 18200228073254775027970435)
      ·
        refine ⟨27300342109882162541955653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18200228073254775027970435 27300342109882162541955653)
        ·
          refine ⟨5118814145602905476616685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27300342109882162541955653 5118814145602905476616685)
          ·
            refine ⟨1919555304601089553731257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5118814145602905476616685 1919555304601089553731257)
            ·
              refine ⟨1439666478450817165298443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919555304601089553731257 1439666478450817165298443)
              ·
                refine ⟨2159499717676225747947665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439666478450817165298443 2159499717676225747947665)
                ·
                  refine ⟨1619624788257169310960749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159499717676225747947665 1619624788257169310960749)
                  ·
                    refine ⟨607359295596438491610281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619624788257169310960749 607359295596438491610281)
                    ·
                      refine ⟨455519471697328868707711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607359295596438491610281 455519471697328868707711)
                      ·
                        rfl

theorem cell23_887121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_887121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887121 prefixEnd_887121 := by exact prefixLift 887121
  have htrace : WordTrace (prefixWord ++ tailWord_887121) baseStart_887121 baseEnd_887121 := by
    simpa [prefixWord, tailWord_887121, baseEnd_887121] using wordTrace_append hprefix tailTrace_887121
  have hstable : (prefixWord ++ tailWord_887121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887121).length < 2 ^ (prefixWord ++ tailWord_887121).sum := by decide
  have hdescent : baseEnd_887121 < baseStart_887121 := by decide
  rcases family_descends (prefixWord ++ tailWord_887121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887127 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 6]
def baseStart_887127 : Nat := 118140960795 + 887127 * 2 ^ 59
def prefixEnd_887127 : Nat := 4983230072969 + 3 ^ 40 * 887127 * 2
def baseEnd_887127 : Nat := 151840850860418615077561

theorem tailTrace_887127 : CollatzResearch.WordTrace tailWord_887127 prefixEnd_887127 151840850860418615077561 := by
  unfold tailWord_887127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356179857097863074443635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21570786571398575382962423 32356179857097863074443635)
  ·
    refine ⟨48534269785646794611665453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32356179857097863074443635 48534269785646794611665453)
    ·
      refine ⟨18200351169617547979374545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48534269785646794611665453 18200351169617547979374545)
      ·
        refine ⟨13650263377213160984530909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18200351169617547979374545 13650263377213160984530909)
        ·
          refine ⟨5118848766454935369199091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13650263377213160984530909 5118848766454935369199091)
          ·
            refine ⟨7678273149682403053798637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118848766454935369199091 7678273149682403053798637)
            ·
              refine ⟨2879352431130901145174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7678273149682403053798637 2879352431130901145174489)
              ·
                refine ⟨2159514323348175858880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879352431130901145174489 2159514323348175858880867)
                ·
                  refine ⟨3239271485022263788321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159514323348175858880867 3239271485022263788321301)
                  ·
                    refine ⟨151840850860418615077561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3239271485022263788321301 151840850860418615077561)
                    ·
                      rfl

theorem cell23_887127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_887127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887127 prefixEnd_887127 := by exact prefixLift 887127
  have htrace : WordTrace (prefixWord ++ tailWord_887127) baseStart_887127 baseEnd_887127 := by
    simpa [prefixWord, tailWord_887127, baseEnd_887127] using wordTrace_append hprefix tailTrace_887127
  have hstable : (prefixWord ++ tailWord_887127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887127).length < 2 ^ (prefixWord ++ tailWord_887127).sum := by decide
  have hdescent : baseEnd_887127 < baseStart_887127 := by decide
  rcases family_descends (prefixWord ++ tailWord_887127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887154 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_887154 : Nat := 118140960795 + 887154 * 2 ^ 59
def prefixEnd_887154 : Nat := 4983230072969 + 3 ^ 40 * 887154 * 2
def baseEnd_887154 : Nat := 455536416558927239595059

theorem tailTrace_887154 : CollatzResearch.WordTrace tailWord_887154 prefixEnd_887154 455536416558927239595059 := by
  unfold tailWord_887154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089291157000011671419129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21571443085333364457117677 8089291157000011671419129)
  ·
    refine ⟨6066968367750008753564347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8089291157000011671419129 6066968367750008753564347)
    ·
      refine ⟨9100452551625013130346521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6066968367750008753564347 9100452551625013130346521)
      ·
        refine ⟨6825339413718759847759891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100452551625013130346521 6825339413718759847759891)
        ·
          refine ⟨10238009120578139771639837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825339413718759847759891 10238009120578139771639837)
          ·
            refine ⟨3839253420216802414364939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10238009120578139771639837 3839253420216802414364939)
            ·
              refine ⟨5758880130325203621547409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839253420216802414364939 5758880130325203621547409)
              ·
                refine ⟨4319160097743902716160557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758880130325203621547409 4319160097743902716160557)
                ·
                  refine ⟨1619685036653963518560209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4319160097743902716160557 1619685036653963518560209)
                  ·
                    refine ⟨1214763777490472638920157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1619685036653963518560209 1214763777490472638920157)
                    ·
                      refine ⟨455536416558927239595059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214763777490472638920157 455536416558927239595059)
                      ·
                        rfl

theorem cell23_887154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_887154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887154 prefixEnd_887154 := by exact prefixLift 887154
  have htrace : WordTrace (prefixWord ++ tailWord_887154) baseStart_887154 baseEnd_887154 := by
    simpa [prefixWord, tailWord_887154, baseEnd_887154] using wordTrace_append hprefix tailTrace_887154
  have hstable : (prefixWord ++ tailWord_887154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887154).length < 2 ^ (prefixWord ++ tailWord_887154).sum := by decide
  have hdescent : baseEnd_887154 < baseStart_887154 := by decide
  rcases family_descends (prefixWord ++ tailWord_887154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887167 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_887167 : Nat := 118140960795 + 887167 * 2 ^ 59
def prefixEnd_887167 : Nat := 4983230072969 + 3 ^ 40 * 887167 * 2
def baseEnd_887167 : Nat := 455543091807435688732499

theorem tailTrace_887167 : CollatzResearch.WordTrace tailWord_887167 prefixEnd_887167 455543091807435688732499 := by
  unfold tailWord_887167
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357638776952949905899755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21571759184635299937266503 32357638776952949905899755)
  ·
    refine ⟨48536458165429424858849633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32357638776952949905899755 48536458165429424858849633)
    ·
      refine ⟨36402343624072068644137225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48536458165429424858849633 36402343624072068644137225)
      ·
        refine ⟨27301757718054051483102919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36402343624072068644137225 27301757718054051483102919)
        ·
          refine ⟨40952636577081077224654379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27301757718054051483102919 40952636577081077224654379)
          ·
            refine ⟨61428954865621615836981569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40952636577081077224654379 61428954865621615836981569)
            ·
              refine ⟨46071716149216211877736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61428954865621615836981569 46071716149216211877736177)
              ·
                refine ⟨34553787111912158908302133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46071716149216211877736177 34553787111912158908302133)
                ·
                  refine ⟨3239417541741764897653325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34553787111912158908302133 3239417541741764897653325)
                  ·
                    refine ⟨1214781578153161836619997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239417541741764897653325 1214781578153161836619997)
                    ·
                      refine ⟨455543091807435688732499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214781578153161836619997 455543091807435688732499)
                      ·
                        rfl

theorem cell23_887167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_887167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887167 prefixEnd_887167 := by exact prefixLift 887167
  have htrace : WordTrace (prefixWord ++ tailWord_887167) baseStart_887167 baseEnd_887167 := by
    simpa [prefixWord, tailWord_887167, baseEnd_887167] using wordTrace_append hprefix tailTrace_887167
  have hstable : (prefixWord ++ tailWord_887167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887167).length < 2 ^ (prefixWord ++ tailWord_887167).sum := by decide
  have hdescent : baseEnd_887167 < baseStart_887167 := by decide
  rcases family_descends (prefixWord ++ tailWord_887167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887188 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_887188 : Nat := 118140960795 + 887188 * 2 ^ 59
def prefixEnd_887188 : Nat := 4983230072969 + 3 ^ 40 * 887188 * 2
def baseEnd_887188 : Nat := 455553874901180106569903

theorem tailTrace_887188 : CollatzResearch.WordTrace tailWord_887188 prefixEnd_887188 455553874901180106569903 := by
  unfold tailWord_887188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179202354938435246207109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21572269806584580328276145 16179202354938435246207109)
  ·
    refine ⟨3033600441550956608663833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16179202354938435246207109 3033600441550956608663833)
    ·
      refine ⟨2275200331163217456497875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3033600441550956608663833 2275200331163217456497875)
      ·
        refine ⟨3412800496744826184746813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275200331163217456497875 3412800496744826184746813)
        ·
          refine ⟨1279800186279309819280055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3412800496744826184746813 1279800186279309819280055)
          ·
            refine ⟨1919700279418964728920083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279800186279309819280055 1919700279418964728920083)
            ·
              refine ⟨2879550419128447093380125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919700279418964728920083 2879550419128447093380125)
              ·
                refine ⟨1079831407173167660017547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2879550419128447093380125 1079831407173167660017547)
                ·
                  refine ⟨1619747110759751490026321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079831407173167660017547 1619747110759751490026321)
                  ·
                    refine ⟨1214810333069813617519741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1619747110759751490026321 1214810333069813617519741)
                    ·
                      refine ⟨455553874901180106569903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214810333069813617519741 455553874901180106569903)
                      ·
                        rfl

theorem cell23_887188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_887188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887188 prefixEnd_887188 := by exact prefixLift 887188
  have htrace : WordTrace (prefixWord ++ tailWord_887188) baseStart_887188 baseEnd_887188 := by
    simpa [prefixWord, tailWord_887188, baseEnd_887188] using wordTrace_append hprefix tailTrace_887188
  have hstable : (prefixWord ++ tailWord_887188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887188).length < 2 ^ (prefixWord ++ tailWord_887188).sum := by decide
  have hdescent : baseEnd_887188 < baseStart_887188 := by decide
  rcases family_descends (prefixWord ++ tailWord_887188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887218 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_887218 : Nat := 118140960795 + 887218 * 2 ^ 59
def prefixEnd_887218 : Nat := 4983230072969 + 3 ^ 40 * 887218 * 2
def baseEnd_887218 : Nat := 455569279320814989194765

theorem tailTrace_887218 : CollatzResearch.WordTrace tailWord_887218 prefixEnd_887218 455569279320814989194765 := by
  unfold tailWord_887218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089874724942046404001577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21572999266512123744004205 8089874724942046404001577)
  ·
    refine ⟨6067406043706534803001183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8089874724942046404001577 6067406043706534803001183)
    ·
      refine ⟨9101109065559802204501775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6067406043706534803001183 9101109065559802204501775)
      ·
        refine ⟨13651663598339703306752663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101109065559802204501775 13651663598339703306752663)
        ·
          refine ⟨20477495397509554960128995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651663598339703306752663 20477495397509554960128995)
          ·
            refine ⟨30716243096264332440193493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20477495397509554960128995 30716243096264332440193493)
            ·
              refine ⟨719911947568695291567035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30716243096264332440193493 719911947568695291567035)
              ·
                refine ⟨1079867921353042937350553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719911947568695291567035 1079867921353042937350553)
                ·
                  refine ⟨809900941014782203012915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079867921353042937350553 809900941014782203012915)
                  ·
                    refine ⟨1214851411522173304519373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 809900941014782203012915 1214851411522173304519373)
                    ·
                      refine ⟨455569279320814989194765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1214851411522173304519373 455569279320814989194765)
                      ·
                        rfl

theorem cell23_887218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_887218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887218 prefixEnd_887218 := by exact prefixLift 887218
  have htrace : WordTrace (prefixWord ++ tailWord_887218) baseStart_887218 baseEnd_887218 := by
    simpa [prefixWord, tailWord_887218, baseEnd_887218] using wordTrace_append hprefix tailTrace_887218
  have hstable : (prefixWord ++ tailWord_887218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887218).length < 2 ^ (prefixWord ++ tailWord_887218).sum := by decide
  have hdescent : baseEnd_887218 < baseStart_887218 := by decide
  rcases family_descends (prefixWord ++ tailWord_887218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887228 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_887228 : Nat := 118140960795 + 887228 * 2 ^ 59
def prefixEnd_887228 : Nat := 4983230072969 + 3 ^ 40 * 887228 * 2
def baseEnd_887228 : Nat := 455574414127359950069719

theorem tailTrace_887228 : CollatzResearch.WordTrace tailWord_887228 prefixEnd_887228 455574414127359950069719 := by
  unfold tailWord_887228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179931814865978661935169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21573242419821304882580225 16179931814865978661935169)
  ·
    refine ⟨12134948861149483996451377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16179931814865978661935169 12134948861149483996451377)
    ·
      refine ⟨9101211645862112997338533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12134948861149483996451377 9101211645862112997338533)
      ·
        refine ⟨1706477183599146187000975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9101211645862112997338533 1706477183599146187000975)
        ·
          refine ⟨2559715775398719280501463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706477183599146187000975 2559715775398719280501463)
          ·
            refine ⟨3839573663098078920752195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559715775398719280501463 3839573663098078920752195)
            ·
              refine ⟨5759360494647118381128293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839573663098078920752195 5759360494647118381128293)
              ·
                refine ⟨1079880092746334696461555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5759360494647118381128293 1079880092746334696461555)
                ·
                  refine ⟨1619820139119502044692333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079880092746334696461555 1619820139119502044692333)
                  ·
                    refine ⟨607432552169813266759625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1619820139119502044692333 607432552169813266759625)
                    ·
                      refine ⟨455574414127359950069719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607432552169813266759625 455574414127359950069719)
                      ·
                        rfl

theorem cell23_887228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_887228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887228 prefixEnd_887228 := by exact prefixLift 887228
  have htrace : WordTrace (prefixWord ++ tailWord_887228) baseStart_887228 baseEnd_887228 := by
    simpa [prefixWord, tailWord_887228, baseEnd_887228] using wordTrace_append hprefix tailTrace_887228
  have hstable : (prefixWord ++ tailWord_887228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887228).length < 2 ^ (prefixWord ++ tailWord_887228).sum := by decide
  have hdescent : baseEnd_887228 < baseStart_887228 := by decide
  rcases family_descends (prefixWord ++ tailWord_887228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887241 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 4, 2, 2]
def baseStart_887241 : Nat := 118140960795 + 887241 * 2 ^ 59
def prefixEnd_887241 : Nat := 4983230072969 + 3 ^ 40 * 887241 * 2
def baseEnd_887241 : Nat := 455581089375868399207159

theorem tailTrace_887241 : CollatzResearch.WordTrace tailWord_887241 prefixEnd_887241 455581089375868399207159 := by
  unfold tailWord_887241
  simp only [CollatzResearch.WordTrace]
  refine ⟨32360337778684860544093577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21573558519123240362729051 32360337778684860544093577)
  ·
    refine ⟨24270253334013645408070183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32360337778684860544093577 24270253334013645408070183)
    ·
      refine ⟨36405380001020468112105275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24270253334013645408070183 36405380001020468112105275)
      ·
        refine ⟨54608070001530702168157913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36405380001020468112105275 54608070001530702168157913)
        ·
          refine ⟨40956052501148026626118435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54608070001530702168157913 40956052501148026626118435)
          ·
            refine ⟨61434078751722039939177653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40956052501148026626118435 61434078751722039939177653)
            ·
              refine ⟨5759444882973941244297905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61434078751722039939177653 5759444882973941244297905)
              ·
                refine ⟨4319583662230455933223429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759444882973941244297905 4319583662230455933223429)
                ·
                  refine ⟨809921936668210487479393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4319583662230455933223429 809921936668210487479393)
                  ·
                    refine ⟨607441452501157865609545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809921936668210487479393 607441452501157865609545)
                    ·
                      refine ⟨455581089375868399207159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607441452501157865609545 455581089375868399207159)
                      ·
                        rfl

theorem cell23_887241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2, 2].length) (baseStart_887241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887241 prefixEnd_887241 := by exact prefixLift 887241
  have htrace : WordTrace (prefixWord ++ tailWord_887241) baseStart_887241 baseEnd_887241 := by
    simpa [prefixWord, tailWord_887241, baseEnd_887241] using wordTrace_append hprefix tailTrace_887241
  have hstable : (prefixWord ++ tailWord_887241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887241).length < 2 ^ (prefixWord ++ tailWord_887241).sum := by decide
  have hdescent : baseEnd_887241 < baseStart_887241 := by decide
  rcases family_descends (prefixWord ++ tailWord_887241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887257 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_887257 : Nat := 118140960795 + 887257 * 2 ^ 59
def prefixEnd_887257 : Nat := 4983230072969 + 3 ^ 40 * 887257 * 2
def baseEnd_887257 : Nat := 455589305066340336607085

theorem tailTrace_887257 : CollatzResearch.WordTrace tailWord_887257 prefixEnd_887257 455589305066340336607085 := by
  unfold tailWord_887257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32360921346626895276676025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21573947564417930184450683 32360921346626895276676025)
  ·
    refine ⟨24270691009970171457507019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32360921346626895276676025 24270691009970171457507019)
    ·
      refine ⟨36406036514955257186260529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24270691009970171457507019 36406036514955257186260529)
      ·
        refine ⟨27304527386216442889695397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36406036514955257186260529 27304527386216442889695397)
        ·
          refine ⟨5119598884915583041817887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27304527386216442889695397 5119598884915583041817887)
          ·
            refine ⟨7679398327373374562726831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119598884915583041817887 7679398327373374562726831)
            ·
              refine ⟨11519097491060061844090247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679398327373374562726831 11519097491060061844090247)
              ·
                refine ⟨17278646236590092766135371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519097491060061844090247 17278646236590092766135371)
                ·
                  refine ⟨25917969354885139149203057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17278646236590092766135371 25917969354885139149203057)
                  ·
                    refine ⟨19438477016163854361902293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25917969354885139149203057 19438477016163854361902293)
                    ·
                      refine ⟨455589305066340336607085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19438477016163854361902293 455589305066340336607085)
                      ·
                        rfl

theorem cell23_887257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_887257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887257 prefixEnd_887257 := by exact prefixLift 887257
  have htrace : WordTrace (prefixWord ++ tailWord_887257) baseStart_887257 baseEnd_887257 := by
    simpa [prefixWord, tailWord_887257, baseEnd_887257] using wordTrace_append hprefix tailTrace_887257
  have hstable : (prefixWord ++ tailWord_887257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887257).length < 2 ^ (prefixWord ++ tailWord_887257).sum := by decide
  have hdescent : baseEnd_887257 < baseStart_887257 := by decide
  rcases family_descends (prefixWord ++ tailWord_887257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887258 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_887258 : Nat := 118140960795 + 887258 * 2 ^ 59
def prefixEnd_887258 : Nat := 4983230072969 + 3 ^ 40 * 887258 * 2
def baseEnd_887258 : Nat := 455589818546994832694581

theorem tailTrace_887258 : CollatzResearch.WordTrace tailWord_887258 prefixEnd_887258 455589818546994832694581 := by
  unfold tailWord_887258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090239454905818111865607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21573971879748848298308285 8090239454905818111865607)
  ·
    refine ⟨12135359182358727167798411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8090239454905818111865607 12135359182358727167798411)
    ·
      refine ⟨18203038773538090751697617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12135359182358727167798411 18203038773538090751697617)
      ·
        refine ⟨13652279080153568063773213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18203038773538090751697617 13652279080153568063773213)
        ·
          refine ⟨5119604655057588023914955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13652279080153568063773213 5119604655057588023914955)
          ·
            refine ⟨7679406982586382035872433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119604655057588023914955 7679406982586382035872433)
            ·
              refine ⟨5759555236939786526904325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7679406982586382035872433 5759555236939786526904325)
              ·
                refine ⟨1079916606926209973794561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5759555236939786526904325 1079916606926209973794561)
                ·
                  refine ⟨809937455194657480345921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079916606926209973794561 809937455194657480345921)
                  ·
                    refine ⟨607453091395993110259441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809937455194657480345921 607453091395993110259441)
                    ·
                      refine ⟨455589818546994832694581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607453091395993110259441 455589818546994832694581)
                      ·
                        rfl

theorem cell23_887258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_887258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887258 prefixEnd_887258 := by exact prefixLift 887258
  have htrace : WordTrace (prefixWord ++ tailWord_887258) baseStart_887258 baseEnd_887258 := by
    simpa [prefixWord, tailWord_887258, baseEnd_887258] using wordTrace_append hprefix tailTrace_887258
  have hstable : (prefixWord ++ tailWord_887258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887258).length < 2 ^ (prefixWord ++ tailWord_887258).sum := by decide
  have hdescent : baseEnd_887258 < baseStart_887258 := by decide
  rcases family_descends (prefixWord ++ tailWord_887258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887309 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_887309 : Nat := 118140960795 + 887309 * 2 ^ 59
def prefixEnd_887309 : Nat := 4983230072969 + 3 ^ 40 * 887309 * 2
def baseEnd_887309 : Nat := 455616006060374133156847

theorem tailTrace_887309 : CollatzResearch.WordTrace tailWord_887309 prefixEnd_887309 455616006060374133156847 := by
  unfold tailWord_887309
  simp only [CollatzResearch.WordTrace]
  refine ⟨32362817942438508157568981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21575211961625672105045987 32362817942438508157568981)
  ·
    refine ⟨758503545525902534943023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32362817942438508157568981 758503545525902534943023)
    ·
      refine ⟨1137755318288853802414535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758503545525902534943023 1137755318288853802414535)
      ·
        refine ⟨1706632977433280703621803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137755318288853802414535 1706632977433280703621803)
        ·
          refine ⟨2559949466149921055432705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706632977433280703621803 2559949466149921055432705)
          ·
            refine ⟨1919962099612440791574529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559949466149921055432705 1919962099612440791574529)
            ·
              refine ⟨1439971574709330593680897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919962099612440791574529 1439971574709330593680897)
              ·
                refine ⟨1079978681031997945260673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439971574709330593680897 1079978681031997945260673)
                ·
                  refine ⟨809984010773998458945505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079978681031997945260673 809984010773998458945505)
                  ·
                    refine ⟨607488008080498844209129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 809984010773998458945505 607488008080498844209129)
                    ·
                      refine ⟨455616006060374133156847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607488008080498844209129 455616006060374133156847)
                      ·
                        rfl

theorem cell23_887309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_887309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887309 prefixEnd_887309 := by exact prefixLift 887309
  have htrace : WordTrace (prefixWord ++ tailWord_887309) baseStart_887309 baseEnd_887309 := by
    simpa [prefixWord, tailWord_887309, baseEnd_887309] using wordTrace_append hprefix tailTrace_887309
  have hstable : (prefixWord ++ tailWord_887309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887309).length < 2 ^ (prefixWord ++ tailWord_887309).sum := by decide
  have hdescent : baseEnd_887309 < baseStart_887309 := by decide
  rcases family_descends (prefixWord ++ tailWord_887309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887331 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 6, 2]
def baseStart_887331 : Nat := 118140960795 + 887331 * 2 ^ 59
def prefixEnd_887331 : Nat := 4983230072969 + 3 ^ 40 * 887331 * 2
def baseEnd_887331 : Nat := 455627302634773047081745

theorem tailTrace_887331 : CollatzResearch.WordTrace tailWord_887331 prefixEnd_887331 455627302634773047081745 := by
  unfold tailWord_887331
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363620348358805914869847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21575746898905870609913231 32363620348358805914869847)
  ·
    refine ⟨48545430522538208872304771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32363620348358805914869847 48545430522538208872304771)
    ·
      refine ⟨72818145783807313308457157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48545430522538208872304771 72818145783807313308457157)
      ·
        refine ⟨13653402334463871245335717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72818145783807313308457157 13653402334463871245335717)
        ·
          refine ⟨2560012937711975858500447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13653402334463871245335717 2560012937711975858500447)
          ·
            refine ⟨3840019406567963787750671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560012937711975858500447 3840019406567963787750671)
            ·
              refine ⟨5760029109851945681626007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840019406567963787750671 5760029109851945681626007)
              ·
                refine ⟨8640043664777918522439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760029109851945681626007 8640043664777918522439011)
                ·
                  refine ⟨12960065497166877783658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640043664777918522439011 12960065497166877783658517)
                  ·
                    refine ⟨607503070179697396108993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12960065497166877783658517 607503070179697396108993)
                    ·
                      refine ⟨455627302634773047081745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607503070179697396108993 455627302634773047081745)
                      ·
                        rfl

theorem cell23_887331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_887331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887331 prefixEnd_887331 := by exact prefixLift 887331
  have htrace : WordTrace (prefixWord ++ tailWord_887331) baseStart_887331 baseEnd_887331 := by
    simpa [prefixWord, tailWord_887331, baseEnd_887331] using wordTrace_append hprefix tailTrace_887331
  have hstable : (prefixWord ++ tailWord_887331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887331).length < 2 ^ (prefixWord ++ tailWord_887331).sum := by decide
  have hdescent : baseEnd_887331 < baseStart_887331 := by decide
  rcases family_descends (prefixWord ++ tailWord_887331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887374 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_887374 : Nat := 118140960795 + 887374 * 2 ^ 59
def prefixEnd_887374 : Nat := 4983230072969 + 3 ^ 40 * 887374 * 2
def baseEnd_887374 : Nat := 455649382302916378844047

theorem tailTrace_887374 : CollatzResearch.WordTrace tailWord_887374 prefixEnd_887374 455649382302916378844047 := by
  unfold tailWord_887374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045648585900378032335647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21576792458135349505790117 4045648585900378032335647)
  ·
    refine ⟨6068472878850567048503471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4045648585900378032335647 6068472878850567048503471)
    ·
      refine ⟨9102709318275850572755207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068472878850567048503471 9102709318275850572755207)
      ·
        refine ⟨13654063977413775859132811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102709318275850572755207 13654063977413775859132811)
        ·
          refine ⟨20481095966120663788699217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13654063977413775859132811 20481095966120663788699217)
          ·
            refine ⟨15360821974590497841524413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20481095966120663788699217 15360821974590497841524413)
            ·
              refine ⟨5760308240471436690571655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15360821974590497841524413 5760308240471436690571655)
              ·
                refine ⟨8640462360707155035857483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760308240471436690571655 8640462360707155035857483)
                ·
                  refine ⟨12960693541060732553786225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640462360707155035857483 12960693541060732553786225)
                  ·
                    refine ⟨9720520155795549415339669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12960693541060732553786225 9720520155795549415339669)
                    ·
                      refine ⟨455649382302916378844047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9720520155795549415339669 455649382302916378844047)
                      ·
                        rfl

theorem cell23_887374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_887374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887374 prefixEnd_887374 := by exact prefixLift 887374
  have htrace : WordTrace (prefixWord ++ tailWord_887374) baseStart_887374 baseEnd_887374 := by
    simpa [prefixWord, tailWord_887374, baseEnd_887374] using wordTrace_append hprefix tailTrace_887374
  have hstable : (prefixWord ++ tailWord_887374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887374).length < 2 ^ (prefixWord ++ tailWord_887374).sum := by decide
  have hdescent : baseEnd_887374 < baseStart_887374 := by decide
  rcases family_descends (prefixWord ++ tailWord_887374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887384 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_887384 : Nat := 118140960795 + 887384 * 2 ^ 59
def prefixEnd_887384 : Nat := 4983230072969 + 3 ^ 40 * 887384 * 2
def baseEnd_887384 : Nat := 151884839036487113239667

theorem tailTrace_887384 : CollatzResearch.WordTrace tailWord_887384 prefixEnd_887384 151884839036487113239667 := by
  unfold tailWord_887384
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182776708583397983274603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21577035611444530644366137 16182776708583397983274603)
  ·
    refine ⟨24274165062875096974911905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16182776708583397983274603 24274165062875096974911905)
    ·
      refine ⟨18205623797156322731183929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24274165062875096974911905 18205623797156322731183929)
      ·
        refine ⟨13654217847867242048387947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18205623797156322731183929 13654217847867242048387947)
        ·
          refine ⟨20481326771800863072581921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13654217847867242048387947 20481326771800863072581921)
          ·
            refine ⟨15360995078850647304436441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20481326771800863072581921 15360995078850647304436441)
            ·
              refine ⟨11520746309137985478327331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15360995078850647304436441 11520746309137985478327331)
              ·
                refine ⟨17281119463706978217490997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520746309137985478327331 17281119463706978217490997)
                ·
                  refine ⟨1620104949722529207889781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17281119463706978217490997 1620104949722529207889781)
                  ·
                    refine ⟨151884839036487113239667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1620104949722529207889781 151884839036487113239667)
                    ·
                      rfl

theorem cell23_887384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_887384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887384 prefixEnd_887384 := by exact prefixLift 887384
  have htrace : WordTrace (prefixWord ++ tailWord_887384) baseStart_887384 baseEnd_887384 := by
    simpa [prefixWord, tailWord_887384, baseEnd_887384] using wordTrace_append hprefix tailTrace_887384
  have hstable : (prefixWord ++ tailWord_887384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887384).length < 2 ^ (prefixWord ++ tailWord_887384).sum := by decide
  have hdescent : baseEnd_887384 < baseStart_887384 := by decide
  rcases family_descends (prefixWord ++ tailWord_887384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887415 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_887415 : Nat := 118140960795 + 887415 * 2 ^ 59
def prefixEnd_887415 : Nat := 4983230072969 + 3 ^ 40 * 887415 * 2
def baseEnd_887415 : Nat := 455670435009750718431359

theorem tailTrace_887415 : CollatzResearch.WordTrace tailWord_887415 prefixEnd_887415 455670435009750718431359 := by
  unfold tailWord_887415
  simp only [CollatzResearch.WordTrace]
  refine ⟨32366684080054488260927699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21577789386702992173951799 32366684080054488260927699)
  ·
    refine ⟨48550026120081732391391549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32366684080054488260927699 48550026120081732391391549)
    ·
      refine ⟨18206259795030649646771831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48550026120081732391391549 18206259795030649646771831)
      ·
        refine ⟨27309389692545974470157747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18206259795030649646771831 27309389692545974470157747)
        ·
          refine ⟨40964084538818961705236621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27309389692545974470157747 40964084538818961705236621)
          ·
            refine ⟨15361531702057110639463733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40964084538818961705236621 15361531702057110639463733)
            ·
              refine ⟨1440143597067854122449725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15361531702057110639463733 1440143597067854122449725)
              ·
                refine ⟨540053848900445295918647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1440143597067854122449725 540053848900445295918647)
                ·
                  refine ⟨810080773350667943877971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540053848900445295918647 810080773350667943877971)
                  ·
                    refine ⟨1215121160026001915816957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 810080773350667943877971 1215121160026001915816957)
                    ·
                      refine ⟨455670435009750718431359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215121160026001915816957 455670435009750718431359)
                      ·
                        rfl

theorem cell23_887415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_887415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887415 prefixEnd_887415 := by exact prefixLift 887415
  have htrace : WordTrace (prefixWord ++ tailWord_887415) baseStart_887415 baseEnd_887415 := by
    simpa [prefixWord, tailWord_887415, baseEnd_887415] using wordTrace_append hprefix tailTrace_887415
  have hstable : (prefixWord ++ tailWord_887415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887415).length < 2 ^ (prefixWord ++ tailWord_887415).sum := by decide
  have hdescent : baseEnd_887415 < baseStart_887415 := by decide
  rcases family_descends (prefixWord ++ tailWord_887415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887426 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_887426 : Nat := 118140960795 + 887426 * 2 ^ 59
def prefixEnd_887426 : Nat := 4983230072969 + 3 ^ 40 * 887426 * 2
def baseEnd_887426 : Nat := 151892027765650058464603

theorem tailTrace_887426 : CollatzResearch.WordTrace tailWord_887426 prefixEnd_887426 151892027765650058464603 := by
  unfold tailWord_887426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091771320753659284894533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21578056855343091426385421 8091771320753659284894533)
  ·
    refine ⟨1517207122641311115917725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8091771320753659284894533 1517207122641311115917725)
    ·
      refine ⟨568952670990491668469147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517207122641311115917725 568952670990491668469147)
      ·
        refine ⟨853429006485737502703721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568952670990491668469147 853429006485737502703721)
        ·
          refine ⟨640071754864303127027791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853429006485737502703721 640071754864303127027791)
          ·
            refine ⟨960107632296454690541687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640071754864303127027791 960107632296454690541687)
            ·
              refine ⟨1440161448444682035812531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960107632296454690541687 1440161448444682035812531)
              ·
                refine ⟨2160242172667023053718797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440161448444682035812531 2160242172667023053718797)
                ·
                  refine ⟨810090814750133645144549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2160242172667023053718797 810090814750133645144549)
                  ·
                    refine ⟨151892027765650058464603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810090814750133645144549 151892027765650058464603)
                    ·
                      rfl

theorem cell23_887426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_887426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887426 prefixEnd_887426 := by exact prefixLift 887426
  have htrace : WordTrace (prefixWord ++ tailWord_887426) baseStart_887426 baseEnd_887426 := by
    simpa [prefixWord, tailWord_887426, baseEnd_887426] using wordTrace_append hprefix tailTrace_887426
  have hstable : (prefixWord ++ tailWord_887426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887426).length < 2 ^ (prefixWord ++ tailWord_887426).sum := by decide
  have hdescent : baseEnd_887426 < baseStart_887426 := by decide
  rcases family_descends (prefixWord ++ tailWord_887426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887431 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 4, 4]
def baseStart_887431 : Nat := 118140960795 + 887431 * 2 ^ 59
def prefixEnd_887431 : Nat := 4983230072969 + 3 ^ 40 * 887431 * 2
def baseEnd_887431 : Nat := 151892883566740885277095

theorem tailTrace_887431 : CollatzResearch.WordTrace tailWord_887431 prefixEnd_887431 151892883566740885277095 := by
  unfold tailWord_887431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367267647996522993510147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21578178431997681995673431 32367267647996522993510147)
  ·
    refine ⟨48550901471994784490265221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32367267647996522993510147 48550901471994784490265221)
    ·
      refine ⟨9103294025999022091924729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48550901471994784490265221 9103294025999022091924729)
      ·
        refine ⟨6827470519499266568943547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103294025999022091924729 6827470519499266568943547)
        ·
          refine ⟨10241205779248899853415321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827470519499266568943547 10241205779248899853415321)
          ·
            refine ⟨7680904334436674890061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10241205779248899853415321 7680904334436674890061491)
            ·
              refine ⟨11521356501655012335092237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680904334436674890061491 11521356501655012335092237)
              ·
                refine ⟨4320508688120629625659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11521356501655012335092237 4320508688120629625659589)
                ·
                  refine ⟨810095379022618054811173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4320508688120629625659589 810095379022618054811173)
                  ·
                    refine ⟨151892883566740885277095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810095379022618054811173 151892883566740885277095)
                    ·
                      rfl

theorem cell23_887431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_887431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887431 prefixEnd_887431 := by exact prefixLift 887431
  have htrace : WordTrace (prefixWord ++ tailWord_887431) baseStart_887431 baseEnd_887431 := by
    simpa [prefixWord, tailWord_887431, baseEnd_887431] using wordTrace_append hprefix tailTrace_887431
  have hstable : (prefixWord ++ tailWord_887431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887431).length < 2 ^ (prefixWord ++ tailWord_887431).sum := by decide
  have hdescent : baseEnd_887431 < baseStart_887431 := by decide
  rcases family_descends (prefixWord ++ tailWord_887431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887448 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_887448 : Nat := 118140960795 + 887448 * 2 ^ 59
def prefixEnd_887448 : Nat := 4983230072969 + 3 ^ 40 * 887448 * 2
def baseEnd_887448 : Nat := 151895793290449696439569

theorem tailTrace_887448 : CollatzResearch.WordTrace tailWord_887448 prefixEnd_887448 151895793290449696439569 := by
  unfold tailWord_887448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183943844467467448439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21578591792623289931252665 16183943844467467448439499)
  ·
    refine ⟨24275915766701201172659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16183943844467467448439499 24275915766701201172659249)
    ·
      refine ⟨18206936825025900879494437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24275915766701201172659249 18206936825025900879494437)
      ·
        refine ⟨3413800654692356414905207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18206936825025900879494437 3413800654692356414905207)
        ·
          refine ⟨5120700982038534622357811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413800654692356414905207 5120700982038534622357811)
          ·
            refine ⟨7681051473057801933536717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120700982038534622357811 7681051473057801933536717)
            ·
              refine ⟨2880394302396675725076269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681051473057801933536717 2880394302396675725076269)
              ·
                refine ⟨1080147863398753396903601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2880394302396675725076269 1080147863398753396903601)
                ·
                  refine ⟨810110897549065047677701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080147863398753396903601 810110897549065047677701)
                  ·
                    refine ⟨151895793290449696439569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810110897549065047677701 151895793290449696439569)
                    ·
                      rfl

theorem cell23_887448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_887448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887448 prefixEnd_887448 := by exact prefixLift 887448
  have htrace : WordTrace (prefixWord ++ tailWord_887448) baseStart_887448 baseEnd_887448 := by
    simpa [prefixWord, tailWord_887448, baseEnd_887448] using wordTrace_append hprefix tailTrace_887448
  have hstable : (prefixWord ++ tailWord_887448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887448).length < 2 ^ (prefixWord ++ tailWord_887448).sum := by decide
  have hdescent : baseEnd_887448 < baseStart_887448 := by decide
  rcases family_descends (prefixWord ++ tailWord_887448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887471 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_887471 : Nat := 118140960795 + 887471 * 2 ^ 59
def prefixEnd_887471 : Nat := 4983230072969 + 3 ^ 40 * 887471 * 2
def baseEnd_887471 : Nat := 455699189926402499331101

theorem tailTrace_887471 : CollatzResearch.WordTrace tailWord_887471 prefixEnd_887471 455699189926402499331101 := by
  unfold tailWord_887471
  simp only [CollatzResearch.WordTrace]
  refine ⟨32368726567851609824966267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21579151045234406549977511 32368726567851609824966267)
  ·
    refine ⟨48553089851777414737449401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32368726567851609824966267 48553089851777414737449401)
    ·
      refine ⟨36414817388833061053087051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48553089851777414737449401 36414817388833061053087051)
      ·
        refine ⟨54622226083249591579630577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36414817388833061053087051 54622226083249591579630577)
        ·
          refine ⟨40966669562437193684722933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54622226083249591579630577 40966669562437193684722933)
          ·
            refine ⟨3840625271478486907942775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40966669562437193684722933 3840625271478486907942775)
            ·
              refine ⟨5760937907217730361914163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840625271478486907942775 5760937907217730361914163)
              ·
                refine ⟨8641406860826595542871245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760937907217730361914163 8641406860826595542871245)
                ·
                  refine ⟨3240527572809973328576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8641406860826595542871245 3240527572809973328576717)
                  ·
                    refine ⟨1215197839803739998216269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240527572809973328576717 1215197839803739998216269)
                    ·
                      refine ⟨455699189926402499331101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215197839803739998216269 455699189926402499331101)
                      ·
                        rfl

theorem cell23_887471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_887471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887471 prefixEnd_887471 := by exact prefixLift 887471
  have htrace : WordTrace (prefixWord ++ tailWord_887471) baseStart_887471 baseEnd_887471 := by
    simpa [prefixWord, tailWord_887471, baseEnd_887471] using wordTrace_append hprefix tailTrace_887471
  have hstable : (prefixWord ++ tailWord_887471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887471).length < 2 ^ (prefixWord ++ tailWord_887471).sum := by decide
  have hdescent : baseEnd_887471 < baseStart_887471 := by decide
  rcases family_descends (prefixWord ++ tailWord_887471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887475 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 1, 2, 3]
def baseStart_887475 : Nat := 118140960795 + 887475 * 2 ^ 59
def prefixEnd_887475 : Nat := 4983230072969 + 3 ^ 40 * 887475 * 2
def baseEnd_887475 : Nat := 455701243849020483681083

theorem tailTrace_887475 : CollatzResearch.WordTrace tailWord_887475 prefixEnd_887475 455701243849020483681083 := by
  unfold tailWord_887475
  simp only [CollatzResearch.WordTrace]
  refine ⟨32368872459837118508111879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21579248306558079005407919 32368872459837118508111879)
  ·
    refine ⟨48553308689755677762167819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32368872459837118508111879 48553308689755677762167819)
    ·
      refine ⟨72829963034633516643251729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48553308689755677762167819 72829963034633516643251729)
      ·
        refine ⟨54622472275975137482438797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72829963034633516643251729 54622472275975137482438797)
        ·
          refine ⟨20483427103490676555914549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54622472275975137482438797 20483427103490676555914549)
          ·
            refine ⟨1920321290952250927116989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20483427103490676555914549 1920321290952250927116989)
            ·
              refine ⟨720120484107094097668871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920321290952250927116989 720120484107094097668871)
              ·
                refine ⟨1080180726160641146503307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720120484107094097668871 1080180726160641146503307)
                ·
                  refine ⟨1620271089240961719754961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080180726160641146503307 1620271089240961719754961)
                  ·
                    refine ⟨1215203316930721289816221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1620271089240961719754961 1215203316930721289816221)
                    ·
                      refine ⟨455701243849020483681083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215203316930721289816221 455701243849020483681083)
                      ·
                        rfl

theorem cell23_887475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 2, 3].length) (baseStart_887475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887475 prefixEnd_887475 := by exact prefixLift 887475
  have htrace : WordTrace (prefixWord ++ tailWord_887475) baseStart_887475 baseEnd_887475 := by
    simpa [prefixWord, tailWord_887475, baseEnd_887475] using wordTrace_append hprefix tailTrace_887475
  have hstable : (prefixWord ++ tailWord_887475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887475).length < 2 ^ (prefixWord ++ tailWord_887475).sum := by decide
  have hdescent : baseEnd_887475 < baseStart_887475 := by decide
  rcases family_descends (prefixWord ++ tailWord_887475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887478 : List Nat := [5, 1, 3, 1, 2, 11]
def baseStart_887478 : Nat := 118140960795 + 887478 * 2 ^ 59
def prefixEnd_887478 : Nat := 4983230072969 + 3 ^ 40 * 887478 * 2
def baseEnd_887478 : Nat := 1875320099962897003883

theorem tailTrace_887478 : CollatzResearch.WordTrace tailWord_887478 prefixEnd_887478 1875320099962897003883 := by
  unfold tailWord_887478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023061367426640626279443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21579321252550833346980725 2023061367426640626279443)
  ·
    refine ⟨3034592051139960939419165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023061367426640626279443 3034592051139960939419165)
    ·
      refine ⟨1137972019177485352282187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3034592051139960939419165 1137972019177485352282187)
      ·
        refine ⟨1706958028766228028423281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137972019177485352282187 1706958028766228028423281)
        ·
          refine ⟨1280218521574671021317461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706958028766228028423281 1280218521574671021317461)
          ·
            refine ⟨1875320099962897003883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1280218521574671021317461 1875320099962897003883)
            ·
              rfl

theorem cell23_887478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 11].length) (baseStart_887478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887478 prefixEnd_887478 := by exact prefixLift 887478
  have htrace : WordTrace (prefixWord ++ tailWord_887478) baseStart_887478 baseEnd_887478 := by
    simpa [prefixWord, tailWord_887478, baseEnd_887478] using wordTrace_append hprefix tailTrace_887478
  have hstable : (prefixWord ++ tailWord_887478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887478).length < 2 ^ (prefixWord ++ tailWord_887478).sum := by decide
  have hdescent : baseEnd_887478 < baseStart_887478 := by decide
  rcases family_descends (prefixWord ++ tailWord_887478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887613 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_887613 : Nat := 118140960795 + 887613 * 2 ^ 59
def prefixEnd_887613 : Nat := 4983230072969 + 3 ^ 40 * 887613 * 2
def baseEnd_887613 : Nat := 455772104179340943755449

theorem tailTrace_887613 : CollatzResearch.WordTrace tailWord_887613 prefixEnd_887613 455772104179340943755449 := by
  unfold tailWord_887613
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373905733337168076635493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21582603822224778717756995 32373905733337168076635493)
  ·
    refine ⟨6070107325000719014369155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32373905733337168076635493 6070107325000719014369155)
    ·
      refine ⟨9105160987501078521553733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070107325000719014369155 9105160987501078521553733)
      ·
        refine ⟨1707217685156452222791325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9105160987501078521553733 1707217685156452222791325)
        ·
          refine ⟨640206631933669583546747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1707217685156452222791325 640206631933669583546747)
          ·
            refine ⟨960309947900504375320121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640206631933669583546747 960309947900504375320121)
            ·
              refine ⟨720232460925378281490091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960309947900504375320121 720232460925378281490091)
              ·
                refine ⟨1080348691388067422235137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720232460925378281490091 1080348691388067422235137)
                ·
                  refine ⟨810261518541050566676353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080348691388067422235137 810261518541050566676353)
                  ·
                    refine ⟨607696138905787925007265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 810261518541050566676353 607696138905787925007265)
                    ·
                      refine ⟨455772104179340943755449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607696138905787925007265 455772104179340943755449)
                      ·
                        rfl

theorem cell23_887613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_887613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887613 prefixEnd_887613 := by exact prefixLift 887613
  have htrace : WordTrace (prefixWord ++ tailWord_887613) baseStart_887613 baseEnd_887613 := by
    simpa [prefixWord, tailWord_887613, baseEnd_887613] using wordTrace_append hprefix tailTrace_887613
  have hstable : (prefixWord ++ tailWord_887613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887613).length < 2 ^ (prefixWord ++ tailWord_887613).sum := by decide
  have hdescent : baseEnd_887613 < baseStart_887613 := by decide
  rcases family_descends (prefixWord ++ tailWord_887613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887655 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_887655 : Nat := 118140960795 + 887655 * 2 ^ 59
def prefixEnd_887655 : Nat := 4983230072969 + 3 ^ 40 * 887655 * 2
def baseEnd_887655 : Nat := 455793670366829779430255

theorem tailTrace_887655 : CollatzResearch.WordTrace tailWord_887655 prefixEnd_887655 455793670366829779430255 := by
  unfold tailWord_887655
  simp only [CollatzResearch.WordTrace]
  refine ⟨32375437599185009249664419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21583625066123339499776279 32375437599185009249664419)
  ·
    refine ⟨48563156398777513874496629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32375437599185009249664419 48563156398777513874496629)
    ·
      refine ⟨4552795912385391925734059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48563156398777513874496629 4552795912385391925734059)
      ·
        refine ⟨6829193868578087888601089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552795912385391925734059 6829193868578087888601089)
        ·
          refine ⟨5121895401433565916450817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829193868578087888601089 5121895401433565916450817)
          ·
            refine ⟨3841421551075174437338113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121895401433565916450817 3841421551075174437338113)
            ·
              refine ⟨2881066163306380828003585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841421551075174437338113 2881066163306380828003585)
              ·
                refine ⟨2160799622479785621002689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881066163306380828003585 2160799622479785621002689)
                ·
                  refine ⟨1620599716859839215752017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160799622479785621002689 1620599716859839215752017)
                  ·
                    refine ⟨1215449787644879411814013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1620599716859839215752017 1215449787644879411814013)
                    ·
                      refine ⟨455793670366829779430255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215449787644879411814013 455793670366829779430255)
                      ·
                        rfl

theorem cell23_887655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_887655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887655 prefixEnd_887655 := by exact prefixLift 887655
  have htrace : WordTrace (prefixWord ++ tailWord_887655) baseStart_887655 baseEnd_887655 := by
    simpa [prefixWord, tailWord_887655, baseEnd_887655] using wordTrace_append hprefix tailTrace_887655
  have hstable : (prefixWord ++ tailWord_887655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887655).length < 2 ^ (prefixWord ++ tailWord_887655).sum := by decide
  have hdescent : baseEnd_887655 < baseStart_887655 := by decide
  rcases family_descends (prefixWord ++ tailWord_887655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887685 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_887685 : Nat := 118140960795 + 887685 * 2 ^ 59
def prefixEnd_887685 : Nat := 4983230072969 + 3 ^ 40 * 887685 * 2
def baseEnd_887685 : Nat := 455809074786464662055117

theorem tailTrace_887685 : CollatzResearch.WordTrace tailWord_887685 prefixEnd_887685 455809074786464662055117 := by
  unfold tailWord_887685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376531789076324373256509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21584354526050882915504339 32376531789076324373256509)
  ·
    refine ⟨12141199420903621639971191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32376531789076324373256509 12141199420903621639971191)
    ·
      refine ⟨18211799131355432459956787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141199420903621639971191 18211799131355432459956787)
      ·
        refine ⟨27317698697033148689935181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18211799131355432459956787 27317698697033148689935181)
        ·
          refine ⟨10244137011387430758725693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27317698697033148689935181 10244137011387430758725693)
          ·
            refine ⟨3841551379270286534522135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10244137011387430758725693 3841551379270286534522135)
            ·
              refine ⟨5762327068905429801783203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841551379270286534522135 5762327068905429801783203)
              ·
                refine ⟨8643490603358144702674805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762327068905429801783203 8643490603358144702674805)
                ·
                  refine ⟨810327244064826065875763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8643490603358144702674805 810327244064826065875763)
                  ·
                    refine ⟨1215490866097239098813645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 810327244064826065875763 1215490866097239098813645)
                    ·
                      refine ⟨455809074786464662055117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215490866097239098813645 455809074786464662055117)
                      ·
                        rfl

theorem cell23_887685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_887685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887685 prefixEnd_887685 := by exact prefixLift 887685
  have htrace : WordTrace (prefixWord ++ tailWord_887685) baseStart_887685 baseEnd_887685 := by
    simpa [prefixWord, tailWord_887685, baseEnd_887685] using wordTrace_append hprefix tailTrace_887685
  have hstable : (prefixWord ++ tailWord_887685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887685).length < 2 ^ (prefixWord ++ tailWord_887685).sum := by decide
  have hdescent : baseEnd_887685 < baseStart_887685 := by decide
  rcases family_descends (prefixWord ++ tailWord_887685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887719 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_887719 : Nat := 118140960795 + 887719 * 2 ^ 59
def prefixEnd_887719 : Nat := 4983230072969 + 3 ^ 40 * 887719 * 2
def baseEnd_887719 : Nat := 455826533128717529029961

theorem tailTrace_887719 : CollatzResearch.WordTrace tailWord_887719 prefixEnd_887719 455826533128717529029961 := by
  unfold tailWord_887719
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377771870953148179994211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585181247302098786662807 32377771870953148179994211)
  ·
    refine ⟨48566657806429722269991317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32377771870953148179994211 48566657806429722269991317)
    ·
      refine ⟨2276562084676393231405843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48566657806429722269991317 2276562084676393231405843)
      ·
        refine ⟨3414843127014589847108765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276562084676393231405843 3414843127014589847108765)
        ·
          refine ⟨1280566172630471192665787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3414843127014589847108765 1280566172630471192665787)
          ·
            refine ⟨1920849258945706788998681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280566172630471192665787 1920849258945706788998681)
            ·
              refine ⟨1440636944209280091749011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920849258945706788998681 1440636944209280091749011)
              ·
                refine ⟨2160955416313920137623517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440636944209280091749011 2160955416313920137623517)
                ·
                  refine ⟨810358281117720051608819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2160955416313920137623517 810358281117720051608819)
                  ·
                    refine ⟨1215537421676580077413229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 810358281117720051608819 1215537421676580077413229)
                    ·
                      refine ⟨455826533128717529029961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1215537421676580077413229 455826533128717529029961)
                      ·
                        rfl

theorem cell23_887719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_887719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887719 prefixEnd_887719 := by exact prefixLift 887719
  have htrace : WordTrace (prefixWord ++ tailWord_887719) baseStart_887719 baseEnd_887719 := by
    simpa [prefixWord, tailWord_887719, baseEnd_887719] using wordTrace_append hprefix tailTrace_887719
  have hstable : (prefixWord ++ tailWord_887719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887719).length < 2 ^ (prefixWord ++ tailWord_887719).sum := by decide
  have hdescent : baseEnd_887719 < baseStart_887719 := by decide
  rcases family_descends (prefixWord ++ tailWord_887719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887735 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 2, 4]
def baseStart_887735 : Nat := 118140960795 + 887735 * 2 ^ 59
def prefixEnd_887735 : Nat := 4983230072969 + 3 ^ 40 * 887735 * 2
def baseEnd_887735 : Nat := 151944916273063155476629

theorem tailTrace_887735 : CollatzResearch.WordTrace tailWord_887735 prefixEnd_887735 151944916273063155476629 := by
  unfold tailWord_887735
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378355438895182912576659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585570292596788608384439 32378355438895182912576659)
  ·
    refine ⟨48567533158342774368864989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32378355438895182912576659 48567533158342774368864989)
    ·
      refine ⟨18212824934378540388324371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48567533158342774368864989 18212824934378540388324371)
      ·
        refine ⟨27319237401567810582486557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18212824934378540388324371 27319237401567810582486557)
        ·
          refine ⟨10244714025587928968432459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27319237401567810582486557 10244714025587928968432459)
          ·
            refine ⟨15367071038381893452648689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244714025587928968432459 15367071038381893452648689)
            ·
              refine ⟨11525303278786420089486517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15367071038381893452648689 11525303278786420089486517)
              ·
                refine ⟨1080497182386226883389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11525303278786420089486517 1080497182386226883389361)
                ·
                  refine ⟨810372886789670162542021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080497182386226883389361 810372886789670162542021)
                  ·
                    refine ⟨151944916273063155476629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810372886789670162542021 151944916273063155476629)
                    ·
                      rfl

theorem cell23_887735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_887735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887735 prefixEnd_887735 := by exact prefixLift 887735
  have htrace : WordTrace (prefixWord ++ tailWord_887735) baseStart_887735 baseEnd_887735 := by
    simpa [prefixWord, tailWord_887735, baseEnd_887735] using wordTrace_append hprefix tailTrace_887735
  have hstable : (prefixWord ++ tailWord_887735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887735).length < 2 ^ (prefixWord ++ tailWord_887735).sum := by decide
  have hdescent : baseEnd_887735 < baseStart_887735 := by decide
  rcases family_descends (prefixWord ++ tailWord_887735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887738 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_887738 : Nat := 118140960795 + 887738 * 2 ^ 59
def prefixEnd_887738 : Nat := 4983230072969 + 3 ^ 40 * 887738 * 2
def baseEnd_887738 : Nat := 455836289261152954692373

theorem tailTrace_887738 : CollatzResearch.WordTrace tailWord_887738 prefixEnd_887738 455836289261152954692373 := by
  unfold tailWord_887738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094616214471078606233967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21585643238589542949957245 8094616214471078606233967)
  ·
    refine ⟨12141924321706617909350951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8094616214471078606233967 12141924321706617909350951)
    ·
      refine ⟨18212886482559926864026427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141924321706617909350951 18212886482559926864026427)
      ·
        refine ⟨27319329723839890296039641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18212886482559926864026427 27319329723839890296039641)
        ·
          refine ⟨20489497292879917722029731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27319329723839890296039641 20489497292879917722029731)
          ·
            refine ⟨30734245939319876583044597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489497292879917722029731 30734245939319876583044597)
            ·
              refine ⟨2881335556811238429660431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30734245939319876583044597 2881335556811238429660431)
              ·
                refine ⟨4322003335216857644490647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881335556811238429660431 4322003335216857644490647)
                ·
                  refine ⟨6483005002825286466735971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322003335216857644490647 6483005002825286466735971)
                  ·
                    refine ⟨9724507504237929700103957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483005002825286466735971 9724507504237929700103957)
                    ·
                      refine ⟨455836289261152954692373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9724507504237929700103957 455836289261152954692373)
                      ·
                        rfl

theorem cell23_887738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_887738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887738 prefixEnd_887738 := by exact prefixLift 887738
  have htrace : WordTrace (prefixWord ++ tailWord_887738) baseStart_887738 baseEnd_887738 := by
    simpa [prefixWord, tailWord_887738, baseEnd_887738] using wordTrace_append hprefix tailTrace_887738
  have hstable : (prefixWord ++ tailWord_887738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887738).length < 2 ^ (prefixWord ++ tailWord_887738).sum := by decide
  have hdescent : baseEnd_887738 < baseStart_887738 := by decide
  rcases family_descends (prefixWord ++ tailWord_887738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887742 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_887742 : Nat := 118140960795 + 887742 * 2 ^ 59
def prefixEnd_887742 : Nat := 4983230072969 + 3 ^ 40 * 887742 * 2
def baseEnd_887742 : Nat := 455838343183770939042355

theorem tailTrace_887742 : CollatzResearch.WordTrace tailWord_887742 prefixEnd_887742 455838343183770939042355 := by
  unfold tailWord_887742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047326343733727888510185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21585740499913215405387653 4047326343733727888510185)
  ·
    refine ⟨3035494757800295916382639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4047326343733727888510185 3035494757800295916382639)
    ·
      refine ⟨4553242136700443874573959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035494757800295916382639 4553242136700443874573959)
      ·
        refine ⟨6829863205050665811860939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553242136700443874573959 6829863205050665811860939)
        ·
          refine ⟨10244794807575998717791409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829863205050665811860939 10244794807575998717791409)
          ·
            refine ⟨7683596105681999038343557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10244794807575998717791409 7683596105681999038343557)
            ·
              refine ⟨1440674269815374819689417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7683596105681999038343557 1440674269815374819689417)
              ·
                refine ⟨1080505702361531114767063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440674269815374819689417 1080505702361531114767063)
                ·
                  refine ⟨1620758553542296672150595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080505702361531114767063 1620758553542296672150595)
                  ·
                    refine ⟨2431137830313445008225893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620758553542296672150595 2431137830313445008225893)
                    ·
                      refine ⟨455838343183770939042355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2431137830313445008225893 455838343183770939042355)
                      ·
                        rfl

theorem cell23_887742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_887742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887742 prefixEnd_887742 := by exact prefixLift 887742
  have htrace : WordTrace (prefixWord ++ tailWord_887742) baseStart_887742 baseEnd_887742 := by
    simpa [prefixWord, tailWord_887742, baseEnd_887742] using wordTrace_append hprefix tailTrace_887742
  have hstable : (prefixWord ++ tailWord_887742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887742).length < 2 ^ (prefixWord ++ tailWord_887742).sum := by decide
  have hdescent : baseEnd_887742 < baseStart_887742 := by decide
  rcases family_descends (prefixWord ++ tailWord_887742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887762 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_887762 : Nat := 118140960795 + 887762 * 2 ^ 59
def prefixEnd_887762 : Nat := 4983230072969 + 3 ^ 40 * 887762 * 2
def baseEnd_887762 : Nat := 455848612796860860792263

theorem tailTrace_887762 : CollatzResearch.WordTrace tailWord_887762 prefixEnd_887762 455848612796860860792263 := by
  unfold tailWord_887762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094835052449341630952385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21586226806531577682539693 8094835052449341630952385)
  ·
    refine ⟨6071126289337006223214289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8094835052449341630952385 6071126289337006223214289)
    ·
      refine ⟨4553344717002754667410717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6071126289337006223214289 4553344717002754667410717)
      ·
        refine ⟨1707504268876033000279019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4553344717002754667410717 1707504268876033000279019)
        ·
          refine ⟨2561256403314049500418529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707504268876033000279019 2561256403314049500418529)
          ·
            refine ⟨1920942302485537125313897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561256403314049500418529 1920942302485537125313897)
            ·
              refine ⟨1440706726864152843985423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920942302485537125313897 1440706726864152843985423)
              ·
                refine ⟨2161060090296229265978135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440706726864152843985423 2161060090296229265978135)
                ·
                  refine ⟨3241590135444343898967203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161060090296229265978135 3241590135444343898967203)
                  ·
                    refine ⟨4862385203166515848450805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3241590135444343898967203 4862385203166515848450805)
                    ·
                      refine ⟨455848612796860860792263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4862385203166515848450805 455848612796860860792263)
                      ·
                        rfl

theorem cell23_887762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_887762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887762 prefixEnd_887762 := by exact prefixLift 887762
  have htrace : WordTrace (prefixWord ++ tailWord_887762) baseStart_887762 baseEnd_887762 := by
    simpa [prefixWord, tailWord_887762, baseEnd_887762] using wordTrace_append hprefix tailTrace_887762
  have hstable : (prefixWord ++ tailWord_887762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887762).length < 2 ^ (prefixWord ++ tailWord_887762).sum := by decide
  have hdescent : baseEnd_887762 < baseStart_887762 := by decide
  rcases family_descends (prefixWord ++ tailWord_887762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887765 : List Nat := [1, 3, 2, 3, 3, 2, 9]
def baseStart_887765 : Nat := 118140960795 + 887765 * 2 ^ 59
def prefixEnd_887765 : Nat := 4983230072969 + 3 ^ 40 * 887765 * 2
def baseEnd_887765 : Nat := 5627779669615115420429

theorem tailTrace_887765 : CollatzResearch.WordTrace tailWord_887765 prefixEnd_887765 5627779669615115420429 := by
  unfold tailWord_887765
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379449628786498036168749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21586299752524332024112499 32379449628786498036168749)
  ·
    refine ⟨12142293610794936763563281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32379449628786498036168749 12142293610794936763563281)
    ·
      refine ⟨9106720208096202572672461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12142293610794936763563281 9106720208096202572672461)
      ·
        refine ⟨3415020078036075964752173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9106720208096202572672461 3415020078036075964752173)
        ·
          refine ⟨1280632529263528486782065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3415020078036075964752173 1280632529263528486782065)
          ·
            refine ⟨960474396947646365086549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280632529263528486782065 960474396947646365086549)
            ·
              refine ⟨5627779669615115420429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 960474396947646365086549 5627779669615115420429)
              ·
                rfl

theorem cell23_887765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 9].length) (baseStart_887765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887765 prefixEnd_887765 := by exact prefixLift 887765
  have htrace : WordTrace (prefixWord ++ tailWord_887765) baseStart_887765 baseEnd_887765 := by
    simpa [prefixWord, tailWord_887765, baseEnd_887765] using wordTrace_append hprefix tailTrace_887765
  have hstable : (prefixWord ++ tailWord_887765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887765).length < 2 ^ (prefixWord ++ tailWord_887765).sum := by decide
  have hdescent : baseEnd_887765 < baseStart_887765 := by decide
  rcases family_descends (prefixWord ++ tailWord_887765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887845 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_887845 : Nat := 118140960795 + 887845 * 2 ^ 59
def prefixEnd_887845 : Nat := 4983230072969 + 3 ^ 40 * 887845 * 2
def baseEnd_887845 : Nat := 455891231691184036054381

theorem tailTrace_887845 : CollatzResearch.WordTrace tailWord_887845 prefixEnd_887845 455891231691184036054381 := by
  unfold tailWord_887845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382367468496671699080989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21588244978997781132720659 32382367468496671699080989)
  ·
    refine ⟨12143387800686251887155371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32382367468496671699080989 12143387800686251887155371)
    ·
      refine ⟨18215081701029377830733057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12143387800686251887155371 18215081701029377830733057)
      ·
        refine ⟨13661311275772033373049793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18215081701029377830733057 13661311275772033373049793)
        ·
          refine ⟨10245983456829025029787345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13661311275772033373049793 10245983456829025029787345)
          ·
            refine ⟨7684487592621768772340509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10245983456829025029787345 7684487592621768772340509)
            ·
              refine ⟨2881682847233163289627691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7684487592621768772340509 2881682847233163289627691)
              ·
                refine ⟨4322524270849744934441537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881682847233163289627691 4322524270849744934441537)
                ·
                  refine ⟨3241893203137308700831153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322524270849744934441537 3241893203137308700831153)
                  ·
                    refine ⟨2431419902352981525623365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3241893203137308700831153 2431419902352981525623365)
                    ·
                      refine ⟨455891231691184036054381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2431419902352981525623365 455891231691184036054381)
                      ·
                        rfl

theorem cell23_887845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_887845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887845 prefixEnd_887845 := by exact prefixLift 887845
  have htrace : WordTrace (prefixWord ++ tailWord_887845) baseStart_887845 baseEnd_887845 := by
    simpa [prefixWord, tailWord_887845, baseEnd_887845] using wordTrace_append hprefix tailTrace_887845
  have hstable : (prefixWord ++ tailWord_887845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887845).length < 2 ^ (prefixWord ++ tailWord_887845).sum := by decide
  have hdescent : baseEnd_887845 < baseStart_887845 := by decide
  rcases family_descends (prefixWord ++ tailWord_887845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887872 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 5]
def baseStart_887872 : Nat := 118140960795 + 887872 * 2 ^ 59
def prefixEnd_887872 : Nat := 4983230072969 + 3 ^ 40 * 887872 * 2
def baseEnd_887872 : Nat := 50656121740983936712973

theorem tailTrace_887872 : CollatzResearch.WordTrace tailWord_887872 prefixEnd_887872 50656121740983936712973 := by
  unfold tailWord_887872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191676119699427655156935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21588901492932570206875913 16191676119699427655156935)
  ·
    refine ⟨24287514179549141482735403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16191676119699427655156935 24287514179549141482735403)
    ·
      refine ⟨36431271269323712224103105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24287514179549141482735403 36431271269323712224103105)
      ·
        refine ⟨27323453451992784168077329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36431271269323712224103105 27323453451992784168077329)
        ·
          refine ⟨20492590088994588126057997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27323453451992784168077329 20492590088994588126057997)
          ·
            refine ⟨7684721283372970547271749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20492590088994588126057997 7684721283372970547271749)
            ·
              refine ⟨1440885240632431977613453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7684721283372970547271749 1440885240632431977613453)
              ·
                refine ⟨540331965237161991605045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1440885240632431977613453 540331965237161991605045)
                ·
                  refine ⟨50656121740983936712973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540331965237161991605045 50656121740983936712973)
                  ·
                    rfl

theorem cell23_887872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 5].length) (baseStart_887872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887872 prefixEnd_887872 := by exact prefixLift 887872
  have htrace : WordTrace (prefixWord ++ tailWord_887872) baseStart_887872 baseEnd_887872 := by
    simpa [prefixWord, tailWord_887872, baseEnd_887872] using wordTrace_append hprefix tailTrace_887872
  have hstable : (prefixWord ++ tailWord_887872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887872).length < 2 ^ (prefixWord ++ tailWord_887872).sum := by decide
  have hdescent : baseEnd_887872 < baseStart_887872 := by decide
  rcases family_descends (prefixWord ++ tailWord_887872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887892 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_887892 : Nat := 118140960795 + 887892 * 2 ^ 59
def prefixEnd_887892 : Nat := 4983230072969 + 3 ^ 40 * 887892 * 2
def baseEnd_887892 : Nat := 455915365281945352166665

theorem tailTrace_887892 : CollatzResearch.WordTrace tailWord_887892 prefixEnd_887892 455915365281945352166665 := by
  unfold tailWord_887892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192040849663199363020965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21589387799550932484027953 16192040849663199363020965)
  ·
    refine ⟨3036007659311849880566431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16192040849663199363020965 3036007659311849880566431)
    ·
      refine ⟨4554011488967774820849647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036007659311849880566431 4554011488967774820849647)
      ·
        refine ⟨6831017233451662231274471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554011488967774820849647 6831017233451662231274471)
        ·
          refine ⟨10246525850177493346911707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831017233451662231274471 10246525850177493346911707)
          ·
            refine ⟨15369788775266240020367561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246525850177493346911707 15369788775266240020367561)
            ·
              refine ⟨11527341581449680015275671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15369788775266240020367561 11527341581449680015275671)
              ·
                refine ⟨17291012372174520022913507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11527341581449680015275671 17291012372174520022913507)
                ·
                  refine ⟨25936518558261780034370261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17291012372174520022913507 25936518558261780034370261)
                  ·
                    refine ⟨607887153709260469555553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25936518558261780034370261 607887153709260469555553)
                    ·
                      refine ⟨455915365281945352166665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607887153709260469555553 455915365281945352166665)
                      ·
                        rfl

theorem cell23_887892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_887892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887892 prefixEnd_887892 := by exact prefixLift 887892
  have htrace : WordTrace (prefixWord ++ tailWord_887892) baseStart_887892 baseEnd_887892 := by
    simpa [prefixWord, tailWord_887892, baseEnd_887892] using wordTrace_append hprefix tailTrace_887892
  have hstable : (prefixWord ++ tailWord_887892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887892).length < 2 ^ (prefixWord ++ tailWord_887892).sum := by decide
  have hdescent : baseEnd_887892 < baseStart_887892 := by decide
  rcases family_descends (prefixWord ++ tailWord_887892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887905 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_887905 : Nat := 118140960795 + 887905 * 2 ^ 59
def prefixEnd_887905 : Nat := 4983230072969 + 3 ^ 40 * 887905 * 2
def baseEnd_887905 : Nat := 455922040530453801304105

theorem tailTrace_887905 : CollatzResearch.WordTrace tailWord_887905 prefixEnd_887905 455922040530453801304105 := by
  unfold tailWord_887905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32384555848279301946265169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21589703898852867964176779 32384555848279301946265169)
  ·
    refine ⟨24288416886209476459698877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32384555848279301946265169 24288416886209476459698877)
    ·
      refine ⟨9108156332328553672387079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24288416886209476459698877 9108156332328553672387079)
      ·
        refine ⟨13662234498492830508580619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108156332328553672387079 13662234498492830508580619)
        ·
          refine ⟨20493351747739245762870929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662234498492830508580619 20493351747739245762870929)
          ·
            refine ⟨15370013810804434322153197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20493351747739245762870929 15370013810804434322153197)
            ·
              refine ⟨5763755179051662870807449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15370013810804434322153197 5763755179051662870807449)
              ·
                refine ⟨4322816384288747153105587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763755179051662870807449 4322816384288747153105587)
                ·
                  refine ⟨6484224576433120729658381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322816384288747153105587 6484224576433120729658381)
                  ·
                    refine ⟨2431584216162420273621893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6484224576433120729658381 2431584216162420273621893)
                    ·
                      refine ⟨455922040530453801304105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2431584216162420273621893 455922040530453801304105)
                      ·
                        rfl

theorem cell23_887905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_887905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887905 prefixEnd_887905 := by exact prefixLift 887905
  have htrace : WordTrace (prefixWord ++ tailWord_887905) baseStart_887905 baseEnd_887905 := by
    simpa [prefixWord, tailWord_887905, baseEnd_887905] using wordTrace_append hprefix tailTrace_887905
  have hstable : (prefixWord ++ tailWord_887905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887905).length < 2 ^ (prefixWord ++ tailWord_887905).sum := by decide
  have hdescent : baseEnd_887905 < baseStart_887905 := by decide
  rcases family_descends (prefixWord ++ tailWord_887905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887922 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_887922 : Nat := 118140960795 + 887922 * 2 ^ 59
def prefixEnd_887922 : Nat := 4983230072969 + 3 ^ 40 * 887922 * 2
def baseEnd_887922 : Nat := 455930769701580234791527

theorem tailTrace_887922 : CollatzResearch.WordTrace tailWord_887922 prefixEnd_887922 455930769701580234791527 := by
  unfold tailWord_887922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096293972304428462408505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21590117259478475899756013 8096293972304428462408505)
  ·
    refine ⟨6072220479228321346806379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8096293972304428462408505 6072220479228321346806379)
    ·
      refine ⟨9108330718842482020209569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072220479228321346806379 9108330718842482020209569)
      ·
        refine ⟨6831248039131861515157177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9108330718842482020209569 6831248039131861515157177)
        ·
          refine ⟨5123436029348896136367883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6831248039131861515157177 5123436029348896136367883)
          ·
            refine ⟨7685154044023344204551825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123436029348896136367883 7685154044023344204551825)
            ·
              refine ⟨5763865533017508153413869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7685154044023344204551825 5763865533017508153413869)
              ·
                refine ⟨2161449574881565557530201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5763865533017508153413869 2161449574881565557530201)
                ·
                  refine ⟨1621087181161174168147651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161449574881565557530201 1621087181161174168147651)
                  ·
                    refine ⟨2431630771741761252221477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1621087181161174168147651 2431630771741761252221477)
                    ·
                      refine ⟨455930769701580234791527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2431630771741761252221477 455930769701580234791527)
                      ·
                        rfl

theorem cell23_887922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_887922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887922 prefixEnd_887922 := by exact prefixLift 887922
  have htrace : WordTrace (prefixWord ++ tailWord_887922) baseStart_887922 baseEnd_887922 := by
    simpa [prefixWord, tailWord_887922, baseEnd_887922] using wordTrace_append hprefix tailTrace_887922
  have hstable : (prefixWord ++ tailWord_887922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887922).length < 2 ^ (prefixWord ++ tailWord_887922).sum := by decide
  have hdescent : baseEnd_887922 < baseStart_887922 := by decide
  rcases family_descends (prefixWord ++ tailWord_887922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887945 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 8]
def baseStart_887945 : Nat := 118140960795 + 887945 * 2 ^ 59
def prefixEnd_887945 : Nat := 4983230072969 + 3 ^ 40 * 887945 * 2
def baseEnd_887945 : Nat := 50660286639625960533769

theorem tailTrace_887945 : CollatzResearch.WordTrace tailWord_887945 prefixEnd_887945 50660286639625960533769 := by
  unfold tailWord_887945
  simp only [CollatzResearch.WordTrace]
  refine ⟨32386014768134388777721289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21590676512089592518480859 32386014768134388777721289)
  ·
    refine ⟨24289511076100791583290967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32386014768134388777721289 24289511076100791583290967)
    ·
      refine ⟨36434266614151187374936451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24289511076100791583290967 36434266614151187374936451)
      ·
        refine ⟨54651399921226781062404677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36434266614151187374936451 54651399921226781062404677)
        ·
          refine ⟨10247137485230021449200877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54651399921226781062404677 10247137485230021449200877)
          ·
            refine ⟨3842676556961258043450329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10247137485230021449200877 3842676556961258043450329)
            ·
              refine ⟨2882007417720943532587747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3842676556961258043450329 2882007417720943532587747)
              ·
                refine ⟨4323011126581415298881621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882007417720943532587747 4323011126581415298881621)
                ·
                  refine ⟨50660286639625960533769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4323011126581415298881621 50660286639625960533769)
                  ·
                    rfl

theorem cell23_887945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_887945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887945 prefixEnd_887945 := by exact prefixLift 887945
  have htrace : WordTrace (prefixWord ++ tailWord_887945) baseStart_887945 baseEnd_887945 := by
    simpa [prefixWord, tailWord_887945, baseEnd_887945] using wordTrace_append hprefix tailTrace_887945
  have hstable : (prefixWord ++ tailWord_887945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887945).length < 2 ^ (prefixWord ++ tailWord_887945).sum := by decide
  have hdescent : baseEnd_887945 < baseStart_887945 := by decide
  rcases family_descends (prefixWord ++ tailWord_887945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887999 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 2, 3, 2]
def baseStart_887999 : Nat := 118140960795 + 887999 * 2 ^ 59
def prefixEnd_887999 : Nat := 4983230072969 + 3 ^ 40 * 887999 * 2
def baseEnd_887999 : Nat := 455970307711976433528673

theorem tailTrace_887999 : CollatzResearch.WordTrace tailWord_887999 prefixEnd_887999 455970307711976433528673 := by
  unfold tailWord_887999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32387984309938756000187051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21591989539959170666791367 32387984309938756000187051)
  ·
    refine ⟨48581976464908134000280577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32387984309938756000187051 48581976464908134000280577)
    ·
      refine ⟨36436482348681100500210433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48581976464908134000280577 36436482348681100500210433)
      ·
        refine ⟨27327361761510825375157825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36436482348681100500210433 27327361761510825375157825)
        ·
          refine ⟨20495521321133119031368369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27327361761510825375157825 20495521321133119031368369)
          ·
            refine ⟨15371640990849839273526277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20495521321133119031368369 15371640990849839273526277)
            ·
              refine ⟨2882182685784344863786177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15371640990849839273526277 2882182685784344863786177)
              ·
                refine ⟨2161637014338258647839633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882182685784344863786177 2161637014338258647839633)
                ·
                  refine ⟨1621227760753693985879725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161637014338258647839633 1621227760753693985879725)
                  ·
                    refine ⟨607960410282635244704897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1621227760753693985879725 607960410282635244704897)
                    ·
                      refine ⟨455970307711976433528673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 607960410282635244704897 455970307711976433528673)
                      ·
                        rfl

theorem cell23_887999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_887999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_887999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_887999 prefixEnd_887999 := by exact prefixLift 887999
  have htrace : WordTrace (prefixWord ++ tailWord_887999) baseStart_887999 baseEnd_887999 := by
    simpa [prefixWord, tailWord_887999, baseEnd_887999] using wordTrace_append hprefix tailTrace_887999
  have hstable : (prefixWord ++ tailWord_887999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887999).length < 2 ^ (prefixWord ++ tailWord_887999).sum := by decide
  have hdescent : baseEnd_887999 < baseStart_887999 := by decide
  rcases family_descends (prefixWord ++ tailWord_887999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888000 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 1, 4]
def baseStart_888000 : Nat := 118140960795 + 888000 * 2 ^ 59
def prefixEnd_888000 : Nat := 4983230072969 + 3 ^ 40 * 888000 * 2
def baseEnd_888000 : Nat := 151990273730876976538723

theorem tailTrace_888000 : CollatzResearch.WordTrace tailWord_888000 prefixEnd_888000 151990273730876976538723 := by
  unfold tailWord_888000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194010391467566585486727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21592013855290088780648969 16194010391467566585486727)
  ·
    refine ⟨24291015587201349878230091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194010391467566585486727 24291015587201349878230091)
    ·
      refine ⟨36436523380802024817345137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24291015587201349878230091 36436523380802024817345137)
      ·
        refine ⟨27327392535601518613008853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36436523380802024817345137 27327392535601518613008853)
        ·
          refine ⟨640485762553160592492395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27327392535601518613008853 640485762553160592492395)
          ·
            refine ⟨960728643829740888738593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640485762553160592492395 960728643829740888738593)
            ·
              refine ⟨720546482872305666553945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960728643829740888738593 720546482872305666553945)
              ·
                refine ⟨540409862154229249915459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720546482872305666553945 540409862154229249915459)
                ·
                  refine ⟨810614793231343874873189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540409862154229249915459 810614793231343874873189)
                  ·
                    refine ⟨151990273730876976538723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810614793231343874873189 151990273730876976538723)
                    ·
                      rfl

theorem cell23_888000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_888000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888000 prefixEnd_888000 := by exact prefixLift 888000
  have htrace : WordTrace (prefixWord ++ tailWord_888000) baseStart_888000 baseEnd_888000 := by
    simpa [prefixWord, tailWord_888000, baseEnd_888000] using wordTrace_append hprefix tailTrace_888000
  have hstable : (prefixWord ++ tailWord_888000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888000).length < 2 ^ (prefixWord ++ tailWord_888000).sum := by decide
  have hdescent : baseEnd_888000 < baseStart_888000 := by decide
  rcases family_descends (prefixWord ++ tailWord_888000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888005 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_888005 : Nat := 118140960795 + 888005 * 2 ^ 59
def prefixEnd_888005 : Nat := 4983230072969 + 3 ^ 40 * 888005 * 2
def baseEnd_888005 : Nat := 151991129531967803351215

theorem tailTrace_888005 : CollatzResearch.WordTrace tailWord_888005 prefixEnd_888005 151991129531967803351215 := by
  unfold tailWord_888005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388203147917019024905469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21592135431944679349936979 32388203147917019024905469)
  ·
    refine ⟨12145576180468882134339551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32388203147917019024905469 12145576180468882134339551)
    ·
      refine ⟨18218364270703323201509327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12145576180468882134339551 18218364270703323201509327)
      ·
        refine ⟨27327546406054984802263991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18218364270703323201509327 27327546406054984802263991)
        ·
          refine ⟨40991319609082477203395987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27327546406054984802263991 40991319609082477203395987)
          ·
            refine ⟨61486979413623715805093981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40991319609082477203395987 61486979413623715805093981)
            ·
              refine ⟨23057617280108893426910243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61486979413623715805093981 23057617280108893426910243)
              ·
                refine ⟨34586425920163340140365365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23057617280108893426910243 34586425920163340140365365)
                ·
                  refine ⟨3242477430015313138159253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34586425920163340140365365 3242477430015313138159253)
                  ·
                    refine ⟨151991129531967803351215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3242477430015313138159253 151991129531967803351215)
                    ·
                      rfl

theorem cell23_888005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_888005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888005 prefixEnd_888005 := by exact prefixLift 888005
  have htrace : WordTrace (prefixWord ++ tailWord_888005) baseStart_888005 baseEnd_888005 := by
    simpa [prefixWord, tailWord_888005, baseEnd_888005] using wordTrace_append hprefix tailTrace_888005
  have hstable : (prefixWord ++ tailWord_888005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888005).length < 2 ^ (prefixWord ++ tailWord_888005).sum := by decide
  have hdescent : baseEnd_888005 < baseStart_888005 := by decide
  rcases family_descends (prefixWord ++ tailWord_888005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888046 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_888046 : Nat := 118140960795 + 888046 * 2 ^ 59
def prefixEnd_888046 : Nat := 4983230072969 + 3 ^ 40 * 888046 * 2
def baseEnd_888046 : Nat := 455994441302737749640957

theorem tailTrace_888046 : CollatzResearch.WordTrace tailWord_888046 prefixEnd_888046 455994441302737749640957 := by
  unfold tailWord_888046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048712317596060378393499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21593132360512322018098661 4048712317596060378393499)
  ·
    refine ⟨6073068476394090567590249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4048712317596060378393499 6073068476394090567590249)
    ·
      refine ⟨4554801357295567925692687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6073068476394090567590249 4554801357295567925692687)
      ·
        refine ⟨6832202035943351888539031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554801357295567925692687 6832202035943351888539031)
        ·
          refine ⟨10248303053915027832808547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832202035943351888539031 10248303053915027832808547)
          ·
            refine ⟨15372454580872541749212821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248303053915027832808547 15372454580872541749212821)
            ·
              refine ⟨720583808478400394494351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15372454580872541749212821 720583808478400394494351)
              ·
                refine ⟨1080875712717600591741527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720583808478400394494351 1080875712717600591741527)
                ·
                  refine ⟨1621313569076400887612291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080875712717600591741527 1621313569076400887612291)
                  ·
                    refine ⟨2431970353614601331418437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1621313569076400887612291 2431970353614601331418437)
                    ·
                      refine ⟨455994441302737749640957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2431970353614601331418437 455994441302737749640957)
                      ·
                        rfl

theorem cell23_888046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_888046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888046 prefixEnd_888046 := by exact prefixLift 888046
  have htrace : WordTrace (prefixWord ++ tailWord_888046) baseStart_888046 baseEnd_888046 := by
    simpa [prefixWord, tailWord_888046, baseEnd_888046] using wordTrace_append hprefix tailTrace_888046
  have hstable : (prefixWord ++ tailWord_888046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888046).length < 2 ^ (prefixWord ++ tailWord_888046).sum := by decide
  have hdescent : baseEnd_888046 < baseStart_888046 := by decide
  rcases family_descends (prefixWord ++ tailWord_888046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888063 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 1, 2, 2]
def baseStart_888063 : Nat := 118140960795 + 888063 * 2 ^ 59
def prefixEnd_888063 : Nat := 4983230072969 + 3 ^ 40 * 888063 * 2
def baseEnd_888063 : Nat := 456003170473864183128379

theorem tailTrace_888063 : CollatzResearch.WordTrace tailWord_888063 prefixEnd_888063 456003170473864183128379 := by
  unfold tailWord_888063
  simp only [CollatzResearch.WordTrace]
  refine ⟨32390318581706894930516843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21593545721137929953677895 32390318581706894930516843)
  ·
    refine ⟨48585477872560342395775265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32390318581706894930516843 48585477872560342395775265)
    ·
      refine ⟨36439108404420256796831449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48585477872560342395775265 36439108404420256796831449)
      ·
        refine ⟨27329331303315192597623587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36439108404420256796831449 27329331303315192597623587)
        ·
          refine ⟨40993996954972788896435381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27329331303315192597623587 40993996954972788896435381)
          ·
            refine ⟨3843187214528698959040817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40993996954972788896435381 3843187214528698959040817)
            ·
              refine ⟨2882390410896524219280613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3843187214528698959040817 2882390410896524219280613)
              ·
                refine ⟨540448202043098291115115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2882390410896524219280613 540448202043098291115115)
                ·
                  refine ⟨810672303064647436672673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540448202043098291115115 810672303064647436672673)
                  ·
                    refine ⟨608004227298485577504505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 810672303064647436672673 608004227298485577504505)
                    ·
                      refine ⟨456003170473864183128379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608004227298485577504505 456003170473864183128379)
                      ·
                        rfl

theorem cell23_888063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_888063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888063 prefixEnd_888063 := by exact prefixLift 888063
  have htrace : WordTrace (prefixWord ++ tailWord_888063) baseStart_888063 baseEnd_888063 := by
    simpa [prefixWord, tailWord_888063, baseEnd_888063] using wordTrace_append hprefix tailTrace_888063
  have hstable : (prefixWord ++ tailWord_888063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888063).length < 2 ^ (prefixWord ++ tailWord_888063).sum := by decide
  have hdescent : baseEnd_888063 < baseStart_888063 := by decide
  rcases family_descends (prefixWord ++ tailWord_888063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888066 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_888066 : Nat := 118140960795 + 888066 * 2 ^ 59
def prefixEnd_888066 : Nat := 4983230072969 + 3 ^ 40 * 888066 * 2
def baseEnd_888066 : Nat := 456004710915827671390865

theorem tailTrace_888066 : CollatzResearch.WordTrace tailWord_888066 prefixEnd_888066 456004710915827671390865 := by
  unfold tailWord_888066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097607000174006610719013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21593618667130684295250701 8097607000174006610719013)
  ·
    refine ⟨1518301312532626239509815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8097607000174006610719013 1518301312532626239509815)
    ·
      refine ⟨2277451968798939359264723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518301312532626239509815 2277451968798939359264723)
      ·
        refine ⟨3416177953198409038897085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277451968798939359264723 3416177953198409038897085)
        ·
          refine ⟨1281066732449403389586407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3416177953198409038897085 1281066732449403389586407)
          ·
            refine ⟨1921600098674105084379611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281066732449403389586407 1921600098674105084379611)
            ·
              refine ⟨2882400148011157626569417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921600098674105084379611 2882400148011157626569417)
              ·
                refine ⟨2161800111008368219927063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882400148011157626569417 2161800111008368219927063)
                ·
                  refine ⟨3242700166512552329890595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161800111008368219927063 3242700166512552329890595)
                  ·
                    refine ⟨4864050249768828494835893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242700166512552329890595 4864050249768828494835893)
                    ·
                      refine ⟨456004710915827671390865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4864050249768828494835893 456004710915827671390865)
                      ·
                        rfl

theorem cell23_888066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_888066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888066 prefixEnd_888066 := by exact prefixLift 888066
  have htrace : WordTrace (prefixWord ++ tailWord_888066) baseStart_888066 baseEnd_888066 := by
    simpa [prefixWord, tailWord_888066, baseEnd_888066] using wordTrace_append hprefix tailTrace_888066
  have hstable : (prefixWord ++ tailWord_888066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888066).length < 2 ^ (prefixWord ++ tailWord_888066).sum := by decide
  have hdescent : baseEnd_888066 < baseStart_888066 := by decide
  rcases family_descends (prefixWord ++ tailWord_888066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888092 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_888092 : Nat := 118140960795 + 888092 * 2 ^ 59
def prefixEnd_888092 : Nat := 4983230072969 + 3 ^ 40 * 888092 * 2
def baseEnd_888092 : Nat := 456018061412844569665745

theorem tailTrace_888092 : CollatzResearch.WordTrace tailWord_888092 prefixEnd_888092 456018061412844569665745 := by
  unfold tailWord_888092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195688149300916441661265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21594250865734555255548353 16195688149300916441661265)
  ·
    refine ⟨12146766111975687331245949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16195688149300916441661265 12146766111975687331245949)
    ·
      refine ⟨4555037291990882749217231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12146766111975687331245949 4555037291990882749217231)
      ·
        refine ⟨6832555937986324123825847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555037291990882749217231 6832555937986324123825847)
        ·
          refine ⟨10248833906979486185738771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832555937986324123825847 10248833906979486185738771)
          ·
            refine ⟨15373250860469229278608157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248833906979486185738771 15373250860469229278608157)
            ·
              refine ⟨5764969072675960979478059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15373250860469229278608157 5764969072675960979478059)
              ·
                refine ⟨8647453609013941469217089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764969072675960979478059 8647453609013941469217089)
                ·
                  refine ⟨6485590206760456101912817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8647453609013941469217089 6485590206760456101912817)
                  ·
                    refine ⟨4864192655070342076434613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6485590206760456101912817 4864192655070342076434613)
                    ·
                      refine ⟨456018061412844569665745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4864192655070342076434613 456018061412844569665745)
                      ·
                        rfl

theorem cell23_888092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_888092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888092 prefixEnd_888092 := by exact prefixLift 888092
  have htrace : WordTrace (prefixWord ++ tailWord_888092) baseStart_888092 baseEnd_888092 := by
    simpa [prefixWord, tailWord_888092, baseEnd_888092] using wordTrace_append hprefix tailTrace_888092
  have hstable : (prefixWord ++ tailWord_888092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888092).length < 2 ^ (prefixWord ++ tailWord_888092).sum := by decide
  have hdescent : baseEnd_888092 < baseStart_888092 := by decide
  rcases family_descends (prefixWord ++ tailWord_888092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888122 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_888122 : Nat := 118140960795 + 888122 * 2 ^ 59
def prefixEnd_888122 : Nat := 4983230072969 + 3 ^ 40 * 888122 * 2
def baseEnd_888122 : Nat := 456033465832479452290607

theorem tailTrace_888122 : CollatzResearch.WordTrace tailWord_888122 prefixEnd_888122 456033465832479452290607 := by
  unfold tailWord_888122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098117622123287001728655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21594980325662098671276413 8098117622123287001728655)
  ·
    refine ⟨12147176433184930502592983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098117622123287001728655 12147176433184930502592983)
    ·
      refine ⟨18220764649777395753889475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147176433184930502592983 18220764649777395753889475)
      ·
        refine ⟨27331146974666093630834213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18220764649777395753889475 27331146974666093630834213)
        ·
          refine ⟨5124590057749892555781415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27331146974666093630834213 5124590057749892555781415)
          ·
            refine ⟨7686885086624838833672123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124590057749892555781415 7686885086624838833672123)
            ·
              refine ⟨11530327629937258250508185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686885086624838833672123 11530327629937258250508185)
              ·
                refine ⟨8647745722452943687881139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11530327629937258250508185 8647745722452943687881139)
                ·
                  refine ⟨12971618583679415531821709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647745722452943687881139 12971618583679415531821709)
                  ·
                    refine ⟨4864356968879780824433141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12971618583679415531821709 4864356968879780824433141)
                    ·
                      refine ⟨456033465832479452290607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4864356968879780824433141 456033465832479452290607)
                      ·
                        rfl

theorem cell23_888122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_888122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888122 prefixEnd_888122 := by exact prefixLift 888122
  have htrace : WordTrace (prefixWord ++ tailWord_888122) baseStart_888122 baseEnd_888122 := by
    simpa [prefixWord, tailWord_888122, baseEnd_888122] using wordTrace_append hprefix tailTrace_888122
  have hstable : (prefixWord ++ tailWord_888122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888122).length < 2 ^ (prefixWord ++ tailWord_888122).sum := by decide
  have hdescent : baseEnd_888122 < baseStart_888122 := by decide
  rcases family_descends (prefixWord ++ tailWord_888122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888134 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_888134 : Nat := 118140960795 + 888134 * 2 ^ 59
def prefixEnd_888134 : Nat := 4983230072969 + 3 ^ 40 * 888134 * 2
def baseEnd_888134 : Nat := 456039627600333405340553

theorem tailTrace_888134 : CollatzResearch.WordTrace tailWord_888134 prefixEnd_888134 456039627600333405340553 := by
  unfold tailWord_888134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012278380139052314260983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21595272109633116037567637 1012278380139052314260983)
  ·
    refine ⟨1518417570208578471391475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012278380139052314260983 1518417570208578471391475)
    ·
      refine ⟨2277626355312867707087213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518417570208578471391475 2277626355312867707087213)
      ·
        refine ⟨854109883242325390157705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2277626355312867707087213 854109883242325390157705)
        ·
          refine ⟨640582412431744042618279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854109883242325390157705 640582412431744042618279)
          ·
            refine ⟨960873618647616063927419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640582412431744042618279 960873618647616063927419)
            ·
              refine ⟨1441310427971424095891129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960873618647616063927419 1441310427971424095891129)
              ·
                refine ⟨1080982820978568071918347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441310427971424095891129 1080982820978568071918347)
                ·
                  refine ⟨1621474231467852107877521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080982820978568071918347 1621474231467852107877521)
                  ·
                    refine ⟨1216105673600889080908141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621474231467852107877521 1216105673600889080908141)
                    ·
                      refine ⟨456039627600333405340553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1216105673600889080908141 456039627600333405340553)
                      ·
                        rfl

theorem cell23_888134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_888134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888134 prefixEnd_888134 := by exact prefixLift 888134
  have htrace : WordTrace (prefixWord ++ tailWord_888134) baseStart_888134 baseEnd_888134 := by
    simpa [prefixWord, tailWord_888134, baseEnd_888134] using wordTrace_append hprefix tailTrace_888134
  have hstable : (prefixWord ++ tailWord_888134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888134).length < 2 ^ (prefixWord ++ tailWord_888134).sum := by decide
  have hdescent : baseEnd_888134 < baseStart_888134 := by decide
  rcases family_descends (prefixWord ++ tailWord_888134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888142 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_888142 : Nat := 118140960795 + 888142 * 2 ^ 59
def prefixEnd_888142 : Nat := 4983230072969 + 3 ^ 40 * 888142 * 2
def baseEnd_888142 : Nat := 50671526160618819337835

theorem tailTrace_888142 : CollatzResearch.WordTrace tailWord_888142 prefixEnd_888142 50671526160618819337835 := by
  unfold tailWord_888142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049149993552586427830335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21595466632280460948428453 4049149993552586427830335)
  ·
    refine ⟨6073724990328879641745503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049149993552586427830335 6073724990328879641745503)
    ·
      refine ⟨9110587485493319462618255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073724990328879641745503 9110587485493319462618255)
      ·
        refine ⟨13665881228239979193927383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110587485493319462618255 13665881228239979193927383)
        ·
          refine ⟨20498821842359968790891075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13665881228239979193927383 20498821842359968790891075)
          ·
            refine ⟨30748232763539953186336613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20498821842359968790891075 30748232763539953186336613)
            ·
              refine ⟨5765293643163741222438115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30748232763539953186336613 5765293643163741222438115)
              ·
                refine ⟨8647940464745611833657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765293643163741222438115 8647940464745611833657173)
                ·
                  refine ⟨50671526160618819337835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8647940464745611833657173 50671526160618819337835)
                  ·
                    rfl

theorem cell23_888142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_888142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888142 prefixEnd_888142 := by exact prefixLift 888142
  have htrace : WordTrace (prefixWord ++ tailWord_888142) baseStart_888142 baseEnd_888142 := by
    simpa [prefixWord, tailWord_888142, baseEnd_888142] using wordTrace_append hprefix tailTrace_888142
  have hstable : (prefixWord ++ tailWord_888142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888142).length < 2 ^ (prefixWord ++ tailWord_888142).sum := by decide
  have hdescent : baseEnd_888142 < baseStart_888142 := by decide
  rcases family_descends (prefixWord ++ tailWord_888142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888159 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 5]
def baseStart_888159 : Nat := 118140960795 + 888159 * 2 ^ 59
def prefixEnd_888159 : Nat := 4983230072969 + 3 ^ 40 * 888159 * 2
def baseEnd_888159 : Nat := 50672496068521756391993

theorem tailTrace_888159 : CollatzResearch.WordTrace tailWord_888159 prefixEnd_888159 50672496068521756391993 := by
  unfold tailWord_888159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32393819989359103326011531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21595879992906068884007687 32393819989359103326011531)
  ·
    refine ⟨48590729984038654989017297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32393819989359103326011531 48590729984038654989017297)
    ·
      refine ⟨36443047488028991241762973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48590729984038654989017297 36443047488028991241762973)
      ·
        refine ⟨13666142808010871715661115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36443047488028991241762973 13666142808010871715661115)
        ·
          refine ⟨20499214212016307573491673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666142808010871715661115 20499214212016307573491673)
          ·
            refine ⟨15374410659012230680118755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20499214212016307573491673 15374410659012230680118755)
            ·
              refine ⟨23061615988518346020178133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15374410659012230680118755 23061615988518346020178133)
              ·
                refine ⟨540506624730898734847925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23061615988518346020178133 540506624730898734847925)
                ·
                  refine ⟨50672496068521756391993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540506624730898734847925 50672496068521756391993)
                  ·
                    rfl

theorem cell23_888159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 5].length) (baseStart_888159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888159 prefixEnd_888159 := by exact prefixLift 888159
  have htrace : WordTrace (prefixWord ++ tailWord_888159) baseStart_888159 baseEnd_888159 := by
    simpa [prefixWord, tailWord_888159, baseEnd_888159] using wordTrace_append hprefix tailTrace_888159
  have hstable : (prefixWord ++ tailWord_888159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888159).length < 2 ^ (prefixWord ++ tailWord_888159).sum := by decide
  have hdescent : baseEnd_888159 < baseStart_888159 := by decide
  rcases family_descends (prefixWord ++ tailWord_888159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888206 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_888206 : Nat := 118140960795 + 888206 * 2 ^ 59
def prefixEnd_888206 : Nat := 4983230072969 + 3 ^ 40 * 888206 * 2
def baseEnd_888206 : Nat := 152025532735819041213407

theorem tailTrace_888206 : CollatzResearch.WordTrace tailWord_888206 prefixEnd_888206 152025532735819041213407 := by
  unfold tailWord_888206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049441777523603794121559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21597022813459220235314981 4049441777523603794121559)
  ·
    refine ⟨6074162666285405691182339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049441777523603794121559 6074162666285405691182339)
    ·
      refine ⟨9111243999428108536773509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6074162666285405691182339 9111243999428108536773509)
      ·
        refine ⟨1708358249892770350645033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9111243999428108536773509 1708358249892770350645033)
        ·
          refine ⟨1281268687419577762983775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708358249892770350645033 1281268687419577762983775)
          ·
            refine ⟨1921903031129366644475663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281268687419577762983775 1921903031129366644475663)
            ·
              refine ⟨2882854546694049966713495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921903031129366644475663 2882854546694049966713495)
              ·
                refine ⟨4324281820041074950070243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882854546694049966713495 4324281820041074950070243)
                ·
                  refine ⟨6486422730061612425105365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324281820041074950070243 6486422730061612425105365)
                  ·
                    refine ⟨152025532735819041213407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6486422730061612425105365 152025532735819041213407)
                    ·
                      rfl

theorem cell23_888206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_888206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888206 prefixEnd_888206 := by exact prefixLift 888206
  have htrace : WordTrace (prefixWord ++ tailWord_888206) baseStart_888206 baseEnd_888206 := by
    simpa [prefixWord, tailWord_888206, baseEnd_888206] using wordTrace_append hprefix tailTrace_888206
  have hstable : (prefixWord ++ tailWord_888206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888206).length < 2 ^ (prefixWord ++ tailWord_888206).sum := by decide
  have hdescent : baseEnd_888206 < baseStart_888206 := by decide
  rcases family_descends (prefixWord ++ tailWord_888206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888210 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_888210 : Nat := 118140960795 + 888210 * 2 ^ 59
def prefixEnd_888210 : Nat := 4983230072969 + 3 ^ 40 * 888210 * 2
def baseEnd_888210 : Nat := 50675405792230567554467

theorem tailTrace_888210 : CollatzResearch.WordTrace tailWord_888210 prefixEnd_888210 50675405792230567554467 := by
  unfold tailWord_888210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098920028043584759029521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21597120074782892690745389 8098920028043584759029521)
  ·
    refine ⟨6074190021032688569272141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8098920028043584759029521 6074190021032688569272141)
    ·
      refine ⟨2277821257887258213477053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6074190021032688569272141 2277821257887258213477053)
      ·
        refine ⟨854182971707721830053895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2277821257887258213477053 854182971707721830053895)
        ·
          refine ⟨1281274457561582745080843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854182971707721830053895 1281274457561582745080843)
          ·
            refine ⟨1921911686342374117621265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281274457561582745080843 1921911686342374117621265)
            ·
              refine ⟨1441433764756780588215949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921911686342374117621265 1441433764756780588215949)
              ·
                refine ⟨540537661783792720580981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441433764756780588215949 540537661783792720580981)
                ·
                  refine ⟨50675405792230567554467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540537661783792720580981 50675405792230567554467)
                  ·
                    rfl

theorem cell23_888210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_888210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888210 prefixEnd_888210 := by exact prefixLift 888210
  have htrace : WordTrace (prefixWord ++ tailWord_888210) baseStart_888210 baseEnd_888210 := by
    simpa [prefixWord, tailWord_888210, baseEnd_888210] using wordTrace_append hprefix tailTrace_888210
  have hstable : (prefixWord ++ tailWord_888210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888210).length < 2 ^ (prefixWord ++ tailWord_888210).sum := by decide
  have hdescent : baseEnd_888210 < baseStart_888210 := by decide
  rcases family_descends (prefixWord ++ tailWord_888210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888316 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_888316 : Nat := 118140960795 + 888316 * 2 ^ 59
def prefixEnd_888316 : Nat := 4983230072969 + 3 ^ 40 * 888316 * 2
def baseEnd_888316 : Nat := 456133081079451693264715

theorem tailTrace_888316 : CollatzResearch.WordTrace tailWord_888316 prefixEnd_888316 456133081079451693264715 := by
  unfold tailWord_888316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199773124895159569738401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21599697499860212759651201 16199773124895159569738401)
  ·
    refine ⟨12149829843671369677303801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16199773124895159569738401 12149829843671369677303801)
    ·
      refine ⟨9112372382753527257977851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12149829843671369677303801 9112372382753527257977851)
      ·
        refine ⟨13668558574130290886966777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112372382753527257977851 13668558574130290886966777)
        ·
          refine ⟨10251418930597718165225083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13668558574130290886966777 10251418930597718165225083)
          ·
            refine ⟨15377128395896577247837625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10251418930597718165225083 15377128395896577247837625)
            ·
              refine ⟨11532846296922432935878219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15377128395896577247837625 11532846296922432935878219)
              ·
                refine ⟨17299269445383649403817329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11532846296922432935878219 17299269445383649403817329)
                ·
                  refine ⟨12974452084037737052862997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17299269445383649403817329 12974452084037737052862997)
                  ·
                    refine ⟨608177441439268924352953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12974452084037737052862997 608177441439268924352953)
                    ·
                      refine ⟨456133081079451693264715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608177441439268924352953 456133081079451693264715)
                      ·
                        rfl

theorem cell23_888316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_888316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888316 prefixEnd_888316 := by exact prefixLift 888316
  have htrace : WordTrace (prefixWord ++ tailWord_888316) baseStart_888316 baseEnd_888316 := by
    simpa [prefixWord, tailWord_888316, baseEnd_888316] using wordTrace_append hprefix tailTrace_888316
  have hstable : (prefixWord ++ tailWord_888316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888316).length < 2 ^ (prefixWord ++ tailWord_888316).sum := by decide
  have hdescent : baseEnd_888316 < baseStart_888316 := by decide
  rcases family_descends (prefixWord ++ tailWord_888316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888344 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_888344 : Nat := 118140960795 + 888344 * 2 ^ 59
def prefixEnd_888344 : Nat := 4983230072969 + 3 ^ 40 * 888344 * 2
def baseEnd_888344 : Nat := 456147458537777583714587

theorem tailTrace_888344 : CollatzResearch.WordTrace tailWord_888344 prefixEnd_888344 456147458537777583714587 := by
  unfold tailWord_888344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16200283746844439960748043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21600378329125919947664057 16200283746844439960748043)
  ·
    refine ⟨24300425620266659941122065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16200283746844439960748043 24300425620266659941122065)
    ·
      refine ⟨18225319215199994955841549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24300425620266659941122065 18225319215199994955841549)
      ·
        refine ⟨6834494705699998108440581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18225319215199994955841549 6834494705699998108440581)
        ·
          refine ⟨1281467757318749645332609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6834494705699998108440581 1281467757318749645332609)
          ·
            refine ⟨961100817989062233999457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281467757318749645332609 961100817989062233999457)
            ·
              refine ⟨720825613491796675499593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961100817989062233999457 720825613491796675499593)
              ·
                refine ⟨540619210118847506624695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720825613491796675499593 540619210118847506624695)
                ·
                  refine ⟨810928815178271259937043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540619210118847506624695 810928815178271259937043)
                  ·
                    refine ⟨1216393222767406889905565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 810928815178271259937043 1216393222767406889905565)
                    ·
                      refine ⟨456147458537777583714587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1216393222767406889905565 456147458537777583714587)
                      ·
                        rfl

theorem cell23_888344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_888344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888344 prefixEnd_888344 := by exact prefixLift 888344
  have htrace : WordTrace (prefixWord ++ tailWord_888344) baseStart_888344 baseEnd_888344 := by
    simpa [prefixWord, tailWord_888344, baseEnd_888344] using wordTrace_append hprefix tailTrace_888344
  have hstable : (prefixWord ++ tailWord_888344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888344).length < 2 ^ (prefixWord ++ tailWord_888344).sum := by decide
  have hdescent : baseEnd_888344 < baseStart_888344 := by decide
  rcases family_descends (prefixWord ++ tailWord_888344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888369 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_888369 : Nat := 118140960795 + 888369 * 2 ^ 59
def prefixEnd_888369 : Nat := 4983230072969 + 3 ^ 40 * 888369 * 2
def baseEnd_888369 : Nat := 152053431851379995300657

theorem tailTrace_888369 : CollatzResearch.WordTrace tailWord_888369 prefixEnd_888369 152053431851379995300657 := by
  unfold tailWord_888369
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401479318598309191156161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21600986212398872794104107 32401479318598309191156161)
  ·
    refine ⟨24301109488948731893367121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32401479318598309191156161 24301109488948731893367121)
    ·
      refine ⟨18225832116711548920025341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24301109488948731893367121 18225832116711548920025341)
      ·
        refine ⟨6834687043766830845009503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18225832116711548920025341 6834687043766830845009503)
        ·
          refine ⟨10252030565650246267514255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6834687043766830845009503 10252030565650246267514255)
          ·
            refine ⟨15378045848475369401271383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252030565650246267514255 15378045848475369401271383)
            ·
              refine ⟨23067068772713054101907075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378045848475369401271383 23067068772713054101907075)
              ·
                refine ⟨34600603159069581152860613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23067068772713054101907075 34600603159069581152860613)
                ·
                  refine ⟨6487613092325546466161365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34600603159069581152860613 6487613092325546466161365)
                  ·
                    refine ⟨152053431851379995300657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6487613092325546466161365 152053431851379995300657)
                    ·
                      rfl

theorem cell23_888369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_888369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888369 prefixEnd_888369 := by exact prefixLift 888369
  have htrace : WordTrace (prefixWord ++ tailWord_888369) baseStart_888369 baseEnd_888369 := by
    simpa [prefixWord, tailWord_888369, baseEnd_888369] using wordTrace_append hprefix tailTrace_888369
  have hstable : (prefixWord ++ tailWord_888369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888369).length < 2 ^ (prefixWord ++ tailWord_888369).sum := by decide
  have hdescent : baseEnd_888369 < baseStart_888369 := by decide
  rcases family_descends (prefixWord ++ tailWord_888369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888496 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_888496 : Nat := 118140960795 + 888496 * 2 ^ 59
def prefixEnd_888496 : Nat := 4983230072969 + 3 ^ 40 * 888496 * 2
def baseEnd_888496 : Nat := 456225507597260989013887

theorem tailTrace_888496 : CollatzResearch.WordTrace tailWord_888496 prefixEnd_888496 456225507597260989013887 := by
  unfold tailWord_888496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203055694569104940514671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21604074259425473254019561 16203055694569104940514671)
  ·
    refine ⟨24304583541853657410772007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16203055694569104940514671 24304583541853657410772007)
    ·
      refine ⟨36456875312780486116158011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24304583541853657410772007 36456875312780486116158011)
      ·
        refine ⟨54685312969170729174237017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36456875312780486116158011 54685312969170729174237017)
        ·
          refine ⟨41013984726878046880677763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54685312969170729174237017 41013984726878046880677763)
          ·
            refine ⟨61520977090317070321016645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41013984726878046880677763 61520977090317070321016645)
            ·
              refine ⟨11535183204434450685190621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61520977090317070321016645 11535183204434450685190621)
              ·
                refine ⟨4325693701662919006946483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11535183204434450685190621 4325693701662919006946483)
                ·
                  refine ⟨6488540552494378510419725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325693701662919006946483 6488540552494378510419725)
                  ·
                    refine ⟨2433202707185391941407397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6488540552494378510419725 2433202707185391941407397)
                    ·
                      refine ⟨456225507597260989013887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2433202707185391941407397 456225507597260989013887)
                      ·
                        rfl

theorem cell23_888496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_888496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888496 prefixEnd_888496 := by exact prefixLift 888496
  have htrace : WordTrace (prefixWord ++ tailWord_888496) baseStart_888496 baseEnd_888496 := by
    simpa [prefixWord, tailWord_888496, baseEnd_888496] using wordTrace_append hprefix tailTrace_888496
  have hstable : (prefixWord ++ tailWord_888496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888496).length < 2 ^ (prefixWord ++ tailWord_888496).sum := by decide
  have hdescent : baseEnd_888496 < baseStart_888496 := by decide
  rcases family_descends (prefixWord ++ tailWord_888496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888530 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_888530 : Nat := 118140960795 + 888530 * 2 ^ 59
def prefixEnd_888530 : Nat := 4983230072969 + 3 ^ 40 * 888530 * 2
def baseEnd_888530 : Nat := 456242965939513855988731

theorem tailTrace_888530 : CollatzResearch.WordTrace tailWord_888530 prefixEnd_888530 456242965939513855988731 := by
  unfold tailWord_888530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101837867753758421941761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21604900980676689125178029 8101837867753758421941761)
  ·
    refine ⟨6076378400815318816456321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8101837867753758421941761 6076378400815318816456321)
    ·
      refine ⟨4557283800611489112342241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6076378400815318816456321 4557283800611489112342241)
      ·
        refine ⟨3417962850458616834256681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557283800611489112342241 3417962850458616834256681)
        ·
          refine ⟨2563472137843962625692511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417962850458616834256681 2563472137843962625692511)
          ·
            refine ⟨3845208206765943938538767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563472137843962625692511 3845208206765943938538767)
            ·
              refine ⟨5767812310148915907808151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845208206765943938538767 5767812310148915907808151)
              ·
                refine ⟨8651718465223373861712227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767812310148915907808151 8651718465223373861712227)
                ·
                  refine ⟨12977577697835060792568341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651718465223373861712227 12977577697835060792568341)
                  ·
                    refine ⟨608323954586018474651641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12977577697835060792568341 608323954586018474651641)
                    ·
                      refine ⟨456242965939513855988731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608323954586018474651641 456242965939513855988731)
                      ·
                        rfl

theorem cell23_888530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_888530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888530 prefixEnd_888530 := by exact prefixLift 888530
  have htrace : WordTrace (prefixWord ++ tailWord_888530) baseStart_888530 baseEnd_888530 := by
    simpa [prefixWord, tailWord_888530, baseEnd_888530] using wordTrace_append hprefix tailTrace_888530
  have hstable : (prefixWord ++ tailWord_888530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888530).length < 2 ^ (prefixWord ++ tailWord_888530).sum := by decide
  have hdescent : baseEnd_888530 < baseStart_888530 := by decide
  rcases family_descends (prefixWord ++ tailWord_888530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888547 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 4]
def baseStart_888547 : Nat := 118140960795 + 888547 * 2 ^ 59
def prefixEnd_888547 : Nat := 4983230072969 + 3 ^ 40 * 888547 * 2
def baseEnd_888547 : Nat := 456251695110640289476153

theorem tailTrace_888547 : CollatzResearch.WordTrace tailWord_888547 prefixEnd_888547 456251695110640289476153 := by
  unfold tailWord_888547
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407971511953445591135895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21605314341302297060757263 32407971511953445591135895)
  ·
    refine ⟨48611957267930168386703843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32407971511953445591135895 48611957267930168386703843)
    ·
      refine ⟨72917935901895252580055765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48611957267930168386703843 72917935901895252580055765)
      ·
        refine ⟨1709014122700669982345057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72917935901895252580055765 1709014122700669982345057)
        ·
          refine ⟨1281760592025502486758793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709014122700669982345057 1281760592025502486758793)
          ·
            refine ⟨961320444019126865069095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281760592025502486758793 961320444019126865069095)
            ·
              refine ⟨1441980666028690297603643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961320444019126865069095 1441980666028690297603643)
              ·
                refine ⟨2162970999043035446405465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441980666028690297603643 2162970999043035446405465)
                ·
                  refine ⟨1622228249282276584804099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2162970999043035446405465 1622228249282276584804099)
                  ·
                    refine ⟨2433342373923414877206149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622228249282276584804099 2433342373923414877206149)
                    ·
                      refine ⟨456251695110640289476153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2433342373923414877206149 456251695110640289476153)
                      ·
                        rfl

theorem cell23_888547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_888547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888547 prefixEnd_888547 := by exact prefixLift 888547
  have htrace : WordTrace (prefixWord ++ tailWord_888547) baseStart_888547 baseEnd_888547 := by
    simpa [prefixWord, tailWord_888547, baseEnd_888547] using wordTrace_append hprefix tailTrace_888547
  have hstable : (prefixWord ++ tailWord_888547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888547).length < 2 ^ (prefixWord ++ tailWord_888547).sum := by decide
  have hdescent : baseEnd_888547 < baseStart_888547 := by decide
  rcases family_descends (prefixWord ++ tailWord_888547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888557 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_888557 : Nat := 118140960795 + 888557 * 2 ^ 59
def prefixEnd_888557 : Nat := 4983230072969 + 3 ^ 40 * 888557 * 2
def baseEnd_888557 : Nat := 152085609972395083450369

theorem tailTrace_888557 : CollatzResearch.WordTrace tailWord_888557 prefixEnd_888557 152085609972395083450369 := by
  unfold tailWord_888557
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408336241917217298999925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21605557494611478199333283 32408336241917217298999925)
  ·
    refine ⟨3038281522679739121781243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32408336241917217298999925 3038281522679739121781243)
    ·
      refine ⟨4557422284019608682671865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038281522679739121781243 4557422284019608682671865)
      ·
        refine ⟨3418066713014706512003899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557422284019608682671865 3418066713014706512003899)
        ·
          refine ⟨5127100069522059768005849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418066713014706512003899 5127100069522059768005849)
          ·
            refine ⟨3845325052141544826004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5127100069522059768005849 3845325052141544826004387)
            ·
              refine ⟨5767987578212317239006581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845325052141544826004387 5767987578212317239006581)
              ·
                refine ⟨540748835457404741156867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5767987578212317239006581 540748835457404741156867)
                ·
                  refine ⟨811123253186107111735301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540748835457404741156867 811123253186107111735301)
                  ·
                    refine ⟨152085609972395083450369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811123253186107111735301 152085609972395083450369)
                    ·
                      rfl

theorem cell23_888557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_888557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888557 prefixEnd_888557 := by exact prefixLift 888557
  have htrace : WordTrace (prefixWord ++ tailWord_888557) baseStart_888557 baseEnd_888557 := by
    simpa [prefixWord, tailWord_888557, baseEnd_888557] using wordTrace_append hprefix tailTrace_888557
  have hstable : (prefixWord ++ tailWord_888557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888557).length < 2 ^ (prefixWord ++ tailWord_888557).sum := by decide
  have hdescent : baseEnd_888557 < baseStart_888557 := by decide
  rcases family_descends (prefixWord ++ tailWord_888557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888564 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_888564 : Nat := 118140960795 + 888564 * 2 ^ 59
def prefixEnd_888564 : Nat := 4983230072969 + 3 ^ 40 * 888564 * 2
def baseEnd_888564 : Nat := 456260424281766722963575

theorem tailTrace_888564 : CollatzResearch.WordTrace tailWord_888564 prefixEnd_888564 456260424281766722963575 := by
  unfold tailWord_888564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204295776445928747252373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21605727701927904996336497 16204295776445928747252373)
  ·
    refine ⟨759576364520902910027455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16204295776445928747252373 759576364520902910027455)
    ·
      refine ⟨1139364546781354365041183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759576364520902910027455 1139364546781354365041183)
      ·
        refine ⟨1709046820172031547561775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139364546781354365041183 1709046820172031547561775)
        ·
          refine ⟨2563570230258047321342663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709046820172031547561775 2563570230258047321342663)
          ·
            refine ⟨3845355345387070982013995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563570230258047321342663 3845355345387070982013995)
            ·
              refine ⟨5768033018080606473020993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845355345387070982013995 5768033018080606473020993)
              ·
                refine ⟨4326024763560454854765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768033018080606473020993 4326024763560454854765745)
                ·
                  refine ⟨3244518572670341141074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326024763560454854765745 3244518572670341141074309)
                  ·
                    refine ⟨608347232375688963951433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244518572670341141074309 608347232375688963951433)
                    ·
                      refine ⟨456260424281766722963575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608347232375688963951433 456260424281766722963575)
                      ·
                        rfl

theorem cell23_888564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_888564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888564 prefixEnd_888564 := by exact prefixLift 888564
  have htrace : WordTrace (prefixWord ++ tailWord_888564) baseStart_888564 baseEnd_888564 := by
    simpa [prefixWord, tailWord_888564, baseEnd_888564] using wordTrace_append hprefix tailTrace_888564
  have hstable : (prefixWord ++ tailWord_888564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888564).length < 2 ^ (prefixWord ++ tailWord_888564).sum := by decide
  have hdescent : baseEnd_888564 < baseStart_888564 := by decide
  rcases family_descends (prefixWord ++ tailWord_888564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888576 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_888576 : Nat := 118140960795 + 888576 * 2 ^ 59
def prefixEnd_888576 : Nat := 4983230072969 + 3 ^ 40 * 888576 * 2
def baseEnd_888576 : Nat := 456266586049620676013519

theorem tailTrace_888576 : CollatzResearch.WordTrace tailWord_888576 prefixEnd_888576 456266586049620676013519 := by
  unfold tailWord_888576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204514614424191771970791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21606019485898922362627721 16204514614424191771970791)
  ·
    refine ⟨24306771921636287657956187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16204514614424191771970791 24306771921636287657956187)
    ·
      refine ⟨36460157882454431486934281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24306771921636287657956187 36460157882454431486934281)
      ·
        refine ⟨27345118411840823615200711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36460157882454431486934281 27345118411840823615200711)
        ·
          refine ⟨41017677617761235422801067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27345118411840823615200711 41017677617761235422801067)
          ·
            refine ⟨61526516426641853134201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41017677617761235422801067 61526516426641853134201601)
            ·
              refine ⟨46144887319981389850651201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61526516426641853134201601 46144887319981389850651201)
              ·
                refine ⟨34608665489986042387988401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46144887319981389850651201 34608665489986042387988401)
                ·
                  refine ⟨25956499117489531790991301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34608665489986042387988401 25956499117489531790991301)
                  ·
                    refine ⟨4866843584529287210810869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25956499117489531790991301 4866843584529287210810869)
                    ·
                      refine ⟨456266586049620676013519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4866843584529287210810869 456266586049620676013519)
                      ·
                        rfl

theorem cell23_888576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_888576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888576 prefixEnd_888576 := by exact prefixLift 888576
  have htrace : WordTrace (prefixWord ++ tailWord_888576) baseStart_888576 baseEnd_888576 := by
    simpa [prefixWord, tailWord_888576, baseEnd_888576] using wordTrace_append hprefix tailTrace_888576
  have hstable : (prefixWord ++ tailWord_888576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888576).length < 2 ^ (prefixWord ++ tailWord_888576).sum := by decide
  have hdescent : baseEnd_888576 < baseStart_888576 := by decide
  rcases family_descends (prefixWord ++ tailWord_888576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888590 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_888590 : Nat := 118140960795 + 888590 * 2 ^ 59
def prefixEnd_888590 : Nat := 4983230072969 + 3 ^ 40 * 888590 * 2
def baseEnd_888590 : Nat := 456273774778783621238455

theorem tailTrace_888590 : CollatzResearch.WordTrace tailWord_888590 prefixEnd_888590 456273774778783621238455 := by
  unfold tailWord_888590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051192481349707991868903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21606359900531775956634149 4051192481349707991868903)
  ·
    refine ⟨6076788722024561987803355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4051192481349707991868903 6076788722024561987803355)
    ·
      refine ⟨9115183083036842981705033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076788722024561987803355 9115183083036842981705033)
      ·
        refine ⟨6836387312277632236278775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115183083036842981705033 6836387312277632236278775)
        ·
          refine ⟨10254580968416448354418163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836387312277632236278775 10254580968416448354418163)
          ·
            refine ⟨15381871452624672531627245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10254580968416448354418163 15381871452624672531627245)
            ·
              refine ⟨5768201794734252199360217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15381871452624672531627245 5768201794734252199360217)
              ·
                refine ⟨4326151346050689149520163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768201794734252199360217 4326151346050689149520163)
                ·
                  refine ⟨6489227019076033724280245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326151346050689149520163 6489227019076033724280245)
                  ·
                    refine ⟨608365033038378161651273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6489227019076033724280245 608365033038378161651273)
                    ·
                      refine ⟨456273774778783621238455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608365033038378161651273 456273774778783621238455)
                      ·
                        rfl

theorem cell23_888590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_888590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888590 prefixEnd_888590 := by exact prefixLift 888590
  have htrace : WordTrace (prefixWord ++ tailWord_888590) baseStart_888590 baseEnd_888590 := by
    simpa [prefixWord, tailWord_888590, baseEnd_888590] using wordTrace_append hprefix tailTrace_888590
  have hstable : (prefixWord ++ tailWord_888590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888590).length < 2 ^ (prefixWord ++ tailWord_888590).sum := by decide
  have hdescent : baseEnd_888590 < baseStart_888590 := by decide
  rcases family_descends (prefixWord ++ tailWord_888590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888620 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_888620 : Nat := 118140960795 + 888620 * 2 ^ 59
def prefixEnd_888620 : Nat := 4983230072969 + 3 ^ 40 * 888620 * 2
def baseEnd_888620 : Nat := 456289179198418503863317

theorem tailTrace_888620 : CollatzResearch.WordTrace tailWord_888620 prefixEnd_888620 456289179198418503863317 := by
  unfold tailWord_888620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205317020344489529271657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21607089360459319372362209 16205317020344489529271657)
  ·
    refine ⟨12153987765258367146953743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16205317020344489529271657 12153987765258367146953743)
    ·
      refine ⟨18230981647887550720430615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153987765258367146953743 18230981647887550720430615)
      ·
        refine ⟨27346472471831326080645923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230981647887550720430615 27346472471831326080645923)
        ·
          refine ⟨41019708707746989120968885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346472471831326080645923 41019708707746989120968885)
          ·
            refine ⟨3845597691351280230090833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41019708707746989120968885 3845597691351280230090833)
            ·
              refine ⟨2884198268513460172568125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845597691351280230090833 2884198268513460172568125)
              ·
                refine ⟨1081574350692547564713047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2884198268513460172568125 1081574350692547564713047)
                ·
                  refine ⟨1622361526038821347069571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081574350692547564713047 1622361526038821347069571)
                  ·
                    refine ⟨2433542289058232020604357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622361526038821347069571 2433542289058232020604357)
                    ·
                      refine ⟨456289179198418503863317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2433542289058232020604357 456289179198418503863317)
                      ·
                        rfl

theorem cell23_888620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_888620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888620 prefixEnd_888620 := by exact prefixLift 888620
  have htrace : WordTrace (prefixWord ++ tailWord_888620) baseStart_888620 baseEnd_888620 := by
    simpa [prefixWord, tailWord_888620, baseEnd_888620] using wordTrace_append hprefix tailTrace_888620
  have hstable : (prefixWord ++ tailWord_888620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888620).length < 2 ^ (prefixWord ++ tailWord_888620).sum := by decide
  have hdescent : baseEnd_888620 < baseStart_888620 := by decide
  rcases family_descends (prefixWord ++ tailWord_888620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888643 : List Nat := [1, 1, 1, 3, 1, 6, 2, 8]
def baseStart_888643 : Nat := 118140960795 + 888643 * 2 ^ 59
def prefixEnd_888643 : Nat := 4983230072969 + 3 ^ 40 * 888643 * 2
def baseEnd_888643 : Nat := 16900036639017478291693

theorem tailTrace_888643 : CollatzResearch.WordTrace tailWord_888643 prefixEnd_888643 16900036639017478291693 := by
  unfold tailWord_888643
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411472919605653986630583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21607648613070435991087055 32411472919605653986630583)
  ·
    refine ⟨48617209379408480979945875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32411472919605653986630583 48617209379408480979945875)
    ·
      refine ⟨72925814069112721469918813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48617209379408480979945875 72925814069112721469918813)
      ·
        refine ⟨27347180275917270551219555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72925814069112721469918813 27347180275917270551219555)
        ·
          refine ⟨41020770413875905826829333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27347180275917270551219555 41020770413875905826829333)
          ·
            refine ⟨1922848613150433085632625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41020770413875905826829333 1922848613150433085632625)
            ·
              refine ⟨1442136459862824814224469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922848613150433085632625 1442136459862824814224469)
              ·
                refine ⟨16900036639017478291693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1442136459862824814224469 16900036639017478291693)
                ·
                  rfl

theorem cell23_888643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 8].length) (baseStart_888643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888643 prefixEnd_888643 := by exact prefixLift 888643
  have htrace : WordTrace (prefixWord ++ tailWord_888643) baseStart_888643 baseEnd_888643 := by
    simpa [prefixWord, tailWord_888643, baseEnd_888643] using wordTrace_append hprefix tailTrace_888643
  have hstable : (prefixWord ++ tailWord_888643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888643).length < 2 ^ (prefixWord ++ tailWord_888643).sum := by decide
  have hdescent : baseEnd_888643 < baseStart_888643 := by decide
  rcases family_descends (prefixWord ++ tailWord_888643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888647 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 2, 4]
def baseStart_888647 : Nat := 118140960795 + 888647 * 2 ^ 59
def prefixEnd_888647 : Nat := 4983230072969 + 3 ^ 40 * 888647 * 2
def baseEnd_888647 : Nat := 152101014392029966075231

theorem tailTrace_888647 : CollatzResearch.WordTrace tailWord_888647 prefixEnd_888647 152101014392029966075231 := by
  unfold tailWord_888647
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411618811591162669776195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21607745874394108446517463 32411618811591162669776195)
  ·
    refine ⟨48617428217386744004664293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32411618811591162669776195 48617428217386744004664293)
    ·
      refine ⟨9115767790760014500874555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48617428217386744004664293 9115767790760014500874555)
      ·
        refine ⟨13673651686140021751311833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115767790760014500874555 13673651686140021751311833)
        ·
          refine ⟨10255238764605016313483875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673651686140021751311833 10255238764605016313483875)
          ·
            refine ⟨15382858146907524470225813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255238764605016313483875 15382858146907524470225813)
            ·
              refine ⟨721071475636290209541835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15382858146907524470225813 721071475636290209541835)
              ·
                refine ⟨1081607213454435314312753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721071475636290209541835 1081607213454435314312753)
                ·
                  refine ⟨811205410090826485734565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081607213454435314312753 811205410090826485734565)
                  ·
                    refine ⟨152101014392029966075231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811205410090826485734565 152101014392029966075231)
                    ·
                      rfl

theorem cell23_888647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_888647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888647 prefixEnd_888647 := by exact prefixLift 888647
  have htrace : WordTrace (prefixWord ++ tailWord_888647) baseStart_888647 baseEnd_888647 := by
    simpa [prefixWord, tailWord_888647, baseEnd_888647] using wordTrace_append hprefix tailTrace_888647
  have hstable : (prefixWord ++ tailWord_888647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888647).length < 2 ^ (prefixWord ++ tailWord_888647).sum := by decide
  have hdescent : baseEnd_888647 < baseStart_888647 := by decide
  rcases family_descends (prefixWord ++ tailWord_888647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888657 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_888657 : Nat := 118140960795 + 888657 * 2 ^ 59
def prefixEnd_888657 : Nat := 4983230072969 + 3 ^ 40 * 888657 * 2
def baseEnd_888657 : Nat := 456308177982634859100647

theorem tailTrace_888657 : CollatzResearch.WordTrace tailWord_888657 prefixEnd_888657 456308177982634859100647 := by
  unfold tailWord_888657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411983541554934377640225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21607989027703289585093483 32411983541554934377640225)
  ·
    refine ⟨24308987656166200783230169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32411983541554934377640225 24308987656166200783230169)
    ·
      refine ⟨18231740742124650587422627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24308987656166200783230169 18231740742124650587422627)
      ·
        refine ⟨27347611113186975881133941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231740742124650587422627 27347611113186975881133941)
        ·
          refine ⟨2563838541861278988856307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27347611113186975881133941 2563838541861278988856307)
          ·
            refine ⟨3845757812791918483284461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563838541861278988856307 3845757812791918483284461)
            ·
              refine ⟨1442159179796969431231673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845757812791918483284461 1442159179796969431231673)
              ·
                refine ⟨1081619384847727073423755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442159179796969431231673 1081619384847727073423755)
                ·
                  refine ⟨1622429077271590610135633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081619384847727073423755 1622429077271590610135633)
                  ·
                    refine ⟨1216821807953692957601725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622429077271590610135633 1216821807953692957601725)
                    ·
                      refine ⟨456308177982634859100647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1216821807953692957601725 456308177982634859100647)
                      ·
                        rfl

theorem cell23_888657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_888657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888657 prefixEnd_888657 := by exact prefixLift 888657
  have htrace : WordTrace (prefixWord ++ tailWord_888657) baseStart_888657 baseEnd_888657 := by
    simpa [prefixWord, tailWord_888657, baseEnd_888657] using wordTrace_append hprefix tailTrace_888657
  have hstable : (prefixWord ++ tailWord_888657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888657).length < 2 ^ (prefixWord ++ tailWord_888657).sum := by decide
  have hdescent : baseEnd_888657 < baseStart_888657 := by decide
  rcases family_descends (prefixWord ++ tailWord_888657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888694 : List Nat := [5, 1, 1, 3, 3, 1, 1, 8]
def baseStart_888694 : Nat := 118140960795 + 888694 * 2 ^ 59
def prefixEnd_888694 : Nat := 4983230072969 + 3 ^ 40 * 888694 * 2
def baseEnd_888694 : Nat := 16901006546920415345851

theorem tailTrace_888694 : CollatzResearch.WordTrace tailWord_888694 prefixEnd_888694 16901006546920415345851 := by
  unfold tailWord_888694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025833315151305606046071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21608888694947259797824757 2025833315151305606046071)
  ·
    refine ⟨3038749972726958409069107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025833315151305606046071 3038749972726958409069107)
    ·
      refine ⟨4558124959090437613603661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038749972726958409069107 4558124959090437613603661)
      ·
        refine ⟨1709296859658914105101373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4558124959090437613603661 1709296859658914105101373)
        ·
          refine ⟨640986322372092789413015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1709296859658914105101373 640986322372092789413015)
          ·
            refine ⟨961479483558139184119523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640986322372092789413015 961479483558139184119523)
            ·
              refine ⟨1442219225337208776179285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961479483558139184119523 1442219225337208776179285)
              ·
                refine ⟨16901006546920415345851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1442219225337208776179285 16901006546920415345851)
                ·
                  rfl

theorem cell23_888694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_888694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888694 prefixEnd_888694 := by exact prefixLift 888694
  have htrace : WordTrace (prefixWord ++ tailWord_888694) baseStart_888694 baseEnd_888694 := by
    simpa [prefixWord, tailWord_888694, baseEnd_888694] using wordTrace_append hprefix tailTrace_888694
  have hstable : (prefixWord ++ tailWord_888694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888694).length < 2 ^ (prefixWord ++ tailWord_888694).sum := by decide
  have hdescent : baseEnd_888694 < baseStart_888694 := by decide
  rcases family_descends (prefixWord ++ tailWord_888694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888727 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_888727 : Nat := 118140960795 + 888727 * 2 ^ 59
def prefixEnd_888727 : Nat := 4983230072969 + 3 ^ 40 * 888727 * 2
def baseEnd_888727 : Nat := 456344121628449585225325

theorem tailTrace_888727 : CollatzResearch.WordTrace tailWord_888727 prefixEnd_888727 456344121628449585225325 := by
  unfold tailWord_888727
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414536651301336332688435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21609691100867557555125623 32414536651301336332688435)
  ·
    refine ⟨48621804976952004499032653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32414536651301336332688435 48621804976952004499032653)
    ·
      refine ⟨18233176866357001687137245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48621804976952004499032653 18233176866357001687137245)
      ·
        refine ⟨6837441324883875632676467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18233176866357001687137245 6837441324883875632676467)
        ·
          refine ⟨10256161987325813449014701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837441324883875632676467 10256161987325813449014701)
          ·
            refine ⟨3846060745247180043380513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10256161987325813449014701 3846060745247180043380513)
            ·
              refine ⟨2884545558935385032535385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846060745247180043380513 2884545558935385032535385)
              ·
                refine ⟨2163409169201538774401539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884545558935385032535385 2163409169201538774401539)
                ·
                  refine ⟨3245113753802308161602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163409169201538774401539 3245113753802308161602309)
                  ·
                    refine ⟨608458828837932780300433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245113753802308161602309 608458828837932780300433)
                    ·
                      refine ⟨456344121628449585225325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608458828837932780300433 456344121628449585225325)
                      ·
                        rfl

theorem cell23_888727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_888727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888727 prefixEnd_888727 := by exact prefixLift 888727
  have htrace : WordTrace (prefixWord ++ tailWord_888727) baseStart_888727 baseEnd_888727 := by
    simpa [prefixWord, tailWord_888727, baseEnd_888727] using wordTrace_append hprefix tailTrace_888727
  have hstable : (prefixWord ++ tailWord_888727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888727).length < 2 ^ (prefixWord ++ tailWord_888727).sum := by decide
  have hdescent : baseEnd_888727 < baseStart_888727 := by decide
  rcases family_descends (prefixWord ++ tailWord_888727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888738 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_888738 : Nat := 118140960795 + 888738 * 2 ^ 59
def prefixEnd_888738 : Nat := 4983230072969 + 3 ^ 40 * 888738 * 2
def baseEnd_888738 : Nat := 456349769915649042187775

theorem tailTrace_888738 : CollatzResearch.WordTrace tailWord_888738 prefixEnd_888738 456349769915649042187775 := by
  unfold tailWord_888738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103734463565371302834717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21609958569507656807559245 8103734463565371302834717)
  ·
    refine ⟨3038900423837014238563019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8103734463565371302834717 3038900423837014238563019)
    ·
      refine ⟨4558350635755521357844529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038900423837014238563019 4558350635755521357844529)
      ·
        refine ⟨3418762976816641018383397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558350635755521357844529 3418762976816641018383397)
        ·
          refine ⟨641018058153120190946887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3418762976816641018383397 641018058153120190946887)
          ·
            refine ⟨961527087229680286420331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641018058153120190946887 961527087229680286420331)
            ·
              refine ⟨1442290630844520429630497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961527087229680286420331 1442290630844520429630497)
              ·
                refine ⟨1081717973133390322222873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442290630844520429630497 1081717973133390322222873)
                ·
                  refine ⟨811288479850042741667155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081717973133390322222873 811288479850042741667155)
                  ·
                    refine ⟨1216932719775064112500733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811288479850042741667155 1216932719775064112500733)
                    ·
                      refine ⟨456349769915649042187775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1216932719775064112500733 456349769915649042187775)
                      ·
                        rfl

theorem cell23_888738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_888738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888738 prefixEnd_888738 := by exact prefixLift 888738
  have htrace : WordTrace (prefixWord ++ tailWord_888738) baseStart_888738 baseEnd_888738 := by
    simpa [prefixWord, tailWord_888738, baseEnd_888738] using wordTrace_append hprefix tailTrace_888738
  have hstable : (prefixWord ++ tailWord_888738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888738).length < 2 ^ (prefixWord ++ tailWord_888738).sum := by decide
  have hdescent : baseEnd_888738 < baseStart_888738 := by decide
  rcases family_descends (prefixWord ++ tailWord_888738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888740 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_888740 : Nat := 118140960795 + 888740 * 2 ^ 59
def prefixEnd_888740 : Nat := 4983230072969 + 3 ^ 40 * 888740 * 2
def baseEnd_888740 : Nat := 456350796876958034362765

theorem tailTrace_888740 : CollatzResearch.WordTrace tailWord_888740 prefixEnd_888740 456350796876958034362765 := by
  unfold tailWord_888740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207505400127119776455837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21610007200169493035274449 16207505400127119776455837)
  ·
    refine ⟨6077814525047669916170939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16207505400127119776455837 6077814525047669916170939)
    ·
      refine ⟨9116721787571504874256409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077814525047669916170939 9116721787571504874256409)
      ·
        refine ⟨6837541340678628655692307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9116721787571504874256409 6837541340678628655692307)
        ·
          refine ⟨10256312011017942983538461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837541340678628655692307 10256312011017942983538461)
          ·
            refine ⟨3846117004131728618826923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10256312011017942983538461 3846117004131728618826923)
            ·
              refine ⟨5769175506197592928240385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846117004131728618826923 5769175506197592928240385)
              ·
                refine ⟨4326881629648194696180289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769175506197592928240385 4326881629648194696180289)
                ·
                  refine ⟨3245161222236146022135217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326881629648194696180289 3245161222236146022135217)
                  ·
                    refine ⟨2433870916677109516601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245161222236146022135217 2433870916677109516601413)
                    ·
                      refine ⟨456350796876958034362765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2433870916677109516601413 456350796876958034362765)
                      ·
                        rfl

theorem cell23_888740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_888740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888740 prefixEnd_888740 := by exact prefixLift 888740
  have htrace : WordTrace (prefixWord ++ tailWord_888740) baseStart_888740 baseEnd_888740 := by
    simpa [prefixWord, tailWord_888740, baseEnd_888740] using wordTrace_append hprefix tailTrace_888740
  have hstable : (prefixWord ++ tailWord_888740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888740).length < 2 ^ (prefixWord ++ tailWord_888740).sum := by decide
  have hdescent : baseEnd_888740 < baseStart_888740 := by decide
  rcases family_descends (prefixWord ++ tailWord_888740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888760 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_888760 : Nat := 118140960795 + 888760 * 2 ^ 59
def prefixEnd_888760 : Nat := 4983230072969 + 3 ^ 40 * 888760 * 2
def baseEnd_888760 : Nat := 456361066490047956112673

theorem tailTrace_888760 : CollatzResearch.WordTrace tailWord_888760 prefixEnd_888760 456361066490047956112673 := by
  unfold tailWord_888760
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207870130090891484319867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21610493506787855312426489 16207870130090891484319867)
  ·
    refine ⟨24311805195136337226479801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16207870130090891484319867 24311805195136337226479801)
    ·
      refine ⟨18233853896352252919859851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24311805195136337226479801 18233853896352252919859851)
      ·
        refine ⟨27350780844528379379789777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233853896352252919859851 27350780844528379379789777)
        ·
          refine ⟨20513085633396284534842333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27350780844528379379789777 20513085633396284534842333)
          ·
            refine ⟨7692407112523606700565875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20513085633396284534842333 7692407112523606700565875)
            ·
              refine ⟨11538610668785410050848813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692407112523606700565875 11538610668785410050848813)
              ·
                refine ⟨4326979000794528769068305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538610668785410050848813 4326979000794528769068305)
                ·
                  refine ⟨3245234250595896576801229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326979000794528769068305 3245234250595896576801229)
                  ·
                    refine ⟨1216962843973461216300461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245234250595896576801229 1216962843973461216300461)
                    ·
                      refine ⟨456361066490047956112673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1216962843973461216300461 456361066490047956112673)
                      ·
                        rfl

theorem cell23_888760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_888760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888760 prefixEnd_888760 := by exact prefixLift 888760
  have htrace : WordTrace (prefixWord ++ tailWord_888760) baseStart_888760 baseEnd_888760 := by
    simpa [prefixWord, tailWord_888760, baseEnd_888760] using wordTrace_append hprefix tailTrace_888760
  have hstable : (prefixWord ++ tailWord_888760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888760).length < 2 ^ (prefixWord ++ tailWord_888760).sum := by decide
  have hdescent : baseEnd_888760 < baseStart_888760 := by decide
  rcases family_descends (prefixWord ++ tailWord_888760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888761 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 2, 2, 2]
def baseStart_888761 : Nat := 118140960795 + 888761 * 2 ^ 59
def prefixEnd_888761 : Nat := 4983230072969 + 3 ^ 40 * 888761 * 2
def baseEnd_888761 : Nat := 456361579970702452200169

theorem tailTrace_888761 : CollatzResearch.WordTrace tailWord_888761 prefixEnd_888761 456361579970702452200169 := by
  unfold tailWord_888761
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415776733178160139426137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610517822118773426284091 32415776733178160139426137)
  ·
    refine ⟨24311832549883620104569603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32415776733178160139426137 24311832549883620104569603)
    ·
      refine ⟨36467748824825430156854405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311832549883620104569603 36467748824825430156854405)
      ·
        refine ⟨6837702904654768154410201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36467748824825430156854405 6837702904654768154410201)
        ·
          refine ⟨5128277178491076115807651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6837702904654768154410201 5128277178491076115807651)
          ·
            refine ⟨7692415767736614173711477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128277178491076115807651 7692415767736614173711477)
            ·
              refine ⟨721163978225307578785451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7692415767736614173711477 721163978225307578785451)
              ·
                refine ⟨1081745967337961368178177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721163978225307578785451 1081745967337961368178177)
                ·
                  refine ⟨811309475503471026133633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081745967337961368178177 811309475503471026133633)
                  ·
                    refine ⟨608482106627603269600225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811309475503471026133633 608482106627603269600225)
                    ·
                      refine ⟨456361579970702452200169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608482106627603269600225 456361579970702452200169)
                      ·
                        rfl

theorem cell23_888761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_888761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888761 prefixEnd_888761 := by exact prefixLift 888761
  have htrace : WordTrace (prefixWord ++ tailWord_888761) baseStart_888761 baseEnd_888761 := by
    simpa [prefixWord, tailWord_888761, baseEnd_888761] using wordTrace_append hprefix tailTrace_888761
  have hstable : (prefixWord ++ tailWord_888761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888761).length < 2 ^ (prefixWord ++ tailWord_888761).sum := by decide
  have hdescent : baseEnd_888761 < baseStart_888761 := by decide
  rcases family_descends (prefixWord ++ tailWord_888761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888763 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 7]
def baseStart_888763 : Nat := 118140960795 + 888763 * 2 ^ 59
def prefixEnd_888763 : Nat := 4983230072969 + 3 ^ 40 * 888763 * 2
def baseEnd_888763 : Nat := 152120868977337148125053

theorem tailTrace_888763 : CollatzResearch.WordTrace tailWord_888763 prefixEnd_888763 152120868977337148125053 := by
  unfold tailWord_888763
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415849679170914480998943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610566452780609653999295 32415849679170914480998943)
  ·
    refine ⟨48623774518756371721498415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32415849679170914480998943 48623774518756371721498415)
    ·
      refine ⟨72935661778134557582247623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48623774518756371721498415 72935661778134557582247623)
      ·
        refine ⟨109403492667201836373371435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72935661778134557582247623 109403492667201836373371435)
        ·
          refine ⟨164105239000802754560057153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109403492667201836373371435 164105239000802754560057153)
          ·
            refine ⟨123078929250602065920042865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164105239000802754560057153 123078929250602065920042865)
            ·
              refine ⟨92309196937951549440032149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123078929250602065920042865 92309196937951549440032149)
              ·
                refine ⟨4326993606466478880001507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92309196937951549440032149 4326993606466478880001507)
                ·
                  refine ⟨6490490409699718320002261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326993606466478880001507 6490490409699718320002261)
                  ·
                    refine ⟨152120868977337148125053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6490490409699718320002261 152120868977337148125053)
                    ·
                      rfl

theorem cell23_888763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_888763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888763 prefixEnd_888763 := by exact prefixLift 888763
  have htrace : WordTrace (prefixWord ++ tailWord_888763) baseStart_888763 baseEnd_888763 := by
    simpa [prefixWord, tailWord_888763, baseEnd_888763] using wordTrace_append hprefix tailTrace_888763
  have hstable : (prefixWord ++ tailWord_888763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888763).length < 2 ^ (prefixWord ++ tailWord_888763).sum := by decide
  have hdescent : baseEnd_888763 < baseStart_888763 := by decide
  rcases family_descends (prefixWord ++ tailWord_888763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888773 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_888773 : Nat := 118140960795 + 888773 * 2 ^ 59
def prefixEnd_888773 : Nat := 4983230072969 + 3 ^ 40 * 888773 * 2
def baseEnd_888773 : Nat := 456367741738556405250113

theorem tailTrace_888773 : CollatzResearch.WordTrace tailWord_888773 prefixEnd_888773 456367741738556405250113 := by
  unfold tailWord_888773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416214409134686188862973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610809606089790792575315 32416214409134686188862973)
  ·
    refine ⟨12156080403425507320823615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32416214409134686188862973 12156080403425507320823615)
    ·
      refine ⟨18234120605138260981235423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12156080403425507320823615 18234120605138260981235423)
      ·
        refine ⟨27351180907707391471853135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18234120605138260981235423 27351180907707391471853135)
        ·
          refine ⟨41026771361561087207779703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27351180907707391471853135 41026771361561087207779703)
          ·
            refine ⟨61540157042341630811669555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41026771361561087207779703 61540157042341630811669555)
            ·
              refine ⟨92310235563512446217504333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61540157042341630811669555 92310235563512446217504333)
              ·
                refine ⟨34616338336317167331564125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92310235563512446217504333 34616338336317167331564125)
                ·
                  refine ⟨12981126876118937749336547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34616338336317167331564125 12981126876118937749336547)
                  ·
                    refine ⟨19471690314178406624004821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981126876118937749336547 19471690314178406624004821)
                    ·
                      refine ⟨456367741738556405250113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19471690314178406624004821 456367741738556405250113)
                      ·
                        rfl

theorem cell23_888773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_888773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888773 prefixEnd_888773 := by exact prefixLift 888773
  have htrace : WordTrace (prefixWord ++ tailWord_888773) baseStart_888773 baseEnd_888773 := by
    simpa [prefixWord, tailWord_888773, baseEnd_888773] using wordTrace_append hprefix tailTrace_888773
  have hstable : (prefixWord ++ tailWord_888773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888773).length < 2 ^ (prefixWord ++ tailWord_888773).sum := by decide
  have hdescent : baseEnd_888773 < baseStart_888773 := by decide
  rcases family_descends (prefixWord ++ tailWord_888773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888780 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_888780 : Nat := 118140960795 + 888780 * 2 ^ 59
def prefixEnd_888780 : Nat := 4983230072969 + 3 ^ 40 * 888780 * 2
def baseEnd_888780 : Nat := 152123778701045959287527

theorem tailTrace_888780 : CollatzResearch.WordTrace tailWord_888780 prefixEnd_888780 152123778701045959287527 := by
  unfold tailWord_888780
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208234860054663192183897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21610979813406217589578529 16208234860054663192183897)
  ·
    refine ⟨12156176145040997394137923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16208234860054663192183897 12156176145040997394137923)
    ·
      refine ⟨18234264217561496091206885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12156176145040997394137923 18234264217561496091206885)
      ·
        refine ⟨3418924540792780517101291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18234264217561496091206885 3418924540792780517101291)
        ·
          refine ⟨5128386811189170775651937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418924540792780517101291 5128386811189170775651937)
          ·
            refine ⟨3846290108391878081738953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5128386811189170775651937 3846290108391878081738953)
            ·
              refine ⟨2884717581293908561304215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846290108391878081738953 2884717581293908561304215)
              ·
                refine ⟨4327076371940862841956323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884717581293908561304215 4327076371940862841956323)
                ·
                  refine ⟨6490614557911294262934485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327076371940862841956323 6490614557911294262934485)
                  ·
                    refine ⟨152123778701045959287527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6490614557911294262934485 152123778701045959287527)
                    ·
                      rfl

theorem cell23_888780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_888780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888780 prefixEnd_888780 := by exact prefixLift 888780
  have htrace : WordTrace (prefixWord ++ tailWord_888780) baseStart_888780 baseEnd_888780 := by
    simpa [prefixWord, tailWord_888780, baseEnd_888780] using wordTrace_append hprefix tailTrace_888780
  have hstable : (prefixWord ++ tailWord_888780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888780).length < 2 ^ (prefixWord ++ tailWord_888780).sum := by decide
  have hdescent : baseEnd_888780 < baseStart_888780 := by decide
  rcases family_descends (prefixWord ++ tailWord_888780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888807 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_888807 : Nat := 118140960795 + 888807 * 2 ^ 59
def prefixEnd_888807 : Nat := 4983230072969 + 3 ^ 40 * 888807 * 2
def baseEnd_888807 : Nat := 456385200080809272224957

theorem tailTrace_888807 : CollatzResearch.WordTrace tailWord_888807 prefixEnd_888807 456385200080809272224957 := by
  unfold tailWord_888807
  simp only [CollatzResearch.WordTrace]
  refine ⟨32417454491011509995600675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21611636327341006663733783 32417454491011509995600675)
  ·
    refine ⟨48626181736517264993401013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32417454491011509995600675 48626181736517264993401013)
    ·
      refine ⟨4558704537798493593131345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48626181736517264993401013 4558704537798493593131345)
      ·
        refine ⟨3419028403348870194848509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558704537798493593131345 3419028403348870194848509)
        ·
          refine ⟨1282135651255826323068191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3419028403348870194848509 1282135651255826323068191)
          ·
            refine ⟨1923203476883739484602287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282135651255826323068191 1923203476883739484602287)
            ·
              refine ⟨2884805215325609226903431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923203476883739484602287 2884805215325609226903431)
              ·
                refine ⟨4327207822988413840355147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884805215325609226903431 4327207822988413840355147)
                ·
                  refine ⟨6490811734482620760532721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327207822988413840355147 6490811734482620760532721)
                  ·
                    refine ⟨4868108800861965570399541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490811734482620760532721 4868108800861965570399541)
                    ·
                      refine ⟨456385200080809272224957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4868108800861965570399541 456385200080809272224957)
                      ·
                        rfl

theorem cell23_888807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_888807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888807 prefixEnd_888807 := by exact prefixLift 888807
  have htrace : WordTrace (prefixWord ++ tailWord_888807) baseStart_888807 baseEnd_888807 := by
    simpa [prefixWord, tailWord_888807, baseEnd_888807] using wordTrace_append hprefix tailTrace_888807
  have hstable : (prefixWord ++ tailWord_888807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888807).length < 2 ^ (prefixWord ++ tailWord_888807).sum := by decide
  have hdescent : baseEnd_888807 < baseStart_888807 := by decide
  rcases family_descends (prefixWord ++ tailWord_888807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888837 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_888837 : Nat := 118140960795 + 888837 * 2 ^ 59
def prefixEnd_888837 : Nat := 4983230072969 + 3 ^ 40 * 888837 * 2
def baseEnd_888837 : Nat := 456400604500444154849819

theorem tailTrace_888837 : CollatzResearch.WordTrace tailWord_888837 prefixEnd_888837 456400604500444154849819 := by
  unfold tailWord_888837
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418548680902825119192765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21612365787268550079461843 32418548680902825119192765)
  ·
    refine ⟨12156955755338559419697287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32418548680902825119192765 12156955755338559419697287)
    ·
      refine ⟨18235433633007839129545931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12156955755338559419697287 18235433633007839129545931)
      ·
        refine ⟨27353150449511758694318897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18235433633007839129545931 27353150449511758694318897)
        ·
          refine ⟨20514862837133819020739173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27353150449511758694318897 20514862837133819020739173)
          ·
            refine ⟨3846536781962591066388595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20514862837133819020739173 3846536781962591066388595)
            ·
              refine ⟨5769805172943886599582893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846536781962591066388595 5769805172943886599582893)
              ·
                refine ⟨2163676939853957474843585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769805172943886599582893 2163676939853957474843585)
                ·
                  refine ⟨1622757704890468106132689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163676939853957474843585 1622757704890468106132689)
                  ·
                    refine ⟨1217068278667851079599517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622757704890468106132689 1217068278667851079599517)
                    ·
                      refine ⟨456400604500444154849819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217068278667851079599517 456400604500444154849819)
                      ·
                        rfl

theorem cell23_888837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_888837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888837 prefixEnd_888837 := by exact prefixLift 888837
  have htrace : WordTrace (prefixWord ++ tailWord_888837) baseStart_888837 baseEnd_888837 := by
    simpa [prefixWord, tailWord_888837, baseEnd_888837] using wordTrace_append hprefix tailTrace_888837
  have hstable : (prefixWord ++ tailWord_888837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888837).length < 2 ^ (prefixWord ++ tailWord_888837).sum := by decide
  have hdescent : baseEnd_888837 < baseStart_888837 := by decide
  rcases family_descends (prefixWord ++ tailWord_888837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888844 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_888844 : Nat := 118140960795 + 888844 * 2 ^ 59
def prefixEnd_888844 : Nat := 4983230072969 + 3 ^ 40 * 888844 * 2
def baseEnd_888844 : Nat := 152134732955008542487429

theorem tailTrace_888844 : CollatzResearch.WordTrace tailWord_888844 prefixEnd_888844 152134732955008542487429 := by
  unfold tailWord_888844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209401995938732657348793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21612535994584976876465057 16209401995938732657348793)
  ·
    refine ⟨12157051496954049493011595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209401995938732657348793 12157051496954049493011595)
    ·
      refine ⟨18235577245431074239517393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12157051496954049493011595 18235577245431074239517393)
      ·
        refine ⟨13676682934073305679638045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18235577245431074239517393 13676682934073305679638045)
        ·
          refine ⟨5128756100277489629864267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13676682934073305679638045 5128756100277489629864267)
          ·
            refine ⟨7693134150416234444796401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128756100277489629864267 7693134150416234444796401)
            ·
              refine ⟨5769850612812175833597301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693134150416234444796401 5769850612812175833597301)
              ·
                refine ⟨540923494951141484399747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5769850612812175833597301 540923494951141484399747)
                ·
                  refine ⟨811385242426712226599621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540923494951141484399747 811385242426712226599621)
                  ·
                    refine ⟨152134732955008542487429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811385242426712226599621 152134732955008542487429)
                    ·
                      rfl

theorem cell23_888844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_888844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888844 prefixEnd_888844 := by exact prefixLift 888844
  have htrace : WordTrace (prefixWord ++ tailWord_888844) baseStart_888844 baseEnd_888844 := by
    simpa [prefixWord, tailWord_888844, baseEnd_888844] using wordTrace_append hprefix tailTrace_888844
  have hstable : (prefixWord ++ tailWord_888844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888844).length < 2 ^ (prefixWord ++ tailWord_888844).sum := by decide
  have hdescent : baseEnd_888844 < baseStart_888844 := by decide
  rcases family_descends (prefixWord ++ tailWord_888844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888861 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_888861 : Nat := 118140960795 + 888861 * 2 ^ 59
def prefixEnd_888861 : Nat := 4983230072969 + 3 ^ 40 * 888861 * 2
def baseEnd_888861 : Nat := 152137642678717353649903

theorem tailTrace_888861 : CollatzResearch.WordTrace tailWord_888861 prefixEnd_888861 152137642678717353649903 := by
  unfold tailWord_888861
  simp only [CollatzResearch.WordTrace]
  refine ⟨32419424032815877218066437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21612949355210584812044291 32419424032815877218066437)
  ·
    refine ⟨6078642006152976978387457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32419424032815877218066437 6078642006152976978387457)
    ·
      refine ⟨4558981504614732733790593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078642006152976978387457 4558981504614732733790593)
      ·
        refine ⟨3419236128461049550342945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558981504614732733790593 3419236128461049550342945)
        ·
          refine ⟨2564427096345787162757209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419236128461049550342945 2564427096345787162757209)
          ·
            refine ⟨1923320322259340372067907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564427096345787162757209 1923320322259340372067907)
            ·
              refine ⟨2884980483389010558101861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923320322259340372067907 2884980483389010558101861)
              ·
                refine ⟨540933840635439479644099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2884980483389010558101861 540933840635439479644099)
                ·
                  refine ⟨811400760953159219466149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540933840635439479644099 811400760953159219466149)
                  ·
                    refine ⟨152137642678717353649903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811400760953159219466149 152137642678717353649903)
                    ·
                      rfl

theorem cell23_888861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_888861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888861 prefixEnd_888861 := by exact prefixLift 888861
  have htrace : WordTrace (prefixWord ++ tailWord_888861) baseStart_888861 baseEnd_888861 := by
    simpa [prefixWord, tailWord_888861, baseEnd_888861] using wordTrace_append hprefix tailTrace_888861
  have hstable : (prefixWord ++ tailWord_888861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888861).length < 2 ^ (prefixWord ++ tailWord_888861).sum := by decide
  have hdescent : baseEnd_888861 < baseStart_888861 := by decide
  rcases family_descends (prefixWord ++ tailWord_888861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888907 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 4]
def baseStart_888907 : Nat := 118140960795 + 888907 * 2 ^ 59
def prefixEnd_888907 : Nat := 4983230072969 + 3 ^ 40 * 888907 * 2
def baseEnd_888907 : Nat := 456436548146258880974497

theorem tailTrace_888907 : CollatzResearch.WordTrace tailWord_888907 prefixEnd_888907 456436548146258880974497 := by
  unfold tailWord_888907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421101790649227074240975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614067860432818049493983 32421101790649227074240975)
  ·
    refine ⟨48631652685973840611361463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421101790649227074240975 48631652685973840611361463)
    ·
      refine ⟨72947479028960760917042195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48631652685973840611361463 72947479028960760917042195)
      ·
        refine ⟨109421218543441141375563293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72947479028960760917042195 109421218543441141375563293)
        ·
          refine ⟨41032956953790428015836235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109421218543441141375563293 41032956953790428015836235)
          ·
            refine ⟨61549435430685642023754353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41032956953790428015836235 61549435430685642023754353)
            ·
              refine ⟨46162076573014231517815765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61549435430685642023754353 46162076573014231517815765)
              ·
                refine ⟨1081923669680021051198807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46162076573014231517815765 1081923669680021051198807)
                ·
                  refine ⟨1622885504520031576798211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081923669680021051198807 1622885504520031576798211)
                  ·
                    refine ⟨2434328256780047365197317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622885504520031576798211 2434328256780047365197317)
                    ·
                      refine ⟨456436548146258880974497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2434328256780047365197317 456436548146258880974497)
                      ·
                        rfl

theorem cell23_888907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 4].length) (baseStart_888907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888907 prefixEnd_888907 := by exact prefixLift 888907
  have htrace : WordTrace (prefixWord ++ tailWord_888907) baseStart_888907 baseEnd_888907 := by
    simpa [prefixWord, tailWord_888907, baseEnd_888907] using wordTrace_append hprefix tailTrace_888907
  have hstable : (prefixWord ++ tailWord_888907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888907).length < 2 ^ (prefixWord ++ tailWord_888907).sum := by decide
  have hdescent : baseEnd_888907 < baseStart_888907 := by decide
  rcases family_descends (prefixWord ++ tailWord_888907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888918 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_888918 : Nat := 118140960795 + 888918 * 2 ^ 59
def prefixEnd_888918 : Nat := 4983230072969 + 3 ^ 40 * 888918 * 2
def baseEnd_888918 : Nat := 456442196433458337936947

theorem tailTrace_888918 : CollatzResearch.WordTrace tailWord_888918 prefixEnd_888918 456442196433458337936947 := by
  unfold tailWord_888918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026343937100585997055713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21614335329072917301927605 2026343937100585997055713)
  ·
    refine ⟨1519757952825439497791785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2026343937100585997055713 1519757952825439497791785)
    ·
      refine ⟨1139818464619079623343839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1519757952825439497791785 1139818464619079623343839)
      ·
        refine ⟨1709727696928619435015759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139818464619079623343839 1709727696928619435015759)
        ·
          refine ⟨2564591545392929152523639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709727696928619435015759 2564591545392929152523639)
          ·
            refine ⟨3846887318089393728785459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564591545392929152523639 3846887318089393728785459)
            ·
              refine ⟨5770330977134090593178189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846887318089393728785459 5770330977134090593178189)
              ·
                refine ⟨2163874116425283972441821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5770330977134090593178189 2163874116425283972441821)
                ·
                  refine ⟨811452793659481489665683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2163874116425283972441821 811452793659481489665683)
                  ·
                    refine ⟨1217179190489222234498525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811452793659481489665683 1217179190489222234498525)
                    ·
                      refine ⟨456442196433458337936947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217179190489222234498525 456442196433458337936947)
                      ·
                        rfl

theorem cell23_888918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_888918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888918 prefixEnd_888918 := by exact prefixLift 888918
  have htrace : WordTrace (prefixWord ++ tailWord_888918) baseStart_888918 baseEnd_888918 := by
    simpa [prefixWord, tailWord_888918, baseEnd_888918] using wordTrace_append hprefix tailTrace_888918
  have hstable : (prefixWord ++ tailWord_888918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888918).length < 2 ^ (prefixWord ++ tailWord_888918).sum := by decide
  have hdescent : baseEnd_888918 < baseStart_888918 := by decide
  rcases family_descends (prefixWord ++ tailWord_888918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888927 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_888927 : Nat := 118140960795 + 888927 * 2 ^ 59
def prefixEnd_888927 : Nat := 4983230072969 + 3 ^ 40 * 888927 * 2
def baseEnd_888927 : Nat := 456446817759348802724405

theorem tailTrace_888927 : CollatzResearch.WordTrace tailWord_888927 prefixEnd_888927 456446817759348802724405 := by
  unfold tailWord_888927
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421831250576770489969035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614554167051180326646023 32421831250576770489969035)
  ·
    refine ⟨48632746875865155734953553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421831250576770489969035 48632746875865155734953553)
    ·
      refine ⟨36474560156898866801215165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48632746875865155734953553 36474560156898866801215165)
      ·
        refine ⟨13677960058837075050455687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36474560156898866801215165 13677960058837075050455687)
        ·
          refine ⟨20516940088255612575683531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13677960058837075050455687 20516940088255612575683531)
          ·
            refine ⟨30775410132383418863525297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20516940088255612575683531 30775410132383418863525297)
            ·
              refine ⟨23081557599287564147643973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30775410132383418863525297 23081557599287564147643973)
              ·
                refine ⟨4327792049866418277683245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23081557599287564147643973 4327792049866418277683245)
                ·
                  refine ⟨1622922018699906854131217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4327792049866418277683245 1622922018699906854131217)
                  ·
                    refine ⟨1217191514024930140598413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622922018699906854131217 1217191514024930140598413)
                    ·
                      refine ⟨456446817759348802724405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217191514024930140598413 456446817759348802724405)
                      ·
                        rfl

theorem cell23_888927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_888927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888927 prefixEnd_888927 := by exact prefixLift 888927
  have htrace : WordTrace (prefixWord ++ tailWord_888927) baseStart_888927 baseEnd_888927 := by
    simpa [prefixWord, tailWord_888927, baseEnd_888927] using wordTrace_append hprefix tailTrace_888927
  have hstable : (prefixWord ++ tailWord_888927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888927).length < 2 ^ (prefixWord ++ tailWord_888927).sum := by decide
  have hdescent : baseEnd_888927 < baseStart_888927 := by decide
  rcases family_descends (prefixWord ++ tailWord_888927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888941 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_888941 : Nat := 118140960795 + 888941 * 2 ^ 59
def prefixEnd_888941 : Nat := 4983230072969 + 3 ^ 40 * 888941 * 2
def baseEnd_888941 : Nat := 456454006488511747949341

theorem tailTrace_888941 : CollatzResearch.WordTrace tailWord_888941 prefixEnd_888941 456454006488511747949341 := by
  unfold tailWord_888941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32422341872526050880978677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614894581684033920652451 32422341872526050880978677)
  ·
    refine ⟨3039594550549317270091751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32422341872526050880978677 3039594550549317270091751)
    ·
      refine ⟨4559391825823975905137627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039594550549317270091751 4559391825823975905137627)
      ·
        refine ⟨6839087738735963857706441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559391825823975905137627 6839087738735963857706441)
        ·
          refine ⟨5129315804051972893279831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839087738735963857706441 5129315804051972893279831)
          ·
            refine ⟨7693973706077959339919747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129315804051972893279831 7693973706077959339919747)
            ·
              refine ⟨11540960559116939009879621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693973706077959339919747 11540960559116939009879621)
              ·
                refine ⟨2163930104834426064352429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11540960559116939009879621 2163930104834426064352429)
                ·
                  refine ⟨811473789312909774132161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2163930104834426064352429 811473789312909774132161)
                  ·
                    refine ⟨608605341984682330599121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811473789312909774132161 608605341984682330599121)
                    ·
                      refine ⟨456454006488511747949341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608605341984682330599121 456454006488511747949341)
                      ·
                        rfl

theorem cell23_888941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_888941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888941 prefixEnd_888941 := by exact prefixLift 888941
  have htrace : WordTrace (prefixWord ++ tailWord_888941) baseStart_888941 baseEnd_888941 := by
    simpa [prefixWord, tailWord_888941, baseEnd_888941] using wordTrace_append hprefix tailTrace_888941
  have hstable : (prefixWord ++ tailWord_888941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888941).length < 2 ^ (prefixWord ++ tailWord_888941).sum := by decide
  have hdescent : baseEnd_888941 < baseStart_888941 := by decide
  rcases family_descends (prefixWord ++ tailWord_888941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888944 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_888944 : Nat := 118140960795 + 888944 * 2 ^ 59
def prefixEnd_888944 : Nat := 4983230072969 + 3 ^ 40 * 888944 * 2
def baseEnd_888944 : Nat := 456455546930475236211827

theorem tailTrace_888944 : CollatzResearch.WordTrace tailWord_888944 prefixEnd_888944 456455546930475236211827 := by
  unfold tailWord_888944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211225645757591196668943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21614967527676788262225257 16211225645757591196668943)
  ·
    refine ⟨24316838468636386795003415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211225645757591196668943 24316838468636386795003415)
    ·
      refine ⟨36475257702954580192505123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24316838468636386795003415 36475257702954580192505123)
      ·
        refine ⟨54712886554431870288757685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36475257702954580192505123 54712886554431870288757685)
        ·
          refine ⟨5129333114477987839571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54712886554431870288757685 5129333114477987839571033)
          ·
            refine ⟨3846999835858490879678275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129333114477987839571033 3846999835858490879678275)
            ·
              refine ⟨5770499753787736319517413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846999835858490879678275 5770499753787736319517413)
              ·
                refine ⟨1081968703835200559909515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5770499753787736319517413 1081968703835200559909515)
                ·
                  refine ⟨1622953055752800839864273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081968703835200559909515 1622953055752800839864273)
                  ·
                    refine ⟨1217214791814600629898205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622953055752800839864273 1217214791814600629898205)
                    ·
                      refine ⟨456455546930475236211827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217214791814600629898205 456455546930475236211827)
                      ·
                        rfl

theorem cell23_888944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_888944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888944 prefixEnd_888944 := by exact prefixLift 888944
  have htrace : WordTrace (prefixWord ++ tailWord_888944) baseStart_888944 baseEnd_888944 := by
    simpa [prefixWord, tailWord_888944, baseEnd_888944] using wordTrace_append hprefix tailTrace_888944
  have hstable : (prefixWord ++ tailWord_888944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888944).length < 2 ^ (prefixWord ++ tailWord_888944).sum := by decide
  have hdescent : baseEnd_888944 < baseStart_888944 := by decide
  rcases family_descends (prefixWord ++ tailWord_888944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888960 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_888960 : Nat := 118140960795 + 888960 * 2 ^ 59
def prefixEnd_888960 : Nat := 4983230072969 + 3 ^ 40 * 888960 * 2
def baseEnd_888960 : Nat := 152154587540315724537251

theorem tailTrace_888960 : CollatzResearch.WordTrace tailWord_888960 prefixEnd_888960 152154587540315724537251 := by
  unfold tailWord_888960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211517429728608562960167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21615356572971478083946889 16211517429728608562960167)
  ·
    refine ⟨24317276144592912844440251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211517429728608562960167 24317276144592912844440251)
    ·
      refine ⟨36475914216889369266660377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24317276144592912844440251 36475914216889369266660377)
      ·
        refine ⟨27356935662667026949995283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36475914216889369266660377 27356935662667026949995283)
        ·
          refine ⟨41035403494000540424992925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27356935662667026949995283 41035403494000540424992925)
          ·
            refine ⟨15388276310250202659372347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41035403494000540424992925 15388276310250202659372347)
            ·
              refine ⟨23082414465375303989058521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388276310250202659372347 23082414465375303989058521)
              ·
                refine ⟨17311810849031477991793891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23082414465375303989058521 17311810849031477991793891)
                ·
                  refine ⟨25967716273547216987690837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311810849031477991793891 25967716273547216987690837)
                  ·
                    refine ⟨152154587540315724537251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25967716273547216987690837 152154587540315724537251)
                    ·
                      rfl

theorem cell23_888960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_888960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_888960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_888960 prefixEnd_888960 := by exact prefixLift 888960
  have htrace : WordTrace (prefixWord ++ tailWord_888960) baseStart_888960 baseEnd_888960 := by
    simpa [prefixWord, tailWord_888960, baseEnd_888960] using wordTrace_append hprefix tailTrace_888960
  have hstable : (prefixWord ++ tailWord_888960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888960).length < 2 ^ (prefixWord ++ tailWord_888960).sum := by decide
  have hdescent : baseEnd_888960 < baseStart_888960 := by decide
  rcases family_descends (prefixWord ++ tailWord_888960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889012 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_889012 : Nat := 118140960795 + 889012 * 2 ^ 59
def prefixEnd_889012 : Nat := 4983230072969 + 3 ^ 40 * 889012 * 2
def baseEnd_889012 : Nat := 456490463614980970161515

theorem tailTrace_889012 : CollatzResearch.WordTrace tailWord_889012 prefixEnd_889012 456490463614980970161515 := by
  unfold tailWord_889012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212465727634415003406645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21616620970179220004542193 16212465727634415003406645)
  ·
    refine ⟨1519918661965726406569373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16212465727634415003406645 1519918661965726406569373)
    ·
      refine ⟨569969498237147402463515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1519918661965726406569373 569969498237147402463515)
      ·
        refine ⟨854954247355721103695273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569969498237147402463515 854954247355721103695273)
        ·
          refine ⟨641215685516790827771455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854954247355721103695273 641215685516790827771455)
          ·
            refine ⟨961823528275186241657183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641215685516790827771455 961823528275186241657183)
            ·
              refine ⟨1442735292412779362485775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961823528275186241657183 1442735292412779362485775)
              ·
                refine ⟨2164102938619169043728663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442735292412779362485775 2164102938619169043728663)
                ·
                  refine ⟨3246154407928753565592995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164102938619169043728663 3246154407928753565592995)
                  ·
                    refine ⟨4869231611893130348389493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3246154407928753565592995 4869231611893130348389493)
                    ·
                      refine ⟨456490463614980970161515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4869231611893130348389493 456490463614980970161515)
                      ·
                        rfl

theorem cell23_889012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_889012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889012 prefixEnd_889012 := by exact prefixLift 889012
  have htrace : WordTrace (prefixWord ++ tailWord_889012) baseStart_889012 baseEnd_889012 := by
    simpa [prefixWord, tailWord_889012, baseEnd_889012] using wordTrace_append hprefix tailTrace_889012
  have hstable : (prefixWord ++ tailWord_889012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889012).length < 2 ^ (prefixWord ++ tailWord_889012).sum := by decide
  have hdescent : baseEnd_889012 < baseStart_889012 := by decide
  rcases family_descends (prefixWord ++ tailWord_889012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889017 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_889017 : Nat := 118140960795 + 889017 * 2 ^ 59
def prefixEnd_889017 : Nat := 4983230072969 + 3 ^ 40 * 889017 * 2
def baseEnd_889017 : Nat := 456493031018253450598991

theorem tailTrace_889017 : CollatzResearch.WordTrace tailWord_889017 prefixEnd_889017 456493031018253450598991 := by
  unfold tailWord_889017
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425113820250715860745305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21616742546833810573830203 32425113820250715860745305)
  ·
    refine ⟨24318835365188036895558979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32425113820250715860745305 24318835365188036895558979)
    ·
      refine ⟨36478253047782055343338469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24318835365188036895558979 36478253047782055343338469)
      ·
        refine ⟨6839672446459135376875963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36478253047782055343338469 6839672446459135376875963)
        ·
          refine ⟨10259508669688703065313945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839672446459135376875963 10259508669688703065313945)
          ·
            refine ⟨7694631502266527298985459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10259508669688703065313945 7694631502266527298985459)
            ·
              refine ⟨11541947253399790948478189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694631502266527298985459 11541947253399790948478189)
              ·
                refine ⟨4328230220024921605679321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11541947253399790948478189 4328230220024921605679321)
                ·
                  refine ⟨3246172665018691204259491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328230220024921605679321 3246172665018691204259491)
                  ·
                    refine ⟨4869258997528036806389237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3246172665018691204259491 4869258997528036806389237)
                    ·
                      refine ⟨456493031018253450598991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4869258997528036806389237 456493031018253450598991)
                      ·
                        rfl

theorem cell23_889017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_889017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889017 prefixEnd_889017 := by exact prefixLift 889017
  have htrace : WordTrace (prefixWord ++ tailWord_889017) baseStart_889017 baseEnd_889017 := by
    simpa [prefixWord, tailWord_889017, baseEnd_889017] using wordTrace_append hprefix tailTrace_889017
  have hstable : (prefixWord ++ tailWord_889017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889017).length < 2 ^ (prefixWord ++ tailWord_889017).sum := by decide
  have hdescent : baseEnd_889017 < baseStart_889017 := by decide
  rcases family_descends (prefixWord ++ tailWord_889017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889025 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_889025 : Nat := 118140960795 + 889025 * 2 ^ 59
def prefixEnd_889025 : Nat := 4983230072969 + 3 ^ 40 * 889025 * 2
def baseEnd_889025 : Nat := 456497138863489419298955

theorem tailTrace_889025 : CollatzResearch.WordTrace tailWord_889025 prefixEnd_889025 456497138863489419298955 := by
  unfold tailWord_889025
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425405604221733227036529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21616937069481155484691019 32425405604221733227036529)
  ·
    refine ⟨24319054203166299920277397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32425405604221733227036529 24319054203166299920277397)
    ·
      refine ⟨1139955665773420308763003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24319054203166299920277397 1139955665773420308763003)
      ·
        refine ⟨1709933498660130463144505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139955665773420308763003 1709933498660130463144505)
        ·
          refine ⟨1282450123995097847358379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709933498660130463144505 1282450123995097847358379)
          ·
            refine ⟨1923675185992646771037569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282450123995097847358379 1923675185992646771037569)
            ·
              refine ⟨1442756389494485078278177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923675185992646771037569 1442756389494485078278177)
              ·
                refine ⟨1082067292120863808708633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442756389494485078278177 1082067292120863808708633)
                ·
                  refine ⟨811550469090647856531475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1082067292120863808708633 811550469090647856531475)
                  ·
                    refine ⟨1217325703635971784797213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 811550469090647856531475 1217325703635971784797213)
                    ·
                      refine ⟨456497138863489419298955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217325703635971784797213 456497138863489419298955)
                      ·
                        rfl

theorem cell23_889025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_889025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889025 prefixEnd_889025 := by exact prefixLift 889025
  have htrace : WordTrace (prefixWord ++ tailWord_889025) baseStart_889025 baseEnd_889025 := by
    simpa [prefixWord, tailWord_889025, baseEnd_889025] using wordTrace_append hprefix tailTrace_889025
  have hstable : (prefixWord ++ tailWord_889025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889025).length < 2 ^ (prefixWord ++ tailWord_889025).sum := by decide
  have hdescent : baseEnd_889025 < baseStart_889025 := by decide
  rcases family_descends (prefixWord ++ tailWord_889025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889026 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_889026 : Nat := 118140960795 + 889026 * 2 ^ 59
def prefixEnd_889026 : Nat := 4983230072969 + 3 ^ 40 * 889026 * 2
def baseEnd_889026 : Nat := 456497652344143915386451

theorem tailTrace_889026 : CollatzResearch.WordTrace tailWord_889026 prefixEnd_889026 456497652344143915386451 := by
  unfold tailWord_889026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106360519304527599455733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21616961384812073598548621 8106360519304527599455733)
  ·
    refine ⟨759971298684799462448975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8106360519304527599455733 759971298684799462448975)
    ·
      refine ⟨1139956948027199193673463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759971298684799462448975 1139956948027199193673463)
      ·
        refine ⟨1709935422040798790510195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139956948027199193673463 1709935422040798790510195)
        ·
          refine ⟨2564903133061198185765293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709935422040798790510195 2564903133061198185765293)
          ·
            refine ⟨961838674897949319661985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2564903133061198185765293 961838674897949319661985)
            ·
              refine ⟨721379006173461989746489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961838674897949319661985 721379006173461989746489)
              ·
                refine ⟨541034254630096492309867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721379006173461989746489 541034254630096492309867)
                ·
                  refine ⟨811551381945144738464801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541034254630096492309867 811551381945144738464801)
                  ·
                    refine ⟨608663536458858553848601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811551381945144738464801 608663536458858553848601)
                    ·
                      refine ⟨456497652344143915386451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608663536458858553848601 456497652344143915386451)
                      ·
                        rfl

theorem cell23_889026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_889026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889026 prefixEnd_889026 := by exact prefixLift 889026
  have htrace : WordTrace (prefixWord ++ tailWord_889026) baseStart_889026 baseEnd_889026 := by
    simpa [prefixWord, tailWord_889026, baseEnd_889026] using wordTrace_append hprefix tailTrace_889026
  have hstable : (prefixWord ++ tailWord_889026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889026).length < 2 ^ (prefixWord ++ tailWord_889026).sum := by decide
  have hdescent : baseEnd_889026 < baseStart_889026 := by decide
  rcases family_descends (prefixWord ++ tailWord_889026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889048 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_889048 : Nat := 118140960795 + 889048 * 2 ^ 59
def prefixEnd_889048 : Nat := 4983230072969 + 3 ^ 40 * 889048 * 2
def baseEnd_889048 : Nat := 456508948918542829311349

theorem tailTrace_889048 : CollatzResearch.WordTrace tailWord_889048 prefixEnd_889048 456508948918542829311349 := by
  unfold tailWord_889048
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213122241569204077561899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21617496322092272103415865 16213122241569204077561899)
  ·
    refine ⟨24319683362353806116342849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213122241569204077561899 24319683362353806116342849)
    ·
      refine ⟨18239762521765354587257137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24319683362353806116342849 18239762521765354587257137)
      ·
        refine ⟨13679821891324015940442853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18239762521765354587257137 13679821891324015940442853)
        ·
          refine ⟨2564966604623252988833035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13679821891324015940442853 2564966604623252988833035)
          ·
            refine ⟨3847449906934879483249553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564966604623252988833035 3847449906934879483249553)
            ·
              refine ⟨2885587430201159612437165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847449906934879483249553 2885587430201159612437165)
              ·
                refine ⟨1082095286325434854663937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885587430201159612437165 1082095286325434854663937)
                ·
                  refine ⟨811571464744076140997953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1082095286325434854663937 811571464744076140997953)
                  ·
                    refine ⟨608678598558057105748465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811571464744076140997953 608678598558057105748465)
                    ·
                      refine ⟨456508948918542829311349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608678598558057105748465 456508948918542829311349)
                      ·
                        rfl

theorem cell23_889048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_889048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889048 prefixEnd_889048 := by exact prefixLift 889048
  have htrace : WordTrace (prefixWord ++ tailWord_889048) baseStart_889048 baseEnd_889048 := by
    simpa [prefixWord, tailWord_889048, baseEnd_889048] using wordTrace_append hprefix tailTrace_889048
  have hstable : (prefixWord ++ tailWord_889048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889048).length < 2 ^ (prefixWord ++ tailWord_889048).sum := by decide
  have hdescent : baseEnd_889048 < baseStart_889048 := by decide
  rcases family_descends (prefixWord ++ tailWord_889048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889067 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 7]
def baseStart_889067 : Nat := 118140960795 + 889067 * 2 ^ 59
def prefixEnd_889067 : Nat := 4983230072969 + 3 ^ 40 * 889067 * 2
def baseEnd_889067 : Nat := 152172901683659418324587

theorem tailTrace_889067 : CollatzResearch.WordTrace tailWord_889067 prefixEnd_889067 152172901683659418324587 := by
  unfold tailWord_889067
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426937470069574400065455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21617958313379716266710303 32426937470069574400065455)
  ·
    refine ⟨48640406205104361600098183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32426937470069574400065455 48640406205104361600098183)
    ·
      refine ⟨72960609307656542400147275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48640406205104361600098183 72960609307656542400147275)
      ·
        refine ⟨109440913961484813600220913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72960609307656542400147275 109440913961484813600220913)
        ·
          refine ⟨82080685471113610200165685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109440913961484813600220913 82080685471113610200165685)
          ·
            refine ⟨7695064262916900956265533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82080685471113610200165685 7695064262916900956265533)
            ·
              refine ⟨2885649098593837858599575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7695064262916900956265533 2885649098593837858599575)
              ·
                refine ⟨4328473647890756787899363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885649098593837858599575 4328473647890756787899363)
                ·
                  refine ⟨6492710471836135181849045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328473647890756787899363 6492710471836135181849045)
                  ·
                    refine ⟨152172901683659418324587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6492710471836135181849045 152172901683659418324587)
                    ·
                      rfl

theorem cell23_889067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_889067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889067 prefixEnd_889067 := by exact prefixLift 889067
  have htrace : WordTrace (prefixWord ++ tailWord_889067) baseStart_889067 baseEnd_889067 := by
    simpa [prefixWord, tailWord_889067, baseEnd_889067] using wordTrace_append hprefix tailTrace_889067
  have hstable : (prefixWord ++ tailWord_889067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889067).length < 2 ^ (prefixWord ++ tailWord_889067).sum := by decide
  have hdescent : baseEnd_889067 < baseStart_889067 := by decide
  rcases family_descends (prefixWord ++ tailWord_889067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889071 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 5]
def baseStart_889071 : Nat := 118140960795 + 889071 * 2 ^ 59
def prefixEnd_889071 : Nat := 4983230072969 + 3 ^ 40 * 889071 * 2
def baseEnd_889071 : Nat := 50724528774844026591527

theorem tailTrace_889071 : CollatzResearch.WordTrace tailWord_889071 prefixEnd_889071 50724528774844026591527 := by
  unfold tailWord_889071
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427083362055083083211067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21618055574703388722140711 32427083362055083083211067)
  ·
    refine ⟨48640625043082624624816601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32427083362055083083211067 48640625043082624624816601)
    ·
      refine ⟨36480468782311968468612451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48640625043082624624816601 36480468782311968468612451)
      ·
        refine ⟨54720703173467952702918677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36480468782311968468612451 54720703173467952702918677)
        ·
          refine ⟨2565032961256310282949313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54720703173467952702918677 2565032961256310282949313)
          ·
            refine ⟨1923774720942232712211985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565032961256310282949313 1923774720942232712211985)
            ·
              refine ⟨1442831040706674534158989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923774720942232712211985 1442831040706674534158989)
              ·
                refine ⟨541061640265002950309621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442831040706674534158989 541061640265002950309621)
                ·
                  refine ⟨50724528774844026591527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 541061640265002950309621 50724528774844026591527)
                  ·
                    rfl

theorem cell23_889071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 5].length) (baseStart_889071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889071 prefixEnd_889071 := by exact prefixLift 889071
  have htrace : WordTrace (prefixWord ++ tailWord_889071) baseStart_889071 baseEnd_889071 := by
    simpa [prefixWord, tailWord_889071, baseEnd_889071] using wordTrace_append hprefix tailTrace_889071
  have hstable : (prefixWord ++ tailWord_889071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889071).length < 2 ^ (prefixWord ++ tailWord_889071).sum := by decide
  have hdescent : baseEnd_889071 < baseStart_889071 := by decide
  rcases family_descends (prefixWord ++ tailWord_889071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889141 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_889141 : Nat := 118140960795 + 889141 * 2 ^ 59
def prefixEnd_889141 : Nat := 4983230072969 + 3 ^ 40 * 889141 * 2
def baseEnd_889141 : Nat := 456556702619410965448421

theorem tailTrace_889141 : CollatzResearch.WordTrace tailWord_889141 prefixEnd_889141 456556702619410965448421 := by
  unfold tailWord_889141
  simp only [CollatzResearch.WordTrace]
  refine ⟨32429636471801485038259277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21619757647867656692172851 32429636471801485038259277)
  ·
    refine ⟨12161113676925556889347229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32429636471801485038259277 12161113676925556889347229)
    ·
      refine ⟨4560417628847083833505211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12161113676925556889347229 4560417628847083833505211)
      ·
        refine ⟨6840626443270625750257817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560417628847083833505211 6840626443270625750257817)
        ·
          refine ⟨5130469832452969312693363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6840626443270625750257817 5130469832452969312693363)
          ·
            refine ⟨7695704748679453969040045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130469832452969312693363 7695704748679453969040045)
            ·
              refine ⟨2885889280754795238390017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7695704748679453969040045 2885889280754795238390017)
              ·
                refine ⟨2164416960566096428792513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885889280754795238390017 2164416960566096428792513)
                ·
                  refine ⟨1623312720424572321594385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164416960566096428792513 1623312720424572321594385)
                  ·
                    refine ⟨1217484540318429241195789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623312720424572321594385 1217484540318429241195789)
                    ·
                      refine ⟨456556702619410965448421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217484540318429241195789 456556702619410965448421)
                      ·
                        rfl

theorem cell23_889141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_889141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889141 prefixEnd_889141 := by exact prefixLift 889141
  have htrace : WordTrace (prefixWord ++ tailWord_889141) baseStart_889141 baseEnd_889141 := by
    simpa [prefixWord, tailWord_889141, baseEnd_889141] using wordTrace_append hprefix tailTrace_889141
  have hstable : (prefixWord ++ tailWord_889141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889141).length < 2 ^ (prefixWord ++ tailWord_889141).sum := by decide
  have hdescent : baseEnd_889141 < baseStart_889141 := by decide
  rcases family_descends (prefixWord ++ tailWord_889141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889157 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_889157 : Nat := 118140960795 + 889157 * 2 ^ 59
def prefixEnd_889157 : Nat := 4983230072969 + 3 ^ 40 * 889157 * 2
def baseEnd_889157 : Nat := 152188306103294300949449

theorem tailTrace_889157 : CollatzResearch.WordTrace tailWord_889157 prefixEnd_889157 152188306103294300949449 := by
  unfold tailWord_889157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32430220039743519770841725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21620146693162346513894483 32430220039743519770841725)
  ·
    refine ⟨12161332514903819914065647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32430220039743519770841725 12161332514903819914065647)
    ·
      refine ⟨18241998772355729871098471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12161332514903819914065647 18241998772355729871098471)
      ·
        refine ⟨27362998158533594806647707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18241998772355729871098471 27362998158533594806647707)
        ·
          refine ⟨41044497237800392209971561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27362998158533594806647707 41044497237800392209971561)
          ·
            refine ⟨30783372928350294157478671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41044497237800392209971561 30783372928350294157478671)
            ·
              refine ⟨46175059392525441236218007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30783372928350294157478671 46175059392525441236218007)
              ·
                refine ⟨69262589088788161854327011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46175059392525441236218007 69262589088788161854327011)
                ·
                  refine ⟨103893883633182242781490517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69262589088788161854327011 103893883633182242781490517)
                  ·
                    refine ⟨152188306103294300949449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 103893883633182242781490517 152188306103294300949449)
                    ·
                      rfl

theorem cell23_889157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_889157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889157 prefixEnd_889157 := by exact prefixLift 889157
  have htrace : WordTrace (prefixWord ++ tailWord_889157) baseStart_889157 baseEnd_889157 := by
    simpa [prefixWord, tailWord_889157, baseEnd_889157] using wordTrace_append hprefix tailTrace_889157
  have hstable : (prefixWord ++ tailWord_889157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889157).length < 2 ^ (prefixWord ++ tailWord_889157).sum := by decide
  have hdescent : baseEnd_889157 < baseStart_889157 := by decide
  rcases family_descends (prefixWord ++ tailWord_889157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889167 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_889167 : Nat := 118140960795 + 889167 * 2 ^ 59
def prefixEnd_889167 : Nat := 4983230072969 + 3 ^ 40 * 889167 * 2
def baseEnd_889167 : Nat := 456570053116427863723301

theorem tailTrace_889167 : CollatzResearch.WordTrace tailWord_889167 prefixEnd_889167 456570053116427863723301 := by
  unfold tailWord_889167
  simp only [CollatzResearch.WordTrace]
  refine ⟨32430584769707291478705755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21620389846471527652470503 32430584769707291478705755)
  ·
    refine ⟨48645877154560937218058633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32430584769707291478705755 48645877154560937218058633)
    ·
      refine ⟨36484407865920702913543975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48645877154560937218058633 36484407865920702913543975)
      ·
        refine ⟨54726611798881054370315963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36484407865920702913543975 54726611798881054370315963)
        ·
          refine ⟨82089917698321581555473945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54726611798881054370315963 82089917698321581555473945)
          ·
            refine ⟨61567438273741186166605459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82089917698321581555473945 61567438273741186166605459)
            ·
              refine ⟨92351157410611779249908189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61567438273741186166605459 92351157410611779249908189)
              ·
                refine ⟨34631684028979417218715571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92351157410611779249908189 34631684028979417218715571)
                ·
                  refine ⟨51947526043469125828073357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631684028979417218715571 51947526043469125828073357)
                  ·
                    refine ⟨19480322266300922185527509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51947526043469125828073357 19480322266300922185527509)
                    ·
                      refine ⟨456570053116427863723301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19480322266300922185527509 456570053116427863723301)
                      ·
                        rfl

theorem cell23_889167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_889167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889167 prefixEnd_889167 := by exact prefixLift 889167
  have htrace : WordTrace (prefixWord ++ tailWord_889167) baseStart_889167 baseEnd_889167 := by
    simpa [prefixWord, tailWord_889167, baseEnd_889167] using wordTrace_append hprefix tailTrace_889167
  have hstable : (prefixWord ++ tailWord_889167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889167).length < 2 ^ (prefixWord ++ tailWord_889167).sum := by decide
  have hdescent : baseEnd_889167 < baseStart_889167 := by decide
  rcases family_descends (prefixWord ++ tailWord_889167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889228 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_889228 : Nat := 118140960795 + 889228 * 2 ^ 59
def prefixEnd_889228 : Nat := 4983230072969 + 3 ^ 40 * 889228 * 2
def baseEnd_889228 : Nat := 456601375436352125060521

theorem tailTrace_889228 : CollatzResearch.WordTrace tailWord_889228 prefixEnd_889228 456601375436352125060521 := by
  unfold tailWord_889228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216404811243149448338169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21621873081657532597784225 16216404811243149448338169)
  ·
    refine ⟨12162303608432362086253627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16216404811243149448338169 12162303608432362086253627)
    ·
      refine ⟨18243455412648543129380441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162303608432362086253627 18243455412648543129380441)
      ·
        refine ⟨13682591559486407347035331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243455412648543129380441 13682591559486407347035331)
        ·
          refine ⟨20523887339229611020552997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682591559486407347035331 20523887339229611020552997)
          ·
            refine ⟨3848228876105552066353687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20523887339229611020552997 3848228876105552066353687)
            ·
              refine ⟨5772343314158328099530531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848228876105552066353687 5772343314158328099530531)
              ·
                refine ⟨8658514971237492149295797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772343314158328099530531 8658514971237492149295797)
                ·
                  refine ⟨811735778553514888996481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8658514971237492149295797 811735778553514888996481)
                  ·
                    refine ⟨608801833915136166747361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 811735778553514888996481 608801833915136166747361)
                    ·
                      refine ⟨456601375436352125060521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608801833915136166747361 456601375436352125060521)
                      ·
                        rfl

theorem cell23_889228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_889228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889228 prefixEnd_889228 := by exact prefixLift 889228
  have htrace : WordTrace (prefixWord ++ tailWord_889228) baseStart_889228 baseEnd_889228 := by
    simpa [prefixWord, tailWord_889228, baseEnd_889228] using wordTrace_append hprefix tailTrace_889228
  have hstable : (prefixWord ++ tailWord_889228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889228).length < 2 ^ (prefixWord ++ tailWord_889228).sum := by decide
  have hdescent : baseEnd_889228 < baseStart_889228 := by decide
  rcases family_descends (prefixWord ++ tailWord_889228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889248 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_889248 : Nat := 118140960795 + 889248 * 2 ^ 59
def prefixEnd_889248 : Nat := 4983230072969 + 3 ^ 40 * 889248 * 2
def baseEnd_889248 : Nat := 456611645049442046810429

theorem tailTrace_889248 : CollatzResearch.WordTrace tailWord_889248 prefixEnd_889248 456611645049442046810429 := by
  unfold tailWord_889248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216769541206921156202199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21622359388275894874936265 16216769541206921156202199)
  ·
    refine ⟨24325154311810381734303299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216769541206921156202199 24325154311810381734303299)
    ·
      refine ⟨36487731467715572601454949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24325154311810381734303299 36487731467715572601454949)
      ·
        refine ⟨6841449650196669862772803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36487731467715572601454949 6841449650196669862772803)
        ·
          refine ⟨10262174475295004794159205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841449650196669862772803 10262174475295004794159205)
          ·
            refine ⟨1924157714117813398904851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10262174475295004794159205 1924157714117813398904851)
            ·
              refine ⟨2886236571176720098357277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924157714117813398904851 2886236571176720098357277)
              ·
                refine ⟨1082338714191270036883979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886236571176720098357277 1082338714191270036883979)
                ·
                  refine ⟨1623508071286905055325969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082338714191270036883979 1623508071286905055325969)
                  ·
                    refine ⟨1217631053465178791494477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623508071286905055325969 1217631053465178791494477)
                    ·
                      refine ⟨456611645049442046810429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217631053465178791494477 456611645049442046810429)
                      ·
                        rfl

theorem cell23_889248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_889248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889248 prefixEnd_889248 := by exact prefixLift 889248
  have htrace : WordTrace (prefixWord ++ tailWord_889248) baseStart_889248 baseEnd_889248 := by
    simpa [prefixWord, tailWord_889248, baseEnd_889248] using wordTrace_append hprefix tailTrace_889248
  have hstable : (prefixWord ++ tailWord_889248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889248).length < 2 ^ (prefixWord ++ tailWord_889248).sum := by decide
  have hdescent : baseEnd_889248 < baseStart_889248 := by decide
  rcases family_descends (prefixWord ++ tailWord_889248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889255 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 2, 4]
def baseStart_889255 : Nat := 118140960795 + 889255 * 2 ^ 59
def prefixEnd_889255 : Nat := 4983230072969 + 3 ^ 40 * 889255 * 2
def baseEnd_889255 : Nat := 152205079804674506474299

theorem tailTrace_889255 : CollatzResearch.WordTrace tailWord_889255 prefixEnd_889255 152205079804674506474299 := by
  unfold tailWord_889255
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433794393388482507909219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21622529595592321671939479 32433794393388482507909219)
  ·
    refine ⟨48650691590082723761863829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32433794393388482507909219 48650691590082723761863829)
    ·
      refine ⟨2280501168285127676337367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48650691590082723761863829 2280501168285127676337367)
      ·
        refine ⟨3420751752427691514506051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280501168285127676337367 3420751752427691514506051)
        ·
          refine ⟨5131127628641537271759077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420751752427691514506051 5131127628641537271759077)
          ·
            refine ⟨962086430370288238454827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5131127628641537271759077 962086430370288238454827)
            ·
              refine ⟨1443129645555432357682241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962086430370288238454827 1443129645555432357682241)
              ·
                refine ⟨1082347234166574268261681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443129645555432357682241 1082347234166574268261681)
                ·
                  refine ⟨811760425624930701196261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1082347234166574268261681 811760425624930701196261)
                  ·
                    refine ⟨152205079804674506474299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811760425624930701196261 152205079804674506474299)
                    ·
                      rfl

theorem cell23_889255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_889255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889255 prefixEnd_889255 := by exact prefixLift 889255
  have htrace : WordTrace (prefixWord ++ tailWord_889255) baseStart_889255 baseEnd_889255 := by
    simpa [prefixWord, tailWord_889255, baseEnd_889255] using wordTrace_append hprefix tailTrace_889255
  have hstable : (prefixWord ++ tailWord_889255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889255).length < 2 ^ (prefixWord ++ tailWord_889255).sum := by decide
  have hdescent : baseEnd_889255 < baseStart_889255 := by decide
  rcases family_descends (prefixWord ++ tailWord_889255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889274 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_889274 : Nat := 118140960795 + 889274 * 2 ^ 59
def prefixEnd_889274 : Nat := 4983230072969 + 3 ^ 40 * 889274 * 2
def baseEnd_889274 : Nat := 456624995546458945085309

theorem tailTrace_889274 : CollatzResearch.WordTrace tailWord_889274 prefixEnd_889274 456624995546458945085309 := by
  unfold tailWord_889274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108621845079912188212719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21622991586879765835233917 8108621845079912188212719)
  ·
    refine ⟨12162932767619868282319079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108621845079912188212719 12162932767619868282319079)
    ·
      refine ⟨18244399151429802423478619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162932767619868282319079 18244399151429802423478619)
      ·
        refine ⟨27366598727144703635217929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18244399151429802423478619 27366598727144703635217929)
        ·
          refine ⟨20524949045358527726413447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27366598727144703635217929 20524949045358527726413447)
          ·
            refine ⟨30787423568037791589620171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20524949045358527726413447 30787423568037791589620171)
            ·
              refine ⟨46181135352056687384430257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787423568037791589620171 46181135352056687384430257)
              ·
                refine ⟨34635851514042515538322693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46181135352056687384430257 34635851514042515538322693)
                ·
                  refine ⟨6494222158882971663435505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34635851514042515538322693 6494222158882971663435505)
                  ·
                    refine ⟨4870666619162228747576629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6494222158882971663435505 4870666619162228747576629)
                    ·
                      refine ⟨456624995546458945085309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4870666619162228747576629 456624995546458945085309)
                      ·
                        rfl

theorem cell23_889274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_889274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889274 prefixEnd_889274 := by exact prefixLift 889274
  have htrace : WordTrace (prefixWord ++ tailWord_889274) baseStart_889274 baseEnd_889274 := by
    simpa [prefixWord, tailWord_889274, baseEnd_889274] using wordTrace_append hprefix tailTrace_889274
  have hstable : (prefixWord ++ tailWord_889274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889274).length < 2 ^ (prefixWord ++ tailWord_889274).sum := by decide
  have hdescent : baseEnd_889274 < baseStart_889274 := by decide
  rcases family_descends (prefixWord ++ tailWord_889274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889278 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_889278 : Nat := 118140960795 + 889278 * 2 ^ 59
def prefixEnd_889278 : Nat := 4983230072969 + 3 ^ 40 * 889278 * 2
def baseEnd_889278 : Nat := 456627049469076929435291

theorem tailTrace_889278 : CollatzResearch.WordTrace tailWord_889278 prefixEnd_889278 456627049469076929435291 := by
  unfold tailWord_889278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054329159038144679499561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21623088848203438290664325 4054329159038144679499561)
  ·
    refine ⟨3040746869278608509624671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4054329159038144679499561 3040746869278608509624671)
    ·
      refine ⟨4561120303917912764437007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040746869278608509624671 4561120303917912764437007)
      ·
        refine ⟨6841680455876869146655511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561120303917912764437007 6841680455876869146655511)
        ·
          refine ⟨10262520683815303719983267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841680455876869146655511 10262520683815303719983267)
          ·
            refine ⟨15393781025722955579974901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262520683815303719983267 15393781025722955579974901)
            ·
              refine ⟨1443166971161527085622647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15393781025722955579974901 1443166971161527085622647)
              ·
                refine ⟨2164750456742290628433971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443166971161527085622647 2164750456742290628433971)
                ·
                  refine ⟨3247125685113435942650957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164750456742290628433971 3247125685113435942650957)
                  ·
                    refine ⟨1217672131917538478494109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247125685113435942650957 1217672131917538478494109)
                    ·
                      refine ⟨456627049469076929435291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1217672131917538478494109 456627049469076929435291)
                      ·
                        rfl

theorem cell23_889278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_889278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889278 prefixEnd_889278 := by exact prefixLift 889278
  have htrace : WordTrace (prefixWord ++ tailWord_889278) baseStart_889278 baseEnd_889278 := by
    simpa [prefixWord, tailWord_889278, baseEnd_889278] using wordTrace_append hprefix tailTrace_889278
  have hstable : (prefixWord ++ tailWord_889278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889278).length < 2 ^ (prefixWord ++ tailWord_889278).sum := by decide
  have hdescent : baseEnd_889278 < baseStart_889278 := by decide
  rcases family_descends (prefixWord ++ tailWord_889278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889344 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_889344 : Nat := 118140960795 + 889344 * 2 ^ 59
def prefixEnd_889344 : Nat := 4983230072969 + 3 ^ 40 * 889344 * 2
def baseEnd_889344 : Nat := 456660939192273671209987

theorem tailTrace_889344 : CollatzResearch.WordTrace tailWord_889344 prefixEnd_889344 456660939192273671209987 := by
  unfold tailWord_889344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218520245033025353949543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21624693660044033805266057 16218520245033025353949543)
  ·
    refine ⟨24327780367549538030924315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218520245033025353949543 24327780367549538030924315)
    ·
      refine ⟨36491670551324307046386473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24327780367549538030924315 36491670551324307046386473)
      ·
        refine ⟨27368752913493230284789855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36491670551324307046386473 27368752913493230284789855)
        ·
          refine ⟨41053129370239845427184783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368752913493230284789855 41053129370239845427184783)
          ·
            refine ⟨61579694055359768140777175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41053129370239845427184783 61579694055359768140777175)
            ·
              refine ⟨92369541083039652211165763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61579694055359768140777175 92369541083039652211165763)
              ·
                refine ⟨138554311624559478316748645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92369541083039652211165763 138554311624559478316748645)
                ·
                  refine ⟨25978933429604902184390371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138554311624559478316748645 25978933429604902184390371)
                  ·
                    refine ⟨38968400144407353276585557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25978933429604902184390371 38968400144407353276585557)
                    ·
                      refine ⟨456660939192273671209987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38968400144407353276585557 456660939192273671209987)
                      ·
                        rfl

theorem cell23_889344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_889344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889344 prefixEnd_889344 := by exact prefixLift 889344
  have htrace : WordTrace (prefixWord ++ tailWord_889344) baseStart_889344 baseEnd_889344 := by
    simpa [prefixWord, tailWord_889344, baseEnd_889344] using wordTrace_append hprefix tailTrace_889344
  have hstable : (prefixWord ++ tailWord_889344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889344).length < 2 ^ (prefixWord ++ tailWord_889344).sum := by decide
  have hdescent : baseEnd_889344 < baseStart_889344 := by decide
  rcases family_descends (prefixWord ++ tailWord_889344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889381 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_889381 : Nat := 118140960795 + 889381 * 2 ^ 59
def prefixEnd_889381 : Nat := 4983230072969 + 3 ^ 40 * 889381 * 2
def baseEnd_889381 : Nat := 456679937976490026447317

theorem tailTrace_889381 : CollatzResearch.WordTrace tailWord_889381 prefixEnd_889381 456679937976490026447317 := by
  unfold tailWord_889381
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438389990932006026995997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21625593327288004017997331 32438389990932006026995997)
  ·
    refine ⟨12164396246599502260123499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32438389990932006026995997 12164396246599502260123499)
    ·
      refine ⟨18246594369899253390185249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164396246599502260123499 18246594369899253390185249)
      ·
        refine ⟨13684945777424440042638937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18246594369899253390185249 13684945777424440042638937)
        ·
          refine ⟨10263709333068330031979203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13684945777424440042638937 10263709333068330031979203)
          ·
            refine ⟨15395563999602495047968805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263709333068330031979203 15395563999602495047968805)
            ·
              refine ⟨2886668249925467821494151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15395563999602495047968805 2886668249925467821494151)
              ·
                refine ⟨4330002374888201732241227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886668249925467821494151 4330002374888201732241227)
                ·
                  refine ⟨6495003562332302598361841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330002374888201732241227 6495003562332302598361841)
                  ·
                    refine ⟨4871252671749226948771381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495003562332302598361841 4871252671749226948771381)
                    ·
                      refine ⟨456679937976490026447317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4871252671749226948771381 456679937976490026447317)
                      ·
                        rfl

theorem cell23_889381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_889381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889381 prefixEnd_889381 := by exact prefixLift 889381
  have htrace : WordTrace (prefixWord ++ tailWord_889381) baseStart_889381 baseEnd_889381 := by
    simpa [prefixWord, tailWord_889381, baseEnd_889381] using wordTrace_append hprefix tailTrace_889381
  have hstable : (prefixWord ++ tailWord_889381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889381).length < 2 ^ (prefixWord ++ tailWord_889381).sum := by decide
  have hdescent : baseEnd_889381 < baseStart_889381 := by decide
  rcases family_descends (prefixWord ++ tailWord_889381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889405 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_889405 : Nat := 118140960795 + 889405 * 2 ^ 59
def prefixEnd_889405 : Nat := 4983230072969 + 3 ^ 40 * 889405 * 2
def baseEnd_889405 : Nat := 152230753837399310849069

theorem tailTrace_889405 : CollatzResearch.WordTrace tailWord_889405 prefixEnd_889405 152230753837399310849069 := by
  unfold tailWord_889405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439265342845058125869669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21626176895230038750579779 32439265342845058125869669)
  ·
    refine ⟨6082362251783448398600563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32439265342845058125869669 6082362251783448398600563)
    ·
      refine ⟨9123543377675172597900845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082362251783448398600563 9123543377675172597900845)
      ·
        refine ⟨3421328766628189724212817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9123543377675172597900845 3421328766628189724212817)
        ·
          refine ⟨2565996574971142293159613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3421328766628189724212817 2565996574971142293159613)
          ·
            refine ⟨962248715614178359934855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2565996574971142293159613 962248715614178359934855)
            ·
              refine ⟨1443373073421267539902283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962248715614178359934855 1443373073421267539902283)
              ·
                refine ⟨2165059610131901309853425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443373073421267539902283 2165059610131901309853425)
                ·
                  refine ⟨1623794707598925982390069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165059610131901309853425 1623794707598925982390069)
                  ·
                    refine ⟨152230753837399310849069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1623794707598925982390069 152230753837399310849069)
                    ·
                      rfl

theorem cell23_889405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_889405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889405 prefixEnd_889405 := by exact prefixLift 889405
  have htrace : WordTrace (prefixWord ++ tailWord_889405) baseStart_889405 baseEnd_889405 := by
    simpa [prefixWord, tailWord_889405, baseEnd_889405] using wordTrace_append hprefix tailTrace_889405
  have hstable : (prefixWord ++ tailWord_889405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889405).length < 2 ^ (prefixWord ++ tailWord_889405).sum := by decide
  have hdescent : baseEnd_889405 < baseStart_889405 := by decide
  rcases family_descends (prefixWord ++ tailWord_889405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889408 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_889408 : Nat := 118140960795 + 889408 * 2 ^ 59
def prefixEnd_889408 : Nat := 4983230072969 + 3 ^ 40 * 889408 * 2
def baseEnd_889408 : Nat := 456693801954161420809693

theorem tailTrace_889408 : CollatzResearch.WordTrace tailWord_889408 prefixEnd_889408 456693801954161420809693 := by
  unfold tailWord_889408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219687380917094819114439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21626249841222793092152585 16219687380917094819114439)
  ·
    refine ⟨24329531071375642228671659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16219687380917094819114439 24329531071375642228671659)
    ·
      refine ⟨36494296607063463343007489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24329531071375642228671659 36494296607063463343007489)
      ·
        refine ⟨27370722455297597507255617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36494296607063463343007489 27370722455297597507255617)
        ·
          refine ⟨20528041841473198130441713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27370722455297597507255617 20528041841473198130441713)
          ·
            refine ⟨15396031381104898597831285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20528041841473198130441713 15396031381104898597831285)
            ·
              refine ⟨1443377941978584243546683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15396031381104898597831285 1443377941978584243546683)
              ·
                refine ⟨2165066912967876365320025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443377941978584243546683 2165066912967876365320025)
                ·
                  refine ⟨1623800184725907273990019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165066912967876365320025 1623800184725907273990019)
                  ·
                    refine ⟨2435700277088860910985029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623800184725907273990019 2435700277088860910985029)
                    ·
                      refine ⟨456693801954161420809693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2435700277088860910985029 456693801954161420809693)
                      ·
                        rfl

theorem cell23_889408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_889408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889408 prefixEnd_889408 := by exact prefixLift 889408
  have htrace : WordTrace (prefixWord ++ tailWord_889408) baseStart_889408 baseEnd_889408 := by
    simpa [prefixWord, tailWord_889408, baseEnd_889408] using wordTrace_append hprefix tailTrace_889408
  have hstable : (prefixWord ++ tailWord_889408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889408).length < 2 ^ (prefixWord ++ tailWord_889408).sum := by decide
  have hdescent : baseEnd_889408 < baseStart_889408 := by decide
  rcases family_descends (prefixWord ++ tailWord_889408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889431 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 8]
def baseStart_889431 : Nat := 118140960795 + 889431 * 2 ^ 59
def prefixEnd_889431 : Nat := 4983230072969 + 3 ^ 40 * 889431 * 2
def baseEnd_889431 : Nat := 50745068001023870091343

theorem tailTrace_889431 : CollatzResearch.WordTrace tailWord_889431 prefixEnd_889431 50745068001023870091343 := by
  unfold tailWord_889431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440213640750864566316147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21626809093833909710877431 32440213640750864566316147)
  ·
    refine ⟨48660320461126296849474221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32440213640750864566316147 48660320461126296849474221)
    ·
      refine ⟨18247620172922361318552833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48660320461126296849474221 18247620172922361318552833)
      ·
        refine ⟨13685715129691770988914625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18247620172922361318552833 13685715129691770988914625)
        ·
          refine ⟨10264286347268828241685969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13685715129691770988914625 10264286347268828241685969)
          ·
            refine ⟨7698214760451621181264477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10264286347268828241685969 7698214760451621181264477)
            ·
              refine ⟨2886830535169357942974179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7698214760451621181264477 2886830535169357942974179)
              ·
                refine ⟨4330245802754036914461269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886830535169357942974179 4330245802754036914461269)
                ·
                  refine ⟨50745068001023870091343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4330245802754036914461269 50745068001023870091343)
                  ·
                    rfl

theorem cell23_889431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 8].length) (baseStart_889431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889431 prefixEnd_889431 := by exact prefixLift 889431
  have htrace : WordTrace (prefixWord ++ tailWord_889431) baseStart_889431 baseEnd_889431 := by
    simpa [prefixWord, tailWord_889431, baseEnd_889431] using wordTrace_append hprefix tailTrace_889431
  have hstable : (prefixWord ++ tailWord_889431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889431).length < 2 ^ (prefixWord ++ tailWord_889431).sum := by decide
  have hdescent : baseEnd_889431 < baseStart_889431 := by decide
  rcases family_descends (prefixWord ++ tailWord_889431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889469 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_889469 : Nat := 118140960795 + 889469 * 2 ^ 59
def prefixEnd_889469 : Nat := 4983230072969 + 3 ^ 40 * 889469 * 2
def baseEnd_889469 : Nat := 152241708091361894048971

theorem tailTrace_889469 : CollatzResearch.WordTrace tailWord_889469 prefixEnd_889469 152241708091361894048971 := by
  unfold tailWord_889469
  simp only [CollatzResearch.WordTrace]
  refine ⟨32441599614613197056199461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21627733076408798037466307 32441599614613197056199461)
  ·
    refine ⟨6082799927739974448037399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32441599614613197056199461 6082799927739974448037399)
    ·
      refine ⟨9124199891609961672056099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082799927739974448037399 9124199891609961672056099)
      ·
        refine ⟨13686299837414942508084149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124199891609961672056099 13686299837414942508084149)
        ·
          refine ⟨1283090609757650860132889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13686299837414942508084149 1283090609757650860132889)
          ·
            refine ⟨962317957318238145099667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283090609757650860132889 962317957318238145099667)
            ·
              refine ⟨1443476935977357217649501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962317957318238145099667 1443476935977357217649501)
              ·
                refine ⟨541303850991508956618563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443476935977357217649501 541303850991508956618563)
                ·
                  refine ⟨811955776487263434927845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541303850991508956618563 811955776487263434927845)
                  ·
                    refine ⟨152241708091361894048971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811955776487263434927845 152241708091361894048971)
                    ·
                      rfl

theorem cell23_889469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_889469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889469 prefixEnd_889469 := by exact prefixLift 889469
  have htrace : WordTrace (prefixWord ++ tailWord_889469) baseStart_889469 baseEnd_889469 := by
    simpa [prefixWord, tailWord_889469, baseEnd_889469] using wordTrace_append hprefix tailTrace_889469
  have hstable : (prefixWord ++ tailWord_889469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889469).length < 2 ^ (prefixWord ++ tailWord_889469).sum := by decide
  have hdescent : baseEnd_889469 < baseStart_889469 := by decide
  rcases family_descends (prefixWord ++ tailWord_889469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889491 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 6]
def baseStart_889491 : Nat := 118140960795 + 889491 * 2 ^ 59
def prefixEnd_889491 : Nat := 4983230072969 + 3 ^ 40 * 889491 * 2
def baseEnd_889491 : Nat := 152245473616161532023937

theorem tailTrace_889491 : CollatzResearch.WordTrace tailWord_889491 prefixEnd_889491 152245473616161532023937 := by
  unfold tailWord_889491
  simp only [CollatzResearch.WordTrace]
  refine ⟨32442402020533494813500327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21628268013688996542333551 32442402020533494813500327)
  ·
    refine ⟨48663603030800242220250491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32442402020533494813500327 48663603030800242220250491)
    ·
      refine ⟨72995404546200363330375737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48663603030800242220250491 72995404546200363330375737)
      ·
        refine ⟨54746553409650272497781803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72995404546200363330375737 54746553409650272497781803)
        ·
          refine ⟨82119830114475408746672705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54746553409650272497781803 82119830114475408746672705)
          ·
            refine ⟨61589872585856556560004529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82119830114475408746672705 61589872585856556560004529)
            ·
              refine ⟨46192404439392417420003397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61589872585856556560004529 46192404439392417420003397)
              ·
                refine ⟨8661075832386078266250637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46192404439392417420003397 8661075832386078266250637)
                ·
                  refine ⟨3247903437144779349843989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8661075832386078266250637 3247903437144779349843989)
                  ·
                    refine ⟨152245473616161532023937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3247903437144779349843989 152245473616161532023937)
                    ·
                      rfl

theorem cell23_889491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_889491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889491 prefixEnd_889491 := by exact prefixLift 889491
  have htrace : WordTrace (prefixWord ++ tailWord_889491) baseStart_889491 baseEnd_889491 := by
    simpa [prefixWord, tailWord_889491, baseEnd_889491] using wordTrace_append hprefix tailTrace_889491
  have hstable : (prefixWord ++ tailWord_889491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889491).length < 2 ^ (prefixWord ++ tailWord_889491).sum := by decide
  have hdescent : baseEnd_889491 < baseStart_889491 := by decide
  rcases family_descends (prefixWord ++ tailWord_889491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889502 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_889502 : Nat := 118140960795 + 889502 * 2 ^ 59
def prefixEnd_889502 : Nat := 4983230072969 + 3 ^ 40 * 889502 * 2
def baseEnd_889502 : Nat := 456742069135684053034261

theorem tailTrace_889502 : CollatzResearch.WordTrace tailWord_889502 prefixEnd_889502 456742069135684053034261 := by
  unfold tailWord_889502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055350402936705461518845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21628535482329095794767173 4055350402936705461518845)
  ·
    refine ⟨1520756401101264548069567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4055350402936705461518845 1520756401101264548069567)
    ·
      refine ⟨2281134601651896822104351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520756401101264548069567 2281134601651896822104351)
      ·
        refine ⟨3421701902477845233156527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281134601651896822104351 3421701902477845233156527)
        ·
          refine ⟨5132552853716767849734791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421701902477845233156527 5132552853716767849734791)
          ·
            refine ⟨7698829280575151774602187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132552853716767849734791 7698829280575151774602187)
            ·
              refine ⟨11548243920862727661903281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698829280575151774602187 11548243920862727661903281)
              ·
                refine ⟨8661182940647045746427461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11548243920862727661903281 8661182940647045746427461)
                ·
                  refine ⟨1623971801371321077455149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8661182940647045746427461 1623971801371321077455149)
                  ·
                    refine ⟨608989425514245404045681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1623971801371321077455149 608989425514245404045681)
                    ·
                      refine ⟨456742069135684053034261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 608989425514245404045681 456742069135684053034261)
                      ·
                        rfl

theorem cell23_889502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_889502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889502 prefixEnd_889502 := by exact prefixLift 889502
  have htrace : WordTrace (prefixWord ++ tailWord_889502) baseStart_889502 baseEnd_889502 := by
    simpa [prefixWord, tailWord_889502, baseEnd_889502] using wordTrace_append hprefix tailTrace_889502
  have hstable : (prefixWord ++ tailWord_889502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889502).length < 2 ^ (prefixWord ++ tailWord_889502).sum := by decide
  have hdescent : baseEnd_889502 < baseStart_889502 := by decide
  rcases family_descends (prefixWord ++ tailWord_889502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889508 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_889508 : Nat := 118140960795 + 889508 * 2 ^ 59
def prefixEnd_889508 : Nat := 4983230072969 + 3 ^ 40 * 889508 * 2
def baseEnd_889508 : Nat := 152248383339870343186411

theorem tailTrace_889508 : CollatzResearch.WordTrace tailWord_889508 prefixEnd_889508 152248383339870343186411 := by
  unfold tailWord_889508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221511030735953358434589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21628681374314604477912785 16221511030735953358434589)
  ·
    refine ⟨6083066636525982509412971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16221511030735953358434589 6083066636525982509412971)
    ·
      refine ⟨9124599954788973764119457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083066636525982509412971 9124599954788973764119457)
      ·
        refine ⟨6843449966091730323089593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9124599954788973764119457 6843449966091730323089593)
        ·
          refine ⟨5132587474568797742317195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843449966091730323089593 5132587474568797742317195)
          ·
            refine ⟨7698881211853196613475793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132587474568797742317195 7698881211853196613475793)
            ·
              refine ⟨5774160908889897460106845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698881211853196613475793 5774160908889897460106845)
              ·
                refine ⟨2165310340833711547540067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774160908889897460106845 2165310340833711547540067)
                ·
                  refine ⟨3247965511250567321310101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165310340833711547540067 3247965511250567321310101)
                  ·
                    refine ⟨152248383339870343186411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3247965511250567321310101 152248383339870343186411)
                    ·
                      rfl

theorem cell23_889508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_889508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889508 prefixEnd_889508 := by exact prefixLift 889508
  have htrace : WordTrace (prefixWord ++ tailWord_889508) baseStart_889508 baseEnd_889508 := by
    simpa [prefixWord, tailWord_889508, baseEnd_889508] using wordTrace_append hprefix tailTrace_889508
  have hstable : (prefixWord ++ tailWord_889508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889508).length < 2 ^ (prefixWord ++ tailWord_889508).sum := by decide
  have hdescent : baseEnd_889508 < baseStart_889508 := by decide
  rcases family_descends (prefixWord ++ tailWord_889508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889525 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_889525 : Nat := 118140960795 + 889525 * 2 ^ 59
def prefixEnd_889525 : Nat := 4983230072969 + 3 ^ 40 * 889525 * 2
def baseEnd_889525 : Nat := 152251293063579154348885

theorem tailTrace_889525 : CollatzResearch.WordTrace tailWord_889525 prefixEnd_889525 152251293063579154348885 := by
  unfold tailWord_889525
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443642102410318620238029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21629094734940212413492019 32443642102410318620238029)
  ·
    refine ⟨12166365788403869482589261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32443642102410318620238029 12166365788403869482589261)
    ·
      refine ⟨4562387170651451055970973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12166365788403869482589261 4562387170651451055970973)
      ·
        refine ⟨1710895188994294145989115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4562387170651451055970973 1710895188994294145989115)
        ·
          refine ⟨2566342783491441218983673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710895188994294145989115 2566342783491441218983673)
          ·
            refine ⟨1924757087618580914237755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566342783491441218983673 1924757087618580914237755)
            ·
              refine ⟨2887135631427871371356633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924757087618580914237755 2887135631427871371356633)
              ·
                refine ⟨2165351723570903528517475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887135631427871371356633 2165351723570903528517475)
                ·
                  refine ⟨3248027585356355292776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165351723570903528517475 3248027585356355292776213)
                  ·
                    refine ⟨152251293063579154348885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3248027585356355292776213 152251293063579154348885)
                    ·
                      rfl

theorem cell23_889525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_889525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889525 prefixEnd_889525 := by exact prefixLift 889525
  have htrace : WordTrace (prefixWord ++ tailWord_889525) baseStart_889525 baseEnd_889525 := by
    simpa [prefixWord, tailWord_889525, baseEnd_889525] using wordTrace_append hprefix tailTrace_889525
  have hstable : (prefixWord ++ tailWord_889525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889525).length < 2 ^ (prefixWord ++ tailWord_889525).sum := by decide
  have hdescent : baseEnd_889525 < baseStart_889525 := by decide
  rcases family_descends (prefixWord ++ tailWord_889525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889532 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_889532 : Nat := 118140960795 + 889532 * 2 ^ 59
def prefixEnd_889532 : Nat := 4983230072969 + 3 ^ 40 * 889532 * 2
def baseEnd_889532 : Nat := 456757473555318935659123

theorem tailTrace_889532 : CollatzResearch.WordTrace tailWord_889532 prefixEnd_889532 456757473555318935659123 := by
  unfold tailWord_889532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221948706692479407871425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21629264942256639210495233 16221948706692479407871425)
  ·
    refine ⟨12166461530019359555903569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16221948706692479407871425 12166461530019359555903569)
    ·
      refine ⟨9124846147514519666927677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12166461530019359555903569 9124846147514519666927677)
      ·
        refine ⟨3421817305317944875097879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9124846147514519666927677 3421817305317944875097879)
        ·
          refine ⟨5132725957976917312646819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421817305317944875097879 5132725957976917312646819)
          ·
            refine ⟨7699088936965375968970229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132725957976917312646819 7699088936965375968970229)
            ·
              refine ⟨721789587840503997090959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7699088936965375968970229 721789587840503997090959)
              ·
                refine ⟨1082684381760755995636439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721789587840503997090959 1082684381760755995636439)
                ·
                  refine ⟨1624026572641133993454659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082684381760755995636439 1624026572641133993454659)
                  ·
                    refine ⟨2436039858961700990181989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624026572641133993454659 2436039858961700990181989)
                    ·
                      refine ⟨456757473555318935659123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2436039858961700990181989 456757473555318935659123)
                      ·
                        rfl

theorem cell23_889532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_889532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889532 prefixEnd_889532 := by exact prefixLift 889532
  have htrace : WordTrace (prefixWord ++ tailWord_889532) baseStart_889532 baseEnd_889532 := by
    simpa [prefixWord, tailWord_889532, baseEnd_889532] using wordTrace_append hprefix tailTrace_889532
  have hstable : (prefixWord ++ tailWord_889532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889532).length < 2 ^ (prefixWord ++ tailWord_889532).sum := by decide
  have hdescent : baseEnd_889532 < baseStart_889532 := by decide
  rcases family_descends (prefixWord ++ tailWord_889532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889535 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_889535 : Nat := 118140960795 + 889535 * 2 ^ 59
def prefixEnd_889535 : Nat := 4983230072969 + 3 ^ 40 * 889535 * 2
def baseEnd_889535 : Nat := 456759013997282423921609

theorem tailTrace_889535 : CollatzResearch.WordTrace tailWord_889535 prefixEnd_889535 456759013997282423921609 := by
  unfold tailWord_889535
  simp only [CollatzResearch.WordTrace]
  refine ⟨32444006832374090328102059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21629337888249393552068039 32444006832374090328102059)
  ·
    refine ⟨48666010248561135492153089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32444006832374090328102059 48666010248561135492153089)
    ·
      refine ⟨36499507686420851619114817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48666010248561135492153089 36499507686420851619114817)
      ·
        refine ⟨27374630764815638714336113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36499507686420851619114817 27374630764815638714336113)
        ·
          refine ⟨20530973073611729035752085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27374630764815638714336113 20530973073611729035752085)
          ·
            refine ⟨962389362825549798550879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20530973073611729035752085 962389362825549798550879)
            ·
              refine ⟨1443584044238324697826319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962389362825549798550879 1443584044238324697826319)
              ·
                refine ⟨2165376066357487046739479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443584044238324697826319 2165376066357487046739479)
                ·
                  refine ⟨3248064099536230570109219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165376066357487046739479 3248064099536230570109219)
                  ·
                    refine ⟨4872096149304345855163829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3248064099536230570109219 4872096149304345855163829)
                    ·
                      refine ⟨456759013997282423921609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4872096149304345855163829 456759013997282423921609)
                      ·
                        rfl

theorem cell23_889535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_889535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889535 prefixEnd_889535 := by exact prefixLift 889535
  have htrace : WordTrace (prefixWord ++ tailWord_889535) baseStart_889535 baseEnd_889535 := by
    simpa [prefixWord, tailWord_889535, baseEnd_889535] using wordTrace_append hprefix tailTrace_889535
  have hstable : (prefixWord ++ tailWord_889535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889535).length < 2 ^ (prefixWord ++ tailWord_889535).sum := by decide
  have hdescent : baseEnd_889535 < baseStart_889535 := by decide
  rcases family_descends (prefixWord ++ tailWord_889535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889578 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_889578 : Nat := 118140960795 + 889578 * 2 ^ 59
def prefixEnd_889578 : Nat := 4983230072969 + 3 ^ 40 * 889578 * 2
def baseEnd_889578 : Nat := 456781093665425755683911

theorem tailTrace_889578 : CollatzResearch.WordTrace tailWord_889578 prefixEnd_889578 456781093665425755683911 := by
  unfold tailWord_889578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111393792804577167979347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21630383447478872447944925 8111393792804577167979347)
  ·
    refine ⟨12167090689206865751969021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8111393792804577167979347 12167090689206865751969021)
    ·
      refine ⟨4562659008452574656988383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12167090689206865751969021 4562659008452574656988383)
      ·
        refine ⟨6843988512678861985482575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4562659008452574656988383 6843988512678861985482575)
        ·
          refine ⟨10265982769018292978223863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6843988512678861985482575 10265982769018292978223863)
          ·
            refine ⟨15398974153527439467335795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265982769018292978223863 15398974153527439467335795)
            ·
              refine ⟨23098461230291159201003693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398974153527439467335795 23098461230291159201003693)
              ·
                refine ⟨8661922961359184700376385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23098461230291159201003693 8661922961359184700376385)
                ·
                  refine ⟨6496442221019388525282289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661922961359184700376385 6496442221019388525282289)
                  ·
                    refine ⟨4872331665764541393961717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496442221019388525282289 4872331665764541393961717)
                    ·
                      refine ⟨456781093665425755683911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4872331665764541393961717 456781093665425755683911)
                      ·
                        rfl

theorem cell23_889578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_889578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889578 prefixEnd_889578 := by exact prefixLift 889578
  have htrace : WordTrace (prefixWord ++ tailWord_889578) baseStart_889578 baseEnd_889578 := by
    simpa [prefixWord, tailWord_889578, baseEnd_889578] using wordTrace_append hprefix tailTrace_889578
  have hstable : (prefixWord ++ tailWord_889578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889578).length < 2 ^ (prefixWord ++ tailWord_889578).sum := by decide
  have hdescent : baseEnd_889578 < baseStart_889578 := by decide
  rcases family_descends (prefixWord ++ tailWord_889578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889592 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_889592 : Nat := 118140960795 + 889592 * 2 ^ 59
def prefixEnd_889592 : Nat := 4983230072969 + 3 ^ 40 * 889592 * 2
def baseEnd_889592 : Nat := 456788282394588700908847

theorem tailTrace_889592 : CollatzResearch.WordTrace tailWord_889592 prefixEnd_889592 456788282394588700908847 := by
  unfold tailWord_889592
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223042896583794531463515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21630723862111726041951353 16223042896583794531463515)
  ·
    refine ⟨24334564344875691797195273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223042896583794531463515 24334564344875691797195273)
    ·
      refine ⟨18250923258656768847896455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24334564344875691797195273 18250923258656768847896455)
      ·
        refine ⟨27376384887985153271844683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18250923258656768847896455 27376384887985153271844683)
        ·
          refine ⟨41064577331977729907767025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27376384887985153271844683 41064577331977729907767025)
          ·
            refine ⟨30798432998983297430825269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41064577331977729907767025 30798432998983297430825269)
            ·
              refine ⟨2887353093654684134139869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30798432998983297430825269 2887353093654684134139869)
              ·
                refine ⟨1082757410120506550302451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2887353093654684134139869 1082757410120506550302451)
                ·
                  refine ⟨1624136115180759825453677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082757410120506550302451 1624136115180759825453677)
                  ·
                    refine ⟨609051043192784934545129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1624136115180759825453677 609051043192784934545129)
                    ·
                      refine ⟨456788282394588700908847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609051043192784934545129 456788282394588700908847)
                      ·
                        rfl

theorem cell23_889592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_889592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889592 prefixEnd_889592 := by exact prefixLift 889592
  have htrace : WordTrace (prefixWord ++ tailWord_889592) baseStart_889592 baseEnd_889592 := by
    simpa [prefixWord, tailWord_889592, baseEnd_889592] using wordTrace_append hprefix tailTrace_889592
  have hstable : (prefixWord ++ tailWord_889592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889592).length < 2 ^ (prefixWord ++ tailWord_889592).sum := by decide
  have hdescent : baseEnd_889592 < baseStart_889592 := by decide
  rcases family_descends (prefixWord ++ tailWord_889592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_889605 : Nat := 118140960795 + 889605 * 2 ^ 59
def prefixEnd_889605 : Nat := 4983230072969 + 3 ^ 40 * 889605 * 2
def baseEnd_889605 : Nat := 456794957643097150046287

theorem tailTrace_889605 : CollatzResearch.WordTrace tailWord_889605 prefixEnd_889605 456794957643097150046287 := by
  unfold tailWord_889605
  simp only [CollatzResearch.WordTrace]
  refine ⟨32446559942120492283150269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21631039961413661522100179 32446559942120492283150269)
  ·
    refine ⟨12167459978295184606181351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32446559942120492283150269 12167459978295184606181351)
    ·
      refine ⟨18251189967442776909272027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12167459978295184606181351 18251189967442776909272027)
      ·
        refine ⟨27376784951164165363908041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18251189967442776909272027 27376784951164165363908041)
        ·
          refine ⟨20532588713373124022931031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27376784951164165363908041 20532588713373124022931031)
          ·
            refine ⟨30798883070059686034396547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532588713373124022931031 30798883070059686034396547)
            ·
              refine ⟨46198324605089529051594821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30798883070059686034396547 46198324605089529051594821)
              ·
                refine ⟨8662185863454286697174029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46198324605089529051594821 8662185863454286697174029)
                ·
                  refine ⟨3248319698795357511440261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8662185863454286697174029 3248319698795357511440261)
                  ·
                    refine ⟨609059943524129533395049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248319698795357511440261 609059943524129533395049)
                    ·
                      refine ⟨456794957643097150046287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609059943524129533395049 456794957643097150046287)
                      ·
                        rfl

theorem cell23_889605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_889605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889605 prefixEnd_889605 := by exact prefixLift 889605
  have htrace : WordTrace (prefixWord ++ tailWord_889605) baseStart_889605 baseEnd_889605 := by
    simpa [prefixWord, tailWord_889605, baseEnd_889605] using wordTrace_append hprefix tailTrace_889605
  have hstable : (prefixWord ++ tailWord_889605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889605).length < 2 ^ (prefixWord ++ tailWord_889605).sum := by decide
  have hdescent : baseEnd_889605 < baseStart_889605 := by decide
  rcases family_descends (prefixWord ++ tailWord_889605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889688 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_889688 : Nat := 118140960795 + 889688 * 2 ^ 59
def prefixEnd_889688 : Nat := 4983230072969 + 3 ^ 40 * 889688 * 2
def baseEnd_889688 : Nat := 152279192179140108436135

theorem tailTrace_889688 : CollatzResearch.WordTrace tailWord_889688 prefixEnd_889688 152279192179140108436135 := by
  unfold tailWord_889688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224793600409898729210859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21633058133879864972281145 16224793600409898729210859)
  ·
    refine ⟨24337190400614848093816289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16224793600409898729210859 24337190400614848093816289)
    ·
      refine ⟨18252892800461136070362217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24337190400614848093816289 18252892800461136070362217)
      ·
        refine ⟨13689669600345852052771663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18252892800461136070362217 13689669600345852052771663)
        ·
          refine ⟨20534504400518778079157495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689669600345852052771663 20534504400518778079157495)
          ·
            refine ⟨30801756600778167118736243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20534504400518778079157495 30801756600778167118736243)
            ·
              refine ⟨46202634901167250678104365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30801756600778167118736243 46202634901167250678104365)
              ·
                refine ⟨17325988087937719004289137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46202634901167250678104365 17325988087937719004289137)
                ·
                  refine ⟨12994491065953289253216853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325988087937719004289137 12994491065953289253216853)
                  ·
                    refine ⟨152279192179140108436135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12994491065953289253216853 152279192179140108436135)
                    ·
                      rfl

theorem cell23_889688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_889688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889688 prefixEnd_889688 := by exact prefixLift 889688
  have htrace : WordTrace (prefixWord ++ tailWord_889688) baseStart_889688 baseEnd_889688 := by
    simpa [prefixWord, tailWord_889688, baseEnd_889688] using wordTrace_append hprefix tailTrace_889688
  have hstable : (prefixWord ++ tailWord_889688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889688).length < 2 ^ (prefixWord ++ tailWord_889688).sum := by decide
  have hdescent : baseEnd_889688 < baseStart_889688 := by decide
  rcases family_descends (prefixWord ++ tailWord_889688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889692 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_889692 : Nat := 118140960795 + 889692 * 2 ^ 59
def prefixEnd_889692 : Nat := 4983230072969 + 3 ^ 40 * 889692 * 2
def baseEnd_889692 : Nat := 152279876820012769886129

theorem tailTrace_889692 : CollatzResearch.WordTrace tailWord_889692 prefixEnd_889692 152279876820012769886129 := by
  unfold tailWord_889692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224866546402653070783665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21633155395203537427711553 16224866546402653070783665)
  ·
    refine ⟨12168649909801989803087749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16224866546402653070783665 12168649909801989803087749)
    ·
      refine ⟨2281621858087873088078953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12168649909801989803087749 2281621858087873088078953)
      ·
        refine ⟨1711216393565904816059215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281621858087873088078953 1711216393565904816059215)
        ·
          refine ⟨2566824590348857224088823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711216393565904816059215 2566824590348857224088823)
          ·
            refine ⟨3850236885523285836133235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566824590348857224088823 3850236885523285836133235)
            ·
              refine ⟨5775355328284928754199853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850236885523285836133235 5775355328284928754199853)
              ·
                refine ⟨2165758248106848282824945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775355328284928754199853 2165758248106848282824945)
                ·
                  refine ⟨1624318686080136212118709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165758248106848282824945 1624318686080136212118709)
                  ·
                    refine ⟨152279876820012769886129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1624318686080136212118709 152279876820012769886129)
                    ·
                      rfl

theorem cell23_889692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_889692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889692 prefixEnd_889692 := by exact prefixLift 889692
  have htrace : WordTrace (prefixWord ++ tailWord_889692) baseStart_889692 baseEnd_889692 := by
    simpa [prefixWord, tailWord_889692, baseEnd_889692] using wordTrace_append hprefix tailTrace_889692
  have hstable : (prefixWord ++ tailWord_889692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889692).length < 2 ^ (prefixWord ++ tailWord_889692).sum := by decide
  have hdescent : baseEnd_889692 < baseStart_889692 := by decide
  rcases family_descends (prefixWord ++ tailWord_889692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889746 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_889746 : Nat := 118140960795 + 889746 * 2 ^ 59
def prefixEnd_889746 : Nat := 4983230072969 + 3 ^ 40 * 889746 * 2
def baseEnd_889746 : Nat := 456867358415381098383139

theorem tailTrace_889746 : CollatzResearch.WordTrace tailWord_889746 prefixEnd_889746 456867358415381098383139 := by
  unfold tailWord_889746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112925658652418341008273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21634468423073115576022061 8112925658652418341008273)
  ·
    refine ⟨6084694243989313755756205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8112925658652418341008273 6084694243989313755756205)
    ·
      refine ⟨2281760341495992658408577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6084694243989313755756205 2281760341495992658408577)
      ·
        refine ⟨1711320256121994493806433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281760341495992658408577 1711320256121994493806433)
        ·
          refine ⟨1283490192091495870354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1711320256121994493806433 1283490192091495870354825)
          ·
            refine ⟨962617644068621902766119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283490192091495870354825 962617644068621902766119)
            ·
              refine ⟨1443926466102932854149179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962617644068621902766119 1443926466102932854149179)
              ·
                refine ⟨2165889699154399281223769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443926466102932854149179 2165889699154399281223769)
                ·
                  refine ⟨1624417274365799460917827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165889699154399281223769 1624417274365799460917827)
                  ·
                    refine ⟨2436625911548699191376741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624417274365799460917827 2436625911548699191376741)
                    ·
                      refine ⟨456867358415381098383139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2436625911548699191376741 456867358415381098383139)
                      ·
                        rfl

theorem cell23_889746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_889746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889746 prefixEnd_889746 := by exact prefixLift 889746
  have htrace : WordTrace (prefixWord ++ tailWord_889746) baseStart_889746 baseEnd_889746 := by
    simpa [prefixWord, tailWord_889746, baseEnd_889746] using wordTrace_append hprefix tailTrace_889746
  have hstable : (prefixWord ++ tailWord_889746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889746).length < 2 ^ (prefixWord ++ tailWord_889746).sum := by decide
  have hdescent : baseEnd_889746 < baseStart_889746 := by decide
  rcases family_descends (prefixWord ++ tailWord_889746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889749 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_889749 : Nat := 118140960795 + 889749 * 2 ^ 59
def prefixEnd_889749 : Nat := 4983230072969 + 3 ^ 40 * 889749 * 2
def baseEnd_889749 : Nat := 456868898857344586645625

theorem tailTrace_889749 : CollatzResearch.WordTrace tailWord_889749 prefixEnd_889749 456868898857344586645625 := by
  unfold tailWord_889749
  simp only [CollatzResearch.WordTrace]
  refine ⟨32451812053598804876392301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21634541369065869917594867 32451812053598804876392301)
  ·
    refine ⟨12169429520099551828647113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32451812053598804876392301 12169429520099551828647113)
    ·
      refine ⟨9127072140074663871485335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12169429520099551828647113 9127072140074663871485335)
      ·
        refine ⟨13690608210111995807228003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127072140074663871485335 13690608210111995807228003)
        ·
          refine ⟨20535912315167993710842005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13690608210111995807228003 20535912315167993710842005)
          ·
            refine ⟨962620889773499705195719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20535912315167993710842005 962620889773499705195719)
            ·
              refine ⟨1443931334660249557793579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962620889773499705195719 1443931334660249557793579)
              ·
                refine ⟨2165897001990374336690369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443931334660249557793579 2165897001990374336690369)
                ·
                  refine ⟨1624422751492780752517777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165897001990374336690369 1624422751492780752517777)
                  ·
                    refine ⟨1218317063619585564388333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1624422751492780752517777 1218317063619585564388333)
                    ·
                      refine ⟨456868898857344586645625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1218317063619585564388333 456868898857344586645625)
                      ·
                        rfl

theorem cell23_889749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_889749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889749 prefixEnd_889749 := by exact prefixLift 889749
  have htrace : WordTrace (prefixWord ++ tailWord_889749) baseStart_889749 baseEnd_889749 := by
    simpa [prefixWord, tailWord_889749, baseEnd_889749] using wordTrace_append hprefix tailTrace_889749
  have hstable : (prefixWord ++ tailWord_889749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889749).length < 2 ^ (prefixWord ++ tailWord_889749).sum := by decide
  have hdescent : baseEnd_889749 < baseStart_889749 := by decide
  rcases family_descends (prefixWord ++ tailWord_889749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889802 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_889802 : Nat := 118140960795 + 889802 * 2 ^ 59
def prefixEnd_889802 : Nat := 4983230072969 + 3 ^ 40 * 889802 * 2
def baseEnd_889802 : Nat := 456896113332032879282881

theorem tailTrace_889802 : CollatzResearch.WordTrace tailWord_889802 prefixEnd_889802 456896113332032879282881 := by
  unfold tailWord_889802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113436280601698732017915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21635830081604529952047773 8113436280601698732017915)
  ·
    refine ⟨12170154420902548098026873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8113436280601698732017915 12170154420902548098026873)
    ·
      refine ⟨9127615815676911073520155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12170154420902548098026873 9127615815676911073520155)
      ·
        refine ⟨13691423723515366610280233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127615815676911073520155 13691423723515366610280233)
        ·
          refine ⟨10268567792636524957710175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13691423723515366610280233 10268567792636524957710175)
          ·
            refine ⟨15402851688954787436565263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10268567792636524957710175 15402851688954787436565263)
            ·
              refine ⟨23104277533432181154847895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402851688954787436565263 23104277533432181154847895)
              ·
                refine ⟨34656416300148271732271843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23104277533432181154847895 34656416300148271732271843)
                ·
                  refine ⟨51984624450222407598407765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34656416300148271732271843 51984624450222407598407765)
                  ·
                    refine ⟨609194817776043839043841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51984624450222407598407765 609194817776043839043841)
                    ·
                      refine ⟨456896113332032879282881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609194817776043839043841 456896113332032879282881)
                      ·
                        rfl

theorem cell23_889802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_889802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889802 prefixEnd_889802 := by exact prefixLift 889802
  have htrace : WordTrace (prefixWord ++ tailWord_889802) baseStart_889802 baseEnd_889802 := by
    simpa [prefixWord, tailWord_889802, baseEnd_889802] using wordTrace_append hprefix tailTrace_889802
  have hstable : (prefixWord ++ tailWord_889802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889802).length < 2 ^ (prefixWord ++ tailWord_889802).sum := by decide
  have hdescent : baseEnd_889802 < baseStart_889802 := by decide
  rcases family_descends (prefixWord ++ tailWord_889802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889846 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_889846 : Nat := 118140960795 + 889846 * 2 ^ 59
def prefixEnd_889846 : Nat := 4983230072969 + 3 ^ 40 * 889846 * 2
def baseEnd_889846 : Nat := 152306235493610235710893

theorem tailTrace_889846 : CollatzResearch.WordTrace tailWord_889846 prefixEnd_889846 152306235493610235710893 := by
  unfold tailWord_889846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028459370890461902667087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21636899956164926961782261 2028459370890461902667087)
  ·
    refine ⟨3042689056335692854000631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028459370890461902667087 3042689056335692854000631)
    ·
      refine ⟨4564033584503539281000947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042689056335692854000631 4564033584503539281000947)
      ·
        refine ⟨6846050376755308921501421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564033584503539281000947 6846050376755308921501421)
        ·
          refine ⟨2567268891283240845563033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6846050376755308921501421 2567268891283240845563033)
          ·
            refine ⟨1925451668462430634172275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2567268891283240845563033 1925451668462430634172275)
            ·
              refine ⟨2888177502693645951258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925451668462430634172275 2888177502693645951258413)
              ·
                refine ⟨1083066563510117231721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2888177502693645951258413 1083066563510117231721905)
                ·
                  refine ⟨812299922632587923791429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083066563510117231721905 812299922632587923791429)
                  ·
                    refine ⟨152306235493610235710893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 812299922632587923791429 152306235493610235710893)
                    ·
                      rfl

theorem cell23_889846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_889846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889846 prefixEnd_889846 := by exact prefixLift 889846
  have htrace : WordTrace (prefixWord ++ tailWord_889846) baseStart_889846 baseEnd_889846 := by
    simpa [prefixWord, tailWord_889846, baseEnd_889846] using wordTrace_append hprefix tailTrace_889846
  have hstable : (prefixWord ++ tailWord_889846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889846).length < 2 ^ (prefixWord ++ tailWord_889846).sum := by decide
  have hdescent : baseEnd_889846 < baseStart_889846 := by decide
  rcases family_descends (prefixWord ++ tailWord_889846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889865 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_889865 : Nat := 118140960795 + 889865 * 2 ^ 59
def prefixEnd_889865 : Nat := 4983230072969 + 3 ^ 40 * 889865 * 2
def baseEnd_889865 : Nat := 456928462613266132795091

theorem tailTrace_889865 : CollatzResearch.WordTrace tailWord_889865 prefixEnd_889865 456928462613266132795091 := by
  unfold tailWord_889865
  simp only [CollatzResearch.WordTrace]
  refine ⟨32456042921178556687615049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21637361947452371125076699 32456042921178556687615049)
  ·
    refine ⟨24342032190883917515711287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32456042921178556687615049 24342032190883917515711287)
    ·
      refine ⟨36513048286325876273566931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24342032190883917515711287 36513048286325876273566931)
      ·
        refine ⟨54769572429488814410350397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36513048286325876273566931 54769572429488814410350397)
        ·
          refine ⟨20538589661058305403881399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54769572429488814410350397 20538589661058305403881399)
          ·
            refine ⟨30807884491587458105822099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538589661058305403881399 30807884491587458105822099)
            ·
              refine ⟨46211826737381187158733149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30807884491587458105822099 46211826737381187158733149)
              ·
                refine ⟨17329435026517945184524931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46211826737381187158733149 17329435026517945184524931)
                ·
                  refine ⟨25994152539776917776787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17329435026517945184524931 25994152539776917776787397)
                  ·
                    refine ⟨4873903601208172083147637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25994152539776917776787397 4873903601208172083147637)
                    ·
                      refine ⟨456928462613266132795091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4873903601208172083147637 456928462613266132795091)
                      ·
                        rfl

theorem cell23_889865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_889865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889865 prefixEnd_889865 := by exact prefixLift 889865
  have htrace : WordTrace (prefixWord ++ tailWord_889865) baseStart_889865 baseEnd_889865 := by
    simpa [prefixWord, tailWord_889865, baseEnd_889865] using wordTrace_append hprefix tailTrace_889865
  have hstable : (prefixWord ++ tailWord_889865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889865).length < 2 ^ (prefixWord ++ tailWord_889865).sum := by decide
  have hdescent : baseEnd_889865 < baseStart_889865 := by decide
  rcases family_descends (prefixWord ++ tailWord_889865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889959 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_889959 : Nat := 118140960795 + 889959 * 2 ^ 59
def prefixEnd_889959 : Nat := 4983230072969 + 3 ^ 40 * 889959 * 2
def baseEnd_889959 : Nat := 456976729794788765019659

theorem tailTrace_889959 : CollatzResearch.WordTrace tailWord_889959 prefixEnd_889959 456976729794788765019659 := by
  unfold tailWord_889959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459471382838010741536931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21639647588558673827691287 32459471382838010741536931)
  ·
    refine ⟨48689207074257016112305397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32459471382838010741536931 48689207074257016112305397)
    ·
      refine ⟨4564613163211595260528631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48689207074257016112305397 4564613163211595260528631)
      ·
        refine ⟨6846919744817392890792947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564613163211595260528631 6846919744817392890792947)
        ·
          refine ⟨10270379617226089336189421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846919744817392890792947 10270379617226089336189421)
          ·
            refine ⟨3851392356459783501071033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10270379617226089336189421 3851392356459783501071033)
            ·
              refine ⟨2888544267344837625803275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851392356459783501071033 2888544267344837625803275)
              ·
                refine ⟨4332816401017256438704913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888544267344837625803275 4332816401017256438704913)
                ·
                  refine ⟨3249612300762942329028685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332816401017256438704913 3249612300762942329028685)
                  ·
                    refine ⟨1218604612786103373385757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249612300762942329028685 1218604612786103373385757)
                    ·
                      refine ⟨456976729794788765019659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1218604612786103373385757 456976729794788765019659)
                      ·
                        rfl

theorem cell23_889959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_889959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889959 prefixEnd_889959 := by exact prefixLift 889959
  have htrace : WordTrace (prefixWord ++ tailWord_889959) baseStart_889959 baseEnd_889959 := by
    simpa [prefixWord, tailWord_889959, baseEnd_889959] using wordTrace_append hprefix tailTrace_889959
  have hstable : (prefixWord ++ tailWord_889959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889959).length < 2 ^ (prefixWord ++ tailWord_889959).sum := by decide
  have hdescent : baseEnd_889959 < baseStart_889959 := by decide
  rcases family_descends (prefixWord ++ tailWord_889959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889960 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_889960 : Nat := 118140960795 + 889960 * 2 ^ 59
def prefixEnd_889960 : Nat := 4983230072969 + 3 ^ 40 * 889960 * 2
def baseEnd_889960 : Nat := 456977243275443261107155

theorem tailTrace_889960 : CollatzResearch.WordTrace tailWord_889960 prefixEnd_889960 456977243275443261107155 := by
  unfold tailWord_889960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229753927917193956161667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21639671903889591941548889 16229753927917193956161667)
  ·
    refine ⟨24344630891875790934242501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229753927917193956161667 24344630891875790934242501)
    ·
      refine ⟨4564618292226710800170469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24344630891875790934242501 4564618292226710800170469)
      ·
        refine ⟨855865929792508275031963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4564618292226710800170469 855865929792508275031963)
        ·
          refine ⟨1283798894688762412547945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855865929792508275031963 1283798894688762412547945)
          ·
            refine ⟨962849171016571809410959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283798894688762412547945 962849171016571809410959)
            ·
              refine ⟨1444273756524857714116439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962849171016571809410959 1444273756524857714116439)
              ·
                refine ⟨2166410634787286571174659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444273756524857714116439 2166410634787286571174659)
                ·
                  refine ⟨3249615952180929856761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166410634787286571174659 3249615952180929856761989)
                  ·
                    refine ⟨609302991033924348142873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249615952180929856761989 609302991033924348142873)
                    ·
                      refine ⟨456977243275443261107155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609302991033924348142873 456977243275443261107155)
                      ·
                        rfl

theorem cell23_889960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_889960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_889960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_889960 prefixEnd_889960 := by exact prefixLift 889960
  have htrace : WordTrace (prefixWord ++ tailWord_889960) baseStart_889960 baseEnd_889960 := by
    simpa [prefixWord, tailWord_889960, baseEnd_889960] using wordTrace_append hprefix tailTrace_889960
  have hstable : (prefixWord ++ tailWord_889960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889960).length < 2 ^ (prefixWord ++ tailWord_889960).sum := by decide
  have hdescent : baseEnd_889960 < baseStart_889960 := by decide
  rcases family_descends (prefixWord ++ tailWord_889960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890042 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_890042 : Nat := 118140960795 + 890042 * 2 ^ 59
def prefixEnd_890042 : Nat := 4983230072969 + 3 ^ 40 * 890042 * 2
def baseEnd_890042 : Nat := 457019348689111940281777

theorem tailTrace_890042 : CollatzResearch.WordTrace tailWord_890042 prefixEnd_890042 457019348689111940281777 := by
  unfold tailWord_890042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115624660384328979202095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21641665761024877277872253 8115624660384328979202095)
  ·
    refine ⟨12173436990576493468803143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8115624660384328979202095 12173436990576493468803143)
    ·
      refine ⟨18260155485864740203204715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12173436990576493468803143 18260155485864740203204715)
      ·
        refine ⟨27390233228797110304807073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18260155485864740203204715 27390233228797110304807073)
        ·
          refine ⟨20542674921597832728605305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27390233228797110304807073 20542674921597832728605305)
          ·
            refine ⟨15407006191198374546453979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20542674921597832728605305 15407006191198374546453979)
            ·
              refine ⟨23110509286797561819680969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15407006191198374546453979 23110509286797561819680969)
              ·
                refine ⟨17332881965098171364760727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110509286797561819680969 17332881965098171364760727)
                ·
                  refine ⟨25999322947647257047141091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17332881965098171364760727 25999322947647257047141091)
                  ·
                    refine ⟨38998984421470885570711637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25999322947647257047141091 38998984421470885570711637)
                    ·
                      refine ⟨457019348689111940281777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38998984421470885570711637 457019348689111940281777)
                      ·
                        rfl

theorem cell23_890042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_890042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890042 prefixEnd_890042 := by exact prefixLift 890042
  have htrace : WordTrace (prefixWord ++ tailWord_890042) baseStart_890042 baseEnd_890042 := by
    simpa [prefixWord, tailWord_890042, baseEnd_890042] using wordTrace_append hprefix tailTrace_890042
  have hstable : (prefixWord ++ tailWord_890042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890042).length < 2 ^ (prefixWord ++ tailWord_890042).sum := by decide
  have hdescent : baseEnd_890042 < baseStart_890042 := by decide
  rcases family_descends (prefixWord ++ tailWord_890042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890093 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_890093 : Nat := 118140960795 + 890093 * 2 ^ 59
def prefixEnd_890093 : Nat := 4983230072969 + 3 ^ 40 * 890093 * 2
def baseEnd_890093 : Nat := 457045536202491240744043

theorem tailTrace_890093 : CollatzResearch.WordTrace tailWord_890093 prefixEnd_890093 457045536202491240744043 := by
  unfold tailWord_890093
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464358764352551626914933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21642905842901701084609955 32464358764352551626914933)
  ·
    refine ⟨3043533634158051715023275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32464358764352551626914933 3043533634158051715023275)
    ·
      refine ⟨4565300451237077572534913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043533634158051715023275 4565300451237077572534913)
      ·
        refine ⟨3423975338427808179401185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4565300451237077572534913 3423975338427808179401185)
        ·
          refine ⟨2567981503820856134550889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423975338427808179401185 2567981503820856134550889)
          ·
            refine ⟨1925986127865642100913167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2567981503820856134550889 1925986127865642100913167)
            ·
              refine ⟨2888979191798463151369751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925986127865642100913167 2888979191798463151369751)
              ·
                refine ⟨4333468787697694727054627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888979191798463151369751 4333468787697694727054627)
                ·
                  refine ⟨6500203181546542090581941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333468787697694727054627 6500203181546542090581941)
                  ·
                    refine ⟨609394048269988320992057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6500203181546542090581941 609394048269988320992057)
                    ·
                      refine ⟨457045536202491240744043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609394048269988320992057 457045536202491240744043)
                      ·
                        rfl

theorem cell23_890093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_890093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890093 prefixEnd_890093 := by exact prefixLift 890093
  have htrace : WordTrace (prefixWord ++ tailWord_890093) baseStart_890093 baseEnd_890093 := by
    simpa [prefixWord, tailWord_890093, baseEnd_890093] using wordTrace_append hprefix tailTrace_890093
  have hstable : (prefixWord ++ tailWord_890093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890093).length < 2 ^ (prefixWord ++ tailWord_890093).sum := by decide
  have hdescent : baseEnd_890093 < baseStart_890093 := by decide
  rcases family_descends (prefixWord ++ tailWord_890093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890099 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 6]
def baseStart_890099 : Nat := 118140960795 + 890099 * 2 ^ 59
def prefixEnd_890099 : Nat := 4983230072969 + 3 ^ 40 * 890099 * 2
def baseEnd_890099 : Nat := 152349539028806072423005

theorem tailTrace_890099 : CollatzResearch.WordTrace tailWord_890099 prefixEnd_890099 152349539028806072423005 := by
  unfold tailWord_890099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464577602330814651633351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643051734887209767755567 32464577602330814651633351)
  ·
    refine ⟨48696866403496221977450027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32464577602330814651633351 48696866403496221977450027)
    ·
      refine ⟨73045299605244332966175041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48696866403496221977450027 73045299605244332966175041)
      ·
        refine ⟨54783974703933249724631281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73045299605244332966175041 54783974703933249724631281)
        ·
          refine ⟨41087981027949937293473461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54783974703933249724631281 41087981027949937293473461)
          ·
            refine ⟨3851998221370306621263137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41087981027949937293473461 3851998221370306621263137)
            ·
              refine ⟨2888998666027729965947353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851998221370306621263137 2888998666027729965947353)
              ·
                refine ⟨2166748999520797474460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888998666027729965947353 2166748999520797474460515)
                ·
                  refine ⟨3250123499281196211690773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166748999520797474460515 3250123499281196211690773)
                  ·
                    refine ⟨152349539028806072423005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3250123499281196211690773 152349539028806072423005)
                    ·
                      rfl

theorem cell23_890099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_890099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890099 prefixEnd_890099 := by exact prefixLift 890099
  have htrace : WordTrace (prefixWord ++ tailWord_890099) baseStart_890099 baseEnd_890099 := by
    simpa [prefixWord, tailWord_890099, baseEnd_890099] using wordTrace_append hprefix tailTrace_890099
  have hstable : (prefixWord ++ tailWord_890099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890099).length < 2 ^ (prefixWord ++ tailWord_890099).sum := by decide
  have hdescent : baseEnd_890099 < baseStart_890099 := by decide
  rcases family_descends (prefixWord ++ tailWord_890099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890106 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_890106 : Nat := 118140960795 + 890106 * 2 ^ 59
def prefixEnd_890106 : Nat := 4983230072969 + 3 ^ 40 * 890106 * 2
def baseEnd_890106 : Nat := 457052211450999689881483

theorem tailTrace_890106 : CollatzResearch.WordTrace tailWord_890106 prefixEnd_890106 457052211450999689881483 := by
  unfold tailWord_890106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116208228326363711784543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21643221942203636564758781 8116208228326363711784543)
  ·
    refine ⟨12174312342489545567676815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8116208228326363711784543 12174312342489545567676815)
    ·
      refine ⟨18261468513734318351515223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174312342489545567676815 18261468513734318351515223)
      ·
        refine ⟨27392202770601477527272835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261468513734318351515223 27392202770601477527272835)
        ·
          refine ⟨41088304155902216290909253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27392202770601477527272835 41088304155902216290909253)
          ·
            refine ⟨7704057029231665554545485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41088304155902216290909253 7704057029231665554545485)
            ·
              refine ⟨2889021385961874582954557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7704057029231665554545485 2889021385961874582954557)
              ·
                refine ⟨1083383019735702968607959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2889021385961874582954557 1083383019735702968607959)
                ·
                  refine ⟨1625074529603554452911939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083383019735702968607959 1625074529603554452911939)
                  ·
                    refine ⟨2437611794405331679367909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1625074529603554452911939 2437611794405331679367909)
                    ·
                      refine ⟨457052211450999689881483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2437611794405331679367909 457052211450999689881483)
                      ·
                        rfl

theorem cell23_890106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_890106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890106 prefixEnd_890106 := by exact prefixLift 890106
  have htrace : WordTrace (prefixWord ++ tailWord_890106) baseStart_890106 baseEnd_890106 := by
    simpa [prefixWord, tailWord_890106, baseEnd_890106] using wordTrace_append hprefix tailTrace_890106
  have hstable : (prefixWord ++ tailWord_890106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890106).length < 2 ^ (prefixWord ++ tailWord_890106).sum := by decide
  have hdescent : baseEnd_890106 < baseStart_890106 := by decide
  rcases family_descends (prefixWord ++ tailWord_890106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890123 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 3, 2, 2]
def baseStart_890123 : Nat := 118140960795 + 890123 * 2 ^ 59
def prefixEnd_890123 : Nat := 4983230072969 + 3 ^ 40 * 890123 * 2
def baseEnd_890123 : Nat := 457060940622126123368905

theorem tailTrace_890123 : CollatzResearch.WordTrace tailWord_890123 prefixEnd_890123 457060940622126123368905 := by
  unfold tailWord_890123
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465452954243866750507023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643635302829244500338015 32465452954243866750507023)
  ·
    refine ⟨48698179431365800125760535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32465452954243866750507023 48698179431365800125760535)
    ·
      refine ⟨73047269147048700188640803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48698179431365800125760535 73047269147048700188640803)
      ·
        refine ⟨109570903720573050282961205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73047269147048700188640803 109570903720573050282961205)
        ·
          refine ⟨10272272223803723464027613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109570903720573050282961205 10272272223803723464027613)
          ·
            refine ⟨3852102083926396299010355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10272272223803723464027613 3852102083926396299010355)
            ·
              refine ⟨5778153125889594448515533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852102083926396299010355 5778153125889594448515533)
              ·
                refine ⟨2166807422208597918193325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5778153125889594448515533 2166807422208597918193325)
                ·
                  refine ⟨812552783328224219322497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2166807422208597918193325 812552783328224219322497)
                  ·
                    refine ⟨609414587496168164491873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 812552783328224219322497 609414587496168164491873)
                    ·
                      refine ⟨457060940622126123368905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609414587496168164491873 457060940622126123368905)
                      ·
                        rfl

theorem cell23_890123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2, 2].length) (baseStart_890123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890123 prefixEnd_890123 := by exact prefixLift 890123
  have htrace : WordTrace (prefixWord ++ tailWord_890123) baseStart_890123 baseEnd_890123 := by
    simpa [prefixWord, tailWord_890123, baseEnd_890123] using wordTrace_append hprefix tailTrace_890123
  have hstable : (prefixWord ++ tailWord_890123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890123).length < 2 ^ (prefixWord ++ tailWord_890123).sum := by decide
  have hdescent : baseEnd_890123 < baseStart_890123 := by decide
  rcases family_descends (prefixWord ++ tailWord_890123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890126 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_890126 : Nat := 118140960795 + 890126 * 2 ^ 59
def prefixEnd_890126 : Nat := 4983230072969 + 3 ^ 40 * 890126 * 2
def baseEnd_890126 : Nat := 457062481064089611631391

theorem tailTrace_890126 : CollatzResearch.WordTrace tailWord_890126 prefixEnd_890126 457062481064089611631391 := by
  unfold tailWord_890126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058195296654124782858279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21643708248821998841910821 4058195296654124782858279)
  ·
    refine ⟨6087292944981187174287419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058195296654124782858279 6087292944981187174287419)
    ·
      refine ⟨9130939417471780761431129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087292944981187174287419 9130939417471780761431129)
      ·
        refine ⟨6848204563103835571073347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9130939417471780761431129 6848204563103835571073347)
        ·
          refine ⟨10272306844655753356610021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848204563103835571073347 10272306844655753356610021)
          ·
            refine ⟨1926057533372953754364379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10272306844655753356610021 1926057533372953754364379)
            ·
              refine ⟨2889086300059430631546569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926057533372953754364379 2889086300059430631546569)
              ·
                refine ⟨2166814725044572973659927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889086300059430631546569 2166814725044572973659927)
                ·
                  refine ⟨3250222087566859460489891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166814725044572973659927 3250222087566859460489891)
                  ·
                    refine ⟨4875333131350289190734837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250222087566859460489891 4875333131350289190734837)
                    ·
                      refine ⟨457062481064089611631391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4875333131350289190734837 457062481064089611631391)
                      ·
                        rfl

theorem cell23_890126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_890126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890126 prefixEnd_890126 := by exact prefixLift 890126
  have htrace : WordTrace (prefixWord ++ tailWord_890126) baseStart_890126 baseEnd_890126 := by
    simpa [prefixWord, tailWord_890126, baseEnd_890126] using wordTrace_append hprefix tailTrace_890126
  have hstable : (prefixWord ++ tailWord_890126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890126).length < 2 ^ (prefixWord ++ tailWord_890126).sum := by decide
  have hdescent : baseEnd_890126 < baseStart_890126 := by decide
  rcases family_descends (prefixWord ++ tailWord_890126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890136 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_890136 : Nat := 118140960795 + 890136 * 2 ^ 59
def prefixEnd_890136 : Nat := 4983230072969 + 3 ^ 40 * 890136 * 2
def baseEnd_890136 : Nat := 457067615870634572506345

theorem tailTrace_890136 : CollatzResearch.WordTrace tailWord_890136 prefixEnd_890136 457067615870634572506345 := by
  unfold tailWord_890136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232963551598384985365131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21643951402131179980486841 16232963551598384985365131)
  ·
    refine ⟨24349445327397577478047697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232963551598384985365131 24349445327397577478047697)
    ·
      refine ⟨18262083995548183108535773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24349445327397577478047697 18262083995548183108535773)
      ·
        refine ⟨6848281498330568665700915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18262083995548183108535773 6848281498330568665700915)
        ·
          refine ⟨10272422247495852998551373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848281498330568665700915 10272422247495852998551373)
          ·
            refine ⟨3852158342810944874456765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10272422247495852998551373 3852158342810944874456765)
            ·
              refine ⟨1444559378554104327921287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852158342810944874456765 1444559378554104327921287)
              ·
                refine ⟨2166839067831156491881931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444559378554104327921287 2166839067831156491881931)
                ·
                  refine ⟨3250258601746734737822897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166839067831156491881931 3250258601746734737822897)
                  ·
                    refine ⟨2437693951310051053367173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250258601746734737822897 2437693951310051053367173)
                    ·
                      refine ⟨457067615870634572506345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2437693951310051053367173 457067615870634572506345)
                      ·
                        rfl

theorem cell23_890136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_890136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890136 prefixEnd_890136 := by exact prefixLift 890136
  have htrace : WordTrace (prefixWord ++ tailWord_890136) baseStart_890136 baseEnd_890136 := by
    simpa [prefixWord, tailWord_890136, baseEnd_890136] using wordTrace_append hprefix tailTrace_890136
  have hstable : (prefixWord ++ tailWord_890136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890136).length < 2 ^ (prefixWord ++ tailWord_890136).sum := by decide
  have hdescent : baseEnd_890136 < baseStart_890136 := by decide
  rcases family_descends (prefixWord ++ tailWord_890136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890146 : List Nat := [3, 3, 1, 1, 4, 1, 1, 9]
def baseStart_890146 : Nat := 118140960795 + 890146 * 2 ^ 59
def prefixEnd_890146 : Nat := 4983230072969 + 3 ^ 40 * 890146 * 2
def baseEnd_890146 : Nat := 16928620395451093828937

theorem tailTrace_890146 : CollatzResearch.WordTrace tailWord_890146 prefixEnd_890146 16928620395451093828937 := by
  unfold tailWord_890146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116572958290135419648573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21644194555440361119062861 8116572958290135419648573)
  ·
    refine ⟨3043714859358800782368215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8116572958290135419648573 3043714859358800782368215)
    ·
      refine ⟨4565572289038201173552323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043714859358800782368215 4565572289038201173552323)
      ·
        refine ⟨6848358433557301760328485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565572289038201173552323 6848358433557301760328485)
        ·
          refine ⟨1284067206291994080061591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6848358433557301760328485 1284067206291994080061591)
          ·
            refine ⟨1926100809437991120092387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284067206291994080061591 1926100809437991120092387)
            ·
              refine ⟨2889151214156986680138581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926100809437991120092387 2889151214156986680138581)
              ·
                refine ⟨16928620395451093828937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2889151214156986680138581 16928620395451093828937)
                ·
                  rfl

theorem cell23_890146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_890146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890146 prefixEnd_890146 := by exact prefixLift 890146
  have htrace : WordTrace (prefixWord ++ tailWord_890146) baseStart_890146 baseEnd_890146 := by
    simpa [prefixWord, tailWord_890146, baseEnd_890146] using wordTrace_append hprefix tailTrace_890146
  have hstable : (prefixWord ++ tailWord_890146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890146).length < 2 ^ (prefixWord ++ tailWord_890146).sum := by decide
  have hdescent : baseEnd_890146 < baseStart_890146 := by decide
  rcases family_descends (prefixWord ++ tailWord_890146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890174 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_890174 : Nat := 118140960795 + 890174 * 2 ^ 59
def prefixEnd_890174 : Nat := 4983230072969 + 3 ^ 40 * 890174 * 2
def baseEnd_890174 : Nat := 457087128135505423831171

theorem tailTrace_890174 : CollatzResearch.WordTrace tailWord_890174 prefixEnd_890174 457087128135505423831171 := by
  unfold tailWord_890174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058414134632387807576697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21644875384706068307075717 4058414134632387807576697)
  ·
    refine ⟨3043810600974290855682523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4058414134632387807576697 3043810600974290855682523)
    ·
      refine ⟨4565715901461436283523785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043810600974290855682523 4565715901461436283523785)
      ·
        refine ⟨3424286926096077212642839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4565715901461436283523785 3424286926096077212642839)
        ·
          refine ⟨5136430389144115818964259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424286926096077212642839 5136430389144115818964259)
          ·
            refine ⟨7704645583716173728446389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136430389144115818964259 7704645583716173728446389)
            ·
              refine ⟨722310523473391287041849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7704645583716173728446389 722310523473391287041849)
              ·
                refine ⟨541732892605043465281387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722310523473391287041849 541732892605043465281387)
                ·
                  refine ⟨812599338907565197922081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541732892605043465281387 812599338907565197922081)
                  ·
                    refine ⟨609449504180673898441561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 812599338907565197922081 609449504180673898441561)
                    ·
                      refine ⟨457087128135505423831171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609449504180673898441561 457087128135505423831171)
                      ·
                        rfl

theorem cell23_890174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_890174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890174 prefixEnd_890174 := by exact prefixLift 890174
  have htrace : WordTrace (prefixWord ++ tailWord_890174) baseStart_890174 baseEnd_890174 := by
    simpa [prefixWord, tailWord_890174, baseEnd_890174] using wordTrace_append hprefix tailTrace_890174
  have hstable : (prefixWord ++ tailWord_890174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890174).length < 2 ^ (prefixWord ++ tailWord_890174).sum := by decide
  have hdescent : baseEnd_890174 < baseStart_890174 := by decide
  rcases family_descends (prefixWord ++ tailWord_890174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890179 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_890179 : Nat := 118140960795 + 890179 * 2 ^ 59
def prefixEnd_890179 : Nat := 4983230072969 + 3 ^ 40 * 890179 * 2
def baseEnd_890179 : Nat := 457089695538777904268647

theorem tailTrace_890179 : CollatzResearch.WordTrace tailWord_890179 prefixEnd_890179 457089695538777904268647 := by
  unfold tailWord_890179
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467495442040988314545591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21644996961360658876363727 32467495442040988314545591)
  ·
    refine ⟨48701243163061482471818387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32467495442040988314545591 48701243163061482471818387)
    ·
      refine ⟨73051864744592223707727581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48701243163061482471818387 73051864744592223707727581)
      ·
        refine ⟨27394449279222083890397843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73051864744592223707727581 27394449279222083890397843)
        ·
          refine ⟨41091673918833125835596765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27394449279222083890397843 41091673918833125835596765)
          ·
            refine ⟨15409377719562422188348787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41091673918833125835596765 15409377719562422188348787)
            ·
              refine ⟨23114066579343633282523181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15409377719562422188348787 23114066579343633282523181)
              ·
                refine ⟨8667774967253862480946193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23114066579343633282523181 8667774967253862480946193)
                ·
                  refine ⟨6500831225440396860709645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8667774967253862480946193 6500831225440396860709645)
                  ·
                    refine ⟨2437811709540148822766117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6500831225440396860709645 2437811709540148822766117)
                    ·
                      refine ⟨457089695538777904268647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2437811709540148822766117 457089695538777904268647)
                      ·
                        rfl

theorem cell23_890179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_890179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890179 prefixEnd_890179 := by exact prefixLift 890179
  have htrace : WordTrace (prefixWord ++ tailWord_890179) baseStart_890179 baseEnd_890179 := by
    simpa [prefixWord, tailWord_890179, baseEnd_890179] using wordTrace_append hprefix tailTrace_890179
  have hstable : (prefixWord ++ tailWord_890179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890179).length < 2 ^ (prefixWord ++ tailWord_890179).sum := by decide
  have hdescent : baseEnd_890179 < baseStart_890179 := by decide
  rcases family_descends (prefixWord ++ tailWord_890179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890213 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_890213 : Nat := 118140960795 + 890213 * 2 ^ 59
def prefixEnd_890213 : Nat := 4983230072969 + 3 ^ 40 * 890213 * 2
def baseEnd_890213 : Nat := 457107153881030771243491

theorem tailTrace_890213 : CollatzResearch.WordTrace tailWord_890213 prefixEnd_890213 457107153881030771243491 := by
  unfold tailWord_890213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32468735523917812121283293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21645823682611874747522195 32468735523917812121283293)
  ·
    refine ⟨12175775821469179545481235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32468735523917812121283293 12175775821469179545481235)
    ·
      refine ⟨18263663732203769318221853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12175775821469179545481235 18263663732203769318221853)
      ·
        refine ⟨6848873899576413494333195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18263663732203769318221853 6848873899576413494333195)
        ·
          refine ⟨10273310849364620241499793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848873899576413494333195 10273310849364620241499793)
          ·
            refine ⟨7704983137023465181124845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273310849364620241499793 7704983137023465181124845)
            ·
              refine ⟨2889368676383799442921817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7704983137023465181124845 2889368676383799442921817)
              ·
                refine ⟨2167026507287849582191363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889368676383799442921817 2167026507287849582191363)
                ·
                  refine ⟨3250539760931774373287045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167026507287849582191363 3250539760931774373287045)
                  ·
                    refine ⟨609476205174707694991321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3250539760931774373287045 609476205174707694991321)
                    ·
                      refine ⟨457107153881030771243491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609476205174707694991321 457107153881030771243491)
                      ·
                        rfl

theorem cell23_890213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_890213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890213 prefixEnd_890213 := by exact prefixLift 890213
  have htrace : WordTrace (prefixWord ++ tailWord_890213) baseStart_890213 baseEnd_890213 := by
    simpa [prefixWord, tailWord_890213, baseEnd_890213] using wordTrace_append hprefix tailTrace_890213
  have hstable : (prefixWord ++ tailWord_890213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890213).length < 2 ^ (prefixWord ++ tailWord_890213).sum := by decide
  have hdescent : baseEnd_890213 < baseStart_890213 := by decide
  rcases family_descends (prefixWord ++ tailWord_890213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890226 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_890226 : Nat := 118140960795 + 890226 * 2 ^ 59
def prefixEnd_890226 : Nat := 4983230072969 + 3 ^ 40 * 890226 * 2
def baseEnd_890226 : Nat := 457113829129539220380931

theorem tailTrace_890226 : CollatzResearch.WordTrace tailWord_890226 prefixEnd_890226 457113829129539220380931 := by
  unfold tailWord_890226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117302418217678835376633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21646139781913810227671021 8117302418217678835376633)
  ·
    refine ⟨6087976813663259126532475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8117302418217678835376633 6087976813663259126532475)
    ·
      refine ⟨9131965220494888689798713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087976813663259126532475 9131965220494888689798713)
      ·
        refine ⟨6848973915371166517349035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131965220494888689798713 6848973915371166517349035)
        ·
          refine ⟨10273460873056749776023553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848973915371166517349035 10273460873056749776023553)
          ·
            refine ⟨7705095654792562332017665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273460873056749776023553 7705095654792562332017665)
            ·
              refine ⟨5778821741094421749013249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7705095654792562332017665 5778821741094421749013249)
              ·
                refine ⟨4334116305820816311759937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778821741094421749013249 4334116305820816311759937)
                ·
                  refine ⟨3250587229365612233819953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334116305820816311759937 3250587229365612233819953)
                  ·
                    refine ⟨2437940422024209175364965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250587229365612233819953 2437940422024209175364965)
                    ·
                      refine ⟨457113829129539220380931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2437940422024209175364965 457113829129539220380931)
                      ·
                        rfl

theorem cell23_890226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_890226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890226 prefixEnd_890226 := by exact prefixLift 890226
  have htrace : WordTrace (prefixWord ++ tailWord_890226) baseStart_890226 baseEnd_890226 := by
    simpa [prefixWord, tailWord_890226, baseEnd_890226] using wordTrace_append hprefix tailTrace_890226
  have hstable : (prefixWord ++ tailWord_890226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890226).length < 2 ^ (prefixWord ++ tailWord_890226).sum := by decide
  have hdescent : baseEnd_890226 < baseStart_890226 := by decide
  rcases family_descends (prefixWord ++ tailWord_890226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890259 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_890259 : Nat := 118140960795 + 890259 * 2 ^ 59
def prefixEnd_890259 : Nat := 4983230072969 + 3 ^ 40 * 890259 * 2
def baseEnd_890259 : Nat := 457130773991137591268279

theorem tailTrace_890259 : CollatzResearch.WordTrace tailWord_890259 prefixEnd_890259 457130773991137591268279 := by
  unfold tailWord_890259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470413281751161977457831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21646942187834107984971887 32470413281751161977457831)
  ·
    refine ⟨48705619922626742966186747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32470413281751161977457831 48705619922626742966186747)
    ·
      refine ⟨73058429883940114449280121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48705619922626742966186747 73058429883940114449280121)
      ·
        refine ⟨54793822412955085836960091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73058429883940114449280121 54793822412955085836960091)
        ·
          refine ⟨82190733619432628755440137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54793822412955085836960091 82190733619432628755440137)
          ·
            refine ⟨61643050214574471566580103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82190733619432628755440137 61643050214574471566580103)
            ·
              refine ⟨92464575321861707349870155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61643050214574471566580103 92464575321861707349870155)
              ·
                refine ⟨138696862982792561024805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92464575321861707349870155 138696862982792561024805233)
                ·
                  refine ⟨104022647237094420768603925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138696862982792561024805233 104022647237094420768603925)
                  ·
                    refine ⟨4876061589238800973528309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104022647237094420768603925 4876061589238800973528309)
                    ·
                      refine ⟨457130773991137591268279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4876061589238800973528309 457130773991137591268279)
                      ·
                        rfl

theorem cell23_890259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_890259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890259 prefixEnd_890259 := by exact prefixLift 890259
  have htrace : WordTrace (prefixWord ++ tailWord_890259) baseStart_890259 baseEnd_890259 := by
    simpa [prefixWord, tailWord_890259, baseEnd_890259] using wordTrace_append hprefix tailTrace_890259
  have hstable : (prefixWord ++ tailWord_890259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890259).length < 2 ^ (prefixWord ++ tailWord_890259).sum := by decide
  have hdescent : baseEnd_890259 < baseStart_890259 := by decide
  rcases family_descends (prefixWord ++ tailWord_890259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890266 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_890266 : Nat := 118140960795 + 890266 * 2 ^ 59
def prefixEnd_890266 : Nat := 4983230072969 + 3 ^ 40 * 890266 * 2
def baseEnd_890266 : Nat := 152378122785239687960249

theorem tailTrace_890266 : CollatzResearch.WordTrace tailWord_890266 prefixEnd_890266 152378122785239687960249 := by
  unfold tailWord_890266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117667148181450543240663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21647112395150534781975101 8117667148181450543240663)
  ·
    refine ⟨12176500722272175814860995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117667148181450543240663 12176500722272175814860995)
    ·
      refine ⟨18264751083408263722291493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176500722272175814860995 18264751083408263722291493)
      ·
        refine ⟨3424640828139049447929655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18264751083408263722291493 3424640828139049447929655)
        ·
          refine ⟨5136961242208574171894483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424640828139049447929655 5136961242208574171894483)
          ·
            refine ⟨7705441863312861257841725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136961242208574171894483 7705441863312861257841725)
            ·
              refine ⟨2889540698742322971690647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7705441863312861257841725 2889540698742322971690647)
              ·
                refine ⟨4334311048113484457535971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889540698742322971690647 4334311048113484457535971)
                ·
                  refine ⟨6501466572170226686303957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334311048113484457535971 6501466572170226686303957)
                  ·
                    refine ⟨152378122785239687960249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6501466572170226686303957 152378122785239687960249)
                    ·
                      rfl

theorem cell23_890266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_890266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890266 prefixEnd_890266 := by exact prefixLift 890266
  have htrace : WordTrace (prefixWord ++ tailWord_890266) baseStart_890266 baseEnd_890266 := by
    simpa [prefixWord, tailWord_890266, baseEnd_890266] using wordTrace_append hprefix tailTrace_890266
  have hstable : (prefixWord ++ tailWord_890266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890266).length < 2 ^ (prefixWord ++ tailWord_890266).sum := by decide
  have hdescent : baseEnd_890266 < baseStart_890266 := by decide
  rcases family_descends (prefixWord ++ tailWord_890266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890360 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 6]
def baseStart_890360 : Nat := 118140960795 + 890360 * 2 ^ 59
def prefixEnd_890360 : Nat := 4983230072969 + 3 ^ 40 * 890360 * 2
def baseEnd_890360 : Nat := 50798070615249077345035

theorem tailTrace_890360 : CollatzResearch.WordTrace tailWord_890360 prefixEnd_890360 50798070615249077345035 := by
  unfold tailWord_890360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237048527192628113442267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21649398036256837484589689 16237048527192628113442267)
  ·
    refine ⟨24355572790788942170163401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16237048527192628113442267 24355572790788942170163401)
    ·
      refine ⟨18266679593091706627622551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24355572790788942170163401 18266679593091706627622551)
      ·
        refine ⟨27400019389637559941433827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18266679593091706627622551 27400019389637559941433827)
        ·
          refine ⟨41100029084456339912150741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27400019389637559941433827 41100029084456339912150741)
          ·
            refine ⟨963281931666945466691033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41100029084456339912150741 963281931666945466691033)
            ·
              refine ⟨722461448750209100018275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963281931666945466691033 722461448750209100018275)
              ·
                refine ⟨1083692173125313650027413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722461448750209100018275 1083692173125313650027413)
                ·
                  refine ⟨50798070615249077345035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1083692173125313650027413 50798070615249077345035)
                  ·
                    rfl

theorem cell23_890360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_890360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890360 prefixEnd_890360 := by exact prefixLift 890360
  have htrace : WordTrace (prefixWord ++ tailWord_890360) baseStart_890360 baseEnd_890360 := by
    simpa [prefixWord, tailWord_890360, baseEnd_890360] using wordTrace_append hprefix tailTrace_890360
  have hstable : (prefixWord ++ tailWord_890360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890360).length < 2 ^ (prefixWord ++ tailWord_890360).sum := by decide
  have hdescent : baseEnd_890360 < baseStart_890360 := by decide
  rcases family_descends (prefixWord ++ tailWord_890360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890398 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_890398 : Nat := 118140960795 + 890398 * 2 ^ 59
def prefixEnd_890398 : Nat := 4983230072969 + 3 ^ 40 * 890398 * 2
def baseEnd_890398 : Nat := 152400715934037515810047

theorem tailTrace_890398 : CollatzResearch.WordTrace tailWord_890398 prefixEnd_890398 152400715934037515810047 := by
  unfold tailWord_890398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059435378530948589595981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21650322018831725811178565 4059435378530948589595981)
  ·
    refine ⟨1522288266949105721098493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4059435378530948589595981 1522288266949105721098493)
    ·
      refine ⟨570858100105914645411935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1522288266949105721098493 570858100105914645411935)
      ·
        refine ⟨856287150158871968117903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570858100105914645411935 856287150158871968117903)
        ·
          refine ⟨1284430725238307952176855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856287150158871968117903 1284430725238307952176855)
          ·
            refine ⟨1926646087857461928265283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284430725238307952176855 1926646087857461928265283)
            ·
              refine ⟨2889969131786192892397925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926646087857461928265283 2889969131786192892397925)
              ·
                refine ⟨541869212209911167324611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2889969131786192892397925 541869212209911167324611)
                ·
                  refine ⟨812803818314866750986917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541869212209911167324611 812803818314866750986917)
                  ·
                    refine ⟨152400715934037515810047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 812803818314866750986917 152400715934037515810047)
                    ·
                      rfl

theorem cell23_890398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_890398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890398 prefixEnd_890398 := by exact prefixLift 890398
  have htrace : WordTrace (prefixWord ++ tailWord_890398) baseStart_890398 baseEnd_890398 := by
    simpa [prefixWord, tailWord_890398, baseEnd_890398] using wordTrace_append hprefix tailTrace_890398
  have hstable : (prefixWord ++ tailWord_890398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890398).length < 2 ^ (prefixWord ++ tailWord_890398).sum := by decide
  have hdescent : baseEnd_890398 < baseStart_890398 := by decide
  rcases family_descends (prefixWord ++ tailWord_890398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890423 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_890423 : Nat := 118140960795 + 890423 * 2 ^ 59
def prefixEnd_890423 : Nat := 4983230072969 + 3 ^ 40 * 890423 * 2
def baseEnd_890423 : Nat := 457214984818474949617525

theorem tailTrace_890423 : CollatzResearch.WordTrace tailWord_890423 prefixEnd_890423 457214984818474949617525 := by
  unfold tailWord_890423
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476394853157017986427923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21650929902104678657618615 32476394853157017986427923)
  ·
    refine ⟨48714592279735526979641885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32476394853157017986427923 48714592279735526979641885)
    ·
      refine ⟨18267972104900822617365707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48714592279735526979641885 18267972104900822617365707)
      ·
        refine ⟨27401958157351233926048561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18267972104900822617365707 27401958157351233926048561)
        ·
          refine ⟨20551468618013425444536421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27401958157351233926048561 20551468618013425444536421)
          ·
            refine ⟨3853400365877517270850579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20551468618013425444536421 3853400365877517270850579)
            ·
              refine ⟨5780100548816275906275869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853400365877517270850579 5780100548816275906275869)
              ·
                refine ⟨2167537705806103464853451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780100548816275906275869 2167537705806103464853451)
                ·
                  refine ⟨3251306558709155197280177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167537705806103464853451 3251306558709155197280177)
                  ·
                    refine ⟨2438479919031866397960133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251306558709155197280177 2438479919031866397960133)
                    ·
                      refine ⟨457214984818474949617525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2438479919031866397960133 457214984818474949617525)
                      ·
                        rfl

theorem cell23_890423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_890423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890423 prefixEnd_890423 := by exact prefixLift 890423
  have htrace : WordTrace (prefixWord ++ tailWord_890423) baseStart_890423 baseEnd_890423 := by
    simpa [prefixWord, tailWord_890423, baseEnd_890423] using wordTrace_append hprefix tailTrace_890423
  have hstable : (prefixWord ++ tailWord_890423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890423).length < 2 ^ (prefixWord ++ tailWord_890423).sum := by decide
  have hdescent : baseEnd_890423 < baseStart_890423 := by decide
  rcases family_descends (prefixWord ++ tailWord_890423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890438 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_890438 : Nat := 118140960795 + 890438 * 2 ^ 59
def prefixEnd_890438 : Nat := 4983230072969 + 3 ^ 40 * 890438 * 2
def baseEnd_890438 : Nat := 457222687028292390929957

theorem tailTrace_890438 : CollatzResearch.WordTrace tailWord_890438 prefixEnd_890438 457222687028292390929957 := by
  unfold tailWord_890438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014904435878208610881999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21651294632068450365482645 1014904435878208610881999)
  ·
    refine ⟨1522356653817312916322999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014904435878208610881999 1522356653817312916322999)
    ·
      refine ⟨2283534980725969374484499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522356653817312916322999 2283534980725969374484499)
      ·
        refine ⟨3425302471088954061726749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283534980725969374484499 3425302471088954061726749)
        ·
          refine ⟨1284488426658357773147531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3425302471088954061726749 1284488426658357773147531)
          ·
            refine ⟨1926732639987536659721297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284488426658357773147531 1926732639987536659721297)
            ·
              refine ⟨1445049479990652494790973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926732639987536659721297 1445049479990652494790973)
              ·
                refine ⟨541893554996494685546615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445049479990652494790973 541893554996494685546615)
                ·
                  refine ⟨812840332494742028319923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541893554996494685546615 812840332494742028319923)
                  ·
                    refine ⟨1219260498742113042479885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 812840332494742028319923 1219260498742113042479885)
                    ·
                      refine ⟨457222687028292390929957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1219260498742113042479885 457222687028292390929957)
                      ·
                        rfl

theorem cell23_890438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_890438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890438 prefixEnd_890438 := by exact prefixLift 890438
  have htrace : WordTrace (prefixWord ++ tailWord_890438) baseStart_890438 baseEnd_890438 := by
    simpa [prefixWord, tailWord_890438, baseEnd_890438] using wordTrace_append hprefix tailTrace_890438
  have hstable : (prefixWord ++ tailWord_890438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890438).length < 2 ^ (prefixWord ++ tailWord_890438).sum := by decide
  have hdescent : baseEnd_890438 < baseStart_890438 := by decide
  rcases family_descends (prefixWord ++ tailWord_890438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890444 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_890444 : Nat := 118140960795 + 890444 * 2 ^ 59
def prefixEnd_890444 : Nat := 4983230072969 + 3 ^ 40 * 890444 * 2
def baseEnd_890444 : Nat := 457225767912219367454929

theorem tailTrace_890444 : CollatzResearch.WordTrace tailWord_890444 prefixEnd_890444 457225767912219367454929 := by
  unfold tailWord_890444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16238580393040469286471193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21651440524053959048628257 16238580393040469286471193)
  ·
    refine ⟨12178935294780351964853395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16238580393040469286471193 12178935294780351964853395)
    ·
      refine ⟨18268402942170527947280093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178935294780351964853395 18268402942170527947280093)
      ·
        refine ⟨6850651103313947980230035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18268402942170527947280093 6850651103313947980230035)
        ·
          refine ⟨10275976654970921970345053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850651103313947980230035 10275976654970921970345053)
          ·
            refine ⟨3853491245614095738879395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10275976654970921970345053 3853491245614095738879395)
            ·
              refine ⟨5780236868421143608319093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853491245614095738879395 5780236868421143608319093)
              ·
                refine ⟨541897206414482213279915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5780236868421143608319093 541897206414482213279915)
                ·
                  refine ⟨812845809621723319919873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541897206414482213279915 812845809621723319919873)
                  ·
                    refine ⟨609634357216292489939905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 812845809621723319919873 609634357216292489939905)
                    ·
                      refine ⟨457225767912219367454929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609634357216292489939905 457225767912219367454929)
                      ·
                        rfl

theorem cell23_890444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_890444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890444 prefixEnd_890444 := by exact prefixLift 890444
  have htrace : WordTrace (prefixWord ++ tailWord_890444) baseStart_890444 baseEnd_890444 := by
    simpa [prefixWord, tailWord_890444, baseEnd_890444] using wordTrace_append hprefix tailTrace_890444
  have hstable : (prefixWord ++ tailWord_890444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890444).length < 2 ^ (prefixWord ++ tailWord_890444).sum := by decide
  have hdescent : baseEnd_890444 < baseStart_890444 := by decide
  rcases family_descends (prefixWord ++ tailWord_890444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890503 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_890503 : Nat := 118140960795 + 890503 * 2 ^ 59
def prefixEnd_890503 : Nat := 4983230072969 + 3 ^ 40 * 890503 * 2
def baseEnd_890503 : Nat := 457256063270834636617157

theorem tailTrace_890503 : CollatzResearch.WordTrace tailWord_890503 prefixEnd_890503 457256063270834636617157 := by
  unfold tailWord_890503
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479312692867191649340163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21652875128578127766226775 32479312692867191649340163)
  ·
    refine ⟨48718969039300787474010245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479312692867191649340163 48718969039300787474010245)
    ·
      refine ⟨9134806694868897651376921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48718969039300787474010245 9134806694868897651376921)
      ·
        refine ⟨6851105021151673238532691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9134806694868897651376921 6851105021151673238532691)
        ·
          refine ⟨10276657531727509857799037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851105021151673238532691 10276657531727509857799037)
          ·
            refine ⟨3853746574397816196674639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10276657531727509857799037 3853746574397816196674639)
            ·
              refine ⟨5780619861596724295011959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853746574397816196674639 5780619861596724295011959)
              ·
                refine ⟨8670929792395086442517939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780619861596724295011959 8670929792395086442517939)
                ·
                  refine ⟨13006394688592629663776909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8670929792395086442517939 13006394688592629663776909)
                  ·
                    refine ⟨4877398008222236123916341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13006394688592629663776909 4877398008222236123916341)
                    ·
                      refine ⟨457256063270834636617157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4877398008222236123916341 457256063270834636617157)
                      ·
                        rfl

theorem cell23_890503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_890503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890503 prefixEnd_890503 := by exact prefixLift 890503
  have htrace : WordTrace (prefixWord ++ tailWord_890503) baseStart_890503 baseEnd_890503 := by
    simpa [prefixWord, tailWord_890503, baseEnd_890503] using wordTrace_append hprefix tailTrace_890503
  have hstable : (prefixWord ++ tailWord_890503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890503).length < 2 ^ (prefixWord ++ tailWord_890503).sum := by decide
  have hdescent : baseEnd_890503 < baseStart_890503 := by decide
  rcases family_descends (prefixWord ++ tailWord_890503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890513 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_890513 : Nat := 118140960795 + 890513 * 2 ^ 59
def prefixEnd_890513 : Nat := 4983230072969 + 3 ^ 40 * 890513 * 2
def baseEnd_890513 : Nat := 457261198077379597492111

theorem tailTrace_890513 : CollatzResearch.WordTrace tailWord_890513 prefixEnd_890513 457261198077379597492111 := by
  unfold tailWord_890513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479677422830963357204193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21653118281887308904802795 32479677422830963357204193)
  ·
    refine ⟨24359758067123222517903145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32479677422830963357204193 24359758067123222517903145)
    ·
      refine ⟨18269818550342416888427359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24359758067123222517903145 18269818550342416888427359)
      ·
        refine ⟨27404727825513625332641039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18269818550342416888427359 27404727825513625332641039)
        ·
          refine ⟨41107091738270437998961559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27404727825513625332641039 41107091738270437998961559)
          ·
            refine ⟨61660637607405656998442339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41107091738270437998961559 61660637607405656998442339)
            ·
              refine ⟨92490956411108485497663509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61660637607405656998442339 92490956411108485497663509)
              ·
                refine ⟨4335513581770710257702977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92490956411108485497663509 4335513581770710257702977)
                ·
                  refine ⟨3251635186328032693277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335513581770710257702977 3251635186328032693277233)
                  ·
                    refine ⟨2438726389746024519957925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251635186328032693277233 2438726389746024519957925)
                    ·
                      refine ⟨457261198077379597492111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2438726389746024519957925 457261198077379597492111)
                      ·
                        rfl

theorem cell23_890513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_890513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890513 prefixEnd_890513 := by exact prefixLift 890513
  have htrace : WordTrace (prefixWord ++ tailWord_890513) baseStart_890513 baseEnd_890513 := by
    simpa [prefixWord, tailWord_890513, baseEnd_890513] using wordTrace_append hprefix tailTrace_890513
  have hstable : (prefixWord ++ tailWord_890513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890513).length < 2 ^ (prefixWord ++ tailWord_890513).sum := by decide
  have hdescent : baseEnd_890513 < baseStart_890513 := by decide
  rcases family_descends (prefixWord ++ tailWord_890513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890553 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_890553 : Nat := 118140960795 + 890553 * 2 ^ 59
def prefixEnd_890553 : Nat := 4983230072969 + 3 ^ 40 * 890553 * 2
def baseEnd_890553 : Nat := 152427245767853146997309

theorem tailTrace_890553 : CollatzResearch.WordTrace tailWord_890553 prefixEnd_890553 152427245767853146997309 := by
  unfold tailWord_890553
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481136342686050188660313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21654090895124033459106875 32481136342686050188660313)
  ·
    refine ⟨24360852257014537641495235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32481136342686050188660313 24360852257014537641495235)
    ·
      refine ⟨36541278385521806462242853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24360852257014537641495235 36541278385521806462242853)
      ·
        refine ⟨6851489697285338711670535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36541278385521806462242853 6851489697285338711670535)
        ·
          refine ⟨10277234545928008067505803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851489697285338711670535 10277234545928008067505803)
          ·
            refine ⟨15415851818892012101258705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277234545928008067505803 15415851818892012101258705)
            ·
              refine ⟨11561888864169009075944029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415851818892012101258705 11561888864169009075944029)
              ·
                refine ⟨4335708324063378403479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11561888864169009075944029 4335708324063378403479011)
                ·
                  refine ⟨6503562486095067605218517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335708324063378403479011 6503562486095067605218517)
                  ·
                    refine ⟨152427245767853146997309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6503562486095067605218517 152427245767853146997309)
                    ·
                      rfl

theorem cell23_890553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_890553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890553 prefixEnd_890553 := by exact prefixLift 890553
  have htrace : WordTrace (prefixWord ++ tailWord_890553) baseStart_890553 baseEnd_890553 := by
    simpa [prefixWord, tailWord_890553, baseEnd_890553] using wordTrace_append hprefix tailTrace_890553
  have hstable : (prefixWord ++ tailWord_890553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890553).length < 2 ^ (prefixWord ++ tailWord_890553).sum := by decide
  have hdescent : baseEnd_890553 < baseStart_890553 := by decide
  rcases family_descends (prefixWord ++ tailWord_890553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890634 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_890634 : Nat := 118140960795 + 890634 * 2 ^ 59
def prefixEnd_890634 : Nat := 4983230072969 + 3 ^ 40 * 890634 * 2
def baseEnd_890634 : Nat := 152441109745524541359685

theorem tailTrace_890634 : CollatzResearch.WordTrace tailWord_890634 prefixEnd_890634 152441109745524541359685 := by
  unfold tailWord_890634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121022663848150255589739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21656060436928400681572637 8121022663848150255589739)
  ·
    refine ⟨12181533995772225383384609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8121022663848150255589739 12181533995772225383384609)
    ·
      refine ⟨9136150496829169037538457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12181533995772225383384609 9136150496829169037538457)
      ·
        refine ⟨6852112872621876778153843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9136150496829169037538457 6852112872621876778153843)
        ·
          refine ⟨10278169308932815167230765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852112872621876778153843 10278169308932815167230765)
          ·
            refine ⟨3854313490849805687711537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10278169308932815167230765 3854313490849805687711537)
            ·
              refine ⟨2890735118137354265783653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854313490849805687711537 2890735118137354265783653)
              ·
                refine ⟨542012834650753924834435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890735118137354265783653 542012834650753924834435)
                ·
                  refine ⟨813019251976130887251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542012834650753924834435 813019251976130887251653)
                  ·
                    refine ⟨152441109745524541359685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813019251976130887251653 152441109745524541359685)
                    ·
                      rfl

theorem cell23_890634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_890634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890634 prefixEnd_890634 := by exact prefixLift 890634
  have htrace : WordTrace (prefixWord ++ tailWord_890634) baseStart_890634 baseEnd_890634 := by
    simpa [prefixWord, tailWord_890634, baseEnd_890634] using wordTrace_append hprefix tailTrace_890634
  have hstable : (prefixWord ++ tailWord_890634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890634).length < 2 ^ (prefixWord ++ tailWord_890634).sum := by decide
  have hdescent : baseEnd_890634 < baseStart_890634 := by decide
  rcases family_descends (prefixWord ++ tailWord_890634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890643 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 9]
def baseStart_890643 : Nat := 118140960795 + 890643 * 2 ^ 59
def prefixEnd_890643 : Nat := 4983230072969 + 3 ^ 40 * 890643 * 2
def baseEnd_890643 : Nat := 152442650187488029622171

theorem tailTrace_890643 : CollatzResearch.WordTrace tailWord_890643 prefixEnd_890643 152442650187488029622171 := by
  unfold tailWord_890643
  simp only [CollatzResearch.WordTrace]
  refine ⟨32484418912359995559436583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21656279274906663706291055 32484418912359995559436583)
  ·
    refine ⟨48726628368539993339154875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32484418912359995559436583 48726628368539993339154875)
    ·
      refine ⟨73089942552809990008732313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48726628368539993339154875 73089942552809990008732313)
      ·
        refine ⟨54817456914607492506549235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73089942552809990008732313 54817456914607492506549235)
        ·
          refine ⟨82226185371911238759823853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54817456914607492506549235 82226185371911238759823853)
          ·
            refine ⟨30834819514466714534933945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82226185371911238759823853 30834819514466714534933945)
            ·
              refine ⟨23126114635850035901200459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30834819514466714534933945 23126114635850035901200459)
              ·
                refine ⟨34689171953775053851800689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23126114635850035901200459 34689171953775053851800689)
                ·
                  refine ⟨26016878965331290388850517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34689171953775053851800689 26016878965331290388850517)
                  ·
                    refine ⟨152442650187488029622171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26016878965331290388850517 152442650187488029622171)
                    ·
                      rfl

theorem cell23_890643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_890643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890643 prefixEnd_890643 := by exact prefixLift 890643
  have htrace : WordTrace (prefixWord ++ tailWord_890643) baseStart_890643 baseEnd_890643 := by
    simpa [prefixWord, tailWord_890643, baseEnd_890643] using wordTrace_append hprefix tailTrace_890643
  have hstable : (prefixWord ++ tailWord_890643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890643).length < 2 ^ (prefixWord ++ tailWord_890643).sum := by decide
  have hdescent : baseEnd_890643 < baseStart_890643 := by decide
  rcases family_descends (prefixWord ++ tailWord_890643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890711 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 1, 5]
def baseStart_890711 : Nat := 118140960795 + 890711 * 2 ^ 59
def prefixEnd_890711 : Nat := 4983230072969 + 3 ^ 40 * 890711 * 2
def baseEnd_890711 : Nat := 152454289082323274272067

theorem tailTrace_890711 : CollatzResearch.WordTrace tailWord_890711 prefixEnd_890711 152454289082323274272067 := by
  unfold tailWord_890711
  simp only [CollatzResearch.WordTrace]
  refine ⟨32486899076113643172911987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21657932717409095448607991 32486899076113643172911987)
  ·
    refine ⟨48730348614170464759367981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32486899076113643172911987 48730348614170464759367981)
    ·
      refine ⟨18273880730313924284762993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48730348614170464759367981 18273880730313924284762993)
      ·
        refine ⟨13705410547735443213572245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18273880730313924284762993 13705410547735443213572245)
        ·
          refine ⟨642441119425098900636199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13705410547735443213572245 642441119425098900636199)
          ·
            refine ⟨963661679137648350954299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642441119425098900636199 963661679137648350954299)
            ·
              refine ⟨1445492518706472526431449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963661679137648350954299 1445492518706472526431449)
              ·
                refine ⟨1084119389029854394823587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445492518706472526431449 1084119389029854394823587)
                ·
                  refine ⟨1626179083544781592235381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084119389029854394823587 1626179083544781592235381)
                  ·
                    refine ⟨152454289082323274272067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1626179083544781592235381 152454289082323274272067)
                    ·
                      rfl

theorem cell23_890711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_890711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890711 prefixEnd_890711 := by exact prefixLift 890711
  have htrace : WordTrace (prefixWord ++ tailWord_890711) baseStart_890711 baseEnd_890711 := by
    simpa [prefixWord, tailWord_890711, baseEnd_890711] using wordTrace_append hprefix tailTrace_890711
  have hstable : (prefixWord ++ tailWord_890711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890711).length < 2 ^ (prefixWord ++ tailWord_890711).sum := by decide
  have hdescent : baseEnd_890711 < baseStart_890711 := by decide
  rcases family_descends (prefixWord ++ tailWord_890711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890714 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_890714 : Nat := 118140960795 + 890714 * 2 ^ 59
def prefixEnd_890714 : Nat := 4983230072969 + 3 ^ 40 * 890714 * 2
def baseEnd_890714 : Nat := 457364407688933311078687

theorem tailTrace_890714 : CollatzResearch.WordTrace tailWord_890714 prefixEnd_890714 457364407688933311078687 := by
  unfold tailWord_890714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121752123775693671317799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21658005663401849790180797 8121752123775693671317799)
  ·
    refine ⟨12182628185663540506976699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8121752123775693671317799 12182628185663540506976699)
    ·
      refine ⟨18273942278495310760465049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182628185663540506976699 18273942278495310760465049)
      ·
        refine ⟨13705456708871483070348787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18273942278495310760465049 13705456708871483070348787)
        ·
          refine ⟨20558185063307224605523181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13705456708871483070348787 20558185063307224605523181)
          ·
            refine ⟨7709319398740209227071193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20558185063307224605523181 7709319398740209227071193)
            ·
              refine ⟨5781989549055156920303395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709319398740209227071193 5781989549055156920303395)
              ·
                refine ⟨8672984323582735380455093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781989549055156920303395 8672984323582735380455093)
                ·
                  refine ⟨813092280335881441917665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8672984323582735380455093 813092280335881441917665)
                  ·
                    refine ⟨609819210251911081438249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813092280335881441917665 609819210251911081438249)
                    ·
                      refine ⟨457364407688933311078687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609819210251911081438249 457364407688933311078687)
                      ·
                        rfl

theorem cell23_890714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_890714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890714 prefixEnd_890714 := by exact prefixLift 890714
  have htrace : WordTrace (prefixWord ++ tailWord_890714) baseStart_890714 baseEnd_890714 := by
    simpa [prefixWord, tailWord_890714, baseEnd_890714] using wordTrace_append hprefix tailTrace_890714
  have hstable : (prefixWord ++ tailWord_890714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890714).length < 2 ^ (prefixWord ++ tailWord_890714).sum := by decide
  have hdescent : baseEnd_890714 < baseStart_890714 := by decide
  rcases family_descends (prefixWord ++ tailWord_890714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890720 : List Nat := [2, 1, 1, 3, 3, 2, 2, 9]
def baseStart_890720 : Nat := 118140960795 + 890720 * 2 ^ 59
def prefixEnd_890720 : Nat := 4983230072969 + 3 ^ 40 * 890720 * 2
def baseEnd_890720 : Nat := 16939536613809640281617

theorem tailTrace_890720 : CollatzResearch.WordTrace tailWord_890720 prefixEnd_890720 16939536613809640281617 := by
  unfold tailWord_890720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243613666540518854994807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21658151555387358473326409 16243613666540518854994807)
  ·
    refine ⟨24365420499810778282492211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16243613666540518854994807 24365420499810778282492211)
    ·
      refine ⟨36548130749716167423738317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24365420499810778282492211 36548130749716167423738317)
      ·
        refine ⟨13705549031143562783901869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36548130749716167423738317 13705549031143562783901869)
        ·
          refine ⟨5139580886678836043963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13705549031143562783901869 5139580886678836043963201)
          ·
            refine ⟨3854685665009127032972401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5139580886678836043963201 3854685665009127032972401)
            ·
              refine ⟨2891014248756845274729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854685665009127032972401 2891014248756845274729301)
              ·
                refine ⟨16939536613809640281617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2891014248756845274729301 16939536613809640281617)
                ·
                  rfl

theorem cell23_890720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_890720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890720 prefixEnd_890720 := by exact prefixLift 890720
  have htrace : WordTrace (prefixWord ++ tailWord_890720) baseStart_890720 baseEnd_890720 := by
    simpa [prefixWord, tailWord_890720, baseEnd_890720] using wordTrace_append hprefix tailTrace_890720
  have hstable : (prefixWord ++ tailWord_890720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890720).length < 2 ^ (prefixWord ++ tailWord_890720).sum := by decide
  have hdescent : baseEnd_890720 < baseStart_890720 := by decide
  rcases family_descends (prefixWord ++ tailWord_890720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890727 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_890727 : Nat := 118140960795 + 890727 * 2 ^ 59
def prefixEnd_890727 : Nat := 4983230072969 + 3 ^ 40 * 890727 * 2
def baseEnd_890727 : Nat := 457371082937441760216127

theorem tailTrace_890727 : CollatzResearch.WordTrace tailWord_890727 prefixEnd_890727 457371082937441760216127 := by
  unfold tailWord_890727
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487482644055677905494435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21658321762703785270329623 32487482644055677905494435)
  ·
    refine ⟨48731223966083516858241653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32487482644055677905494435 48731223966083516858241653)
    ·
      refine ⟨4568552246820329705460155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48731223966083516858241653 4568552246820329705460155)
      ·
        refine ⟨6852828370230494558190233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568552246820329705460155 6852828370230494558190233)
        ·
          refine ⟨5139621277672870918642675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6852828370230494558190233 5139621277672870918642675)
          ·
            refine ⟨7709431916509306377964013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139621277672870918642675 7709431916509306377964013)
            ·
              refine ⟨2891036968690989891736505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7709431916509306377964013 2891036968690989891736505)
              ·
                refine ⟨2168277726518242418802379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891036968690989891736505 2168277726518242418802379)
                ·
                  refine ⟨3252416589777363628203569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168277726518242418802379 3252416589777363628203569)
                  ·
                    refine ⟨2439312442333022721152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3252416589777363628203569 2439312442333022721152677)
                    ·
                      refine ⟨457371082937441760216127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2439312442333022721152677 457371082937441760216127)
                      ·
                        rfl

theorem cell23_890727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_890727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890727 prefixEnd_890727 := by exact prefixLift 890727
  have htrace : WordTrace (prefixWord ++ tailWord_890727) baseStart_890727 baseEnd_890727 := by
    simpa [prefixWord, tailWord_890727, baseEnd_890727] using wordTrace_append hprefix tailTrace_890727
  have hstable : (prefixWord ++ tailWord_890727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890727).length < 2 ^ (prefixWord ++ tailWord_890727).sum := by decide
  have hdescent : baseEnd_890727 < baseStart_890727 := by decide
  rcases family_descends (prefixWord ++ tailWord_890727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890731 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 1, 2, 2]
def baseStart_890731 : Nat := 118140960795 + 890731 * 2 ^ 59
def prefixEnd_890731 : Nat := 4983230072969 + 3 ^ 40 * 890731 * 2
def baseEnd_890731 : Nat := 457373136860059744566109

theorem tailTrace_890731 : CollatzResearch.WordTrace tailWord_890731 prefixEnd_890731 457373136860059744566109 := by
  unfold tailWord_890731
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487628536041186588640047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21658419024027457725760031 32487628536041186588640047)
  ·
    refine ⟨48731442804061779882960071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32487628536041186588640047 48731442804061779882960071)
    ·
      refine ⟨73097164206092669824440107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48731442804061779882960071 73097164206092669824440107)
      ·
        refine ⟨109645746309139004736660161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73097164206092669824440107 109645746309139004736660161)
        ·
          refine ⟨82234309731854253552495121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109645746309139004736660161 82234309731854253552495121)
          ·
            refine ⟨61675732298890690164371341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82234309731854253552495121 61675732298890690164371341)
            ·
              refine ⟨23128399612084008811639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61675732298890690164371341 23128399612084008811639253)
              ·
                refine ⟨542071865908218956522795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23128399612084008811639253 542071865908218956522795)
                ·
                  refine ⟨813107798862328434784193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542071865908218956522795 813107798862328434784193)
                  ·
                    refine ⟨609830849146746326088145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813107798862328434784193 609830849146746326088145)
                    ·
                      refine ⟨457373136860059744566109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 609830849146746326088145 457373136860059744566109)
                      ·
                        rfl

theorem cell23_890731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 2, 2].length) (baseStart_890731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890731 prefixEnd_890731 := by exact prefixLift 890731
  have htrace : WordTrace (prefixWord ++ tailWord_890731) baseStart_890731 baseEnd_890731 := by
    simpa [prefixWord, tailWord_890731, baseEnd_890731] using wordTrace_append hprefix tailTrace_890731
  have hstable : (prefixWord ++ tailWord_890731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890731).length < 2 ^ (prefixWord ++ tailWord_890731).sum := by decide
  have hdescent : baseEnd_890731 < baseStart_890731 := by decide
  rcases family_descends (prefixWord ++ tailWord_890731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890734 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_890734 : Nat := 118140960795 + 890734 * 2 ^ 59
def prefixEnd_890734 : Nat := 4983230072969 + 3 ^ 40 * 890734 * 2
def baseEnd_890734 : Nat := 457374677302023232828595

theorem tailTrace_890734 : CollatzResearch.WordTrace tailWord_890734 prefixEnd_890734 457374677302023232828595 := by
  unfold tailWord_890734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060967244378789762624907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21658491970020212067332837 4060967244378789762624907)
  ·
    refine ⟨6091450866568184643937361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4060967244378789762624907 6091450866568184643937361)
    ·
      refine ⟨4568588149926138482953021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6091450866568184643937361 4568588149926138482953021)
      ·
        refine ⟨1713220556222301931107383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4568588149926138482953021 1713220556222301931107383)
        ·
          refine ⟨2569830834333452896661075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713220556222301931107383 2569830834333452896661075)
          ·
            refine ⟨3854746251500179344991613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569830834333452896661075 3854746251500179344991613)
            ·
              refine ⟨1445529844312567254371855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3854746251500179344991613 1445529844312567254371855)
              ·
                refine ⟨2168294766468850881557783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445529844312567254371855 2168294766468850881557783)
                ·
                  refine ⟨3252442149703276322336675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168294766468850881557783 3252442149703276322336675)
                  ·
                    refine ⟨4878663224554914483505013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3252442149703276322336675 4878663224554914483505013)
                    ·
                      refine ⟨457374677302023232828595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4878663224554914483505013 457374677302023232828595)
                      ·
                        rfl

theorem cell23_890734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_890734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890734 prefixEnd_890734 := by exact prefixLift 890734
  have htrace : WordTrace (prefixWord ++ tailWord_890734) baseStart_890734 baseEnd_890734 := by
    simpa [prefixWord, tailWord_890734, baseEnd_890734] using wordTrace_append hprefix tailTrace_890734
  have hstable : (prefixWord ++ tailWord_890734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890734).length < 2 ^ (prefixWord ++ tailWord_890734).sum := by decide
  have hdescent : baseEnd_890734 < baseStart_890734 := by decide
  rcases family_descends (prefixWord ++ tailWord_890734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890742 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_890742 : Nat := 118140960795 + 890742 * 2 ^ 59
def prefixEnd_890742 : Nat := 4983230072969 + 3 ^ 40 * 890742 * 2
def baseEnd_890742 : Nat := 457378785147259201528559

theorem tailTrace_890742 : CollatzResearch.WordTrace tailWord_890742 prefixEnd_890742 457378785147259201528559 := by
  unfold tailWord_890742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030501858687583466705655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21658686492667556978193653 2030501858687583466705655)
  ·
    refine ⟨3045752788031375200058483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030501858687583466705655 3045752788031375200058483)
    ·
      refine ⟨4568629182047062800087725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045752788031375200058483 4568629182047062800087725)
      ·
        refine ⟨1713235943267648550032897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4568629182047062800087725 1713235943267648550032897)
        ·
          refine ⟨1284926957450736412524673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713235943267648550032897 1284926957450736412524673)
          ·
            refine ⟨963695218088052309393505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284926957450736412524673 963695218088052309393505)
            ·
              refine ⟨722771413566039232045129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963695218088052309393505 722771413566039232045129)
              ·
                refine ⟨542078560174529424033847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722771413566039232045129 542078560174529424033847)
                ·
                  refine ⟨813117840261794136050771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542078560174529424033847 813117840261794136050771)
                  ·
                    refine ⟨1219676760392691204076157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 813117840261794136050771 1219676760392691204076157)
                    ·
                      refine ⟨457378785147259201528559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1219676760392691204076157 457378785147259201528559)
                      ·
                        rfl

theorem cell23_890742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_890742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890742 prefixEnd_890742 := by exact prefixLift 890742
  have htrace : WordTrace (prefixWord ++ tailWord_890742) baseStart_890742 baseEnd_890742 := by
    simpa [prefixWord, tailWord_890742, baseEnd_890742] using wordTrace_append hprefix tailTrace_890742
  have hstable : (prefixWord ++ tailWord_890742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890742).length < 2 ^ (prefixWord ++ tailWord_890742).sum := by decide
  have hdescent : baseEnd_890742 < baseStart_890742 := by decide
  rcases family_descends (prefixWord ++ tailWord_890742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890782 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_890782 : Nat := 118140960795 + 890782 * 2 ^ 59
def prefixEnd_890782 : Nat := 4983230072969 + 3 ^ 40 * 890782 * 2
def baseEnd_890782 : Nat := 457399324373439045028375

theorem tailTrace_890782 : CollatzResearch.WordTrace tailWord_890782 prefixEnd_890782 457399324373439045028375 := by
  unfold tailWord_890782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061186082357052787343325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21659659105904281532497733 4061186082357052787343325)
  ·
    refine ⟨1522944780883894795253747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4061186082357052787343325 1522944780883894795253747)
    ·
      refine ⟨2284417171325842192880621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522944780883894795253747 2284417171325842192880621)
      ·
        refine ⟨856656439247190822330233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2284417171325842192880621 856656439247190822330233)
        ·
          refine ⟨642492329435393116747675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856656439247190822330233 642492329435393116747675)
          ·
            refine ⟨963738494153089675121513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642492329435393116747675 963738494153089675121513)
            ·
              refine ⟨722803870614817256341135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963738494153089675121513 722803870614817256341135)
              ·
                refine ⟨1084205805922225884511703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722803870614817256341135 1084205805922225884511703)
                ·
                  refine ⟨1626308708883338826767555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084205805922225884511703 1626308708883338826767555)
                  ·
                    refine ⟨2439463063325008240151333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626308708883338826767555 2439463063325008240151333)
                    ·
                      refine ⟨457399324373439045028375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2439463063325008240151333 457399324373439045028375)
                      ·
                        rfl

theorem cell23_890782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_890782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890782 prefixEnd_890782 := by exact prefixLift 890782
  have htrace : WordTrace (prefixWord ++ tailWord_890782) baseStart_890782 baseEnd_890782 := by
    simpa [prefixWord, tailWord_890782, baseEnd_890782] using wordTrace_append hprefix tailTrace_890782
  have hstable : (prefixWord ++ tailWord_890782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890782).length < 2 ^ (prefixWord ++ tailWord_890782).sum := by decide
  have hdescent : baseEnd_890782 < baseStart_890782 := by decide
  rcases family_descends (prefixWord ++ tailWord_890782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890785 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_890785 : Nat := 118140960795 + 890785 * 2 ^ 59
def prefixEnd_890785 : Nat := 4983230072969 + 3 ^ 40 * 890785 * 2
def baseEnd_890785 : Nat := 457400864815402533290861

theorem tailTrace_890785 : CollatzResearch.WordTrace tailWord_890785 prefixEnd_890785 457400864815402533290861 := by
  unfold tailWord_890785
  simp only [CollatzResearch.WordTrace]
  refine ⟨32489598077845553811105809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21659732051897035874070539 32489598077845553811105809)
  ·
    refine ⟨24367198558384165358329357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32489598077845553811105809 24367198558384165358329357)
    ·
      refine ⟨9137699459394062009373509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24367198558384165358329357 9137699459394062009373509)
      ·
        refine ⟨1713318648636386626757533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9137699459394062009373509 1713318648636386626757533)
        ·
          refine ⟨642494493238644985034075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1713318648636386626757533 642494493238644985034075)
          ·
            refine ⟨963741739857967477551113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642494493238644985034075 963741739857967477551113)
            ·
              refine ⟨722806304893475608163335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963741739857967477551113 722806304893475608163335)
              ·
                refine ⟨1084209457340213412245003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722806304893475608163335 1084209457340213412245003)
                ·
                  refine ⟨1626314186010320118367505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084209457340213412245003 1626314186010320118367505)
                  ·
                    refine ⟨1219735639507740088775629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1626314186010320118367505 1219735639507740088775629)
                    ·
                      refine ⟨457400864815402533290861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1219735639507740088775629 457400864815402533290861)
                      ·
                        rfl

theorem cell23_890785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_890785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890785 prefixEnd_890785 := by exact prefixLift 890785
  have htrace : WordTrace (prefixWord ++ tailWord_890785) baseStart_890785 baseEnd_890785 := by
    simpa [prefixWord, tailWord_890785, baseEnd_890785] using wordTrace_append hprefix tailTrace_890785
  have hstable : (prefixWord ++ tailWord_890785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890785).length < 2 ^ (prefixWord ++ tailWord_890785).sum := by decide
  have hdescent : baseEnd_890785 < baseStart_890785 := by decide
  rcases family_descends (prefixWord ++ tailWord_890785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890877 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_890877 : Nat := 118140960795 + 890877 * 2 ^ 59
def prefixEnd_890877 : Nat := 4983230072969 + 3 ^ 40 * 890877 * 2
def baseEnd_890877 : Nat := 457448105035616173340437

theorem tailTrace_890877 : CollatzResearch.WordTrace tailWord_890877 prefixEnd_890877 457448105035616173340437 := by
  unfold tailWord_890877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492953593512253523454885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21661969062341502348969923 32492953593512253523454885)
  ·
    refine ⟨6092428798783547535647791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32492953593512253523454885 6092428798783547535647791)
    ·
      refine ⟨9138643198175321303471687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092428798783547535647791 9138643198175321303471687)
      ·
        refine ⟨13707964797262981955207531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138643198175321303471687 13707964797262981955207531)
        ·
          refine ⟨20561947195894472932811297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13707964797262981955207531 20561947195894472932811297)
          ·
            refine ⟨15421460396920854699608473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20561947195894472932811297 15421460396920854699608473)
            ·
              refine ⟨11566095297690641024706355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15421460396920854699608473 11566095297690641024706355)
              ·
                refine ⟨17349142946535961537059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566095297690641024706355 17349142946535961537059533)
                ·
                  refine ⟨6505928604950985576397325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17349142946535961537059533 6505928604950985576397325)
                  ·
                    refine ⟨2439723226856619591148997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6505928604950985576397325 2439723226856619591148997)
                    ·
                      refine ⟨457448105035616173340437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2439723226856619591148997 457448105035616173340437)
                      ·
                        rfl

theorem cell23_890877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_890877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890877 prefixEnd_890877 := by exact prefixLift 890877
  have htrace : WordTrace (prefixWord ++ tailWord_890877) baseStart_890877 baseEnd_890877 := by
    simpa [prefixWord, tailWord_890877, baseEnd_890877] using wordTrace_append hprefix tailTrace_890877
  have hstable : (prefixWord ++ tailWord_890877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890877).length < 2 ^ (prefixWord ++ tailWord_890877).sum := by decide
  have hdescent : baseEnd_890877 < baseStart_890877 := by decide
  rcases family_descends (prefixWord ++ tailWord_890877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890998 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_890998 : Nat := 118140960795 + 890998 * 2 ^ 59
def prefixEnd_890998 : Nat := 4983230072969 + 3 ^ 40 * 890998 * 2
def baseEnd_890998 : Nat := 152503412064936733309127

theorem tailTrace_890998 : CollatzResearch.WordTrace tailWord_890998 prefixEnd_890998 152503412064936733309127 := by
  unfold tailWord_890998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031085426629618199288103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21664911217382594125739765 2031085426629618199288103)
  ·
    refine ⟨3046628139944427298932155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031085426629618199288103 3046628139944427298932155)
    ·
      refine ⟨4569942209916640948398233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046628139944427298932155 4569942209916640948398233)
      ·
        refine ⟨3427456657437480711298675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4569942209916640948398233 3427456657437480711298675)
        ·
          refine ⟨5141184986156221066948013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427456657437480711298675 5141184986156221066948013)
          ·
            refine ⟨1927944369808582900105505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5141184986156221066948013 1927944369808582900105505)
            ·
              refine ⟨1445958277356437175079129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1927944369808582900105505 1445958277356437175079129)
              ·
                refine ⟨1084468708017327881309347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445958277356437175079129 1084468708017327881309347)
                ·
                  refine ⟨1626703062025991821964021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084468708017327881309347 1626703062025991821964021)
                  ·
                    refine ⟨152503412064936733309127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1626703062025991821964021 152503412064936733309127)
                    ·
                      rfl

theorem cell23_890998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_890998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_890998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_890998 prefixEnd_890998 := by exact prefixLift 890998
  have htrace : WordTrace (prefixWord ++ tailWord_890998) baseStart_890998 baseEnd_890998 := by
    simpa [prefixWord, tailWord_890998, baseEnd_890998] using wordTrace_append hprefix tailTrace_890998
  have hstable : (prefixWord ++ tailWord_890998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890998).length < 2 ^ (prefixWord ++ tailWord_890998).sum := by decide
  have hdescent : baseEnd_890998 < baseStart_890998 := by decide
  rcases family_descends (prefixWord ++ tailWord_890998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891001 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_891001 : Nat := 118140960795 + 891001 * 2 ^ 59
def prefixEnd_891001 : Nat := 4983230072969 + 3 ^ 40 * 891001 * 2
def baseEnd_891001 : Nat := 457511776636773688189867

theorem tailTrace_891001 : CollatzResearch.WordTrace tailWord_891001 prefixEnd_891001 457511776636773688189867 := by
  unfold tailWord_891001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497476245063022700968857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21664984163375348467312571 32497476245063022700968857)
  ·
    refine ⟨24373107183797267025726643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32497476245063022700968857 24373107183797267025726643)
    ·
      refine ⟨36559660775695900538589965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24373107183797267025726643 36559660775695900538589965)
      ·
        refine ⟨13709872790885962701971237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36559660775695900538589965 13709872790885962701971237)
        ·
          refine ⟨2570601148291118006619607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13709872790885962701971237 2570601148291118006619607)
          ·
            refine ⟨3855901722436677009929411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570601148291118006619607 3855901722436677009929411)
            ·
              refine ⟨5783852583655015514894117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855901722436677009929411 5783852583655015514894117)
              ·
                refine ⟨1084472359435315409042647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5783852583655015514894117 1084472359435315409042647)
                ·
                  refine ⟨1626708539152973113563971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084472359435315409042647 1626708539152973113563971)
                  ·
                    refine ⟨2440062808729459670345957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626708539152973113563971 2440062808729459670345957)
                    ·
                      refine ⟨457511776636773688189867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2440062808729459670345957 457511776636773688189867)
                      ·
                        rfl

theorem cell23_891001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_891001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891001 prefixEnd_891001 := by exact prefixLift 891001
  have htrace : WordTrace (prefixWord ++ tailWord_891001) baseStart_891001 baseEnd_891001 := by
    simpa [prefixWord, tailWord_891001, baseEnd_891001] using wordTrace_append hprefix tailTrace_891001
  have hstable : (prefixWord ++ tailWord_891001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891001).length < 2 ^ (prefixWord ++ tailWord_891001).sum := by decide
  have hdescent : baseEnd_891001 < baseStart_891001 := by decide
  rcases family_descends (prefixWord ++ tailWord_891001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891068 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_891068 : Nat := 118140960795 + 891068 * 2 ^ 59
def prefixEnd_891068 : Nat := 4983230072969 + 3 ^ 40 * 891068 * 2
def baseEnd_891068 : Nat := 457546179840624926052059

theorem tailTrace_891068 : CollatzResearch.WordTrace tailWord_891068 prefixEnd_891068 457546179840624926052059 := by
  unfold tailWord_891068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249959967910146571828929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21666613290546862095771905 16249959967910146571828929)
  ·
    refine ⟨12187469975932609928871697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16249959967910146571828929 12187469975932609928871697)
    ·
      refine ⟨9140602481949457446653773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12187469975932609928871697 9140602481949457446653773)
      ·
        refine ⟨3427725930731046542495165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9140602481949457446653773 3427725930731046542495165)
        ·
          refine ⟨1285397224024142453435687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3427725930731046542495165 1285397224024142453435687)
          ·
            refine ⟨1928095836036213680153531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285397224024142453435687 1928095836036213680153531)
            ·
              refine ⟨2892143754054320520230297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928095836036213680153531 2892143754054320520230297)
              ·
                refine ⟨2169107815540740390172723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892143754054320520230297 2169107815540740390172723)
                ·
                  refine ⟨3253661723311110585259085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169107815540740390172723 3253661723311110585259085)
                  ·
                    refine ⟨1220123146241666469472157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253661723311110585259085 1220123146241666469472157)
                    ·
                      refine ⟨457546179840624926052059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220123146241666469472157 457546179840624926052059)
                      ·
                        rfl

theorem cell23_891068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_891068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891068 prefixEnd_891068 := by exact prefixLift 891068
  have htrace : WordTrace (prefixWord ++ tailWord_891068) baseStart_891068 baseEnd_891068 := by
    simpa [prefixWord, tailWord_891068, baseEnd_891068] using wordTrace_append hprefix tailTrace_891068
  have hstable : (prefixWord ++ tailWord_891068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891068).length < 2 ^ (prefixWord ++ tailWord_891068).sum := by decide
  have hdescent : baseEnd_891068 < baseStart_891068 := by decide
  rcases family_descends (prefixWord ++ tailWord_891068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891101 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_891101 : Nat := 118140960795 + 891101 * 2 ^ 59
def prefixEnd_891101 : Nat := 4983230072969 + 3 ^ 40 * 891101 * 2
def baseEnd_891101 : Nat := 152521041567407765646469

theorem tailTrace_891101 : CollatzResearch.WordTrace tailWord_891101 prefixEnd_891101 152521041567407765646469 := by
  unfold tailWord_891101
  simp only [CollatzResearch.WordTrace]
  refine ⟨32501123544700739779609157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21667415696467159853072771 32501123544700739779609157)
  ·
    refine ⟨6093960664631388708676717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32501123544700739779609157 6093960664631388708676717)
    ·
      refine ⟨2285235249236770765753769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6093960664631388708676717 2285235249236770765753769)
      ·
        refine ⟨1713926436927578074315327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285235249236770765753769 1713926436927578074315327)
        ·
          refine ⟨2570889655391367111472991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713926436927578074315327 2570889655391367111472991)
          ·
            refine ⟨3856334483087050667209487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570889655391367111472991 3856334483087050667209487)
            ·
              refine ⟨5784501724630576000814231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856334483087050667209487 5784501724630576000814231)
              ·
                refine ⟨8676752586945864001221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784501724630576000814231 8676752586945864001221347)
                ·
                  refine ⟨13015128880418796001832021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676752586945864001221347 13015128880418796001832021)
                  ·
                    refine ⟨152521041567407765646469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13015128880418796001832021 152521041567407765646469)
                    ·
                      rfl

theorem cell23_891101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_891101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891101 prefixEnd_891101 := by exact prefixLift 891101
  have htrace : WordTrace (prefixWord ++ tailWord_891101) baseStart_891101 baseEnd_891101 := by
    simpa [prefixWord, tailWord_891101, baseEnd_891101] using wordTrace_append hprefix tailTrace_891101
  have hstable : (prefixWord ++ tailWord_891101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891101).length < 2 ^ (prefixWord ++ tailWord_891101).sum := by decide
  have hdescent : baseEnd_891101 < baseStart_891101 := by decide
  rcases family_descends (prefixWord ++ tailWord_891101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891108 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_891108 : Nat := 118140960795 + 891108 * 2 ^ 59
def prefixEnd_891108 : Nat := 4983230072969 + 3 ^ 40 * 891108 * 2
def baseEnd_891108 : Nat := 457566719066804769551875

theorem tailTrace_891108 : CollatzResearch.WordTrace tailWord_891108 prefixEnd_891108 457566719066804769551875 := by
  unfold tailWord_891108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250689427837689987556989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21667585903783586650075985 16250689427837689987556989)
  ·
    refine ⟨6094008535439133745333871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16250689427837689987556989 6094008535439133745333871)
    ·
      refine ⟨9141012803158700618000807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6094008535439133745333871 9141012803158700618000807)
      ·
        refine ⟨13711519204738050927001211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9141012803158700618000807 13711519204738050927001211)
        ·
          refine ⟨20567278807107076390501817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711519204738050927001211 20567278807107076390501817)
          ·
            refine ⟨15425459105330307292876363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20567278807107076390501817 15425459105330307292876363)
            ·
              refine ⟨23138188657995460939314545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425459105330307292876363 23138188657995460939314545)
              ·
                refine ⟨17353641493496595704485909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23138188657995460939314545 17353641493496595704485909)
                ·
                  refine ⟨813451945007652923647777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17353641493496595704485909 813451945007652923647777)
                  ·
                    refine ⟨610088958755739692735833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813451945007652923647777 610088958755739692735833)
                    ·
                      refine ⟨457566719066804769551875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610088958755739692735833 457566719066804769551875)
                      ·
                        rfl

theorem cell23_891108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_891108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891108 prefixEnd_891108 := by exact prefixLift 891108
  have htrace : WordTrace (prefixWord ++ tailWord_891108) baseStart_891108 baseEnd_891108 := by
    simpa [prefixWord, tailWord_891108, baseEnd_891108] using wordTrace_append hprefix tailTrace_891108
  have hstable : (prefixWord ++ tailWord_891108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891108).length < 2 ^ (prefixWord ++ tailWord_891108).sum := by decide
  have hdescent : baseEnd_891108 < baseStart_891108 := by decide
  rcases family_descends (prefixWord ++ tailWord_891108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891138 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_891138 : Nat := 118140960795 + 891138 * 2 ^ 59
def prefixEnd_891138 : Nat := 4983230072969 + 3 ^ 40 * 891138 * 2
def baseEnd_891138 : Nat := 457582123486439652176737

theorem tailTrace_891138 : CollatzResearch.WordTrace tailWord_891138 prefixEnd_891138 457582123486439652176737 := by
  unfold tailWord_891138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125618261391673774676517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21668315363711130065804045 8125618261391673774676517)
  ·
    refine ⟨1523553424010938832751847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8125618261391673774676517 1523553424010938832751847)
    ·
      refine ⟨2285330136016408249127771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523553424010938832751847 2285330136016408249127771)
      ·
        refine ⟨3427995204024612373691657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2285330136016408249127771 3427995204024612373691657)
        ·
          refine ⟨2570996403018459280268743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427995204024612373691657 2570996403018459280268743)
          ·
            refine ⟨3856494604527688920403115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570996403018459280268743 3856494604527688920403115)
            ·
              refine ⟨5784741906791533380604673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856494604527688920403115 5784741906791533380604673)
              ·
                refine ⟨4338556430093650035453505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5784741906791533380604673 4338556430093650035453505)
                ·
                  refine ⟨3253917322570237526590129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338556430093650035453505 3253917322570237526590129)
                  ·
                    refine ⟨2440437991927678144942597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3253917322570237526590129 2440437991927678144942597)
                    ·
                      refine ⟨457582123486439652176737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2440437991927678144942597 457582123486439652176737)
                      ·
                        rfl

theorem cell23_891138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_891138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891138 prefixEnd_891138 := by exact prefixLift 891138
  have htrace : WordTrace (prefixWord ++ tailWord_891138) baseStart_891138 baseEnd_891138 := by
    simpa [prefixWord, tailWord_891138, baseEnd_891138] using wordTrace_append hprefix tailTrace_891138
  have hstable : (prefixWord ++ tailWord_891138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891138).length < 2 ^ (prefixWord ++ tailWord_891138).sum := by decide
  have hdescent : baseEnd_891138 < baseStart_891138 := by decide
  rcases family_descends (prefixWord ++ tailWord_891138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891151 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 7, 2]
def baseStart_891151 : Nat := 118140960795 + 891151 * 2 ^ 59
def prefixEnd_891151 : Nat := 4983230072969 + 3 ^ 40 * 891151 * 2
def baseEnd_891151 : Nat := 457588798734948101314177

theorem tailTrace_891151 : CollatzResearch.WordTrace tailWord_891151 prefixEnd_891151 457588798734948101314177 := by
  unfold tailWord_891151
  simp only [CollatzResearch.WordTrace]
  refine ⟨32502947194519598318929307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21668631463013065545952871 32502947194519598318929307)
  ·
    refine ⟨48754420791779397478393961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32502947194519598318929307 48754420791779397478393961)
    ·
      refine ⟨36565815593834548108795471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48754420791779397478393961 36565815593834548108795471)
      ·
        refine ⟨54848723390751822163193207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36565815593834548108795471 54848723390751822163193207)
        ·
          refine ⟨82273085086127733244789811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54848723390751822163193207 82273085086127733244789811)
          ·
            refine ⟨123409627629191599867184717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82273085086127733244789811 123409627629191599867184717)
            ·
              refine ⟨46278610360946849950194269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123409627629191599867184717 46278610360946849950194269)
              ·
                refine ⟨17354478885355068731322851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46278610360946849950194269 17354478885355068731322851)
                ·
                  refine ⟨26031718328032603096984277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17354478885355068731322851 26031718328032603096984277)
                  ·
                    refine ⟨610118398313264135085569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26031718328032603096984277 610118398313264135085569)
                    ·
                      refine ⟨457588798734948101314177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610118398313264135085569 457588798734948101314177)
                      ·
                        rfl

theorem cell23_891151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7, 2].length) (baseStart_891151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891151 prefixEnd_891151 := by exact prefixLift 891151
  have htrace : WordTrace (prefixWord ++ tailWord_891151) baseStart_891151 baseEnd_891151 := by
    simpa [prefixWord, tailWord_891151, baseEnd_891151] using wordTrace_append hprefix tailTrace_891151
  have hstable : (prefixWord ++ tailWord_891151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891151).length < 2 ^ (prefixWord ++ tailWord_891151).sum := by decide
  have hdescent : baseEnd_891151 < baseStart_891151 := by decide
  rcases family_descends (prefixWord ++ tailWord_891151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891191 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 5, 4]
def baseStart_891191 : Nat := 118140960795 + 891191 * 2 ^ 59
def prefixEnd_891191 : Nat := 4983230072969 + 3 ^ 40 * 891191 * 2
def baseEnd_891191 : Nat := 152536445987042648271331

theorem tailTrace_891191 : CollatzResearch.WordTrace tailWord_891191 prefixEnd_891191 152536445987042648271331 := by
  unfold tailWord_891191
  simp only [CollatzResearch.WordTrace]
  refine ⟨32504406114374685150385427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21669604076249790100256951 32504406114374685150385427)
  ·
    refine ⟨48756609171562027725578141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32504406114374685150385427 48756609171562027725578141)
    ·
      refine ⟨18283728439335760397091803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48756609171562027725578141 18283728439335760397091803)
      ·
        refine ⟨27425592659003640595637705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283728439335760397091803 27425592659003640595637705)
        ·
          refine ⟨20569194494252730446728279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27425592659003640595637705 20569194494252730446728279)
          ·
            refine ⟨30853791741379095670092419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20569194494252730446728279 30853791741379095670092419)
            ·
              refine ⟨46280687612068643505138629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30853791741379095670092419 46280687612068643505138629)
              ·
                refine ⟨8677628927262870657213493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46280687612068643505138629 8677628927262870657213493)
                ·
                  refine ⟨813527711930894124113765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8677628927262870657213493 813527711930894124113765)
                  ·
                    refine ⟨152536445987042648271331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813527711930894124113765 152536445987042648271331)
                    ·
                      rfl

theorem cell23_891191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_891191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891191 prefixEnd_891191 := by exact prefixLift 891191
  have htrace : WordTrace (prefixWord ++ tailWord_891191) baseStart_891191 baseEnd_891191 := by
    simpa [prefixWord, tailWord_891191, baseEnd_891191] using wordTrace_append hprefix tailTrace_891191
  have hstable : (prefixWord ++ tailWord_891191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891191).length < 2 ^ (prefixWord ++ tailWord_891191).sum := by decide
  have hdescent : baseEnd_891191 < baseStart_891191 := by decide
  rcases family_descends (prefixWord ++ tailWord_891191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891198 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_891198 : Nat := 118140960795 + 891198 * 2 ^ 59
def prefixEnd_891198 : Nat := 4983230072969 + 3 ^ 40 * 891198 * 2
def baseEnd_891198 : Nat := 457612932325709417426461

theorem tailTrace_891198 : CollatzResearch.WordTrace tailWord_891198 prefixEnd_891198 457612932325709417426461 := by
  unfold tailWord_891198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063082678168665668236281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21669774283566216897260165 4063082678168665668236281)
  ·
    refine ⟨3047312008626499251177211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063082678168665668236281 3047312008626499251177211)
    ·
      refine ⟨4570968012939748876765817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047312008626499251177211 4570968012939748876765817)
      ·
        refine ⟨3428226009704811657574363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4570968012939748876765817 3428226009704811657574363)
        ·
          refine ⟨5142339014557217486361545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428226009704811657574363 5142339014557217486361545)
          ·
            refine ⟨3856754260917913114771159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142339014557217486361545 3856754260917913114771159)
            ·
              refine ⟨5785131391376869672156739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856754260917913114771159 5785131391376869672156739)
              ·
                refine ⟨8677697087065304508235109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785131391376869672156739 8677697087065304508235109)
                ·
                  refine ⟨1627068203824744595294083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8677697087065304508235109 1627068203824744595294083)
                  ·
                    refine ⟨2440602305737116892941125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627068203824744595294083 2440602305737116892941125)
                    ·
                      refine ⟨457612932325709417426461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2440602305737116892941125 457612932325709417426461)
                      ·
                        rfl

theorem cell23_891198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_891198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891198 prefixEnd_891198 := by exact prefixLift 891198
  have htrace : WordTrace (prefixWord ++ tailWord_891198) baseStart_891198 baseEnd_891198 := by
    simpa [prefixWord, tailWord_891198, baseEnd_891198] using wordTrace_append hprefix tailTrace_891198
  have hstable : (prefixWord ++ tailWord_891198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891198).length < 2 ^ (prefixWord ++ tailWord_891198).sum := by decide
  have hdescent : baseEnd_891198 < baseStart_891198 := by decide
  rcases family_descends (prefixWord ++ tailWord_891198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891208 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_891208 : Nat := 118140960795 + 891208 * 2 ^ 59
def prefixEnd_891208 : Nat := 4983230072969 + 3 ^ 40 * 891208 * 2
def baseEnd_891208 : Nat := 152539355710751459433805

theorem tailTrace_891208 : CollatzResearch.WordTrace tailWord_891208 prefixEnd_891208 152539355710751459433805 := by
  unfold tailWord_891208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252513077656548526877139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21670017436875398035836185 16252513077656548526877139)
  ·
    refine ⟨24378769616484822790315709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252513077656548526877139 24378769616484822790315709)
    ·
      refine ⟨9142038606181808546368391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24378769616484822790315709 9142038606181808546368391)
      ·
        refine ⟨13713057909272712819552587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142038606181808546368391 13713057909272712819552587)
        ·
          refine ⟨20569586863909069229328881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713057909272712819552587 20569586863909069229328881)
          ·
            refine ⟨15427190147931801921996661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20569586863909069229328881 15427190147931801921996661)
            ·
              refine ⟨1446299076368606430187187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15427190147931801921996661 1446299076368606430187187)
              ·
                refine ⟨2169448614552909645280781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446299076368606430187187 2169448614552909645280781)
                ·
                  refine ⟨813543230457341116980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2169448614552909645280781 813543230457341116980293)
                  ·
                    refine ⟨152539355710751459433805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813543230457341116980293 152539355710751459433805)
                    ·
                      rfl

theorem cell23_891208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_891208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891208 prefixEnd_891208 := by exact prefixLift 891208
  have htrace : WordTrace (prefixWord ++ tailWord_891208) baseStart_891208 baseEnd_891208 := by
    simpa [prefixWord, tailWord_891208, baseEnd_891208] using wordTrace_append hprefix tailTrace_891208
  have hstable : (prefixWord ++ tailWord_891208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891208).length < 2 ^ (prefixWord ++ tailWord_891208).sum := by decide
  have hdescent : baseEnd_891208 < baseStart_891208 := by decide
  rcases family_descends (prefixWord ++ tailWord_891208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891231 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_891231 : Nat := 118140960795 + 891231 * 2 ^ 59
def prefixEnd_891231 : Nat := 4983230072969 + 3 ^ 40 * 891231 * 2
def baseEnd_891231 : Nat := 457629877187307788313809

theorem tailTrace_891231 : CollatzResearch.WordTrace tailWord_891231 prefixEnd_891231 457629877187307788313809 := by
  unfold tailWord_891231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32505865034229771981841547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21670576689486514654561031 32505865034229771981841547)
  ·
    refine ⟨48758797551344657972762321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32505865034229771981841547 48758797551344657972762321)
    ·
      refine ⟨36569098163508493479571741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48758797551344657972762321 36569098163508493479571741)
      ·
        refine ⟨13713411811315685054839403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36569098163508493479571741 13713411811315685054839403)
        ·
          refine ⟨20570117716973527582259105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713411811315685054839403 20570117716973527582259105)
          ·
            refine ⟨15427588287730145686694329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20570117716973527582259105 15427588287730145686694329)
            ·
              refine ⟨11570691215797609265020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15427588287730145686694329 11570691215797609265020747)
              ·
                refine ⟨17356036823696413897531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570691215797609265020747 17356036823696413897531121)
                ·
                  refine ⟨13017027617772310423148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356036823696413897531121 13017027617772310423148341)
                  ·
                    refine ⟨1220346339166154102170157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017027617772310423148341 1220346339166154102170157)
                    ·
                      refine ⟨457629877187307788313809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220346339166154102170157 457629877187307788313809)
                      ·
                        rfl

theorem cell23_891231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_891231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891231 prefixEnd_891231 := by exact prefixLift 891231
  have htrace : WordTrace (prefixWord ++ tailWord_891231) baseStart_891231 baseEnd_891231 := by
    simpa [prefixWord, tailWord_891231, baseEnd_891231] using wordTrace_append hprefix tailTrace_891231
  have hstable : (prefixWord ++ tailWord_891231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891231).length < 2 ^ (prefixWord ++ tailWord_891231).sum := by decide
  have hdescent : baseEnd_891231 < baseStart_891231 := by decide
  rcases family_descends (prefixWord ++ tailWord_891231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891298 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_891298 : Nat := 118140960795 + 891298 * 2 ^ 59
def prefixEnd_891298 : Nat := 4983230072969 + 3 ^ 40 * 891298 * 2
def baseEnd_891298 : Nat := 152554760130386342058667

theorem tailTrace_891298 : CollatzResearch.WordTrace tailWord_891298 prefixEnd_891298 152554760130386342058667 := by
  unfold tailWord_891298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127077181246760606132637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21672205816658028283020365 8127077181246760606132637)
  ·
    refine ⟨3047653942967535227299739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8127077181246760606132637 3047653942967535227299739)
    ·
      refine ⟨4571480914451302840949609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047653942967535227299739 4571480914451302840949609)
      ·
        refine ⟨3428610685838477130712207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4571480914451302840949609 3428610685838477130712207)
        ·
          refine ⟨5142916028757715696068311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428610685838477130712207 5142916028757715696068311)
          ·
            refine ⟨7714374043136573544102467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142916028757715696068311 7714374043136573544102467)
            ·
              refine ⟨11571561064704860316153701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714374043136573544102467 11571561064704860316153701)
              ·
                refine ⟨2169667699632161309278819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11571561064704860316153701 2169667699632161309278819)
                ·
                  refine ⟨3254501549448241963918229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169667699632161309278819 3254501549448241963918229)
                  ·
                    refine ⟨152554760130386342058667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3254501549448241963918229 152554760130386342058667)
                    ·
                      rfl

theorem cell23_891298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_891298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891298 prefixEnd_891298 := by exact prefixLift 891298
  have htrace : WordTrace (prefixWord ++ tailWord_891298) baseStart_891298 baseEnd_891298 := by
    simpa [prefixWord, tailWord_891298, baseEnd_891298] using wordTrace_append hprefix tailTrace_891298
  have hstable : (prefixWord ++ tailWord_891298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891298).length < 2 ^ (prefixWord ++ tailWord_891298).sum := by decide
  have hdescent : baseEnd_891298 < baseStart_891298 := by decide
  rcases family_descends (prefixWord ++ tailWord_891298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891306 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_891306 : Nat := 118140960795 + 891306 * 2 ^ 59
def prefixEnd_891306 : Nat := 4983230072969 + 3 ^ 40 * 891306 * 2
def baseEnd_891306 : Nat := 50852043137377221652885

theorem tailTrace_891306 : CollatzResearch.WordTrace tailWord_891306 prefixEnd_891306 50852043137377221652885 := by
  unfold tailWord_891306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127150127239514947705443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21672400339305373193881181 8127150127239514947705443)
  ·
    refine ⟨12190725190859272421558165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8127150127239514947705443 12190725190859272421558165)
    ·
      refine ⟨571440243321528394760539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12190725190859272421558165 571440243321528394760539)
      ·
        refine ⟨857160364982292592140809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571440243321528394760539 857160364982292592140809)
        ·
          refine ⟨642870273736719444105607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857160364982292592140809 642870273736719444105607)
          ·
            refine ⟨964305410605079166158411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642870273736719444105607 964305410605079166158411)
            ·
              refine ⟨1446458115907618749237617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964305410605079166158411 1446458115907618749237617)
              ·
                refine ⟨1084843586930714061928213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446458115907618749237617 1084843586930714061928213)
                ·
                  refine ⟨50852043137377221652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1084843586930714061928213 50852043137377221652885)
                  ·
                    rfl

theorem cell23_891306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_891306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891306 prefixEnd_891306 := by exact prefixLift 891306
  have htrace : WordTrace (prefixWord ++ tailWord_891306) baseStart_891306 baseEnd_891306 := by
    simpa [prefixWord, tailWord_891306, baseEnd_891306] using wordTrace_append hprefix tailTrace_891306
  have hstable : (prefixWord ++ tailWord_891306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891306).length < 2 ^ (prefixWord ++ tailWord_891306).sum := by decide
  have hdescent : baseEnd_891306 < baseStart_891306 := by decide
  rcases family_descends (prefixWord ++ tailWord_891306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891316 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_891316 : Nat := 118140960795 + 891316 * 2 ^ 59
def prefixEnd_891316 : Nat := 4983230072969 + 3 ^ 40 * 891316 * 2
def baseEnd_891316 : Nat := 457673523042939955750919

theorem tailTrace_891316 : CollatzResearch.WordTrace tailWord_891316 prefixEnd_891316 457673523042939955750919 := by
  unfold tailWord_891316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254482619460915749342901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21672643492614554332457201 16254482619460915749342901)
  ·
    refine ⟨1523857745574460851500897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16254482619460915749342901 1523857745574460851500897)
    ·
      refine ⟨1142893309180845638625673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523857745574460851500897 1142893309180845638625673)
      ·
        refine ⟨857169981885634228969255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142893309180845638625673 857169981885634228969255)
        ·
          refine ⟨1285754972828451343453883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857169981885634228969255 1285754972828451343453883)
          ·
            refine ⟨1928632459242677015180825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285754972828451343453883 1928632459242677015180825)
            ·
              refine ⟨1446474344432007761385619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928632459242677015180825 1446474344432007761385619)
              ·
                refine ⟨2169711516648011642078429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446474344432007761385619 2169711516648011642078429)
                ·
                  refine ⟨813641818743004365779411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2169711516648011642078429 813641818743004365779411)
                  ·
                    refine ⟨1220462728114506548669117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 813641818743004365779411 1220462728114506548669117)
                    ·
                      refine ⟨457673523042939955750919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220462728114506548669117 457673523042939955750919)
                      ·
                        rfl

theorem cell23_891316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_891316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891316 prefixEnd_891316 := by exact prefixLift 891316
  have htrace : WordTrace (prefixWord ++ tailWord_891316) baseStart_891316 baseEnd_891316 := by
    simpa [prefixWord, tailWord_891316, baseEnd_891316] using wordTrace_append hprefix tailTrace_891316
  have hstable : (prefixWord ++ tailWord_891316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891316).length < 2 ^ (prefixWord ++ tailWord_891316).sum := by decide
  have hdescent : baseEnd_891316 < baseStart_891316 := by decide
  rcases family_descends (prefixWord ++ tailWord_891316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891332 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_891332 : Nat := 118140960795 + 891332 * 2 ^ 59
def prefixEnd_891332 : Nat := 4983230072969 + 3 ^ 40 * 891332 * 2
def baseEnd_891332 : Nat := 152560579577803964383615

theorem tailTrace_891332 : CollatzResearch.WordTrace tailWord_891332 prefixEnd_891332 152560579577803964383615 := by
  unfold tailWord_891332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254774403431933115634125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21673032537909244154178833 16254774403431933115634125)
  ·
    refine ⟨6095540401286974918362797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16254774403431933115634125 6095540401286974918362797)
    ·
      refine ⟨2285827650482615594386049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6095540401286974918362797 2285827650482615594386049)
      ·
        refine ⟨1714370737861961695789537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285827650482615594386049 1714370737861961695789537)
        ·
          refine ⟨1285778053396471271842153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714370737861961695789537 1285778053396471271842153)
          ·
            refine ⟨964333540047353453881615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285778053396471271842153 964333540047353453881615)
            ·
              refine ⟨1446500310071030180822423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964333540047353453881615 1446500310071030180822423)
              ·
                refine ⟨2169750465106545271233635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446500310071030180822423 2169750465106545271233635)
                ·
                  refine ⟨3254625697659817906850453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169750465106545271233635 3254625697659817906850453)
                  ·
                    refine ⟨152560579577803964383615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3254625697659817906850453 152560579577803964383615)
                    ·
                      rfl

theorem cell23_891332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_891332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891332 prefixEnd_891332 := by exact prefixLift 891332
  have htrace : WordTrace (prefixWord ++ tailWord_891332) baseStart_891332 baseEnd_891332 := by
    simpa [prefixWord, tailWord_891332, baseEnd_891332] using wordTrace_append hprefix tailTrace_891332
  have hstable : (prefixWord ++ tailWord_891332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891332).length < 2 ^ (prefixWord ++ tailWord_891332).sum := by decide
  have hdescent : baseEnd_891332 < baseStart_891332 := by decide
  rcases family_descends (prefixWord ++ tailWord_891332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891335 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_891335 : Nat := 118140960795 + 891335 * 2 ^ 59
def prefixEnd_891335 : Nat := 4983230072969 + 3 ^ 40 * 891335 * 2
def baseEnd_891335 : Nat := 457683279175375381413331

theorem tailTrace_891335 : CollatzResearch.WordTrace tailWord_891335 prefixEnd_891335 457683279175375381413331 := by
  unfold tailWord_891335
  simp only [CollatzResearch.WordTrace]
  refine ⟨32509658225852997743627459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21673105483901998495751639 32509658225852997743627459)
  ·
    refine ⟨48764487338779496615441189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32509658225852997743627459 48764487338779496615441189)
    ·
      refine ⟨9143341376021155615395223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48764487338779496615441189 9143341376021155615395223)
      ·
        refine ⟨13715012064031733423092835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9143341376021155615395223 13715012064031733423092835)
        ·
          refine ⟨20572518096047600134639253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13715012064031733423092835 20572518096047600134639253)
          ·
            refine ⟨964336785752231256311215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20572518096047600134639253 964336785752231256311215)
            ·
              refine ⟨1446505178628346884466823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964336785752231256311215 1446505178628346884466823)
              ·
                refine ⟨2169757767942520326700235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446505178628346884466823 2169757767942520326700235)
                ·
                  refine ⟨3254636651913780490050353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169757767942520326700235 3254636651913780490050353)
                  ·
                    refine ⟨2440977488935335367537765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254636651913780490050353 2440977488935335367537765)
                    ·
                      refine ⟨457683279175375381413331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2440977488935335367537765 457683279175375381413331)
                      ·
                        rfl

theorem cell23_891335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_891335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891335 prefixEnd_891335 := by exact prefixLift 891335
  have htrace : WordTrace (prefixWord ++ tailWord_891335) baseStart_891335 baseEnd_891335 := by
    simpa [prefixWord, tailWord_891335, baseEnd_891335] using wordTrace_append hprefix tailTrace_891335
  have hstable : (prefixWord ++ tailWord_891335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891335).length < 2 ^ (prefixWord ++ tailWord_891335).sum := by decide
  have hdescent : baseEnd_891335 < baseStart_891335 := by decide
  rcases family_descends (prefixWord ++ tailWord_891335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891362 : List Nat := [3, 3, 3, 2, 1, 2, 9]
def baseStart_891362 : Nat := 118140960795 + 891362 * 2 ^ 59
def prefixEnd_891362 : Nat := 4983230072969 + 3 ^ 40 * 891362 * 2
def baseEnd_891362 : Nat := 5650582014235145379947

theorem tailTrace_891362 : CollatzResearch.WordTrace tailWord_891362 prefixEnd_891362 5650582014235145379947 := by
  unfold tailWord_891362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127660749188795338715085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21673761997836787569906893 8127660749188795338715085)
  ·
    refine ⟨3047872780945798252018157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8127660749188795338715085 3047872780945798252018157)
    ·
      refine ⟨1142952292854674344506809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3047872780945798252018157 1142952292854674344506809)
      ·
        refine ⟨857214219641005758380107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142952292854674344506809 857214219641005758380107)
        ·
          refine ⟨1285821329461508637570161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857214219641005758380107 1285821329461508637570161)
          ·
            refine ⟨964365997096131478177621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285821329461508637570161 964365997096131478177621)
            ·
              refine ⟨5650582014235145379947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 964365997096131478177621 5650582014235145379947)
              ·
                rfl

theorem cell23_891362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 9].length) (baseStart_891362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891362 prefixEnd_891362 := by exact prefixLift 891362
  have htrace : WordTrace (prefixWord ++ tailWord_891362) baseStart_891362 baseEnd_891362 := by
    simpa [prefixWord, tailWord_891362, baseEnd_891362] using wordTrace_append hprefix tailTrace_891362
  have hstable : (prefixWord ++ tailWord_891362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891362).length < 2 ^ (prefixWord ++ tailWord_891362).sum := by decide
  have hdescent : baseEnd_891362 < baseStart_891362 := by decide
  rcases family_descends (prefixWord ++ tailWord_891362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891373 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_891373 : Nat := 118140960795 + 891373 * 2 ^ 59
def prefixEnd_891373 : Nat := 4983230072969 + 3 ^ 40 * 891373 * 2
def baseEnd_891373 : Nat := 457702791440246232738157

theorem tailTrace_891373 : CollatzResearch.WordTrace tailWord_891373 prefixEnd_891373 457702791440246232738157 := by
  unfold tailWord_891373
  simp only [CollatzResearch.WordTrace]
  refine ⟨32511044199715330233510773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21674029466476886822340515 32511044199715330233510773)
  ·
    refine ⟨3047910393723312209391635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32511044199715330233510773 3047910393723312209391635)
    ·
      refine ⟨4571865590584968314087453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047910393723312209391635 4571865590584968314087453)
      ·
        refine ⟨1714449596469363117782795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4571865590584968314087453 1714449596469363117782795)
        ·
          refine ⟨2571674394704044676674193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714449596469363117782795 2571674394704044676674193)
          ·
            refine ⟨1928755796028033507505645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571674394704044676674193 1928755796028033507505645)
            ·
              refine ⟨723283423510512565314617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928755796028033507505645 723283423510512565314617)
              ·
                refine ⟨542462567632884423985963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723283423510512565314617 542462567632884423985963)
                ·
                  refine ⟨813693851449326635978945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542462567632884423985963 813693851449326635978945)
                  ·
                    refine ⟨610270388586994976984209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813693851449326635978945 610270388586994976984209)
                    ·
                      refine ⟨457702791440246232738157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610270388586994976984209 457702791440246232738157)
                      ·
                        rfl

theorem cell23_891373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_891373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891373 prefixEnd_891373 := by exact prefixLift 891373
  have htrace : WordTrace (prefixWord ++ tailWord_891373) baseStart_891373 baseEnd_891373 := by
    simpa [prefixWord, tailWord_891373, baseEnd_891373] using wordTrace_append hprefix tailTrace_891373
  have hstable : (prefixWord ++ tailWord_891373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891373).length < 2 ^ (prefixWord ++ tailWord_891373).sum := by decide
  have hdescent : baseEnd_891373 < baseStart_891373 := by decide
  rcases family_descends (prefixWord ++ tailWord_891373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891382 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_891382 : Nat := 118140960795 + 891382 * 2 ^ 59
def prefixEnd_891382 : Nat := 4983230072969 + 3 ^ 40 * 891382 * 2
def baseEnd_891382 : Nat := 457707412766136697525615

theorem tailTrace_891382 : CollatzResearch.WordTrace tailWord_891382 prefixEnd_891382 457707412766136697525615 := by
  unfold tailWord_891382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031960778542670298161775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21674248304455149847058933 2031960778542670298161775)
  ·
    refine ⟨3047941167814005447242663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031960778542670298161775 3047941167814005447242663)
    ·
      refine ⟨4571911751721008170863995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047941167814005447242663 4571911751721008170863995)
      ·
        refine ⟨6857867627581512256295993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571911751721008170863995 6857867627581512256295993)
        ·
          refine ⟨5143400720686134192221995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857867627581512256295993 5143400720686134192221995)
          ·
            refine ⟨7715101081029201288332993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143400720686134192221995 7715101081029201288332993)
            ·
              refine ⟨5786325810771900966249745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715101081029201288332993 5786325810771900966249745)
              ·
                refine ⟨4339744358078925724687309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786325810771900966249745 4339744358078925724687309)
                ·
                  refine ⟨1627404134279597146757741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4339744358078925724687309 1627404134279597146757741)
                  ·
                    refine ⟨610276550354848930034153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627404134279597146757741 610276550354848930034153)
                    ·
                      refine ⟨457707412766136697525615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610276550354848930034153 457707412766136697525615)
                      ·
                        rfl

theorem cell23_891382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_891382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891382 prefixEnd_891382 := by exact prefixLift 891382
  have htrace : WordTrace (prefixWord ++ tailWord_891382) baseStart_891382 baseEnd_891382 := by
    simpa [prefixWord, tailWord_891382, baseEnd_891382] using wordTrace_append hprefix tailTrace_891382
  have hstable : (prefixWord ++ tailWord_891382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891382).length < 2 ^ (prefixWord ++ tailWord_891382).sum := by decide
  have hdescent : baseEnd_891382 < baseStart_891382 := by decide
  rcases family_descends (prefixWord ++ tailWord_891382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891395 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 4, 2]
def baseStart_891395 : Nat := 118140960795 + 891395 * 2 ^ 59
def prefixEnd_891395 : Nat := 4983230072969 + 3 ^ 40 * 891395 * 2
def baseEnd_891395 : Nat := 457714088014645146663055

theorem tailTrace_891395 : CollatzResearch.WordTrace tailWord_891395 prefixEnd_891395 457714088014645146663055 := by
  unfold tailWord_891395
  simp only [CollatzResearch.WordTrace]
  refine ⟨32511846605635627990811639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21674564403757085327207759 32511846605635627990811639)
  ·
    refine ⟨48767769908453441986217459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32511846605635627990811639 48767769908453441986217459)
    ·
      refine ⟨73151654862680162979326189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48767769908453441986217459 73151654862680162979326189)
      ·
        refine ⟨27431870573505061117247321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73151654862680162979326189 27431870573505061117247321)
        ·
          refine ⟨20573902930128795837935491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27431870573505061117247321 20573902930128795837935491)
          ·
            refine ⟨30860854395193193756903237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20573902930128795837935491 30860854395193193756903237)
            ·
              refine ⟨5786410199098723829419357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30860854395193193756903237 5786410199098723829419357)
              ·
                refine ⟨2169903824662021436032259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5786410199098723829419357 2169903824662021436032259)
                ·
                  refine ⟨3254855736993032154048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169903824662021436032259 3254855736993032154048389)
                  ·
                    refine ⟨610285450686193528884073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3254855736993032154048389 610285450686193528884073)
                    ·
                      refine ⟨457714088014645146663055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610285450686193528884073 457714088014645146663055)
                      ·
                        rfl

theorem cell23_891395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_891395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891395 prefixEnd_891395 := by exact prefixLift 891395
  have htrace : WordTrace (prefixWord ++ tailWord_891395) baseStart_891395 baseEnd_891395 := by
    simpa [prefixWord, tailWord_891395, baseEnd_891395] using wordTrace_append hprefix tailTrace_891395
  have hstable : (prefixWord ++ tailWord_891395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891395).length < 2 ^ (prefixWord ++ tailWord_891395).sum := by decide
  have hdescent : baseEnd_891395 < baseStart_891395 := by decide
  rcases family_descends (prefixWord ++ tailWord_891395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891445 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_891445 : Nat := 118140960795 + 891445 * 2 ^ 59
def prefixEnd_891445 : Nat := 4983230072969 + 3 ^ 40 * 891445 * 2
def baseEnd_891445 : Nat := 457739762047369951037825

theorem tailTrace_891445 : CollatzResearch.WordTrace tailWord_891445 prefixEnd_891445 457739762047369951037825 := by
  unfold tailWord_891445
  simp only [CollatzResearch.WordTrace]
  refine ⟨32513670255454486530131789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21675780170302991020087859 32513670255454486530131789)
  ·
    refine ⟨12192626345795432448799421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32513670255454486530131789 12192626345795432448799421)
    ·
      refine ⟨4572234879673287168299783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12192626345795432448799421 4572234879673287168299783)
      ·
        refine ⟨6858352319509930752449675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572234879673287168299783 6858352319509930752449675)
        ·
          refine ⟨10287528479264896128674513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858352319509930752449675 10287528479264896128674513)
          ·
            refine ⟨7715646359448672096505885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10287528479264896128674513 7715646359448672096505885)
            ·
              refine ⟨2893367384793252036189707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7715646359448672096505885 2893367384793252036189707)
              ·
                refine ⟨4340051077189878054284561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893367384793252036189707 4340051077189878054284561)
                ·
                  refine ⟨3255038307892408540713421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340051077189878054284561 3255038307892408540713421)
                  ·
                    refine ⟨1220639365459653202767533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255038307892408540713421 1220639365459653202767533)
                    ·
                      refine ⟨457739762047369951037825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220639365459653202767533 457739762047369951037825)
                      ·
                        rfl

theorem cell23_891445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_891445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891445 prefixEnd_891445 := by exact prefixLift 891445
  have htrace : WordTrace (prefixWord ++ tailWord_891445) baseStart_891445 baseEnd_891445 := by
    simpa [prefixWord, tailWord_891445, baseEnd_891445] using wordTrace_append hprefix tailTrace_891445
  have hstable : (prefixWord ++ tailWord_891445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891445).length < 2 ^ (prefixWord ++ tailWord_891445).sum := by decide
  have hdescent : baseEnd_891445 < baseStart_891445 := by decide
  rcases family_descends (prefixWord ++ tailWord_891445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891446 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_891446 : Nat := 118140960795 + 891446 * 2 ^ 59
def prefixEnd_891446 : Nat := 4983230072969 + 3 ^ 40 * 891446 * 2
def baseEnd_891446 : Nat := 457740275528024447125321

theorem tailTrace_891446 : CollatzResearch.WordTrace tailWord_891446 prefixEnd_891446 457740275528024447125321 := by
  unfold tailWord_891446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032106670528178981307387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21675804485633909133945461 2032106670528178981307387)
  ·
    refine ⟨3048160005792268471961081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032106670528178981307387 3048160005792268471961081)
    ·
      refine ⟨2286120004344201353970811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3048160005792268471961081 2286120004344201353970811)
      ·
        refine ⟨3429180006516302030956217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286120004344201353970811 3429180006516302030956217)
        ·
          refine ⟨2571885004887226523217163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429180006516302030956217 2571885004887226523217163)
          ·
            refine ⟨3857827507330839784825745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571885004887226523217163 3857827507330839784825745)
            ·
              refine ⟨2893370630498129838619309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857827507330839784825745 2893370630498129838619309)
              ·
                refine ⟨1085013986436798689482241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2893370630498129838619309 1085013986436798689482241)
                ·
                  refine ⟨813760489827599017111681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085013986436798689482241 813760489827599017111681)
                  ·
                    refine ⟨610320367370699262833761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813760489827599017111681 610320367370699262833761)
                    ·
                      refine ⟨457740275528024447125321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610320367370699262833761 457740275528024447125321)
                      ·
                        rfl

theorem cell23_891446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_891446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891446 prefixEnd_891446 := by exact prefixLift 891446
  have htrace : WordTrace (prefixWord ++ tailWord_891446) baseStart_891446 baseEnd_891446 := by
    simpa [prefixWord, tailWord_891446, baseEnd_891446] using wordTrace_append hprefix tailTrace_891446
  have hstable : (prefixWord ++ tailWord_891446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891446).length < 2 ^ (prefixWord ++ tailWord_891446).sum := by decide
  have hdescent : baseEnd_891446 < baseStart_891446 := by decide
  rcases family_descends (prefixWord ++ tailWord_891446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891448 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_891448 : Nat := 118140960795 + 891448 * 2 ^ 59
def prefixEnd_891448 : Nat := 4983230072969 + 3 ^ 40 * 891448 * 2
def baseEnd_891448 : Nat := 152580434163111146433437

theorem tailTrace_891448 : CollatzResearch.WordTrace tailWord_891448 prefixEnd_891448 152580434163111146433437 := by
  unfold tailWord_891448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16256889837221809021245499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21675853116295745361660665 16256889837221809021245499)
  ·
    refine ⟨24385334755832713531868249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16256889837221809021245499 24385334755832713531868249)
    ·
      refine ⟨18289001066874535148901187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24385334755832713531868249 18289001066874535148901187)
      ·
        refine ⟨27433501600311802723351781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18289001066874535148901187 27433501600311802723351781)
        ·
          refine ⟨5143781550058463010628459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27433501600311802723351781 5143781550058463010628459)
          ·
            refine ⟨7715672325087694515942689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143781550058463010628459 7715672325087694515942689)
            ·
              refine ⟨5786754243815770886957017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715672325087694515942689 5786754243815770886957017)
              ·
                refine ⟨4340065682861828165217763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786754243815770886957017 4340065682861828165217763)
                ·
                  refine ⟨6510098524292742247826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340065682861828165217763 6510098524292742247826645)
                  ·
                    refine ⟨152580434163111146433437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6510098524292742247826645 152580434163111146433437)
                    ·
                      rfl

theorem cell23_891448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_891448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891448 prefixEnd_891448 := by exact prefixLift 891448
  have htrace : WordTrace (prefixWord ++ tailWord_891448) baseStart_891448 baseEnd_891448 := by
    simpa [prefixWord, tailWord_891448, baseEnd_891448] using wordTrace_append hprefix tailTrace_891448
  have hstable : (prefixWord ++ tailWord_891448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891448).length < 2 ^ (prefixWord ++ tailWord_891448).sum := by decide
  have hdescent : baseEnd_891448 < baseStart_891448 := by decide
  rcases family_descends (prefixWord ++ tailWord_891448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891455 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 5, 2]
def baseStart_891455 : Nat := 118140960795 + 891455 * 2 ^ 59
def prefixEnd_891455 : Nat := 4983230072969 + 3 ^ 40 * 891455 * 2
def baseEnd_891455 : Nat := 457744896853914911912779

theorem tailTrace_891455 : CollatzResearch.WordTrace tailWord_891455 prefixEnd_891455 457744896853914911912779 := by
  unfold tailWord_891455
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514034985418258237995819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21676023323612172158663879 32514034985418258237995819)
  ·
    refine ⟨48771052478127387356993729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514034985418258237995819 48771052478127387356993729)
    ·
      refine ⟨36578289358595540517745297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48771052478127387356993729 36578289358595540517745297)
      ·
        refine ⟨27433717018946655388308973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36578289358595540517745297 27433717018946655388308973)
        ·
          refine ⟨10287643882104995770615865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27433717018946655388308973 10287643882104995770615865)
          ·
            refine ⟨7715732911578746827961899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10287643882104995770615865 7715732911578746827961899)
            ·
              refine ⟨11573599367368120241942849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715732911578746827961899 11573599367368120241942849)
              ·
                refine ⟨8680199525526090181457137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11573599367368120241942849 8680199525526090181457137)
                ·
                  refine ⟨6510149644144567636092853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680199525526090181457137 6510149644144567636092853)
                  ·
                    refine ⟨610326529138553215883705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6510149644144567636092853 610326529138553215883705)
                    ·
                      refine ⟨457744896853914911912779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610326529138553215883705 457744896853914911912779)
                      ·
                        rfl

theorem cell23_891455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_891455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891455 prefixEnd_891455 := by exact prefixLift 891455
  have htrace : WordTrace (prefixWord ++ tailWord_891455) baseStart_891455 baseEnd_891455 := by
    simpa [prefixWord, tailWord_891455, baseEnd_891455] using wordTrace_append hprefix tailTrace_891455
  have hstable : (prefixWord ++ tailWord_891455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891455).length < 2 ^ (prefixWord ++ tailWord_891455).sum := by decide
  have hdescent : baseEnd_891455 < baseStart_891455 := by decide
  rcases family_descends (prefixWord ++ tailWord_891455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891469 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 5]
def baseStart_891469 : Nat := 118140960795 + 891469 * 2 ^ 59
def prefixEnd_891469 : Nat := 4983230072969 + 3 ^ 40 * 891469 * 2
def baseEnd_891469 : Nat := 50861342842564206348635

theorem tailTrace_891469 : CollatzResearch.WordTrace tailWord_891469 prefixEnd_891469 50861342842564206348635 := by
  unfold tailWord_891469
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514545607367538629005461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21676363738245025752670307 32514545607367538629005461)
  ·
    refine ⟨1524119325345353373234631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32514545607367538629005461 1524119325345353373234631)
    ·
      refine ⟨2286178988018030059851947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524119325345353373234631 2286178988018030059851947)
      ·
        refine ⟨3429268482027045089777921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286178988018030059851947 3429268482027045089777921)
        ·
          refine ⟨2571951361520283817333441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429268482027045089777921 2571951361520283817333441)
          ·
            refine ⟨1928963521140212863000081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571951361520283817333441 1928963521140212863000081)
            ·
              refine ⟨1446722640855159647250061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928963521140212863000081 1446722640855159647250061)
              ·
                refine ⟨542520990320684867718773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1446722640855159647250061 542520990320684867718773)
                ·
                  refine ⟨50861342842564206348635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542520990320684867718773 50861342842564206348635)
                  ·
                    rfl

theorem cell23_891469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_891469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891469 prefixEnd_891469 := by exact prefixLift 891469
  have htrace : WordTrace (prefixWord ++ tailWord_891469) baseStart_891469 baseEnd_891469 := by
    simpa [prefixWord, tailWord_891469, baseEnd_891469] using wordTrace_append hprefix tailTrace_891469
  have hstable : (prefixWord ++ tailWord_891469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891469).length < 2 ^ (prefixWord ++ tailWord_891469).sum := by decide
  have hdescent : baseEnd_891469 < baseStart_891469 := by decide
  rcases family_descends (prefixWord ++ tailWord_891469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891486 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_891486 : Nat := 118140960795 + 891486 * 2 ^ 59
def prefixEnd_891486 : Nat := 4983230072969 + 3 ^ 40 * 891486 * 2
def baseEnd_891486 : Nat := 50862312750467143402793

theorem tailTrace_891486 : CollatzResearch.WordTrace tailWord_891486 prefixEnd_891486 50862312750467143402793 := by
  unfold tailWord_891486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064395706038243816546789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21676777098870633688249541 4064395706038243816546789)
  ·
    refine ⟨762074194882170715602523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4064395706038243816546789 762074194882170715602523)
    ·
      refine ⟨1143111292323256073403785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762074194882170715602523 1143111292323256073403785)
      ·
        refine ⟨857333469242442055052839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143111292323256073403785 857333469242442055052839)
        ·
          refine ⟨1286000203863663082579259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857333469242442055052839 1286000203863663082579259)
          ·
            refine ⟨1929000305795494623868889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286000203863663082579259 1929000305795494623868889)
            ·
              refine ⟨1446750229346620967901667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929000305795494623868889 1446750229346620967901667)
              ·
                refine ⟨2170125344019931451852501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446750229346620967901667 2170125344019931451852501)
                ·
                  refine ⟨50862312750467143402793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2170125344019931451852501 50862312750467143402793)
                  ·
                    rfl

theorem cell23_891486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_891486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891486 prefixEnd_891486 := by exact prefixLift 891486
  have htrace : WordTrace (prefixWord ++ tailWord_891486) baseStart_891486 baseEnd_891486 := by
    simpa [prefixWord, tailWord_891486, baseEnd_891486] using wordTrace_append hprefix tailTrace_891486
  have hstable : (prefixWord ++ tailWord_891486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891486).length < 2 ^ (prefixWord ++ tailWord_891486).sum := by decide
  have hdescent : baseEnd_891486 < baseStart_891486 := by decide
  rcases family_descends (prefixWord ++ tailWord_891486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891488 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_891488 : Nat := 118140960795 + 891488 * 2 ^ 59
def prefixEnd_891488 : Nat := 4983230072969 + 3 ^ 40 * 891488 * 2
def baseEnd_891488 : Nat := 457761841715513282800127

theorem tailTrace_891488 : CollatzResearch.WordTrace tailWord_891488 prefixEnd_891488 457761841715513282800127 := by
  unfold tailWord_891488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257619297149352436973559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21676825729532469915964745 16257619297149352436973559)
  ·
    refine ⟨24386428945724028655460339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16257619297149352436973559 24386428945724028655460339)
    ·
      refine ⟨36579643418586042983190509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24386428945724028655460339 36579643418586042983190509)
      ·
        refine ⟨13717366281969766118696441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36579643418586042983190509 13717366281969766118696441)
        ·
          refine ⟨10288024711477324589022331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13717366281969766118696441 10288024711477324589022331)
          ·
            refine ⟨15432037067215986883533497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10288024711477324589022331 15432037067215986883533497)
            ·
              refine ⟨11574027800411990162650123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15432037067215986883533497 11574027800411990162650123)
              ·
                refine ⟨17361041700617985243975185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11574027800411990162650123 17361041700617985243975185)
                ·
                  refine ⟨13020781275463488932981389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17361041700617985243975185 13020781275463488932981389)
                  ·
                    refine ⟨4882792978298808349868021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13020781275463488932981389 4882792978298808349868021)
                    ·
                      refine ⟨457761841715513282800127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4882792978298808349868021 457761841715513282800127)
                      ·
                        rfl

theorem cell23_891488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_891488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891488 prefixEnd_891488 := by exact prefixLift 891488
  have htrace : WordTrace (prefixWord ++ tailWord_891488) baseStart_891488 baseEnd_891488 := by
    simpa [prefixWord, tailWord_891488, baseEnd_891488] using wordTrace_append hprefix tailTrace_891488
  have hstable : (prefixWord ++ tailWord_891488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891488).length < 2 ^ (prefixWord ++ tailWord_891488).sum := by decide
  have hdescent : baseEnd_891488 < baseStart_891488 := by decide
  rcases family_descends (prefixWord ++ tailWord_891488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891546 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_891546 : Nat := 118140960795 + 891546 * 2 ^ 59
def prefixEnd_891546 : Nat := 4983230072969 + 3 ^ 40 * 891546 * 2
def baseEnd_891546 : Nat := 152597207864491351958287

theorem tailTrace_891546 : CollatzResearch.WordTrace tailWord_891546 prefixEnd_891546 152597207864491351958287 := by
  unfold tailWord_891546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8129338507022145194889623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21678236018725720519705661 8129338507022145194889623)
  ·
    refine ⟨12194007760533217792334435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8129338507022145194889623 12194007760533217792334435)
    ·
      refine ⟨18291011640799826688501653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194007760533217792334435 18291011640799826688501653)
      ·
        refine ⟨857391170662491876023515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18291011640799826688501653 857391170662491876023515)
        ·
          refine ⟨1286086755993737814035273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857391170662491876023515 1286086755993737814035273)
          ·
            refine ⟨964565066995303360526455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286086755993737814035273 964565066995303360526455)
            ·
              refine ⟨1446847600492955040789683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964565066995303360526455 1446847600492955040789683)
              ·
                refine ⟨2170271400739432561184525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446847600492955040789683 2170271400739432561184525)
                ·
                  refine ⟨813851775277287210444197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2170271400739432561184525 813851775277287210444197)
                  ·
                    refine ⟨152597207864491351958287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813851775277287210444197 152597207864491351958287)
                    ·
                      rfl

theorem cell23_891546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_891546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891546 prefixEnd_891546 := by exact prefixLift 891546
  have htrace : WordTrace (prefixWord ++ tailWord_891546) baseStart_891546 baseEnd_891546 := by
    simpa [prefixWord, tailWord_891546, baseEnd_891546] using wordTrace_append hprefix tailTrace_891546
  have hstable : (prefixWord ++ tailWord_891546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891546).length < 2 ^ (prefixWord ++ tailWord_891546).sum := by decide
  have hdescent : baseEnd_891546 < baseStart_891546 := by decide
  rcases family_descends (prefixWord ++ tailWord_891546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891559 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 6]
def baseStart_891559 : Nat := 118140960795 + 891559 * 2 ^ 59
def prefixEnd_891559 : Nat := 4983230072969 + 3 ^ 40 * 891559 * 2
def baseEnd_891559 : Nat := 50866477649109167223589

theorem tailTrace_891559 : CollatzResearch.WordTrace tailWord_891559 prefixEnd_891559 50866477649109167223589 := by
  unfold tailWord_891559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517828177041483999781731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21678552118027655999854487 32517828177041483999781731)
  ·
    refine ⟨48776742265562225999672597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32517828177041483999781731 48776742265562225999672597)
    ·
      refine ⟨2286409793698229343734653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48776742265562225999672597 2286409793698229343734653)
      ·
        refine ⟨857403672636836003900495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2286409793698229343734653 857403672636836003900495)
        ·
          refine ⟨1286105508955254005850743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857403672636836003900495 1286105508955254005850743)
          ·
            refine ⟨1929158263432881008776115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286105508955254005850743 1929158263432881008776115)
            ·
              refine ⟨2893737395149321513164173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929158263432881008776115 2893737395149321513164173)
              ·
                refine ⟨1085151523180995567436565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2893737395149321513164173 1085151523180995567436565)
                ·
                  refine ⟨50866477649109167223589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1085151523180995567436565 50866477649109167223589)
                  ·
                    rfl

theorem cell23_891559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 6].length) (baseStart_891559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891559 prefixEnd_891559 := by exact prefixLift 891559
  have htrace : WordTrace (prefixWord ++ tailWord_891559) baseStart_891559 baseEnd_891559 := by
    simpa [prefixWord, tailWord_891559, baseEnd_891559] using wordTrace_append hprefix tailTrace_891559
  have hstable : (prefixWord ++ tailWord_891559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891559).length < 2 ^ (prefixWord ++ tailWord_891559).sum := by decide
  have hdescent : baseEnd_891559 < baseStart_891559 := by decide
  rcases family_descends (prefixWord ++ tailWord_891559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891597 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_891597 : Nat := 118140960795 + 891597 * 2 ^ 59
def prefixEnd_891597 : Nat := 4983230072969 + 3 ^ 40 * 891597 * 2
def baseEnd_891597 : Nat := 152605937035617785445709

theorem tailTrace_891597 : CollatzResearch.WordTrace tailWord_891597 prefixEnd_891597 152605937035617785445709 := by
  unfold tailWord_891597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519214150903816489665045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21679476100602544326443363 32519214150903816489665045)
  ·
    refine ⟨1524338163323616397953049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32519214150903816489665045 1524338163323616397953049)
    ·
      refine ⟨1143253622492712298464787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524338163323616397953049 1143253622492712298464787)
      ·
        refine ⟨1714880433739068447697181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143253622492712298464787 1714880433739068447697181)
        ·
          refine ⟨643080162652150667886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1714880433739068447697181 643080162652150667886443)
          ·
            refine ⟨964620243978226001829665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643080162652150667886443 964620243978226001829665)
            ·
              refine ⟨723465182983669501372249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964620243978226001829665 723465182983669501372249)
              ·
                refine ⟨542598887237752126029187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723465182983669501372249 542598887237752126029187)
                ·
                  refine ⟨813898330856628189043781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542598887237752126029187 813898330856628189043781)
                  ·
                    refine ⟨152605937035617785445709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813898330856628189043781 152605937035617785445709)
                    ·
                      rfl

theorem cell23_891597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_891597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891597 prefixEnd_891597 := by exact prefixLift 891597
  have htrace : WordTrace (prefixWord ++ tailWord_891597) baseStart_891597 baseEnd_891597 := by
    simpa [prefixWord, tailWord_891597, baseEnd_891597] using wordTrace_append hprefix tailTrace_891597
  have hstable : (prefixWord ++ tailWord_891597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891597).length < 2 ^ (prefixWord ++ tailWord_891597).sum := by decide
  have hdescent : baseEnd_891597 < baseStart_891597 := by decide
  rcases family_descends (prefixWord ++ tailWord_891597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891609 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 3, 2, 2]
def baseStart_891609 : Nat := 118140960795 + 891609 * 2 ^ 59
def prefixEnd_891609 : Nat := 4983230072969 + 3 ^ 40 * 891609 * 2
def baseEnd_891609 : Nat := 457823972874707309387071

theorem tailTrace_891609 : CollatzResearch.WordTrace tailWord_891609 prefixEnd_891609 457823972874707309387071 := by
  unfold tailWord_891609
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519651826860342539101881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21679767884573561692734587 32519651826860342539101881)
  ·
    refine ⟨24389738870145256904326411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32519651826860342539101881 24389738870145256904326411)
    ·
      refine ⟨36584608305217885356489617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24389738870145256904326411 36584608305217885356489617)
      ·
        refine ⟨27438456228913414017367213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36584608305217885356489617 27438456228913414017367213)
        ·
          refine ⟨10289421085842530256512705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27438456228913414017367213 10289421085842530256512705)
          ·
            refine ⟨7717065814381897692384529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289421085842530256512705 7717065814381897692384529)
            ·
              refine ⟨5787799360786423269288397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717065814381897692384529 5787799360786423269288397)
              ·
                refine ⟨2170424760294908725983149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5787799360786423269288397 2170424760294908725983149)
                ·
                  refine ⟨813909285110590772243681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2170424760294908725983149 813909285110590772243681)
                  ·
                    refine ⟨610431963832943079182761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 813909285110590772243681 610431963832943079182761)
                    ·
                      refine ⟨457823972874707309387071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610431963832943079182761 457823972874707309387071)
                      ·
                        rfl

theorem cell23_891609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_891609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891609 prefixEnd_891609 := by exact prefixLift 891609
  have htrace : WordTrace (prefixWord ++ tailWord_891609) baseStart_891609 baseEnd_891609 := by
    simpa [prefixWord, tailWord_891609, baseEnd_891609] using wordTrace_append hprefix tailTrace_891609
  have hstable : (prefixWord ++ tailWord_891609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891609).length < 2 ^ (prefixWord ++ tailWord_891609).sum := by decide
  have hdescent : baseEnd_891609 < baseStart_891609 := by decide
  rcases family_descends (prefixWord ++ tailWord_891609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891615 : List Nat := [1, 1, 2, 3, 2, 3, 3, 8]
def baseStart_891615 : Nat := 118140960795 + 891615 * 2 ^ 59
def prefixEnd_891615 : Nat := 4983230072969 + 3 ^ 40 * 891615 * 2
def baseEnd_891615 : Nat := 16956557546616084663409

theorem tailTrace_891615 : CollatzResearch.WordTrace tailWord_891615 prefixEnd_891615 16956557546616084663409 := by
  unfold tailWord_891615
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519870664838605563820299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21679913776559070375880199 32519870664838605563820299)
  ·
    refine ⟨48779805997257908345730449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32519870664838605563820299 48779805997257908345730449)
    ·
      refine ⟨36584854497943431259297837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48779805997257908345730449 36584854497943431259297837)
      ·
        refine ⟨13719320436728786722236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36584854497943431259297837 13719320436728786722236689)
        ·
          refine ⟨10289490327546590041677517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719320436728786722236689 10289490327546590041677517)
          ·
            refine ⟨3858558872829971265629069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10289490327546590041677517 3858558872829971265629069)
            ·
              refine ⟨1446959577311239224610901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3858558872829971265629069 1446959577311239224610901)
              ·
                refine ⟨16956557546616084663409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1446959577311239224610901 16956557546616084663409)
                ·
                  rfl

theorem cell23_891615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 8].length) (baseStart_891615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891615 prefixEnd_891615 := by exact prefixLift 891615
  have htrace : WordTrace (prefixWord ++ tailWord_891615) baseStart_891615 baseEnd_891615 := by
    simpa [prefixWord, tailWord_891615, baseEnd_891615] using wordTrace_append hprefix tailTrace_891615
  have hstable : (prefixWord ++ tailWord_891615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891615).length < 2 ^ (prefixWord ++ tailWord_891615).sum := by decide
  have hdescent : baseEnd_891615 < baseStart_891615 := by decide
  rcases family_descends (prefixWord ++ tailWord_891615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891619 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 2, 4]
def baseStart_891619 : Nat := 118140960795 + 891619 * 2 ^ 59
def prefixEnd_891619 : Nat := 4983230072969 + 3 ^ 40 * 891619 * 2
def baseEnd_891619 : Nat := 152609702560417423420675

theorem tailTrace_891619 : CollatzResearch.WordTrace tailWord_891619 prefixEnd_891619 152609702560417423420675 := by
  unfold tailWord_891619
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520016556824114246965911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21680011037882742831310607 32520016556824114246965911)
  ·
    refine ⟨48780024835236171370448867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32520016556824114246965911 48780024835236171370448867)
    ·
      refine ⟨73170037252854257055673301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48780024835236171370448867 73170037252854257055673301)
      ·
        refine ⟨1714922748113771649742343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73170037252854257055673301 1714922748113771649742343)
        ·
          refine ⟨2572384122170657474613515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714922748113771649742343 2572384122170657474613515)
          ·
            refine ⟨3858576183255986211920273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572384122170657474613515 3858576183255986211920273)
            ·
              refine ⟨2893932137441989658940205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858576183255986211920273 2893932137441989658940205)
              ·
                refine ⟨1085224551540746122102577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2893932137441989658940205 1085224551540746122102577)
                ·
                  refine ⟨813918413655559591576933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085224551540746122102577 813918413655559591576933)
                  ·
                    refine ⟨152609702560417423420675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813918413655559591576933 152609702560417423420675)
                    ·
                      rfl

theorem cell23_891619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 4].length) (baseStart_891619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891619 prefixEnd_891619 := by exact prefixLift 891619
  have htrace : WordTrace (prefixWord ++ tailWord_891619) baseStart_891619 baseEnd_891619 := by
    simpa [prefixWord, tailWord_891619, baseEnd_891619] using wordTrace_append hprefix tailTrace_891619
  have hstable : (prefixWord ++ tailWord_891619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891619).length < 2 ^ (prefixWord ++ tailWord_891619).sum := by decide
  have hdescent : baseEnd_891619 < baseStart_891619 := by decide
  rcases family_descends (prefixWord ++ tailWord_891619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891629 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_891629 : Nat := 118140960795 + 891629 * 2 ^ 59
def prefixEnd_891629 : Nat := 4983230072969 + 3 ^ 40 * 891629 * 2
def baseEnd_891629 : Nat := 457834242487797231136979

theorem tailTrace_891629 : CollatzResearch.WordTrace tailWord_891629 prefixEnd_891629 457834242487797231136979 := by
  unfold tailWord_891629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520381286787885954829941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21680254191191923969886627 32520381286787885954829941)
  ·
    refine ⟨3048785745636364308265307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32520381286787885954829941 3048785745636364308265307)
    ·
      refine ⟨4573178618454546462397961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048785745636364308265307 4573178618454546462397961)
      ·
        refine ⟨3429883963840909846798471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4573178618454546462397961 3429883963840909846798471)
        ·
          refine ⟨5144825945761364770197707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429883963840909846798471 5144825945761364770197707)
          ·
            refine ⟨7717238918642047155296561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144825945761364770197707 7717238918642047155296561)
            ·
              refine ⟨5787929188981535366472421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717238918642047155296561 5787929188981535366472421)
              ·
                refine ⟨1085236722934037881213579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5787929188981535366472421 1085236722934037881213579)
                ·
                  refine ⟨1627855084401056821820369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085236722934037881213579 1627855084401056821820369)
                  ·
                    refine ⟨1220891313300792616365277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1627855084401056821820369 1220891313300792616365277)
                    ·
                      refine ⟨457834242487797231136979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220891313300792616365277 457834242487797231136979)
                      ·
                        rfl

theorem cell23_891629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_891629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891629 prefixEnd_891629 := by exact prefixLift 891629
  have htrace : WordTrace (prefixWord ++ tailWord_891629) baseStart_891629 baseEnd_891629 := by
    simpa [prefixWord, tailWord_891629, baseEnd_891629] using wordTrace_append hprefix tailTrace_891629
  have hstable : (prefixWord ++ tailWord_891629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891629).length < 2 ^ (prefixWord ++ tailWord_891629).sum := by decide
  have hdescent : baseEnd_891629 < baseStart_891629 := by decide
  rcases family_descends (prefixWord ++ tailWord_891629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891637 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_891637 : Nat := 118140960795 + 891637 * 2 ^ 59
def prefixEnd_891637 : Nat := 4983230072969 + 3 ^ 40 * 891637 * 2
def baseEnd_891637 : Nat := 457838350333033199836943

theorem tailTrace_891637 : CollatzResearch.WordTrace tailWord_891637 prefixEnd_891637 457838350333033199836943 := by
  unfold tailWord_891637
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520673070758903321121165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21680448713839268880747443 32520673070758903321121165)
  ·
    refine ⟨12195252401534588745420437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32520673070758903321121165 12195252401534588745420437)
    ·
      refine ⟨571652456321933847441583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12195252401534588745420437 571652456321933847441583)
      ·
        refine ⟨857478684482900771162375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571652456321933847441583 857478684482900771162375)
        ·
          refine ⟨1286218026724351156743563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857478684482900771162375 1286218026724351156743563)
          ·
            refine ⟨1929327040086526735115345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286218026724351156743563 1929327040086526735115345)
            ·
              refine ⟨1446995280064895051336509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929327040086526735115345 1446995280064895051336509)
              ·
                refine ⟨542623230024335644251191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1446995280064895051336509 542623230024335644251191)
                ·
                  refine ⟨813934845036503466376787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542623230024335644251191 813934845036503466376787)
                  ·
                    refine ⟨1220902267554755199565181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 813934845036503466376787 1220902267554755199565181)
                    ·
                      refine ⟨457838350333033199836943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220902267554755199565181 457838350333033199836943)
                      ·
                        rfl

theorem cell23_891637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_891637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891637 prefixEnd_891637 := by exact prefixLift 891637
  have htrace : WordTrace (prefixWord ++ tailWord_891637) baseStart_891637 baseEnd_891637 := by
    simpa [prefixWord, tailWord_891637, baseEnd_891637] using wordTrace_append hprefix tailTrace_891637
  have hstable : (prefixWord ++ tailWord_891637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891637).length < 2 ^ (prefixWord ++ tailWord_891637).sum := by decide
  have hdescent : baseEnd_891637 < baseStart_891637 := by decide
  rcases family_descends (prefixWord ++ tailWord_891637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891642 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_891642 : Nat := 118140960795 + 891642 * 2 ^ 59
def prefixEnd_891642 : Nat := 4983230072969 + 3 ^ 40 * 891642 * 2
def baseEnd_891642 : Nat := 457840917736305680274419

theorem tailTrace_891642 : CollatzResearch.WordTrace tailWord_891642 prefixEnd_891642 457840917736305680274419 := by
  unfold tailWord_891642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130213858935197293763295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21680570290493859450035453 8130213858935197293763295)
  ·
    refine ⟨12195320788402795940644943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130213858935197293763295 12195320788402795940644943)
    ·
      refine ⟨18292981182604193910967415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12195320788402795940644943 18292981182604193910967415)
      ·
        refine ⟨27439471773906290866451123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292981182604193910967415 27439471773906290866451123)
        ·
          refine ⟨41159207660859436299676685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27439471773906290866451123 41159207660859436299676685)
          ·
            refine ⟨15434702872822288612378757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41159207660859436299676685 15434702872822288612378757)
            ·
              refine ⟨2894006788654179114821017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15434702872822288612378757 2894006788654179114821017)
              ·
                refine ⟨2170505091490634336115763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2894006788654179114821017 2170505091490634336115763)
                ·
                  refine ⟨3255757637235951504173645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170505091490634336115763 3255757637235951504173645)
                  ·
                    refine ⟨1220909113963481814065117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255757637235951504173645 1220909113963481814065117)
                    ·
                      refine ⟨457840917736305680274419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220909113963481814065117 457840917736305680274419)
                      ·
                        rfl

theorem cell23_891642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_891642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891642 prefixEnd_891642 := by exact prefixLift 891642
  have htrace : WordTrace (prefixWord ++ tailWord_891642) baseStart_891642 baseEnd_891642 := by
    simpa [prefixWord, tailWord_891642, baseEnd_891642] using wordTrace_append hprefix tailTrace_891642
  have hstable : (prefixWord ++ tailWord_891642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891642).length < 2 ^ (prefixWord ++ tailWord_891642).sum := by decide
  have hdescent : baseEnd_891642 < baseStart_891642 := by decide
  rcases family_descends (prefixWord ++ tailWord_891642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891646 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_891646 : Nat := 118140960795 + 891646 * 2 ^ 59
def prefixEnd_891646 : Nat := 4983230072969 + 3 ^ 40 * 891646 * 2
def baseEnd_891646 : Nat := 457842971658923664624401

theorem tailTrace_891646 : CollatzResearch.WordTrace tailWord_891646 prefixEnd_891646 457842971658923664624401 := by
  unfold tailWord_891646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4065125165965787232274849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21680667551817531905465861 4065125165965787232274849)
  ·
    refine ⟨3048843874474340424206137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4065125165965787232274849 3048843874474340424206137)
    ·
      refine ⟨2286632905855755318154603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3048843874474340424206137 2286632905855755318154603)
      ·
        refine ⟨3429949358783632977231905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286632905855755318154603 3429949358783632977231905)
        ·
          refine ⟨2572462019087724732923929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3429949358783632977231905 2572462019087724732923929)
          ·
            refine ⟨1929346514315793549692947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2572462019087724732923929 1929346514315793549692947)
            ·
              refine ⟨2894019771473690324539421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929346514315793549692947 2894019771473690324539421)
              ·
                refine ⟨1085257414302633871702283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2894019771473690324539421 1085257414302633871702283)
                ·
                  refine ⟨1627886121453950807553425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085257414302633871702283 1627886121453950807553425)
                  ·
                    refine ⟨1220914591090463105665069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1627886121453950807553425 1220914591090463105665069)
                    ·
                      refine ⟨457842971658923664624401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1220914591090463105665069 457842971658923664624401)
                      ·
                        rfl

theorem cell23_891646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_891646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891646 prefixEnd_891646 := by exact prefixLift 891646
  have htrace : WordTrace (prefixWord ++ tailWord_891646) baseStart_891646 baseEnd_891646 := by
    simpa [prefixWord, tailWord_891646, baseEnd_891646] using wordTrace_append hprefix tailTrace_891646
  have hstable : (prefixWord ++ tailWord_891646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891646).length < 2 ^ (prefixWord ++ tailWord_891646).sum := by decide
  have hdescent : baseEnd_891646 < baseStart_891646 := by decide
  rcases family_descends (prefixWord ++ tailWord_891646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891665 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_891665 : Nat := 118140960795 + 891665 * 2 ^ 59
def prefixEnd_891665 : Nat := 4983230072969 + 3 ^ 40 * 891665 * 2
def baseEnd_891665 : Nat := 457852727791359090286813

theorem tailTrace_891665 : CollatzResearch.WordTrace tailWord_891665 prefixEnd_891665 457852727791359090286813 := by
  unfold tailWord_891665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32521694314657464103140449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21681129543104976068760299 32521694314657464103140449)
  ·
    refine ⟨24391270735993098077355337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32521694314657464103140449 24391270735993098077355337)
    ·
      refine ⟨18293453051994823558016503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24391270735993098077355337 18293453051994823558016503)
      ·
        refine ⟨27440179577992235337024755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18293453051994823558016503 27440179577992235337024755)
        ·
          refine ⟨41160269366988353005537133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27440179577992235337024755 41160269366988353005537133)
          ·
            refine ⟨15435101012620632377076425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41160269366988353005537133 15435101012620632377076425)
            ·
              refine ⟨11576325759465474282807319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15435101012620632377076425 11576325759465474282807319)
              ·
                refine ⟨17364488639198211424210979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576325759465474282807319 17364488639198211424210979)
                ·
                  refine ⟨26046732958797317136316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17364488639198211424210979 26046732958797317136316469)
                  ·
                    refine ⟨2441881214887248481529669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26046732958797317136316469 2441881214887248481529669)
                    ·
                      refine ⟨457852727791359090286813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2441881214887248481529669 457852727791359090286813)
                      ·
                        rfl

theorem cell23_891665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_891665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891665 prefixEnd_891665 := by exact prefixLift 891665
  have htrace : WordTrace (prefixWord ++ tailWord_891665) baseStart_891665 baseEnd_891665 := by
    simpa [prefixWord, tailWord_891665, baseEnd_891665] using wordTrace_append hprefix tailTrace_891665
  have hstable : (prefixWord ++ tailWord_891665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891665).length < 2 ^ (prefixWord ++ tailWord_891665).sum := by decide
  have hdescent : baseEnd_891665 < baseStart_891665 := by decide
  rcases family_descends (prefixWord ++ tailWord_891665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891715 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_891715 : Nat := 118140960795 + 891715 * 2 ^ 59
def prefixEnd_891715 : Nat := 4983230072969 + 3 ^ 40 * 891715 * 2
def baseEnd_891715 : Nat := 457878401824083894661583

theorem tailTrace_891715 : CollatzResearch.WordTrace tailWord_891715 prefixEnd_891715 457878401824083894661583 := by
  unfold tailWord_891715
  simp only [CollatzResearch.WordTrace]
  refine ⟨32523517964476322642460599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21682345309650881761640399 32523517964476322642460599)
  ·
    refine ⟨48785276946714483963690899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32523517964476322642460599 48785276946714483963690899)
    ·
      refine ⟨73177915420071725945536349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48785276946714483963690899 73177915420071725945536349)
      ·
        refine ⟨27441718282526897229576131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73177915420071725945536349 27441718282526897229576131)
        ·
          refine ⟨41162577423790345844364197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27441718282526897229576131 41162577423790345844364197)
          ·
            refine ⟨7717983266960689845818287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41162577423790345844364197 7717983266960689845818287)
            ·
              refine ⟨11576974900441034768727431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717983266960689845818287 11576974900441034768727431)
              ·
                refine ⟨17365462350661552153091147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576974900441034768727431 17365462350661552153091147)
                ·
                  refine ⟨26048193525992328229636721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17365462350661552153091147 26048193525992328229636721)
                  ·
                    refine ⟨19536145144494246172227541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26048193525992328229636721 19536145144494246172227541)
                    ·
                      refine ⟨457878401824083894661583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19536145144494246172227541 457878401824083894661583)
                      ·
                        rfl

theorem cell23_891715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_891715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891715 prefixEnd_891715 := by exact prefixLift 891715
  have htrace : WordTrace (prefixWord ++ tailWord_891715) baseStart_891715 baseEnd_891715 := by
    simpa [prefixWord, tailWord_891715, baseEnd_891715] using wordTrace_append hprefix tailTrace_891715
  have hstable : (prefixWord ++ tailWord_891715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891715).length < 2 ^ (prefixWord ++ tailWord_891715).sum := by decide
  have hdescent : baseEnd_891715 < baseStart_891715 := by decide
  rcases family_descends (prefixWord ++ tailWord_891715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891762 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_891762 : Nat := 118140960795 + 891762 * 2 ^ 59
def prefixEnd_891762 : Nat := 4983230072969 + 3 ^ 40 * 891762 * 2
def baseEnd_891762 : Nat := 457902535414845210773867

theorem tailTrace_891762 : CollatzResearch.WordTrace tailWord_891762 prefixEnd_891762 457902535414845210773867 := by
  unfold tailWord_891762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131308048826512417355385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21683488130204033112947693 8131308048826512417355385)
  ·
    refine ⟨6098481036619884313016539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8131308048826512417355385 6098481036619884313016539)
    ·
      refine ⟨9147721554929826469524809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098481036619884313016539 9147721554929826469524809)
      ·
        refine ⟨6860791166197369852143607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9147721554929826469524809 6860791166197369852143607)
        ·
          refine ⟨10291186749296054778215411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860791166197369852143607 10291186749296054778215411)
          ·
            refine ⟨15436780123944082167323117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10291186749296054778215411 15436780123944082167323117)
            ·
              refine ⟨5788792546479030812746169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15436780123944082167323117 5788792546479030812746169)
              ·
                refine ⟨4341594409859273109559627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788792546479030812746169 4341594409859273109559627)
                ·
                  refine ⟨6512391614788909664339441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341594409859273109559627 6512391614788909664339441)
                  ·
                    refine ⟨4884293711091682248254581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6512391614788909664339441 4884293711091682248254581)
                    ·
                      refine ⟨457902535414845210773867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4884293711091682248254581 457902535414845210773867)
                      ·
                        rfl

theorem cell23_891762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_891762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891762 prefixEnd_891762 := by exact prefixLift 891762
  have htrace : WordTrace (prefixWord ++ tailWord_891762) baseStart_891762 baseEnd_891762 := by
    simpa [prefixWord, tailWord_891762, baseEnd_891762] using wordTrace_append hprefix tailTrace_891762
  have hstable : (prefixWord ++ tailWord_891762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891762).length < 2 ^ (prefixWord ++ tailWord_891762).sum := by decide
  have hdescent : baseEnd_891762 < baseStart_891762 := by decide
  rcases family_descends (prefixWord ++ tailWord_891762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891799 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 3, 4]
def baseStart_891799 : Nat := 118140960795 + 891799 * 2 ^ 59
def prefixEnd_891799 : Nat := 4983230072969 + 3 ^ 40 * 891799 * 2
def baseEnd_891799 : Nat := 152640511399687188670399

theorem tailTrace_891799 : CollatzResearch.WordTrace tailWord_891799 prefixEnd_891799 152640511399687188670399 := by
  unfold tailWord_891799
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526581696172004988518451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21684387797448003325678967 32526581696172004988518451)
  ·
    refine ⟨48789872544258007482777677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32526581696172004988518451 48789872544258007482777677)
    ·
      refine ⟨18296202204096752806041629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48789872544258007482777677 18296202204096752806041629)
      ·
        refine ⟨6861075826536282302265611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18296202204096752806041629 6861075826536282302265611)
        ·
          refine ⟨10291613739804423453398417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861075826536282302265611 10291613739804423453398417)
          ·
            refine ⟨7718710304853317590048813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291613739804423453398417 7718710304853317590048813)
            ·
              refine ⟨2894516364319994096268305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7718710304853317590048813 2894516364319994096268305)
              ·
                refine ⟨2170887273239995572201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2894516364319994096268305 2170887273239995572201229)
                ·
                  refine ⟨814082727464998339575461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2170887273239995572201229 814082727464998339575461)
                  ·
                    refine ⟨152640511399687188670399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814082727464998339575461 152640511399687188670399)
                    ·
                      rfl

theorem cell23_891799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_891799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891799 prefixEnd_891799 := by exact prefixLift 891799
  have htrace : WordTrace (prefixWord ++ tailWord_891799) baseStart_891799 baseEnd_891799 := by
    simpa [prefixWord, tailWord_891799, baseEnd_891799] using wordTrace_append hprefix tailTrace_891799
  have hstable : (prefixWord ++ tailWord_891799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891799).length < 2 ^ (prefixWord ++ tailWord_891799).sum := by decide
  have hdescent : baseEnd_891799 < baseStart_891799 := by decide
  rcases family_descends (prefixWord ++ tailWord_891799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891812 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 8]
def baseStart_891812 : Nat := 118140960795 + 891812 * 2 ^ 59
def prefixEnd_891812 : Nat := 4983230072969 + 3 ^ 40 * 891812 * 2
def baseEnd_891812 : Nat := 50880912160841112794293

theorem tailTrace_891812 : CollatzResearch.WordTrace tailWord_891812 prefixEnd_891812 50880912160841112794293 := by
  unfold tailWord_891812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263527922562454104370845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21684703896749938805827793 16263527922562454104370845)
  ·
    refine ⟨6098822970960920289139067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16263527922562454104370845 6098822970960920289139067)
    ·
      refine ⟨9148234456441380433708601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098822970960920289139067 9148234456441380433708601)
      ·
        refine ⟨6861175842331035325281451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9148234456441380433708601 6861175842331035325281451)
        ·
          refine ⟨10291763763496552987922177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6861175842331035325281451 10291763763496552987922177)
          ·
            refine ⟨7718822822622414740941633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10291763763496552987922177 7718822822622414740941633)
            ·
              refine ⟨5789117116966811055706225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718822822622414740941633 5789117116966811055706225)
              ·
                refine ⟨4341837837725108291779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5789117116966811055706225 4341837837725108291779669)
                ·
                  refine ⟨50880912160841112794293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4341837837725108291779669 50880912160841112794293)
                  ·
                    rfl

theorem cell23_891812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_891812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891812 prefixEnd_891812 := by exact prefixLift 891812
  have htrace : WordTrace (prefixWord ++ tailWord_891812) baseStart_891812 baseEnd_891812 := by
    simpa [prefixWord, tailWord_891812, baseEnd_891812] using wordTrace_append hprefix tailTrace_891812
  have hstable : (prefixWord ++ tailWord_891812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891812).length < 2 ^ (prefixWord ++ tailWord_891812).sum := by decide
  have hdescent : baseEnd_891812 < baseStart_891812 := by decide
  rcases family_descends (prefixWord ++ tailWord_891812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891832 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_891832 : Nat := 118140960795 + 891832 * 2 ^ 59
def prefixEnd_891832 : Nat := 4983230072969 + 3 ^ 40 * 891832 * 2
def baseEnd_891832 : Nat := 457938479060659936898545

theorem tailTrace_891832 : CollatzResearch.WordTrace tailWord_891832 prefixEnd_891832 457938479060659936898545 := by
  unfold tailWord_891832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16263892652526225812234875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21685190203368301082979833 16263892652526225812234875)
  ·
    refine ⟨24395838978789338718352313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16263892652526225812234875 24395838978789338718352313)
    ·
      refine ⟨18296879234092004038764235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24395838978789338718352313 18296879234092004038764235)
      ·
        refine ⟨27445318851138006058146353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18296879234092004038764235 27445318851138006058146353)
        ·
          refine ⟨20583989138353504543609765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27445318851138006058146353 20583989138353504543609765)
          ·
            refine ⟨3859497963441282101926831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20583989138353504543609765 3859497963441282101926831)
            ·
              refine ⟨5789246945161923152890247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859497963441282101926831 5789246945161923152890247)
              ·
                refine ⟨8683870417742884729335371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789246945161923152890247 8683870417742884729335371)
                ·
                  refine ⟨13025805626614327094003057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8683870417742884729335371 13025805626614327094003057)
                  ·
                    refine ⟨9769354219960745320502293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13025805626614327094003057 9769354219960745320502293)
                    ·
                      refine ⟨457938479060659936898545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9769354219960745320502293 457938479060659936898545)
                      ·
                        rfl

theorem cell23_891832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_891832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891832 prefixEnd_891832 := by exact prefixLift 891832
  have htrace : WordTrace (prefixWord ++ tailWord_891832) baseStart_891832 baseEnd_891832 := by
    simpa [prefixWord, tailWord_891832, baseEnd_891832] using wordTrace_append hprefix tailTrace_891832
  have hstable : (prefixWord ++ tailWord_891832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891832).length < 2 ^ (prefixWord ++ tailWord_891832).sum := by decide
  have hdescent : baseEnd_891832 < baseStart_891832 := by decide
  rcases family_descends (prefixWord ++ tailWord_891832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891866 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_891866 : Nat := 118140960795 + 891866 * 2 ^ 59
def prefixEnd_891866 : Nat := 4983230072969 + 3 ^ 40 * 891866 * 2
def baseEnd_891866 : Nat := 457955937402912803873389

theorem tailTrace_891866 : CollatzResearch.WordTrace tailWord_891866 prefixEnd_891866 457955937402912803873389 := by
  unfold tailWord_891866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132256346732318857801863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21686016924619516954138301 8132256346732318857801863)
  ·
    refine ⟨12198384520098478286702795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132256346732318857801863 12198384520098478286702795)
    ·
      refine ⟨18297576780147717430054193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198384520098478286702795 18297576780147717430054193)
      ·
        refine ⟨13723182585110788072540645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18297576780147717430054193 13723182585110788072540645)
        ·
          refine ⟨2573096734708272763601371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13723182585110788072540645 2573096734708272763601371)
          ·
            refine ⟨3859645102062409145402057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573096734708272763601371 3859645102062409145402057)
            ·
              refine ⟨2894733826546806859051543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3859645102062409145402057 2894733826546806859051543)
              ·
                refine ⟨4342100739820210288577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894733826546806859051543 4342100739820210288577315)
                ·
                  refine ⟨6513151109730315432865973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342100739820210288577315 6513151109730315432865973)
                  ·
                    refine ⟨610607916537217071831185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6513151109730315432865973 610607916537217071831185)
                    ·
                      refine ⟨457955937402912803873389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610607916537217071831185 457955937402912803873389)
                      ·
                        rfl

theorem cell23_891866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_891866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891866 prefixEnd_891866 := by exact prefixLift 891866
  have htrace : WordTrace (prefixWord ++ tailWord_891866) baseStart_891866 baseEnd_891866 := by
    simpa [prefixWord, tailWord_891866, baseEnd_891866] using wordTrace_append hprefix tailTrace_891866
  have hstable : (prefixWord ++ tailWord_891866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891866).length < 2 ^ (prefixWord ++ tailWord_891866).sum := by decide
  have hdescent : baseEnd_891866 < baseStart_891866 := by decide
  rcases family_descends (prefixWord ++ tailWord_891866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891899 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3]
def baseStart_891899 : Nat := 118140960795 + 891899 * 2 ^ 59
def prefixEnd_891899 : Nat := 4983230072969 + 3 ^ 40 * 891899 * 2
def baseEnd_891899 : Nat := 457972882264511174760737

theorem tailTrace_891899 : CollatzResearch.WordTrace tailWord_891899 prefixEnd_891899 457972882264511174760737 := by
  unfold tailWord_891899
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530228995809722067158751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21686819330539814711439167 32530228995809722067158751)
  ·
    refine ⟨48795343493714583100738127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32530228995809722067158751 48795343493714583100738127)
    ·
      refine ⟨73193015240571874651107191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48795343493714583100738127 73193015240571874651107191)
      ·
        refine ⟨109789522860857811976660787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73193015240571874651107191 109789522860857811976660787)
        ·
          refine ⟨164684284291286717964991181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109789522860857811976660787 164684284291286717964991181)
          ·
            refine ⟨61756606609232519236871693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164684284291286717964991181 61756606609232519236871693)
            ·
              refine ⟨23158727478462194713826885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61756606609232519236871693 23158727478462194713826885)
              ·
                refine ⟨4342261402211661508842541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23158727478462194713826885 4342261402211661508842541)
                ·
                  refine ⟨1628348025829373065815953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4342261402211661508842541 1628348025829373065815953)
                  ·
                    refine ⟨1221261019372029799361965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628348025829373065815953 1221261019372029799361965)
                    ·
                      refine ⟨457972882264511174760737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221261019372029799361965 457972882264511174760737)
                      ·
                        rfl

theorem cell23_891899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].length) (baseStart_891899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891899 prefixEnd_891899 := by exact prefixLift 891899
  have htrace : WordTrace (prefixWord ++ tailWord_891899) baseStart_891899 baseEnd_891899 := by
    simpa [prefixWord, tailWord_891899, baseEnd_891899] using wordTrace_append hprefix tailTrace_891899
  have hstable : (prefixWord ++ tailWord_891899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891899).length < 2 ^ (prefixWord ++ tailWord_891899).sum := by decide
  have hdescent : baseEnd_891899 < baseStart_891899 := by decide
  rcases family_descends (prefixWord ++ tailWord_891899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891909 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_891909 : Nat := 118140960795 + 891909 * 2 ^ 59
def prefixEnd_891909 : Nat := 4983230072969 + 3 ^ 40 * 891909 * 2
def baseEnd_891909 : Nat := 457978017071056135635691

theorem tailTrace_891909 : CollatzResearch.WordTrace tailWord_891909 prefixEnd_891909 457978017071056135635691 := by
  unfold tailWord_891909
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530593725773493775022781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21687062483848995850015187 32530593725773493775022781)
  ·
    refine ⟨12198972647165060165633543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32530593725773493775022781 12198972647165060165633543)
    ·
      refine ⟨18298458970747590248450315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198972647165060165633543 18298458970747590248450315)
      ·
        refine ⟨27447688456121385372675473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18298458970747590248450315 27447688456121385372675473)
        ·
          refine ⟨20585766342091039029506605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27447688456121385372675473 20585766342091039029506605)
          ·
            refine ⟨7719662378284139636064977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20585766342091039029506605 7719662378284139636064977)
            ·
              refine ⟨5789746783713104727048733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7719662378284139636064977 5789746783713104727048733)
              ·
                refine ⟨2171155043892414272643275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5789746783713104727048733 2171155043892414272643275)
                ·
                  refine ⟨3256732565838621408964913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171155043892414272643275 3256732565838621408964913)
                  ·
                    refine ⟨2442549424378966056723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256732565838621408964913 2442549424378966056723685)
                    ·
                      refine ⟨457978017071056135635691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2442549424378966056723685 457978017071056135635691)
                      ·
                        rfl

theorem cell23_891909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_891909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891909 prefixEnd_891909 := by exact prefixLift 891909
  have htrace : WordTrace (prefixWord ++ tailWord_891909) baseStart_891909 baseEnd_891909 := by
    simpa [prefixWord, tailWord_891909, baseEnd_891909] using wordTrace_append hprefix tailTrace_891909
  have hstable : (prefixWord ++ tailWord_891909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891909).length < 2 ^ (prefixWord ++ tailWord_891909).sum := by decide
  have hdescent : baseEnd_891909 < baseStart_891909 := by decide
  rcases family_descends (prefixWord ++ tailWord_891909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891916 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_891916 : Nat := 118140960795 + 891916 * 2 ^ 59
def prefixEnd_891916 : Nat := 4983230072969 + 3 ^ 40 * 891916 * 2
def baseEnd_891916 : Nat := 457981611435637608248159

theorem tailTrace_891916 : CollatzResearch.WordTrace tailWord_891916 prefixEnd_891916 457981611435637608248159 := by
  unfold tailWord_891916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265424518374066985263801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21687232691165422647018401 16265424518374066985263801)
  ·
    refine ⟨12199068388780550238947851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16265424518374066985263801 12199068388780550238947851)
    ·
      refine ⟨18298602583170825358421777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199068388780550238947851 18298602583170825358421777)
      ·
        refine ⟨13723951937378119018816333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18298602583170825358421777 13723951937378119018816333)
        ·
          refine ⟨5146481976516794632056125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13723951937378119018816333 5146481976516794632056125)
          ·
            refine ⟨1929930741193797987021047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5146481976516794632056125 1929930741193797987021047)
            ·
              refine ⟨2894896111790696980531571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929930741193797987021047 2894896111790696980531571)
              ·
                refine ⟨4342344167686045470797357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894896111790696980531571 4342344167686045470797357)
                ·
                  refine ⟨1628379062882267051549009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4342344167686045470797357 1628379062882267051549009)
                  ·
                    refine ⟨1221284297161700288661757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628379062882267051549009 1221284297161700288661757)
                    ·
                      refine ⟨457981611435637608248159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221284297161700288661757 457981611435637608248159)
                      ·
                        rfl

theorem cell23_891916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_891916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891916 prefixEnd_891916 := by exact prefixLift 891916
  have htrace : WordTrace (prefixWord ++ tailWord_891916) baseStart_891916 baseEnd_891916 := by
    simpa [prefixWord, tailWord_891916, baseEnd_891916] using wordTrace_append hprefix tailTrace_891916
  have hstable : (prefixWord ++ tailWord_891916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891916).length < 2 ^ (prefixWord ++ tailWord_891916).sum := by decide
  have hdescent : baseEnd_891916 < baseStart_891916 := by decide
  rcases family_descends (prefixWord ++ tailWord_891916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891929 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_891929 : Nat := 118140960795 + 891929 * 2 ^ 59
def prefixEnd_891929 : Nat := 4983230072969 + 3 ^ 40 * 891929 * 2
def baseEnd_891929 : Nat := 457988286684146057385599

theorem tailTrace_891929 : CollatzResearch.WordTrace tailWord_891929 prefixEnd_891929 457988286684146057385599 := by
  unfold tailWord_891929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32531323185701037190750841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21687548790467358127167227 32531323185701037190750841)
  ·
    refine ⟨24398492389275777893063131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32531323185701037190750841 24398492389275777893063131)
    ·
      refine ⟨36597738583913666839594697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24398492389275777893063131 36597738583913666839594697)
      ·
        refine ⟨27448303937935250129696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36597738583913666839594697 27448303937935250129696023)
        ·
          refine ⟨41172455906902875194544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27448303937935250129696023 41172455906902875194544035)
          ·
            refine ⟨61758683860354312791816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41172455906902875194544035 61758683860354312791816053)
            ·
              refine ⟨5789876611908216824232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61758683860354312791816053 5789876611908216824232755)
              ·
                refine ⟨8684814917862325236349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789876611908216824232755 8684814917862325236349133)
                ·
                  refine ⟨3256805594198371963630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8684814917862325236349133 3256805594198371963630925)
                  ·
                    refine ⟨1221302097824389486361597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256805594198371963630925 1221302097824389486361597)
                    ·
                      refine ⟨457988286684146057385599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221302097824389486361597 457988286684146057385599)
                      ·
                        rfl

theorem cell23_891929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_891929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891929 prefixEnd_891929 := by exact prefixLift 891929
  have htrace : WordTrace (prefixWord ++ tailWord_891929) baseStart_891929 baseEnd_891929 := by
    simpa [prefixWord, tailWord_891929, baseEnd_891929] using wordTrace_append hprefix tailTrace_891929
  have hstable : (prefixWord ++ tailWord_891929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891929).length < 2 ^ (prefixWord ++ tailWord_891929).sum := by decide
  have hdescent : baseEnd_891929 < baseStart_891929 := by decide
  rcases family_descends (prefixWord ++ tailWord_891929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891930 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_891930 : Nat := 118140960795 + 891930 * 2 ^ 59
def prefixEnd_891930 : Nat := 4983230072969 + 3 ^ 40 * 891930 * 2
def baseEnd_891930 : Nat := 457988800164800553473095

theorem tailTrace_891930 : CollatzResearch.WordTrace tailWord_891930 prefixEnd_891930 457988800164800553473095 := by
  unfold tailWord_891930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132839914674353590384311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21687573105798276241024829 8132839914674353590384311)
  ·
    refine ⟨12199259872011530385576467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132839914674353590384311 12199259872011530385576467)
    ·
      refine ⟨18298889808017295578364701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199259872011530385576467 18298889808017295578364701)
      ·
        refine ⟨6862083678006485841886763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18298889808017295578364701 6862083678006485841886763)
        ·
          refine ⟨10293125517009728762830145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862083678006485841886763 10293125517009728762830145)
          ·
            refine ⟨7719844137757296572122609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10293125517009728762830145 7719844137757296572122609)
            ·
              refine ⟨5789883103317972429091957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7719844137757296572122609 5789883103317972429091957)
              ·
                refine ⟨542801540936059915227371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5789883103317972429091957 542801540936059915227371)
                ·
                  refine ⟨814202311404089872841057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542801540936059915227371 814202311404089872841057)
                  ·
                    refine ⟨610651733553067404630793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814202311404089872841057 610651733553067404630793)
                    ·
                      refine ⟨457988800164800553473095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610651733553067404630793 457988800164800553473095)
                      ·
                        rfl

theorem cell23_891930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_891930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891930 prefixEnd_891930 := by exact prefixLift 891930
  have htrace : WordTrace (prefixWord ++ tailWord_891930) baseStart_891930 baseEnd_891930 := by
    simpa [prefixWord, tailWord_891930, baseEnd_891930] using wordTrace_append hprefix tailTrace_891930
  have hstable : (prefixWord ++ tailWord_891930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891930).length < 2 ^ (prefixWord ++ tailWord_891930).sum := by decide
  have hdescent : baseEnd_891930 < baseStart_891930 := by decide
  rcases family_descends (prefixWord ++ tailWord_891930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891933 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_891933 : Nat := 118140960795 + 891933 * 2 ^ 59
def prefixEnd_891933 : Nat := 4983230072969 + 3 ^ 40 * 891933 * 2
def baseEnd_891933 : Nat := 457990340606764041735581

theorem tailTrace_891933 : CollatzResearch.WordTrace tailWord_891933 prefixEnd_891933 457990340606764041735581 := by
  unfold tailWord_891933
  simp only [CollatzResearch.WordTrace]
  refine ⟨32531469077686545873896453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21687646051791030582597635 32531469077686545873896453)
  ·
    refine ⟨6099650452066227351355585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32531469077686545873896453 6099650452066227351355585)
    ·
      refine ⟨4574737839049670513516689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6099650452066227351355585 4574737839049670513516689)
      ·
        refine ⟨3431053379287252885137517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574737839049670513516689 3431053379287252885137517)
        ·
          refine ⟨1286645017232719831926569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3431053379287252885137517 1286645017232719831926569)
          ·
            refine ⟨964983762924539873944927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286645017232719831926569 964983762924539873944927)
            ·
              refine ⟨1447475644386809810917391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964983762924539873944927 1447475644386809810917391)
              ·
                refine ⟨2171213466580214716376087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447475644386809810917391 2171213466580214716376087)
                ·
                  refine ⟨3256820199870322074564131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171213466580214716376087 3256820199870322074564131)
                  ·
                    refine ⟨4885230299805483111846197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3256820199870322074564131 4885230299805483111846197)
                    ·
                      refine ⟨457990340606764041735581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4885230299805483111846197 457990340606764041735581)
                      ·
                        rfl

theorem cell23_891933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_891933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891933 prefixEnd_891933 := by exact prefixLift 891933
  have htrace : WordTrace (prefixWord ++ tailWord_891933) baseStart_891933 baseEnd_891933 := by
    simpa [prefixWord, tailWord_891933, baseEnd_891933] using wordTrace_append hprefix tailTrace_891933
  have hstable : (prefixWord ++ tailWord_891933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891933).length < 2 ^ (prefixWord ++ tailWord_891933).sum := by decide
  have hdescent : baseEnd_891933 < baseStart_891933 := by decide
  rcases family_descends (prefixWord ++ tailWord_891933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891936 : List Nat := [2, 1, 1, 7, 2, 10]
def baseStart_891936 : Nat := 118140960795 + 891936 * 2 ^ 59
def prefixEnd_891936 : Nat := 4983230072969 + 3 ^ 40 * 891936 * 2
def baseEnd_891936 : Nat := 1884740251229331399169

theorem tailTrace_891936 : CollatzResearch.WordTrace tailWord_891936 prefixEnd_891936 1884740251229331399169 := by
  unfold tailWord_891936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265789248337838693127831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21687718997783784924170441 16265789248337838693127831)
  ·
    refine ⟨24398683872506758039691747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16265789248337838693127831 24398683872506758039691747)
    ·
      refine ⟨36598025808760137059537621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24398683872506758039691747 36598025808760137059537621)
      ·
        refine ⟨857766229892815712332913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36598025808760137059537621 857766229892815712332913)
        ·
          refine ⟨643324672419611784249685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857766229892815712332913 643324672419611784249685)
          ·
            refine ⟨1884740251229331399169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 643324672419611784249685 1884740251229331399169)
            ·
              rfl

theorem cell23_891936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 10].length) (baseStart_891936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891936 prefixEnd_891936 := by exact prefixLift 891936
  have htrace : WordTrace (prefixWord ++ tailWord_891936) baseStart_891936 baseEnd_891936 := by
    simpa [prefixWord, tailWord_891936, baseEnd_891936] using wordTrace_append hprefix tailTrace_891936
  have hstable : (prefixWord ++ tailWord_891936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891936).length < 2 ^ (prefixWord ++ tailWord_891936).sum := by decide
  have hdescent : baseEnd_891936 < baseStart_891936 := by decide
  rcases family_descends (prefixWord ++ tailWord_891936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891989 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_891989 : Nat := 118140960795 + 891989 * 2 ^ 59
def prefixEnd_891989 : Nat := 4983230072969 + 3 ^ 40 * 891989 * 2
def baseEnd_891989 : Nat := 458019095523415822635323

theorem tailTrace_891989 : CollatzResearch.WordTrace tailWord_891989 prefixEnd_891989 458019095523415822635323 := by
  unfold tailWord_891989
  simp only [CollatzResearch.WordTrace]
  refine ⟨32533511565483667437935021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21689007710322444958623347 32533511565483667437935021)
  ·
    refine ⟨12200066837056375289225633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32533511565483667437935021 12200066837056375289225633)
    ·
      refine ⟨9150050127792281466919225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200066837056375289225633 9150050127792281466919225)
      ·
        refine ⟨6862537595844211100189419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9150050127792281466919225 6862537595844211100189419)
        ·
          refine ⟨10293806393766316650284129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862537595844211100189419 10293806393766316650284129)
          ·
            refine ⟨7720354795324737487713097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10293806393766316650284129 7720354795324737487713097)
            ·
              refine ⟨5790266096493553115784823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720354795324737487713097 5790266096493553115784823)
              ·
                refine ⟨8685399144740329673677235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790266096493553115784823 8685399144740329673677235)
                ·
                  refine ⟨13028098717110494510515853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685399144740329673677235 13028098717110494510515853)
                  ·
                    refine ⟨4885537018916435441443445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13028098717110494510515853 4885537018916435441443445)
                    ·
                      refine ⟨458019095523415822635323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4885537018916435441443445 458019095523415822635323)
                      ·
                        rfl

theorem cell23_891989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_891989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891989 prefixEnd_891989 := by exact prefixLift 891989
  have htrace : WordTrace (prefixWord ++ tailWord_891989) baseStart_891989 baseEnd_891989 := by
    simpa [prefixWord, tailWord_891989, baseEnd_891989] using wordTrace_append hprefix tailTrace_891989
  have hstable : (prefixWord ++ tailWord_891989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891989).length < 2 ^ (prefixWord ++ tailWord_891989).sum := by decide
  have hdescent : baseEnd_891989 < baseStart_891989 := by decide
  rcases family_descends (prefixWord ++ tailWord_891989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891999 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_891999 : Nat := 118140960795 + 891999 * 2 ^ 59
def prefixEnd_891999 : Nat := 4983230072969 + 3 ^ 40 * 891999 * 2
def baseEnd_891999 : Nat := 458024230329960783510277

theorem tailTrace_891999 : CollatzResearch.WordTrace tailWord_891999 prefixEnd_891999 458024230329960783510277 := by
  unfold tailWord_891999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32533876295447439145799051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21689250863631626097199367 32533876295447439145799051)
  ·
    refine ⟨48800814443171158718698577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32533876295447439145799051 48800814443171158718698577)
    ·
      refine ⟨36600610832378369039023933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48800814443171158718698577 36600610832378369039023933)
      ·
        refine ⟨13725229062141888389633975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36600610832378369039023933 13725229062141888389633975)
        ·
          refine ⟨20587843593212832584450963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725229062141888389633975 20587843593212832584450963)
          ·
            refine ⟨30881765389819248876676445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20587843593212832584450963 30881765389819248876676445)
            ·
              refine ⟨11580662021182218328753667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30881765389819248876676445 11580662021182218328753667)
              ·
                refine ⟨17370993031773327493130501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580662021182218328753667 17370993031773327493130501)
                ·
                  refine ⟨3257061193457498904961969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17370993031773327493130501 3257061193457498904961969)
                  ·
                    refine ⟨2442795895093124178721477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3257061193457498904961969 2442795895093124178721477)
                    ·
                      refine ⟨458024230329960783510277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2442795895093124178721477 458024230329960783510277)
                      ·
                        rfl

theorem cell23_891999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_891999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_891999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_891999 prefixEnd_891999 := by exact prefixLift 891999
  have htrace : WordTrace (prefixWord ++ tailWord_891999) baseStart_891999 baseEnd_891999 := by
    simpa [prefixWord, tailWord_891999, baseEnd_891999] using wordTrace_append hprefix tailTrace_891999
  have hstable : (prefixWord ++ tailWord_891999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891999).length < 2 ^ (prefixWord ++ tailWord_891999).sum := by decide
  have hdescent : baseEnd_891999 < baseStart_891999 := by decide
  rcases family_descends (prefixWord ++ tailWord_891999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892009 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 7]
def baseStart_892009 : Nat := 118140960795 + 892009 * 2 ^ 59
def prefixEnd_892009 : Nat := 4983230072969 + 3 ^ 40 * 892009 * 2
def baseEnd_892009 : Nat := 50892151681833971598359

theorem tailTrace_892009 : CollatzResearch.WordTrace tailWord_892009 prefixEnd_892009 50892151681833971598359 := by
  unfold tailWord_892009
  simp only [CollatzResearch.WordTrace]
  refine ⟨32534241025411210853663081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21689494016940807235775387 32534241025411210853663081)
  ·
    refine ⟨24400680769058408140247311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32534241025411210853663081 24400680769058408140247311)
    ·
      refine ⟨36601021153587612210370967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24400680769058408140247311 36601021153587612210370967)
      ·
        refine ⟨54901531730381418315556451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36601021153587612210370967 54901531730381418315556451)
        ·
          refine ⟨82352297595572127473334677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54901531730381418315556451 82352297595572127473334677)
          ·
            refine ⟨3860263949792443475312563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82352297595572127473334677 3860263949792443475312563)
            ·
              refine ⟨5790395924688665212968845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860263949792443475312563 5790395924688665212968845)
              ·
                refine ⟨2171398471758249454863317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790395924688665212968845 2171398471758249454863317)
                ·
                  refine ⟨50892151681833971598359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2171398471758249454863317 50892151681833971598359)
                  ·
                    rfl

theorem cell23_892009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_892009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892009 prefixEnd_892009 := by exact prefixLift 892009
  have htrace : WordTrace (prefixWord ++ tailWord_892009) baseStart_892009 baseEnd_892009 := by
    simpa [prefixWord, tailWord_892009, baseEnd_892009] using wordTrace_append hprefix tailTrace_892009
  have hstable : (prefixWord ++ tailWord_892009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892009).length < 2 ^ (prefixWord ++ tailWord_892009).sum := by decide
  have hdescent : baseEnd_892009 < baseStart_892009 := by decide
  rcases family_descends (prefixWord ++ tailWord_892009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892056 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_892056 : Nat := 118140960795 + 892056 * 2 ^ 59
def prefixEnd_892056 : Nat := 4983230072969 + 3 ^ 40 * 892056 * 2
def baseEnd_892056 : Nat := 152684499575755686832505

theorem tailTrace_892056 : CollatzResearch.WordTrace tailWord_892056 prefixEnd_892056 152684499575755686832505 := by
  unfold tailWord_892056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267977628120468940312011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21690636837493958587082681 16267977628120468940312011)
  ·
    refine ⟨24401966442180703410468017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16267977628120468940312011 24401966442180703410468017)
    ·
      refine ⟨18301474831635527557851013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24401966442180703410468017 18301474831635527557851013)
      ·
        refine ⟨3431526530931661417097065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18301474831635527557851013 3431526530931661417097065)
        ·
          refine ⟨2573644898198746062822799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431526530931661417097065 2573644898198746062822799)
          ·
            refine ⟨3860467347298119094234199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573644898198746062822799 3860467347298119094234199)
            ·
              refine ⟨5790701020947178641351299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860467347298119094234199 5790701020947178641351299)
              ·
                refine ⟨8686051531420767962026949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790701020947178641351299 8686051531420767962026949)
                ·
                  refine ⟨1628634662141393992880053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8686051531420767962026949 1628634662141393992880053)
                  ·
                    refine ⟨152684499575755686832505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1628634662141393992880053 152684499575755686832505)
                    ·
                      rfl

theorem cell23_892056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_892056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892056 prefixEnd_892056 := by exact prefixLift 892056
  have htrace : WordTrace (prefixWord ++ tailWord_892056) baseStart_892056 baseEnd_892056 := by
    simpa [prefixWord, tailWord_892056, baseEnd_892056] using wordTrace_append hprefix tailTrace_892056
  have hstable : (prefixWord ++ tailWord_892056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892056).length < 2 ^ (prefixWord ++ tailWord_892056).sum := by decide
  have hdescent : baseEnd_892056 < baseStart_892056 := by decide
  rcases family_descends (prefixWord ++ tailWord_892056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892059 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_892059 : Nat := 118140960795 + 892059 * 2 ^ 59
def prefixEnd_892059 : Nat := 4983230072969 + 3 ^ 40 * 892059 * 2
def baseEnd_892059 : Nat := 458055039169230548760001

theorem tailTrace_892059 : CollatzResearch.WordTrace tailWord_892059 prefixEnd_892059 458055039169230548760001 := by
  unfold tailWord_892059
  simp only [CollatzResearch.WordTrace]
  refine ⟨32536064675230069392983231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21690709783486712928655487 32536064675230069392983231)
  ·
    refine ⟨48804097012845104089474847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32536064675230069392983231 48804097012845104089474847)
    ·
      refine ⟨73206145519267656134212271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48804097012845104089474847 73206145519267656134212271)
      ·
        refine ⟨109809218278901484201318407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73206145519267656134212271 109809218278901484201318407)
        ·
          refine ⟨164713827418352226301977611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109809218278901484201318407 164713827418352226301977611)
          ·
            refine ⟨247070741127528339452966417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164713827418352226301977611 247070741127528339452966417)
            ·
              refine ⟨185303055845646254589724813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247070741127528339452966417 185303055845646254589724813)
              ·
                refine ⟨69488645942117345471146805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185303055845646254589724813 69488645942117345471146805)
                ·
                  refine ⟨6514560557073501137920013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69488645942117345471146805 6514560557073501137920013)
                  ·
                    refine ⟨2442960208902562926720005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6514560557073501137920013 2442960208902562926720005)
                    ·
                      refine ⟨458055039169230548760001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2442960208902562926720005 458055039169230548760001)
                      ·
                        rfl

theorem cell23_892059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_892059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892059 prefixEnd_892059 := by exact prefixLift 892059
  have htrace : WordTrace (prefixWord ++ tailWord_892059) baseStart_892059 baseEnd_892059 := by
    simpa [prefixWord, tailWord_892059, baseEnd_892059] using wordTrace_append hprefix tailTrace_892059
  have hstable : (prefixWord ++ tailWord_892059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892059).length < 2 ^ (prefixWord ++ tailWord_892059).sum := by decide
  have hdescent : baseEnd_892059 < baseStart_892059 := by decide
  rcases family_descends (prefixWord ++ tailWord_892059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892060 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 5]
def baseStart_892060 : Nat := 118140960795 + 892060 * 2 ^ 59
def prefixEnd_892060 : Nat := 4983230072969 + 3 ^ 40 * 892060 * 2
def baseEnd_892060 : Nat := 50895061405542782760833

theorem tailTrace_892060 : CollatzResearch.WordTrace tailWord_892060 prefixEnd_892060 50895061405542782760833 := by
  unfold tailWord_892060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268050574113223281884817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21690734098817631042513089 16268050574113223281884817)
  ·
    refine ⟨12201037930584917461413613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16268050574113223281884817 12201037930584917461413613)
    ·
      refine ⟨4575389223969344048030105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12201037930584917461413613 4575389223969344048030105)
      ·
        refine ⟨3431541917977008036022579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4575389223969344048030105 3431541917977008036022579)
        ·
          refine ⟨5147312876965512054033869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431541917977008036022579 5147312876965512054033869)
          ·
            refine ⟨1930242328862067020262701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5147312876965512054033869 1930242328862067020262701)
            ·
              refine ⟨723840873323275132598513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1930242328862067020262701 723840873323275132598513)
              ·
                refine ⟨542880654992456349448885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723840873323275132598513 542880654992456349448885)
                ·
                  refine ⟨50895061405542782760833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542880654992456349448885 50895061405542782760833)
                  ·
                    rfl

theorem cell23_892060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_892060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892060 prefixEnd_892060 := by exact prefixLift 892060
  have htrace : WordTrace (prefixWord ++ tailWord_892060) baseStart_892060 baseEnd_892060 := by
    simpa [prefixWord, tailWord_892060, baseEnd_892060] using wordTrace_append hprefix tailTrace_892060
  have hstable : (prefixWord ++ tailWord_892060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892060).length < 2 ^ (prefixWord ++ tailWord_892060).sum := by decide
  have hdescent : baseEnd_892060 < baseStart_892060 := by decide
  rcases family_descends (prefixWord ++ tailWord_892060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892099 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 8]
def baseStart_892099 : Nat := 118140960795 + 892099 * 2 ^ 59
def prefixEnd_892099 : Nat := 4983230072969 + 3 ^ 40 * 892099 * 2
def baseEnd_892099 : Nat := 50897286488378932473313

theorem tailTrace_892099 : CollatzResearch.WordTrace tailWord_892099 prefixEnd_892099 50897286488378932473313 := by
  unfold tailWord_892099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32537523595085156224439351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21691682396723437482959567 32537523595085156224439351)
  ·
    refine ⟨48806285392627734336659027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32537523595085156224439351 48806285392627734336659027)
    ·
      refine ⟨73209428088941601504988541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48806285392627734336659027 73209428088941601504988541)
      ·
        refine ⟨27453535533353100564370703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73209428088941601504988541 27453535533353100564370703)
        ·
          refine ⟨41180303300029650846556055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453535533353100564370703 41180303300029650846556055)
          ·
            refine ⟨61770454950044476269834083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41180303300029650846556055 61770454950044476269834083)
            ·
              refine ⟨92655682425066714404751125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61770454950044476269834083 92655682425066714404751125)
              ·
                refine ⟨4343235113675002237722709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92655682425066714404751125 4343235113675002237722709)
                ·
                  refine ⟨50897286488378932473313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4343235113675002237722709 50897286488378932473313)
                  ·
                    rfl

theorem cell23_892099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 8].length) (baseStart_892099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892099 prefixEnd_892099 := by exact prefixLift 892099
  have htrace : WordTrace (prefixWord ++ tailWord_892099) baseStart_892099 baseEnd_892099 := by
    simpa [prefixWord, tailWord_892099, baseEnd_892099] using wordTrace_append hprefix tailTrace_892099
  have hstable : (prefixWord ++ tailWord_892099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892099).length < 2 ^ (prefixWord ++ tailWord_892099).sum := by decide
  have hdescent : baseEnd_892099 < baseStart_892099 := by decide
  rcases family_descends (prefixWord ++ tailWord_892099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892153 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 5, 2]
def baseStart_892153 : Nat := 118140960795 + 892153 * 2 ^ 59
def prefixEnd_892153 : Nat := 4983230072969 + 3 ^ 40 * 892153 * 2
def baseEnd_892153 : Nat := 458103306350753180984569

theorem tailTrace_892153 : CollatzResearch.WordTrace tailWord_892153 prefixEnd_892153 458103306350753180984569 := by
  unfold tailWord_892153
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539493136889523446905113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21692995424593015631270075 32539493136889523446905113)
  ·
    refine ⟨24404619852667142585178835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32539493136889523446905113 24404619852667142585178835)
    ·
      refine ⟨36606929779000713877768253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24404619852667142585178835 36606929779000713877768253)
      ·
        refine ⟨13727598667125267704163095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36606929779000713877768253 13727598667125267704163095)
        ·
          refine ⟨20591398000687901556244643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727598667125267704163095 20591398000687901556244643)
          ·
            refine ⟨30887097001031852334366965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20591398000687901556244643 30887097001031852334366965)
            ·
              refine ⟨2895665343846736156346903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30887097001031852334366965 2895665343846736156346903)
              ·
                refine ⟨4343498015770104234520355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895665343846736156346903 4343498015770104234520355)
                ·
                  refine ⟨6515247023655156351780533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343498015770104234520355 6515247023655156351780533)
                  ·
                    refine ⟨610804408467670907979425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6515247023655156351780533 610804408467670907979425)
                    ·
                      refine ⟨458103306350753180984569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610804408467670907979425 458103306350753180984569)
                      ·
                        rfl

theorem cell23_892153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_892153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892153 prefixEnd_892153 := by exact prefixLift 892153
  have htrace : WordTrace (prefixWord ++ tailWord_892153) baseStart_892153 baseEnd_892153 := by
    simpa [prefixWord, tailWord_892153, baseEnd_892153] using wordTrace_append hprefix tailTrace_892153
  have hstable : (prefixWord ++ tailWord_892153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892153).length < 2 ^ (prefixWord ++ tailWord_892153).sum := by decide
  have hdescent : baseEnd_892153 < baseStart_892153 := by decide
  rcases family_descends (prefixWord ++ tailWord_892153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892163 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 1, 5]
def baseStart_892163 : Nat := 118140960795 + 892163 * 2 ^ 59
def prefixEnd_892163 : Nat := 4983230072969 + 3 ^ 40 * 892163 * 2
def baseEnd_892163 : Nat := 152702813719099380619841

theorem tailTrace_892163 : CollatzResearch.WordTrace tailWord_892163 prefixEnd_892163 152702813719099380619841 := by
  unfold tailWord_892163
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539857866853295154769143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21693238577902196769846095 32539857866853295154769143)
  ·
    refine ⟨48809786800279942732153715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32539857866853295154769143 48809786800279942732153715)
    ·
      refine ⟨73214680200419914098230573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48809786800279942732153715 73214680200419914098230573)
      ·
        refine ⟨27455505075157467786836465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73214680200419914098230573 27455505075157467786836465)
        ·
          refine ⟨20591628806368100840127349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27455505075157467786836465 20591628806368100840127349)
          ·
            refine ⟨1930465200597009453761939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20591628806368100840127349 1930465200597009453761939)
            ·
              refine ⟨2895697800895514180642909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930465200597009453761939 2895697800895514180642909)
              ·
                refine ⟨1085886675335817817741091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895697800895514180642909 1085886675335817817741091)
                ·
                  refine ⟨1628830013003726726611637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085886675335817817741091 1628830013003726726611637)
                  ·
                    refine ⟨152702813719099380619841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1628830013003726726611637 152702813719099380619841)
                    ·
                      rfl

theorem cell23_892163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 5].length) (baseStart_892163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892163 prefixEnd_892163 := by exact prefixLift 892163
  have htrace : WordTrace (prefixWord ++ tailWord_892163) baseStart_892163 baseEnd_892163 := by
    simpa [prefixWord, tailWord_892163, baseEnd_892163] using wordTrace_append hprefix tailTrace_892163
  have hstable : (prefixWord ++ tailWord_892163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892163).length < 2 ^ (prefixWord ++ tailWord_892163).sum := by decide
  have hdescent : baseEnd_892163 < baseStart_892163 := by decide
  rcases family_descends (prefixWord ++ tailWord_892163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892200 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_892200 : Nat := 118140960795 + 892200 * 2 ^ 59
def prefixEnd_892200 : Nat := 4983230072969 + 3 ^ 40 * 892200 * 2
def baseEnd_892200 : Nat := 458127439941514497096853

theorem tailTrace_892200 : CollatzResearch.WordTrace tailWord_892200 prefixEnd_892200 458127439941514497096853 := by
  unfold tailWord_892200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270603683859625236933027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21694138245146166982577369 16270603683859625236933027)
  ·
    refine ⟨24405905525789437855399541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16270603683859625236933027 24405905525789437855399541)
    ·
      refine ⟨2288053643042759798943707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24405905525789437855399541 2288053643042759798943707)
      ·
        refine ⟨3432080464564139698415561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288053643042759798943707 3432080464564139698415561)
        ·
          refine ⟨2574060348423104773811671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432080464564139698415561 2574060348423104773811671)
          ·
            refine ⟨3861090522634657160717507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574060348423104773811671 3861090522634657160717507)
            ·
              refine ⟨5791635783951985741076261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861090522634657160717507 5791635783951985741076261)
              ·
                refine ⟨1085931709490997326451799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5791635783951985741076261 1085931709490997326451799)
                ·
                  refine ⟨1628897564236495989677699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085931709490997326451799 1628897564236495989677699)
                  ·
                    refine ⟨2443346346354743984516549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1628897564236495989677699 2443346346354743984516549)
                    ·
                      refine ⟨458127439941514497096853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2443346346354743984516549 458127439941514497096853)
                      ·
                        rfl

theorem cell23_892200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_892200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892200 prefixEnd_892200 := by exact prefixLift 892200
  have htrace : WordTrace (prefixWord ++ tailWord_892200) baseStart_892200 baseEnd_892200 := by
    simpa [prefixWord, tailWord_892200, baseEnd_892200] using wordTrace_append hprefix tailTrace_892200
  have hstable : (prefixWord ++ tailWord_892200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892200).length < 2 ^ (prefixWord ++ tailWord_892200).sum := by decide
  have hdescent : baseEnd_892200 < baseStart_892200 := by decide
  rcases family_descends (prefixWord ++ tailWord_892200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892220 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_892220 : Nat := 118140960795 + 892220 * 2 ^ 59
def prefixEnd_892220 : Nat := 4983230072969 + 3 ^ 40 * 892220 * 2
def baseEnd_892220 : Nat := 458137709554604418846761

theorem tailTrace_892220 : CollatzResearch.WordTrace tailWord_892220 prefixEnd_892220 458137709554604418846761 := by
  unfold tailWord_892220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270968413823396944797057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21694624551764529259729409 16270968413823396944797057)
  ·
    refine ⟨12203226310367547708597793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16270968413823396944797057 12203226310367547708597793)
    ·
      refine ⟨9152419732775660781448345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12203226310367547708597793 9152419732775660781448345)
      ·
        refine ⟨6864314799581745586086259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9152419732775660781448345 6864314799581745586086259)
        ·
          refine ⟨10296472199372618379129389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864314799581745586086259 10296472199372618379129389)
          ·
            refine ⟨3861177074764731892173521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10296472199372618379129389 3861177074764731892173521)
            ·
              refine ⟨2895882806073548919130141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861177074764731892173521 2895882806073548919130141)
              ·
                refine ⟨1085956052277580844673803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895882806073548919130141 1085956052277580844673803)
                ·
                  refine ⟨1628934078416371267010705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085956052277580844673803 1628934078416371267010705)
                  ·
                    refine ⟨1221700558812278450258029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628934078416371267010705 1221700558812278450258029)
                    ·
                      refine ⟨458137709554604418846761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221700558812278450258029 458137709554604418846761)
                      ·
                        rfl

theorem cell23_892220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_892220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892220 prefixEnd_892220 := by exact prefixLift 892220
  have htrace : WordTrace (prefixWord ++ tailWord_892220) baseStart_892220 baseEnd_892220 := by
    simpa [prefixWord, tailWord_892220, baseEnd_892220] using wordTrace_append hprefix tailTrace_892220
  have hstable : (prefixWord ++ tailWord_892220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892220).length < 2 ^ (prefixWord ++ tailWord_892220).sum := by decide
  have hdescent : baseEnd_892220 < baseStart_892220 := by decide
  rcases family_descends (prefixWord ++ tailWord_892220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892293 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_892293 : Nat := 118140960795 + 892293 * 2 ^ 59
def prefixEnd_892293 : Nat := 4983230072969 + 3 ^ 40 * 892293 * 2
def baseEnd_892293 : Nat := 458175193642382633233925

theorem tailTrace_892293 : CollatzResearch.WordTrace tailWord_892293 prefixEnd_892293 458175193642382633233925 := by
  unfold tailWord_892293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32544599356382327357001533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21696399570921551571334355 32544599356382327357001533)
  ·
    refine ⟨12204224758643372758875575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32544599356382327357001533 12204224758643372758875575)
    ·
      refine ⟨18306337137965059138313363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12204224758643372758875575 18306337137965059138313363)
      ·
        refine ⟨27459505706947588707470045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18306337137965059138313363 27459505706947588707470045)
        ·
          refine ⟨10297314640105345765301267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27459505706947588707470045 10297314640105345765301267)
          ·
            refine ⟨15445971960158018647951901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10297314640105345765301267 15445971960158018647951901)
            ·
              refine ⟨5792239485059256992981963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15445971960158018647951901 5792239485059256992981963)
              ·
                refine ⟨8688359227588885489472945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792239485059256992981963 8688359227588885489472945)
                ·
                  refine ⟨6516269420691664117104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688359227588885489472945 6516269420691664117104709)
                  ·
                    refine ⟨1221800516379687021957133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516269420691664117104709 1221800516379687021957133)
                    ·
                      refine ⟨458175193642382633233925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221800516379687021957133 458175193642382633233925)
                      ·
                        rfl

theorem cell23_892293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_892293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892293 prefixEnd_892293 := by exact prefixLift 892293
  have htrace : WordTrace (prefixWord ++ tailWord_892293) baseStart_892293 baseEnd_892293 := by
    simpa [prefixWord, tailWord_892293, baseEnd_892293] using wordTrace_append hprefix tailTrace_892293
  have hstable : (prefixWord ++ tailWord_892293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892293).length < 2 ^ (prefixWord ++ tailWord_892293).sum := by decide
  have hdescent : baseEnd_892293 < baseStart_892293 := by decide
  rcases family_descends (prefixWord ++ tailWord_892293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892313 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 7]
def baseStart_892313 : Nat := 118140960795 + 892313 * 2 ^ 59
def prefixEnd_892313 : Nat := 4983230072969 + 3 ^ 40 * 892313 * 2
def baseEnd_892313 : Nat := 50909495917274728331537

theorem tailTrace_892313 : CollatzResearch.WordTrace tailWord_892313 prefixEnd_892313 50909495917274728331537 := by
  unfold tailWord_892313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545328816309870772729593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21696885877539913848486395 32545328816309870772729593)
  ·
    refine ⟨24408996612232403079547195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32545328816309870772729593 24408996612232403079547195)
    ·
      refine ⟨36613494918348604619320793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24408996612232403079547195 36613494918348604619320793)
      ·
        refine ⟨27460121188761453464490595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36613494918348604619320793 27460121188761453464490595)
        ·
          refine ⟨41190181783142180196735893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27460121188761453464490595 41190181783142180196735893)
          ·
            refine ⟨1930789771084789696721995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41190181783142180196735893 1930789771084789696721995)
            ·
              refine ⟨2896184656627184545082993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930789771084789696721995 2896184656627184545082993)
              ·
                refine ⟨2172138492470388408812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896184656627184545082993 2172138492470388408812245)
                ·
                  refine ⟨50909495917274728331537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2172138492470388408812245 50909495917274728331537)
                  ·
                    rfl

theorem cell23_892313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_892313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892313 prefixEnd_892313 := by exact prefixLift 892313
  have htrace : WordTrace (prefixWord ++ tailWord_892313) baseStart_892313 baseEnd_892313 := by
    simpa [prefixWord, tailWord_892313, baseEnd_892313] using wordTrace_append hprefix tailTrace_892313
  have hstable : (prefixWord ++ tailWord_892313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892313).length < 2 ^ (prefixWord ++ tailWord_892313).sum := by decide
  have hdescent : baseEnd_892313 < baseStart_892313 := by decide
  rcases family_descends (prefixWord ++ tailWord_892313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892323 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3]
def baseStart_892323 : Nat := 118140960795 + 892323 * 2 ^ 59
def prefixEnd_892323 : Nat := 4983230072969 + 3 ^ 40 * 892323 * 2
def baseEnd_892323 : Nat := 458190598062017515858787

theorem tailTrace_892323 : CollatzResearch.WordTrace tailWord_892323 prefixEnd_892323 458190598062017515858787 := by
  unfold tailWord_892323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545693546273642480593623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21697129030849094987062415 32545693546273642480593623)
  ·
    refine ⟨48818540319410463720890435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32545693546273642480593623 48818540319410463720890435)
    ·
      refine ⟨73227810479115695581335653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48818540319410463720890435 73227810479115695581335653)
      ·
        refine ⟨13730214464834192921500435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73227810479115695581335653 13730214464834192921500435)
        ·
          refine ⟨20595321697251289382250653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13730214464834192921500435 20595321697251289382250653)
          ·
            refine ⟨7723245636469233518343995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20595321697251289382250653 7723245636469233518343995)
            ·
              refine ⟨11584868454703850277515993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723245636469233518343995 11584868454703850277515993)
              ·
                refine ⟨8688651341027887708136995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11584868454703850277515993 8688651341027887708136995)
                ·
                  refine ⟨13032977011541831562205493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8688651341027887708136995 13032977011541831562205493)
                  ·
                    refine ⟨1221841594832046708956765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032977011541831562205493 1221841594832046708956765)
                    ·
                      refine ⟨458190598062017515858787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221841594832046708956765 458190598062017515858787)
                      ·
                        rfl

theorem cell23_892323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_892323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892323 prefixEnd_892323 := by exact prefixLift 892323
  have htrace : WordTrace (prefixWord ++ tailWord_892323) baseStart_892323 baseEnd_892323 := by
    simpa [prefixWord, tailWord_892323, baseEnd_892323] using wordTrace_append hprefix tailTrace_892323
  have hstable : (prefixWord ++ tailWord_892323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892323).length < 2 ^ (prefixWord ++ tailWord_892323).sum := by decide
  have hdescent : baseEnd_892323 < baseStart_892323 := by decide
  rcases family_descends (prefixWord ++ tailWord_892323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892328 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_892328 : Nat := 118140960795 + 892328 * 2 ^ 59
def prefixEnd_892328 : Nat := 4983230072969 + 3 ^ 40 * 892328 * 2
def baseEnd_892328 : Nat := 458193165465289996296265

theorem tailTrace_892328 : CollatzResearch.WordTrace tailWord_892328 prefixEnd_892328 458193165465289996296265 := by
  unfold tailWord_892328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16272937955627764167262819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21697250607503685556350425 16272937955627764167262819)
  ·
    refine ⟨24409406933441646250894229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16272937955627764167262819 24409406933441646250894229)
    ·
      refine ⟨1144190950005077168010667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24409406933441646250894229 1144190950005077168010667)
      ·
        refine ⟨1716286425007615752016001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144190950005077168010667 1716286425007615752016001)
        ·
          refine ⟨1287214818755711814012001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716286425007615752016001 1287214818755711814012001)
          ·
            refine ⟨965411114066783860509001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287214818755711814012001 965411114066783860509001)
            ·
              refine ⟨724058335550087895381751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965411114066783860509001 724058335550087895381751)
              ·
                refine ⟨1086087503325131843072627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724058335550087895381751 1086087503325131843072627)
                ·
                  refine ⟨1629131254987697764608941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086087503325131843072627 1629131254987697764608941)
                  ·
                    refine ⟨610924220620386661728353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629131254987697764608941 610924220620386661728353)
                    ·
                      refine ⟨458193165465289996296265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610924220620386661728353 458193165465289996296265)
                      ·
                        rfl

theorem cell23_892328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_892328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892328 prefixEnd_892328 := by exact prefixLift 892328
  have htrace : WordTrace (prefixWord ++ tailWord_892328) baseStart_892328 baseEnd_892328 := by
    simpa [prefixWord, tailWord_892328, baseEnd_892328] using wordTrace_append hprefix tailTrace_892328
  have hstable : (prefixWord ++ tailWord_892328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892328).length < 2 ^ (prefixWord ++ tailWord_892328).sum := by decide
  have hdescent : baseEnd_892328 < baseStart_892328 := by decide
  rcases family_descends (prefixWord ++ tailWord_892328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892341 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_892341 : Nat := 118140960795 + 892341 * 2 ^ 59
def prefixEnd_892341 : Nat := 4983230072969 + 3 ^ 40 * 892341 * 2
def baseEnd_892341 : Nat := 458199840713798445433705

theorem tailTrace_892341 : CollatzResearch.WordTrace tailWord_892341 prefixEnd_892341 458199840713798445433705 := by
  unfold tailWord_892341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546350060208431554748877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21697566706805621036499251 32546350060208431554748877)
  ·
    refine ⟨12204881272578161833030829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32546350060208431554748877 12204881272578161833030829)
    ·
      refine ⟨4576830477216810687386561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12204881272578161833030829 4576830477216810687386561)
      ·
        refine ⟨3432622857912608015539921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4576830477216810687386561 3432622857912608015539921)
        ·
          refine ⟨2574467143434456011654941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432622857912608015539921 2574467143434456011654941)
          ·
            refine ⟨965425178787921004370603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2574467143434456011654941 965425178787921004370603)
            ·
              refine ⟨1448137768181881506555905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965425178787921004370603 1448137768181881506555905)
              ·
                refine ⟨1086103326136411129916929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448137768181881506555905 1086103326136411129916929)
                ·
                  refine ⟨814577494602308347437697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086103326136411129916929 814577494602308347437697)
                  ·
                    refine ⟨610933120951731260578273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814577494602308347437697 610933120951731260578273)
                    ·
                      refine ⟨458199840713798445433705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 610933120951731260578273 458199840713798445433705)
                      ·
                        rfl

theorem cell23_892341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_892341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892341 prefixEnd_892341 := by exact prefixLift 892341
  have htrace : WordTrace (prefixWord ++ tailWord_892341) baseStart_892341 baseEnd_892341 := by
    simpa [prefixWord, tailWord_892341, baseEnd_892341] using wordTrace_append hprefix tailTrace_892341
  have hstable : (prefixWord ++ tailWord_892341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892341).length < 2 ^ (prefixWord ++ tailWord_892341).sum := by decide
  have hdescent : baseEnd_892341 < baseStart_892341 := by decide
  rcases family_descends (prefixWord ++ tailWord_892341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892343 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 4, 5]
def baseStart_892343 : Nat := 118140960795 + 892343 * 2 ^ 59
def prefixEnd_892343 : Nat := 4983230072969 + 3 ^ 40 * 892343 * 2
def baseEnd_892343 : Nat := 152733622558369145869565

theorem tailTrace_892343 : CollatzResearch.WordTrace tailWord_892343 prefixEnd_892343 152733622558369145869565 := by
  unfold tailWord_892343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546423006201185896321683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21697615337467457264214455 32546423006201185896321683)
  ·
    refine ⟨48819634509301778844482525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32546423006201185896321683 48819634509301778844482525)
    ·
      refine ⟨18307362940988167066680947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48819634509301778844482525 18307362940988167066680947)
      ·
        refine ⟨27461044411482250600021421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307362940988167066680947 27461044411482250600021421)
        ·
          refine ⟨10297891654305843975008033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27461044411482250600021421 10297891654305843975008033)
          ·
            refine ⟨7723418740729382981256025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10297891654305843975008033 7723418740729382981256025)
            ·
              refine ⟨5792564055547037235942019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723418740729382981256025 5792564055547037235942019)
              ·
                refine ⟨8688846083320555853913029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792564055547037235942019 8688846083320555853913029)
                ·
                  refine ⟨1629158640622604222608693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8688846083320555853913029 1629158640622604222608693)
                  ·
                    refine ⟨152733622558369145869565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1629158640622604222608693 152733622558369145869565)
                    ·
                      rfl

theorem cell23_892343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_892343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892343 prefixEnd_892343 := by exact prefixLift 892343
  have htrace : WordTrace (prefixWord ++ tailWord_892343) baseStart_892343 baseEnd_892343 := by
    simpa [prefixWord, tailWord_892343, baseEnd_892343] using wordTrace_append hprefix tailTrace_892343
  have hstable : (prefixWord ++ tailWord_892343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892343).length < 2 ^ (prefixWord ++ tailWord_892343).sum := by decide
  have hdescent : baseEnd_892343 < baseStart_892343 := by decide
  rcases family_descends (prefixWord ++ tailWord_892343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892363 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_892363 : Nat := 118140960795 + 892363 * 2 ^ 59
def prefixEnd_892363 : Nat := 4983230072969 + 3 ^ 40 * 892363 * 2
def baseEnd_892363 : Nat := 458211137288197359358603

theorem tailTrace_892363 : CollatzResearch.WordTrace tailWord_892363 prefixEnd_892363 458211137288197359358603 := by
  unfold tailWord_892363
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547152466128729312049743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21698101644085819541366495 32547152466128729312049743)
  ·
    refine ⟨48820728699193093968074615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32547152466128729312049743 48820728699193093968074615)
    ·
      refine ⟨73231093048789640952111923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48820728699193093968074615 73231093048789640952111923)
      ·
        refine ⟨109846639573184461428167885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73231093048789640952111923 109846639573184461428167885)
        ·
          refine ⟨41192489839944173035562957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109846639573184461428167885 41192489839944173035562957)
          ·
            refine ⟨15447183689979064888336109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41192489839944173035562957 15447183689979064888336109)
            ·
              refine ⟨5792693883742149333126041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15447183689979064888336109 5792693883742149333126041)
              ·
                refine ⟨4344520412806611999844531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792693883742149333126041 4344520412806611999844531)
                ·
                  refine ⟨6516780619209917999766797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344520412806611999844531 6516780619209917999766797)
                  ·
                    refine ⟨2443792732203719249912549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516780619209917999766797 2443792732203719249912549)
                    ·
                      refine ⟨458211137288197359358603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2443792732203719249912549 458211137288197359358603)
                      ·
                        rfl

theorem cell23_892363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_892363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892363 prefixEnd_892363 := by exact prefixLift 892363
  have htrace : WordTrace (prefixWord ++ tailWord_892363) baseStart_892363 baseEnd_892363 := by
    simpa [prefixWord, tailWord_892363, baseEnd_892363] using wordTrace_append hprefix tailTrace_892363
  have hstable : (prefixWord ++ tailWord_892363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892363).length < 2 ^ (prefixWord ++ tailWord_892363).sum := by decide
  have hdescent : baseEnd_892363 < baseStart_892363 := by decide
  rcases family_descends (prefixWord ++ tailWord_892363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892373 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_892373 : Nat := 118140960795 + 892373 * 2 ^ 59
def prefixEnd_892373 : Nat := 4983230072969 + 3 ^ 40 * 892373 * 2
def baseEnd_892373 : Nat := 152738757364914106744519

theorem tailTrace_892373 : CollatzResearch.WordTrace tailWord_892373 prefixEnd_892373 152738757364914106744519 := by
  unfold tailWord_892373
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547517196092501019913773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21698344797395000679942515 32547517196092501019913773)
  ·
    refine ⟨12205318948534687882467665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32547517196092501019913773 12205318948534687882467665)
    ·
      refine ⟨9153989211401015911850749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12205318948534687882467665 9153989211401015911850749)
      ·
        refine ⟨3432745954275380966944031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9153989211401015911850749 3432745954275380966944031)
        ·
          refine ⟨5149118931413071450416047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432745954275380966944031 5149118931413071450416047)
          ·
            refine ⟨7723678397119607175624071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149118931413071450416047 7723678397119607175624071)
            ·
              refine ⟨11585517595679410763436107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723678397119607175624071 11585517595679410763436107)
              ·
                refine ⟨17378276393519116145154161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585517595679410763436107 17378276393519116145154161)
                ·
                  refine ⟨13033707295139337108865621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17378276393519116145154161 13033707295139337108865621)
                  ·
                    refine ⟨152738757364914106744519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13033707295139337108865621 152738757364914106744519)
                    ·
                      rfl

theorem cell23_892373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_892373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892373 prefixEnd_892373 := by exact prefixLift 892373
  have htrace : WordTrace (prefixWord ++ tailWord_892373) baseStart_892373 baseEnd_892373 := by
    simpa [prefixWord, tailWord_892373, baseEnd_892373] using wordTrace_append hprefix tailTrace_892373
  have hstable : (prefixWord ++ tailWord_892373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892373).length < 2 ^ (prefixWord ++ tailWord_892373).sum := by decide
  have hdescent : baseEnd_892373 < baseStart_892373 := by decide
  rcases family_descends (prefixWord ++ tailWord_892373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892400 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_892400 : Nat := 118140960795 + 892400 * 2 ^ 59
def prefixEnd_892400 : Nat := 4983230072969 + 3 ^ 40 * 892400 * 2
def baseEnd_892400 : Nat := 458230136072413714595933

theorem tailTrace_892400 : CollatzResearch.WordTrace tailWord_892400 prefixEnd_892400 458230136072413714595933 := by
  unfold tailWord_892400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274250983497342315573327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21699001311329789754097769 16274250983497342315573327)
  ·
    refine ⟨24411376475246013473359991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16274250983497342315573327 24411376475246013473359991)
    ·
      refine ⟨36617064712869020210039987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24411376475246013473359991 36617064712869020210039987)
      ·
        refine ⟨54925597069303530315059981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36617064712869020210039987 54925597069303530315059981)
        ·
          refine ⟨20597098900988823868147493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54925597069303530315059981 20597098900988823868147493)
          ·
            refine ⟨3861956043935404475277655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20597098900988823868147493 3861956043935404475277655)
            ·
              refine ⟨5792934065903106712916483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861956043935404475277655 5792934065903106712916483)
              ·
                refine ⟨8689401098854660069374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792934065903106712916483 8689401098854660069374725)
                ·
                  refine ⟨1629262706035248763007761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8689401098854660069374725 1629262706035248763007761)
                  ·
                    refine ⟨1221947029526436572255821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1629262706035248763007761 1221947029526436572255821)
                    ·
                      refine ⟨458230136072413714595933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1221947029526436572255821 458230136072413714595933)
                      ·
                        rfl

theorem cell23_892400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_892400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892400 prefixEnd_892400 := by exact prefixLift 892400
  have htrace : WordTrace (prefixWord ++ tailWord_892400) baseStart_892400 baseEnd_892400 := by
    simpa [prefixWord, tailWord_892400, baseEnd_892400] using wordTrace_append hprefix tailTrace_892400
  have hstable : (prefixWord ++ tailWord_892400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892400).length < 2 ^ (prefixWord ++ tailWord_892400).sum := by decide
  have hdescent : baseEnd_892400 < baseStart_892400 := by decide
  rcases family_descends (prefixWord ++ tailWord_892400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892480 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_892480 : Nat := 118140960795 + 892480 * 2 ^ 59
def prefixEnd_892480 : Nat := 4983230072969 + 3 ^ 40 * 892480 * 2
def baseEnd_892480 : Nat := 152757071508257800531855

theorem tailTrace_892480 : CollatzResearch.WordTrace tailWord_892480 prefixEnd_892480 152757071508257800531855 := by
  unfold tailWord_892480
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275709903352429147029447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21700946537803238862705929 16275709903352429147029447)
  ·
    refine ⟨24413564855028643720544171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16275709903352429147029447 24413564855028643720544171)
    ·
      refine ⟨36620347282542965580816257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24413564855028643720544171 36620347282542965580816257)
      ·
        refine ⟨27465260461907224185612193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36620347282542965580816257 27465260461907224185612193)
        ·
          refine ⟨20598945346430418139209145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27465260461907224185612193 20598945346430418139209145)
          ·
            refine ⟨15449209009822813604406859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598945346430418139209145 15449209009822813604406859)
            ·
              refine ⟨23173813514734220406610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15449209009822813604406859 23173813514734220406610289)
              ·
                refine ⟨17380360136050665304957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23173813514734220406610289 17380360136050665304957717)
                ·
                  refine ⟨814704381377374936169893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17380360136050665304957717 814704381377374936169893)
                  ·
                    refine ⟨152757071508257800531855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814704381377374936169893 152757071508257800531855)
                    ·
                      rfl

theorem cell23_892480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_892480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892480 prefixEnd_892480 := by exact prefixLift 892480
  have htrace : WordTrace (prefixWord ++ tailWord_892480) baseStart_892480 baseEnd_892480 := by
    simpa [prefixWord, tailWord_892480, baseEnd_892480] using wordTrace_append hprefix tailTrace_892480
  have hstable : (prefixWord ++ tailWord_892480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892480).length < 2 ^ (prefixWord ++ tailWord_892480).sum := by decide
  have hdescent : baseEnd_892480 < baseStart_892480 := by decide
  rcases family_descends (prefixWord ++ tailWord_892480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892521 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 1, 2, 2]
def baseStart_892521 : Nat := 118140960795 + 892521 * 2 ^ 59
def prefixEnd_892521 : Nat := 4983230072969 + 3 ^ 40 * 892521 * 2
def baseEnd_892521 : Nat := 458292267231607741182877

theorem tailTrace_892521 : CollatzResearch.WordTrace tailWord_892521 prefixEnd_892521 458292267231607741182877 := by
  unfold tailWord_892521
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552915199556322296301417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21701943466370881530867611 32552915199556322296301417)
  ·
    refine ⟨24414686399667241722226063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32552915199556322296301417 24414686399667241722226063)
    ·
      refine ⟨36622029599500862583339095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24414686399667241722226063 36622029599500862583339095)
      ·
        refine ⟨54933044399251293875008643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36622029599500862583339095 54933044399251293875008643)
        ·
          refine ⟨82399566598876940812512965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54933044399251293875008643 82399566598876940812512965)
          ·
            refine ⟨15449918737289426402346181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82399566598876940812512965 15449918737289426402346181)
            ·
              refine ⟨2896859763241767450439909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15449918737289426402346181 2896859763241767450439909)
              ·
                refine ⟨543161205607831396957483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2896859763241767450439909 543161205607831396957483)
                ·
                  refine ⟨814741808411747095436225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543161205607831396957483 814741808411747095436225)
                  ·
                    refine ⟨611056356308810321577169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814741808411747095436225 611056356308810321577169)
                    ·
                      refine ⟨458292267231607741182877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611056356308810321577169 458292267231607741182877)
                      ·
                        rfl

theorem cell23_892521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 2, 2].length) (baseStart_892521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892521 prefixEnd_892521 := by exact prefixLift 892521
  have htrace : WordTrace (prefixWord ++ tailWord_892521) baseStart_892521 baseEnd_892521 := by
    simpa [prefixWord, tailWord_892521, baseEnd_892521] using wordTrace_append hprefix tailTrace_892521
  have hstable : (prefixWord ++ tailWord_892521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892521).length < 2 ^ (prefixWord ++ tailWord_892521).sum := by decide
  have hdescent : baseEnd_892521 < baseStart_892521 := by decide
  rcases family_descends (prefixWord ++ tailWord_892521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892534 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_892534 : Nat := 118140960795 + 892534 * 2 ^ 59
def prefixEnd_892534 : Nat := 4983230072969 + 3 ^ 40 * 892534 * 2
def baseEnd_892534 : Nat := 458298942480116190320317

theorem tailTrace_892534 : CollatzResearch.WordTrace tailWord_892534 prefixEnd_892534 458298942480116190320317 := by
  unfold tailWord_892534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034586834281826594782791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21702259565672817011016437 2034586834281826594782791)
  ·
    refine ⟨3051880251422739892174187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034586834281826594782791 3051880251422739892174187)
    ·
      refine ⟨4577820377134109838261281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051880251422739892174187 4577820377134109838261281)
      ·
        refine ⟨3433365282850582378695961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577820377134109838261281 3433365282850582378695961)
        ·
          refine ⟨2575023962137936784021971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433365282850582378695961 2575023962137936784021971)
          ·
            refine ⟨3862535943206905176032957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575023962137936784021971 3862535943206905176032957)
            ·
              refine ⟨1448450978702589441012359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3862535943206905176032957 1448450978702589441012359)
              ·
                refine ⟨2172676468053884161518539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448450978702589441012359 2172676468053884161518539)
                ·
                  refine ⟨3259014702080826242277809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172676468053884161518539 3259014702080826242277809)
                  ·
                    refine ⟨2444261026560619681708357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259014702080826242277809 2444261026560619681708357)
                    ·
                      refine ⟨458298942480116190320317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2444261026560619681708357 458298942480116190320317)
                      ·
                        rfl

theorem cell23_892534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_892534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892534 prefixEnd_892534 := by exact prefixLift 892534
  have htrace : WordTrace (prefixWord ++ tailWord_892534) baseStart_892534 baseEnd_892534 := by
    simpa [prefixWord, tailWord_892534, baseEnd_892534] using wordTrace_append hprefix tailTrace_892534
  have hstable : (prefixWord ++ tailWord_892534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892534).length < 2 ^ (prefixWord ++ tailWord_892534).sum := by decide
  have hdescent : baseEnd_892534 < baseStart_892534 := by decide
  rcases family_descends (prefixWord ++ tailWord_892534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892554 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_892554 : Nat := 118140960795 + 892554 * 2 ^ 59
def prefixEnd_892554 : Nat := 4983230072969 + 3 ^ 40 * 892554 * 2
def baseEnd_892554 : Nat := 458309212093206112070225

theorem tailTrace_892554 : CollatzResearch.WordTrace tailWord_892554 prefixEnd_892554 458309212093206112070225 := by
  unfold tailWord_892554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138529702109192233063179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21702745872291179288168477 8138529702109192233063179)
  ·
    refine ⟨12207794553163788349594769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138529702109192233063179 12207794553163788349594769)
    ·
      refine ⟨9155845914872841262196077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12207794553163788349594769 9155845914872841262196077)
      ·
        refine ⟨3433442218077315473323529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9155845914872841262196077 3433442218077315473323529)
        ·
          refine ⟨2575081663557986604992647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433442218077315473323529 2575081663557986604992647)
          ·
            refine ⟨3862622495336979907488971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575081663557986604992647 3862622495336979907488971)
            ·
              refine ⟨5793933743005469861233457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862622495336979907488971 5793933743005469861233457)
              ·
                refine ⟨4345450307254102395925093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793933743005469861233457 4345450307254102395925093)
                ·
                  refine ⟨814771932610144199235955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4345450307254102395925093 814771932610144199235955)
                  ·
                    refine ⟨1222157898915216298853933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 814771932610144199235955 1222157898915216298853933)
                    ·
                      refine ⟨458309212093206112070225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1222157898915216298853933 458309212093206112070225)
                      ·
                        rfl

theorem cell23_892554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_892554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892554 prefixEnd_892554 := by exact prefixLift 892554
  have htrace : WordTrace (prefixWord ++ tailWord_892554) baseStart_892554 baseEnd_892554 := by
    simpa [prefixWord, tailWord_892554, baseEnd_892554] using wordTrace_append hprefix tailTrace_892554
  have hstable : (prefixWord ++ tailWord_892554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892554).length < 2 ^ (prefixWord ++ tailWord_892554).sum := by decide
  have hdescent : baseEnd_892554 < baseStart_892554 := by decide
  rcases family_descends (prefixWord ++ tailWord_892554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892598 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_892598 : Nat := 118140960795 + 892598 * 2 ^ 59
def prefixEnd_892598 : Nat := 4983230072969 + 3 ^ 40 * 892598 * 2
def baseEnd_892598 : Nat := 458331805242003939920023

theorem tailTrace_892598 : CollatzResearch.WordTrace tailWord_892598 prefixEnd_892598 458331805242003939920023 := by
  unfold tailWord_892598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034732726267335277928403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21703815746851576297902965 2034732726267335277928403)
  ·
    refine ⟨3052099089401002916892605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034732726267335277928403 3052099089401002916892605)
    ·
      refine ⟨1144537158525376093834727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3052099089401002916892605 1144537158525376093834727)
      ·
        refine ⟨1716805737788064140752091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144537158525376093834727 1716805737788064140752091)
        ·
          refine ⟨2575208606682096211128137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716805737788064140752091 2575208606682096211128137)
          ·
            refine ⟨1931406455011572158346103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2575208606682096211128137 1931406455011572158346103)
            ·
              refine ⟨2897109682517358237519155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931406455011572158346103 2897109682517358237519155)
              ·
                refine ⟨4345664523776037356278733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897109682517358237519155 4345664523776037356278733)
                ·
                  refine ⟨1629624196416014008604525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4345664523776037356278733 1629624196416014008604525)
                  ·
                    refine ⟨611109073656005253226697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629624196416014008604525 611109073656005253226697)
                    ·
                      refine ⟨458331805242003939920023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611109073656005253226697 458331805242003939920023)
                      ·
                        rfl

theorem cell23_892598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_892598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892598 prefixEnd_892598 := by exact prefixLift 892598
  have htrace : WordTrace (prefixWord ++ tailWord_892598) baseStart_892598 baseEnd_892598 := by
    simpa [prefixWord, tailWord_892598, baseEnd_892598] using wordTrace_append hprefix tailTrace_892598
  have hstable : (prefixWord ++ tailWord_892598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892598).length < 2 ^ (prefixWord ++ tailWord_892598).sum := by decide
  have hdescent : baseEnd_892598 < baseStart_892598 := by decide
  rcases family_descends (prefixWord ++ tailWord_892598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
